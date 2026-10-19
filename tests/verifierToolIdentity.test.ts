import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { formalVerificationToolIdentity } from '../src/math/verifier';

describe('formal verification tool identity', () => {
  let root: string, tools: string, project: string, env: NodeJS.ProcessEnv;
  const executable = (file: string, body = '#!/bin/sh\nexit 71\n') => {
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, body, { mode: 0o700 });
    return file;
  };
  function fakeElan(name: string) {
    const home = path.join(root, name);
    executable(path.join(home, 'bin', 'elan'), '#!/bin/sh\n' +
      'if [ "$1" != "which" ] || [ "$2" != "lean" ]; then exit 99; fi\n' +
      'printf "which lean\\n" >> "$ELAN_HOME/probes"\n' +
      'IFS= read -r selected < "$ELAN_HOME/selected-toolchain" || exit 98\n' +
      'printf "%s/toolchains/%s/bin/lean\\n" "$ELAN_HOME" "$selected"\n');
    for (const version of ['first', 'second']) for (const command of ['lean', 'lake'])
      executable(path.join(home, 'toolchains', version, 'bin', command));
    fs.writeFileSync(path.join(home, 'selected-toolchain'), 'first\n');
    return home;
  }
  const identity = (environment = env) => formalVerificationToolIdentity(project, environment);

  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'verifier-tool-identity-')));
    tools = path.join(root, 'tools');
    project = path.join(root, 'project');
    fs.mkdirSync(project);
    for (const command of ['lean', 'lake']) executable(path.join(tools, command));
    env = { PATH: tools, ELAN_HOME: path.join(root, 'no-elan-home'),
      DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS: path.join(root, 'no-trusted-elan-home') };
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  it('returns a stable identity for unchanged actual executable paths and bytes', () => {
    const first = identity();
    expect(first).toMatch(/^[a-f0-9]{64}$/u);
    expect(identity()).toBe(first);
  });

  it.each(['lean', 'lake'] as const)('invalidates an in-place %s rewrite with the same size and restored mtime', command => {
    const first = identity(), file = path.join(tools, command), before = fs.statSync(file);
    fs.writeFileSync(file, '#!/bin/sh\nexit 72\n');
    fs.utimesSync(file, before.atimeMs / 1000, before.mtimeMs / 1000);
    expect(fs.statSync(file).size).toBe(before.size);
    const changed = identity();
    expect(changed).toBeDefined();
    expect(changed).not.toBe(first);
    expect(identity()).toBe(changed);
  });

  it.each(['lean', 'lake'] as const)('invalidates an atomic %s replacement at the unchanged path', command => {
    const first = identity(), file = path.join(tools, command), before = fs.statSync(file);
    const replacement = executable(file + '.replacement', '#!/bin/sh\nexit 72\n');
    fs.utimesSync(replacement, before.atimeMs / 1000, before.mtimeMs / 1000);
    fs.renameSync(replacement, file);
    expect(fs.statSync(file).size).toBe(before.size);
    expect(fs.statSync(file).ino).not.toBe(before.ino);
    const changed = identity();
    expect(changed).toBeDefined();
    expect(changed).not.toBe(first);
  });

  it.each(['lean', 'lake'] as const)('disables reuse if the selected PATH %s executable disappears', command => {
    expect(identity()).toBeDefined();
    fs.rmSync(path.join(tools, command));
    expect(identity()).toBeUndefined();
  });

  it('disables reuse for non-executable files, directories and relative PATH entries', () => {
    fs.chmodSync(path.join(tools, 'lean'), 0o600);
    expect(identity()).toBeUndefined();
    fs.rmSync(path.join(tools, 'lean'));
    fs.mkdirSync(path.join(tools, 'lean'));
    expect(identity()).toBeUndefined();
    for (const PATH of ['', '.', `${tools}${path.delimiter}.`, `relative${path.delimiter}${tools}`])
      expect(identity({ ...env, PATH })).toBeUndefined();
  });

  it('tracks a PATH symlink retargeting to a different real executable', () => {
    const first = identity(), file = path.join(tools, 'lean');
    const replacement = executable(path.join(root, 'another-toolchain', 'lean'));
    fs.rmSync(file);
    fs.symlinkSync(replacement, file);
    const changed = identity();
    expect(changed).toBeDefined();
    expect(changed).not.toBe(first);
  });

  it('tracks the toolchain selected by fake elan while PATH and ELAN_HOME remain unchanged', () => {
    const home = fakeElan('elan-home'), environment = { ...env, ELAN_HOME: home };
    const first = identity(environment);
    expect(first).toBeDefined();
    expect(identity(environment)).toBe(first);
    fs.writeFileSync(path.join(home, 'selected-toolchain'), 'second\n');
    const second = identity(environment);
    expect(second).toBeDefined();
    expect(second).not.toBe(first);
    expect(fs.readFileSync(path.join(home, 'probes'), 'utf8')).toBe('which lean\n'.repeat(3));
    const selected = path.join(home, 'toolchains', 'second', 'bin', 'lean');
    fs.writeFileSync(selected, '#!/bin/sh\nexit 72\n');
    expect(identity(environment)).not.toBe(second);
  });

  it('tracks ELAN_HOME selection even when the PATH wrappers have identical bytes', () => {
    const firstHome = fakeElan('first-elan-home'), secondHome = fakeElan('second-elan-home');
    const first = identity({ ...env, ELAN_HOME: firstHome });
    const second = identity({ ...env, ELAN_HOME: secondHome });
    expect(first).toBeDefined();
    expect(second).toBeDefined();
    expect(first).not.toBe(second);
  });

  it('disables reuse when fake elan cannot identify a complete selected toolchain', () => {
    const home = fakeElan('elan-home'), environment = { ...env, ELAN_HOME: home };
    expect(identity(environment)).toBeDefined();
    fs.rmSync(path.join(home, 'toolchains', 'first', 'bin', 'lake'));
    expect(identity(environment)).toBeUndefined();
    fs.writeFileSync(path.join(home, 'selected-toolchain'), 'missing\n');
    expect(identity(environment)).toBeUndefined();
    fs.rmSync(path.join(home, 'selected-toolchain'));
    expect(identity(environment)).toBeUndefined();
  });
});
