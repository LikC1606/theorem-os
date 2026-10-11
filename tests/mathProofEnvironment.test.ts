import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { prepareMathProofEnvironment } from '../src/math/mathProofEnvironment';
import { MATH_SEALED_ENVIRONMENT_HELPER } from '../src/math/mathSealedEnvironmentHelper';

describe.skipIf(process.platform !== 'linux')('proof environment tool preflight', () => {
  let directory: string;
  let tools: string;
  let project: string;
  let packages: string;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'proof-environment-tools-')));
    tools = path.join(directory, 'tools');
    project = path.join(directory, 'project');
    packages = path.join(directory, 'packages');
    for (const root of [tools, project, packages]) fs.mkdirSync(root);
    fs.writeFileSync(path.join(packages, 'Dependency.lean'), 'example : True := by trivial\n');
    for (const name of ['squashfuse', 'fusermount', 'mksquashfs']) {
      fs.writeFileSync(path.join(tools, name), '#!/bin/sh\nexit 99\n', { mode: 0o700 });
    }
  });
  afterEach(() => {
    vi.restoreAllMocks();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['squashfuse', 'fusermount', 'mksquashfs'])(
    'rejects missing %s before creating or copying a dependency snapshot', async name => {
      fs.unlinkSync(path.join(tools, name));
      const temporary = vi.spyOn(fs, 'mkdtempSync');
      const phases: string[] = [];
      await expect(prepareMathProofEnvironment(project, packages, {
        env: { PATH: tools }, onProgress: phase => phases.push(phase),
      })).rejects.toThrow('requires squashfuse, fusermount, and mksquashfs');
      expect(phases).toEqual(['enumerating_dependencies', 'cache_miss']);
      expect(temporary).not.toHaveBeenCalled();
    }
  );

  it('requires the compressor for a new image but allows mounting cached images without it', () => {
    fs.unlinkSync(path.join(tools, 'mksquashfs'));
    for (const mode of ['mount', 'build']) {
      const probe = spawnSync('/usr/bin/python3', ['-c', MATH_SEALED_ENVIRONMENT_HELPER, '--check-tools', mode], {
        env: { PATH: tools }, encoding: 'utf8', timeout: 5000, maxBuffer: 4096,
      });
      expect(probe.status).toBe(mode === 'mount' ? 0 : 1);
      expect(JSON.parse(probe.stdout).state).toBe(mode === 'mount' ? 'ready' : 'blocked');
    }
  });

  it('accepts snapfuse and fusermount3 without invoking any of the tools', () => {
    fs.renameSync(path.join(tools, 'squashfuse'), path.join(tools, 'snapfuse'));
    fs.renameSync(path.join(tools, 'fusermount'), path.join(tools, 'fusermount3'));
    const probe = spawnSync('/usr/bin/python3', ['-c', MATH_SEALED_ENVIRONMENT_HELPER, '--check-tools', 'build'], {
      env: { PATH: tools }, encoding: 'utf8', timeout: 5000, maxBuffer: 4096,
    });
    expect(probe.status).toBe(0);
    expect(JSON.parse(probe.stdout)).toEqual({ state: 'ready' });
  });
});
