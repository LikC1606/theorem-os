import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('resolved mathematics environment', () => {
  it.skipIf(process.platform !== 'linux')('runs Git without a supplied PATH while retaining pinned tool priority', () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    for (const source of [{}, { DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT: '/pinned/tools', ELAN_HOME: '/pinned/elan' }]) {
      const env = resolveMathematicsRuntimeEnvironment(source, path.join(root, 'absent.env'));
      const result = spawnSync('git', ['--version'], { env, encoding: 'utf8', timeout: 5000 });
      expect(result.error).toBeUndefined();
      expect(result.status).toBe(0);
      expect(result.stdout).toMatch(/^git version /u);
      expect(env.HOME).toBeUndefined();
      if (source.ELAN_HOME)
        expect(env.PATH?.split(path.delimiter).slice(0, 3)).toEqual(['/pinned/tools/bin', '/pinned/tools', '/pinned/elan/bin']);
    }
  });

  it.skipIf(process.platform !== 'linux')('runs Git when a local env file extends an unset PATH', () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, 'math.env');
    fs.writeFileSync(file, 'ELAN_HOME=/pinned/elan\nPATH=${ELAN_HOME}/bin:${PATH}\n');
    const env = resolveMathematicsRuntimeEnvironment({}, file);
    const result = spawnSync('git', ['--version'], { env, encoding: 'utf8', timeout: 5000 });
    expect(result.error).toBeUndefined();
    expect(result.status).toBe(0);
    expect(result.stdout).toMatch(/^git version /u);
    expect(env.PATH?.split(path.delimiter)[0]).toBe('/pinned/elan/bin');
    expect(env.HOME).toBeUndefined();
  });

  it.each(['/restricted/bin', ''])('keeps the supplied PATH %j restricted when a local env file extends it', suppliedPath => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, 'math.env');
    fs.writeFileSync(file, 'ELAN_HOME=/pinned/elan\nPATH=${ELAN_HOME}/bin:${PATH}\n');
    const env = resolveMathematicsRuntimeEnvironment({ PATH: suppliedPath }, file);
    expect(env.PATH?.split(path.delimiter)).toEqual(
      ['/pinned/elan/bin', suppliedPath, ...(process.platform === 'linux' ? ['/usr/sbin'] : [])].filter(Boolean));
  });

  it.each(['/restricted/bin', ''])('does not broaden the explicit PATH %j to system defaults', suppliedPath => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const env = resolveMathematicsRuntimeEnvironment({ PATH: suppliedPath }, path.join(root, 'absent.env'));
    expect(env.PATH?.split(path.delimiter)).toEqual(
      [suppliedPath, ...(process.platform === 'linux' ? ['/usr/sbin'] : [])].filter(Boolean));
  });

  it.each(['/restricted/bin', ''])('preserves the frozen PATH %j over caller defaults', pinnedPath => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, 'math.json');
    fs.writeFileSync(file, JSON.stringify(projectMathematicsRuntimeEnvironment({
      DEEPSCIENTIST_MATH_ENV_FILE: file, PATH: pinnedPath,
    })));
    const env = resolveMathematicsRuntimeEnvironment({ DEEPSCIENTIST_MATH_ENV_FILE: file, PATH: '/usr/bin:/bin' });
    expect(env.PATH?.split(path.delimiter)).toEqual(
      [pinnedPath, ...(process.platform === 'linux' ? ['/usr/sbin'] : [])].filter(Boolean));
  });

  it('finds pinned tool bin directories and Linux administration tools while retaining explicit PATH priority', () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const env = resolveMathematicsRuntimeEnvironment({ PATH: '/custom/bin:/usr/bin',
      DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT: '/pinned/tools', ELAN_HOME: '/pinned/elan' }, path.join(root, 'absent.env'));
    expect(env.PATH?.split(path.delimiter).slice(0, 3)).toEqual(['/pinned/tools/bin', '/pinned/tools', '/pinned/elan/bin']);
    expect(env.PATH?.split(path.delimiter).indexOf('/custom/bin')).toBeLessThan(env.PATH!.split(path.delimiter).indexOf('/usr/bin'));
    if (process.platform === 'linux') expect(env.PATH?.split(path.delimiter)).toContain('/usr/sbin');
  });

  it('freezes the runner proxy route for subprocesses and resume', () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, 'math.json');
    fs.writeFileSync(file, JSON.stringify(projectMathematicsRuntimeEnvironment({
      DEEPSCIENTIST_MATH_ENV_FILE: file, HTTP_PROXY: 'http://runner:18082',
    })));
    const env = resolveMathematicsRuntimeEnvironment({ DEEPSCIENTIST_MATH_ENV_FILE: file,
      HTTP_PROXY: 'http://127.0.0.1:18081', https_proxy: 'http://obsolete:18081' });
    expect(env.HTTP_PROXY).toBe('http://runner:18082');
    expect(env.https_proxy).toBeUndefined();
    expect(projectMathematicsRuntimeEnvironment(env).HTTP_PROXY).toBe('http://runner:18082');
  });

  it('passes the configured verifier concurrency through a local environment file', () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, 'math.env');
    fs.writeFileSync(file, 'DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY=1\n');
    const env = resolveMathematicsRuntimeEnvironment({}, file);
    expect(env.DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY).toBe('1');
    expect(projectMathematicsRuntimeEnvironment(env).DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY).toBe('1');
  });

  it.each(['.env', '.json'])('keeps a host snapshot after its %s defaults change', extension => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-env-')); roots.push(root);
    const file = path.join(root, `math${extension}`);
    const write = (value: string) => fs.writeFileSync(file, extension === '.json'
      ? JSON.stringify(projectMathematicsRuntimeEnvironment({ LEAN_PATH: value, DEEPSCIENTIST_MATH_ENV_FILE: file }))
      : `LEAN_PATH=${value}\n`);
    write('pinned');
    const env = resolveMathematicsRuntimeEnvironment({ DEEPSCIENTIST_MATH_ENV_FILE: file, API_TOKEN: 'private' });
    write('changed');
    const derived = resolveMathematicsRuntimeEnvironment({ ...env, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: '/host/corpus', API_TOKEN: 'private' });
    expect(derived.LEAN_PATH).toBe('pinned');
    expect(derived.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS).toBe('/host/corpus');
    expect(derived.API_TOKEN).toBeUndefined();
    expect(Object.isFrozen(derived)).toBe(true);
    expect(resolveMathematicsRuntimeEnvironment({ DEEPSCIENTIST_MATH_ENV_FILE: file }).LEAN_PATH).toBe('changed');
    const next = path.join(root, 'next.env'); fs.writeFileSync(next, 'DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS=/next\n');
    expect(resolveMathematicsRuntimeEnvironment(env, next).DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS).toBe('/next');
  });
});
