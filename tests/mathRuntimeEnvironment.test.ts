import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('resolved mathematics environment', () => {
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
