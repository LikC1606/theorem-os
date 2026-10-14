import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';

const roots: string[] = [];
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('resolved mathematics environment', () => {
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
