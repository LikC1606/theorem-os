import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { checkCodexProviderConnectivity } from '../src/runtime/codexConnectivity';

const run = vi.hoisted(() => vi.fn());
vi.mock('../src/math/mathProcess', () => ({ runMathProcess: run }));
const roots: string[] = [];
afterEach(() => { vi.clearAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function profile() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-connectivity-')); roots.push(root);
  fs.writeFileSync(path.join(root, 'config.toml'), 'model_provider="local"\n[model_providers.local]\nbase_url="http://provider/v1"\n');
  return root;
}
describe('provider connectivity without inference', () => {
  it.each([200, 401, 404, 405])('accepts HTTP %s as evidence of a reachable route', async httpStatus => {
    run.mockResolvedValue({ exitCode: 0, stdout: String(httpStatus) });
    const env = { HTTP_PROXY: 'http://relay:18082' };
    expect(await checkCodexProviderConnectivity({ profile: profile(), env })).toEqual({ status: 'reachable', httpStatus });
    expect(run.mock.calls[0][1]).toContain('--head');
    expect(run.mock.calls[0][1].at(-1)).toBe('http://provider/v1/models');
    expect(run.mock.calls[0][2].env).toBe(env);
    expect(run.mock.calls[0][1]).not.toContain('--header');
  });
  it.each([{ exitCode: 7, stdout: '000' }, { exitCode: 28, stdout: '000' }, { exitCode: 0, stdout: '407' }])(
    'blocks a broken or unauthenticated proxy route: %s', async result => {
      run.mockResolvedValue(result);
      expect(await checkCodexProviderConnectivity({ profile: profile(), env: {} })).toMatchObject({ status: 'unavailable' });
    });
});
