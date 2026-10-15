import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { diagnoseEnvironment, formatDoctorReport } from '../src/math/doctor';

const mocks = vi.hoisted(() => ({ run: vi.fn(), network: vi.fn(), readiness: vi.fn(), packages: vi.fn(), prepare: vi.fn() }));
vi.mock('../src/math/mathProcess', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProcess')>(), runMathProcess: mocks.run,
}));
vi.mock('../src/runtime/codexConnectivity', () => ({ checkCodexProviderConnectivity: mocks.network }));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: mocks.readiness }));
vi.mock('../src/math/verifier', () => ({ resolveMathematicsLakePackagesCache: mocks.packages }));
vi.mock('../src/math/mathProofEnvironment', () => ({ prepareMathProofEnvironment: mocks.prepare }));
const roots: string[] = [];
afterEach(() => { vi.resetAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });
function fixture() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-doctor-')); roots.push(root);
  for (const name of ['bun', 'node', 'git', 'lean', 'lake', 'codex', 'bwrap'])
    fs.writeFileSync(path.join(root, name), '', { mode: 0o700 });
  const file = path.join(root, 'math.env'); fs.writeFileSync(file, '');
  const env = { PATH: root, CODEX_HOME: path.join(root, 'profile'), DEEPSCIENTIST_MATH_ENV_FILE: file };
  mocks.run.mockImplementation(async (command: string, args: string[]) => ({ exitCode: 0, stdout:
    command.endsWith('/node') ? 'v22.1.0' : command.endsWith('/bun') ? '1.2.0' : '', stderr: '' }));
  return { root, env };
}
describe('environment doctor', () => {
  it('checks every pinned dependency before warming the reusable image and disposes its mount', async () => {
    const { root, env } = fixture();
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.35.0-rc3\n');
    fs.writeFileSync(path.join(root, 'lake-manifest.json'), JSON.stringify({ packages: [{ name: 'TauCeti', rev: 'pinned' }] }));
    mocks.readiness.mockReturnValue({ status: 'ready', toolchain: 'leanprover/lean4:v4.35.0-rc3' });
    expect((await diagnoseEnvironment({ env, project: root, prepare: true })).checks)
      .toContainEqual(expect.objectContaining({ id: 'project-dependencies', status: 'fail', fix: expect.stringContaining('TauCeti@pinned') }));
    expect(mocks.prepare).not.toHaveBeenCalled();
    mocks.packages.mockReturnValue(root);
    const dispose = vi.fn().mockResolvedValue(undefined);
    mocks.prepare.mockResolvedValue({ stats: { files: 2, bytes: 123 }, dispose });
    const cacheDir = path.join(root, 'image-cache');
    expect((await diagnoseEnvironment({ env, project: root, prepare: true, cacheDir })).checks)
      .toContainEqual(expect.objectContaining({ id: 'project-image', status: 'pass' }));
    expect(mocks.prepare).toHaveBeenCalledWith(root, root, expect.objectContaining({ cacheRoot: cacheDir }));
    expect(dispose).toHaveBeenCalledOnce();
  });

  it('provides actionable failures for missing executables and incompatible versions', async () => {
    const { root, env } = fixture();
    fs.unlinkSync(path.join(root, 'codex'));
    mocks.run.mockResolvedValue({ exitCode: 0, stdout: 'v20.1.0' });
    const report = await diagnoseEnvironment({ env });
    expect(report.status).toBe('needs_attention');
    expect(report.checks).toContainEqual(expect.objectContaining({ id: 'codex', status: 'fail', fix: expect.stringContaining('--codex') }));
    expect(report.checks).toContainEqual(expect.objectContaining({ id: 'node-version', status: 'fail' }));
  });
  it('checks login with the selected profile and never starts an agent or a network probe by default', async () => {
    const { env } = fixture();
    const report = await diagnoseEnvironment({ env });
    expect(report.checks.find(check => check.id === 'codex-auth')?.status).toBe('pass');
    expect(mocks.run).toHaveBeenCalledWith(expect.stringContaining('/codex'), ['login', 'status'],
      expect.objectContaining({ env: expect.objectContaining({ CODEX_HOME: env.CODEX_HOME }) }));
    expect(mocks.run.mock.calls.every(([, args]) => !args.includes('app-server') && !args.includes('exec'))).toBe(true);
    expect(mocks.network).not.toHaveBeenCalled();
    expect(formatDoctorReport(report)).toContain('startup preflight');
  });
  it('reports authentication and namespace failures without echoing provider output', async () => {
    const { env } = fixture();
    const run = mocks.run.getMockImplementation()!;
    mocks.run.mockImplementation((command, args, options) =>
      args.includes('login') || args.includes('--unshare-all')
        ? Promise.resolve({ exitCode: 1, stdout: 'SECRET', stderr: 'SECRET' }) : run(command, args, options));
    const report = await diagnoseEnvironment({ env });
    expect(report.checks).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: 'codex-auth', status: 'fail' }), expect.objectContaining({ id: 'sandbox', status: 'fail' }),
    ]));
    expect(JSON.stringify(report)).not.toContain('SECRET');
  });
  it('rejects an explicitly missing environment file', async () => {
    const { env } = fixture(); env.DEEPSCIENTIST_MATH_ENV_FILE += '.missing';
    expect(await diagnoseEnvironment({ env })).toMatchObject({ status: 'needs_attention', checks:
      expect.arrayContaining([expect.objectContaining({ id: 'environment', status: 'fail' })]) });
    expect(mocks.run).not.toHaveBeenCalled();
  });
  it('does not launch the compiler for a missing project toolchain', async () => {
    const { root, env } = fixture();
    fs.writeFileSync(path.join(root, 'elan'), '', { mode: 0o700 });
    fs.unlinkSync(path.join(root, 'lean'));
    fs.symlinkSync(path.join(root, 'elan'), path.join(root, 'lean'));
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    const report = await diagnoseEnvironment({ env, project: root });
    expect(report.checks).toContainEqual(expect.objectContaining({ id: 'project-toolchain', status: 'fail' }));
    expect(mocks.readiness).not.toHaveBeenCalled();
  });
  it('uses the existing credential-free provider check only when requested', async () => {
    const { env } = fixture(); mocks.network.mockResolvedValue({ status: 'reachable', httpStatus: 401 });
    const report = await diagnoseEnvironment({ env, network: true });
    expect(mocks.network).toHaveBeenCalledOnce();
    expect(report.checks).toContainEqual(expect.objectContaining({ id: 'provider', status: 'pass' }));
  });
  it('can check the Lean-only replay without requiring a Codex installation or login', async () => {
    const { root, env } = fixture(); fs.unlinkSync(path.join(root, 'codex'));
    const report = await diagnoseEnvironment({ env, leanOnly: true });
    expect(report.checks.some(check => check.id === 'codex' || check.id === 'codex-auth')).toBe(false);
    expect(report.status).toBe('ready');
    expect(mocks.network).not.toHaveBeenCalled();
  });
  it('checks a bare compiler even when an unrelated Elan installation is on PATH', async () => {
    const { root, env } = fixture();
    fs.writeFileSync(path.join(root, 'elan'), '', { mode: 0o700 });
    fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.33.0\n');
    mocks.readiness.mockReturnValue({ status: 'ready', toolchain: 'leanprover/lean4:v4.33.0' });
    const report = await diagnoseEnvironment({ env, project: root, leanOnly: true });
    expect(report.checks).toContainEqual(expect.objectContaining({ id: 'project-toolchain', status: 'pass' }));
    expect(mocks.readiness).toHaveBeenCalledOnce();
  });
});
