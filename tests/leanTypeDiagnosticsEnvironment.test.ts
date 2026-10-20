import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { checkLeanType } from '../src/math/leanTypeDiagnostics';

const { resolve, diagnostics } = vi.hoisted(() => ({ resolve: vi.fn(), diagnostics: vi.fn() }));
vi.mock('../src/math/mathProofEnvironment', () => ({ resolveMathProofEnvironment: resolve }));
vi.mock('../src/math/leanDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: diagnostics,
}));

describe('sealed type query environment binding', () => {
  let directory: string, project: string, packages: string, verify: ReturnType<typeof vi.fn>;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'type-query-binding-')));
    project = path.join(directory, 'worker/generated/problem'); packages = path.join(directory, 'sealed-packages');
    fs.mkdirSync(project, { recursive: true }); fs.mkdirSync(path.join(packages, 'dependency'), { recursive: true });
    fs.writeFileSync(path.join(project, 'Submission.lean'), 'namespace Geometry\ntheorem original : True := by sorry\nend Geometry\n');
    fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    fs.writeFileSync(path.join(project, 'lakefile.toml'), 'name = "binding_fixture"\n');
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ name: 'binding_fixture', packages: [{ name: 'dependency' }] }));
    verify = vi.fn(); resolve.mockReset().mockReturnValue({ packagesRoot: packages, identity: 'b'.repeat(64), verify });
    diagnostics.mockReset().mockImplementation(async input => {
      expect(input.timeoutMs).toBe(Infinity);
      expect(fs.realpathSync(path.join(input.projectRoot, '.lake/packages'))).toBe(packages);
      const overrides = JSON.parse(fs.readFileSync(path.join(input.projectRoot, '.lake/package-overrides.json'), 'utf8'));
      expect(overrides.packages[0].dir).toBe(path.join(input.projectRoot, '.lake/packages/dependency'));
      fs.writeFileSync(path.join(input.projectRoot, '.lake/type-diagnostic.json'), JSON.stringify({ type: 'True' }));
      return { exitCode: 0, timedOut: false, phases: [], diagnosticArtifacts: [], stdout: '', stderr: '' };
    });
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });
  const check = () => checkLeanType({ projectRoot: project, file: 'Submission.lean', context: 'Geometry.original', type: 'True', timeoutMs: Infinity });

  it.each(['missing', 'obsolete'] as const)('binds the fixed dependency root for a nested clone when the worker package link is %s', async state => {
    if (state === 'obsolete') {
      const obsolete = path.join(directory, 'obsolete-packages'); fs.mkdirSync(obsolete);
      fs.mkdirSync(path.join(project, '.lake')); fs.symlinkSync(obsolete, path.join(project, '.lake/packages'), 'dir');
    }
    const before = fs.readFileSync(path.join(project, 'Submission.lean'));
    const result = await check();
    expect(result).toMatchObject({ status: 'elaborated', type: 'True', proofAcceptance: 'not-assessed' });
    expect(verify).toHaveBeenCalledTimes(2);
    const clone = diagnostics.mock.calls[0][0].projectRoot;
    expect(resolve.mock.calls.map(([root]) => root)).toEqual([project, project, clone, project]);
    for (const config of ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json'])
      expect(fs.readFileSync(path.join(clone, config))).toEqual(fs.readFileSync(path.join(project, config)));
    expect(fs.readFileSync(path.join(project, 'Submission.lean'))).toEqual(before);
    expect(fs.existsSync(path.join(project, '.lake/build'))).toBe(false);
  });

  it('refuses a changed sealed identity before starting clone diagnostics', async () => {
    resolve.mockReturnValueOnce({ packagesRoot: packages, identity: 'b'.repeat(64), verify })
      .mockReturnValueOnce({ packagesRoot: packages, identity: 'b'.repeat(64), verify })
      .mockReturnValueOnce({ packagesRoot: packages, identity: 'c'.repeat(64), verify });
    await expect(check()).rejects.toThrow('math_type_diagnostics_environment_changed');
    expect(diagnostics).not.toHaveBeenCalled();
  });

  it('refuses an expired original environment before starting clone diagnostics', async () => {
    verify.mockImplementation(() => { throw new Error('Sealed environment expired'); });
    await expect(check()).rejects.toThrow('Sealed environment expired');
    expect(diagnostics).not.toHaveBeenCalled();
  });
});
