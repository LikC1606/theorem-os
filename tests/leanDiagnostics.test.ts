import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../src/math/leanDiagnostics';

const run = vi.hoisted(() => vi.fn());
vi.mock('../src/math/verifier', () => ({ runMathematicsSandboxedCommand: run }));

describe('bounded local Lean diagnostics', () => {
  let root: string;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-diagnostics-'));
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'import ChallengeDeps\ntheorem result : True := by trivial\n');
    fs.writeFileSync(path.join(root, 'ChallengeDeps.lean'), 'def fixed : Nat := 2\n');
    run.mockReset().mockImplementation(async input => {
      const output = input.args.at(-1).match(/-o '([^']+)'/)[1];
      fs.mkdirSync(path.dirname(path.join(root, output)), { recursive: true });
      fs.writeFileSync(path.join(root, output), 'compiled');
      return { started: true, exitCode: 0, timedOut: false, aborted: false, durationMs: 1, stdout: '#check output', stderr: '' };
    });
  });
  afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

  it('prepares imports, reuses unchanged artifacts, and rebuilds changed dependencies', async () => {
    const input = { projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 };
    const prepared = await runLeanDiagnostics({ ...input, dependenciesOnly: true });
    expect(prepared.phases.map(phase => phase.file)).toEqual(['ChallengeDeps.lean']);
    expect(run).toHaveBeenCalledTimes(1);
    const checked = await runLeanDiagnostics(input);
    expect(checked.phases[0].cached).toBe(true);
    expect(checked.stdout).toContain('#check output');
    expect(run).toHaveBeenCalledTimes(2);
    fs.writeFileSync(path.join(root, 'ChallengeDeps.lean'), 'def fixed : Nat := 3\n');
    await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(4);
    fs.writeFileSync(path.join(root, '.lake/build/lib/lean/ChallengeDeps.olean'), 'tampered');
    await runLeanDiagnostics(input);
    expect(run).toHaveBeenCalledTimes(6);
  });

  it.each([{ exitCode: 1, timedOut: false }, { exitCode: null, timedOut: true }])
    ('preserves errors/timeouts and stops before checking dependants (%j)', async failure => {
      run.mockResolvedValueOnce({ started: true, aborted: false, durationMs: 50,
        stdout: 'error: unsolved goals\n' + 'x'.repeat(20000), stderr: '', ...failure });
      const result = await runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 });
      expect(result).toMatchObject(failure);
      expect(result.stdout).toContain('error: unsolved goals');
      expect(Buffer.byteLength(result.stdout)).toBeLessThanOrEqual(8000);
      expect(run).toHaveBeenCalledTimes(1);
    });

  it('rejects protected imports before invoking Lean', async () => {
    fs.writeFileSync(path.join(root, 'Submission.lean'), 'import Solution\n');
    await expect(runLeanDiagnostics({ projectRoot: root, files: ['Submission.lean'], timeoutMs: 1000 }))
      .rejects.toThrow('math_construction_import_excluded');
    expect(run).not.toHaveBeenCalled();
  });

  it('writes valid path overrides without changing the frozen manifest', () => {
    const manifest = JSON.stringify({ packages: [{ name: 'mathlib', type: 'git', rev: 'pinned' }] });
    fs.writeFileSync(path.join(root, 'lake-manifest.json'), manifest);
    prepareLeanDiagnosticOverrides(root);
    const override = JSON.parse(fs.readFileSync(path.join(root, '.lake/package-overrides.json'), 'utf8'));
    expect(override).toMatchObject({ schemaVersion: '1.2.0', packages: [{ type: 'path', rev: 'pinned',
      dir: path.join(root, '.lake/packages/mathlib') }] });
    expect(fs.readFileSync(path.join(root, 'lake-manifest.json'), 'utf8')).toBe(manifest);
  });
});
