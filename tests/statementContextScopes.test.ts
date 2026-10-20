import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import { runLeanProcess } from '../src/math/mathProcess';
import { captureStatementContexts } from '../src/solver/statementReview';
import { git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import type { CooperativeTask } from '../src/solver/tasks';

const { run } = vi.hoisted(() => ({ run: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  runMathematicsSandboxedCommand: run,
}));
const toolchain = path.join(os.homedir(), '.elan', 'toolchains', 'leanprover--lean4---v4.33.0', 'bin');
const lean = path.join(toolchain, 'lean');

describe.skipIf(!fs.existsSync(lean))('local Lean statement type scopes', () => {
  let directory: string, workspace: string, project: string, problem: SolverProblem, commit: string;
  let injected: boolean;
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'statement-type-scope-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace); problem = readSolverProblem(workspace, receipt.activeProblemPath);
    project = path.join(workspace, problem.projectRelative); commit = problem.baseCommit; injected = false;
    run.mockReset().mockImplementation(async input => {
      const result = await runLeanProcess('/bin/sh', ['-ceu', input.args.at(-1)], {
        cwd: input.checkoutRoot, timeoutMs: input.timeoutMs, signal: input.signal,
        outputLimit: input.outputLimit, outputCapture: input.outputCapture,
        env: { ...process.env, PATH: `${toolchain}:${process.env.PATH}`,
          LEAN_PATH: path.join(input.checkoutRoot, '.lake', 'build', 'lib', 'lean') },
      });
      injected ||= fs.existsSync(path.join(input.checkoutRoot, '.lake', 'injected-marker'));
      return result;
    });
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));
  const helper = (name: string, type: string): CooperativeTask => ({ id: name, kind: 'lemma', objective: 'Inspect a closed helper type.',
    dependsOn: [], revision: 0, theoremName: name, proofPath: 'Submission.lean', type, statementReview: true,
    informalStatement: 'INTENT_SECRET' });
  const update = (change: (source: string) => string) => {
    const file = path.join(project, 'Submission.lean');
    // These scopes form the fixture's frozen input, rather than an accepted solver edit.
    fs.writeFileSync(file, change(fs.readFileSync(file, 'utf8')));
    git(workspace, ['add', '--', `${problem.projectRelative}/Submission.lean`]);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Prepare scoped statement fixture']);
    commit = git(workspace, ['rev-parse', 'HEAD']);
  };
  const capture = (tasks: CooperativeTask[]) => captureStatementContexts(problem, tasks, workspace, commit, {}, undefined, 30_000);

  it('resolves a pending helper in the original declaration namespace without needing its proof', async () => {
    update(source => source.replace('theorem add_zero', 'def reviewBase : Nat := 0\ntheorem add_zero'));
    const before = fs.readFileSync(path.join(project, 'Submission.lean'));
    const contexts = await capture([helper('Tutorial.pending', 'reviewBase = 0')]);
    expect(contexts.get('Tutorial.pending')?.type).toContain('Tutorial.reviewBase');
    expect(JSON.stringify([...contexts])).not.toContain('INTENT_SECRET');
    expect(fs.readFileSync(path.join(project, 'Submission.lean'))).toEqual(before);
    expect(fs.existsSync(path.join(project, '.lake', 'build'))).toBe(false);
  });

  it('keeps different helper namespaces and open scopes independent in one query', async () => {
    update(source => source + '\nnamespace FirstData\ndef value : Nat := 1\nend FirstData\n' +
      'namespace SecondData\ndef value : Bool := true\nend SecondData\n' +
      'namespace First\nopen FirstData\ntheorem helper : value = 1 := by sorry\nend First\n' +
      'namespace Second\nopen SecondData\ntheorem helper : value = true := by sorry\nend Second\n');
    const contexts = await capture([helper('First.helper', 'value = 1'), helper('Second.helper', 'value = true')]);
    expect(contexts.get('First.helper')?.type).toContain('FirstData.value');
    expect(contexts.get('Second.helper')?.type).toContain('SecondData.value');
    expect(contexts.get('Second.helper')?.type).not.toContain('FirstData');
  });

  it('restores matching goal lookup scopes for a pending helper while keeping original goals fixed', async () => {
    update(source => 'namespace SharedData\ndef value : Nat := 1\nend SharedData\n' +
      source.replace('namespace Tutorial', 'namespace Tutorial\nopen SharedData'));
    const target = problem.targets[0]!;
    const goal: CooperativeTask = { id: 'original', kind: 'goal', objective: 'Inspect the fixed target.',
      theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0 };
    const contexts = await capture([helper('Tutorial.pending', 'value = 1'), goal]);
    expect(contexts.get('Tutorial.pending')?.type).toContain('SharedData.value');
    expect(contexts.get('original')?.type).toContain('HAdd.hAdd n 0');
    expect(contexts.get('original')?.type).not.toContain('SharedData');
  });

  it('restores a requested namespace when no original target can supply lookup scopes', async () => {
    update(source => source + '\nnamespace NewSpace\ndef value : Nat := 1\nend NewSpace\n');
    const contexts = await capture([helper('NewSpace.pending', 'value = 1')]);
    expect(contexts.get('NewSpace.pending')?.type).toContain('NewSpace.value');
  });

  it('rejects conflicting original goal lookup scopes instead of choosing an arbitrary anchor', async () => {
    update(source => 'namespace FirstData\ndef value : Nat := 1\nend FirstData\n' +
      'namespace SecondData\ndef value : Bool := true\nend SecondData\n' + source
        .replace('theorem add_zero', 'open FirstData\ntheorem add_zero')
        .replace('theorem zero_add', 'open SecondData\ntheorem zero_add'));
    await expect(capture([helper('Tutorial.pending', 'value = 1')])).rejects.toThrow('Helper declaration context is ambiguous.');
    expect(run).not.toHaveBeenCalled();
    const diagnosticsRoot = path.join(directory, 'statement-diagnostics');
    const manifest = JSON.parse(fs.readFileSync(path.join(diagnosticsRoot, fs.readdirSync(diagnosticsRoot)[0]!, 'manifest.json'), 'utf8'));
    expect(manifest.reason).toContain('Helper declaration context is ambiguous.');
    expect(manifest.files.map((file: { path: string }) => file.path)).toContain('project/Submission.lean');
  });

  it('does not let an earlier root open names for a later pending helper', async () => {
    update(source => source + '\nnamespace FirstData\ndef value : Nat := 1\nend FirstData\n' +
      'open FirstData\ntheorem scopedHelper : value = 1 := by sorry\n');
    await expect(capture([helper('scopedHelper', 'value = 1'), helper('Outside.pending', 'value = 1')]))
      .rejects.toThrow('math_statement_elaboration_failed');
  });

  it('parses a requested type as one term without executing following commands', async () => {
    const payload = 'True\nrun_cmd IO.FS.writeFile ".lake/injected-marker" "bad"';
    await expect(capture([helper('Tutorial.pending', payload)])).rejects.toThrow('math_statement_elaboration_failed');
    expect(injected).toBe(false);
    expect(fs.existsSync(path.join(project, '.lake', 'injected-marker'))).toBe(false);
  });

  it('rejects malformed helper names before restoring a namespace', async () => {
    const name = 'Tutorial\nrun_cmd IO.FS.writeFile ".lake/injected-marker" "bad"\n.pending';
    await expect(capture([helper(name, 'True')])).rejects.toThrow('Helper declaration name is invalid.');
    expect(run).not.toHaveBeenCalled();
    expect(injected).toBe(false);
  });
});
