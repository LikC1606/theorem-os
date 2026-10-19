import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { commitSolverSources, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { captureStatementContexts } from '../src/solver/statementReview';
import type { CooperativeTask } from '../src/solver/tasks';

const { diagnostics } = vi.hoisted(() => ({ diagnostics: vi.fn() }));
vi.mock('../src/math/leanDiagnostics', async original => ({
  ...await original<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: diagnostics,
}));

describe('persistent statement projection diagnostics', () => {
  let directory: string, workspace: string, problem: SolverProblem, commit: string, project: string;
  let tasks: CooperativeTask[];
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'statement-projection-diagnostics-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace); problem = readSolverProblem(workspace, receipt.activeProblemPath);
    commit = commitSolverSources(problem, workspace);
    tasks = [{ id: 'goal', kind: 'goal', objective: 'Prove original.', dependsOn: [], revision: 0,
      proofPath: problem.targets[0].proofPath, theoremName: problem.targets[0].theoremName }];
    diagnostics.mockReset();
  });
  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  const capture = () => captureStatementContexts(problem, tasks, workspace, commit, {}, undefined, 1000);
  const manifest = () => {
    const root = path.join(directory, 'statement-diagnostics'), saved = path.join(root, fs.readdirSync(root)[0]);
    return { root: saved, value: JSON.parse(fs.readFileSync(path.join(saved, 'manifest.json'), 'utf8')) };
  };

  it('retains hash-checked full diagnostics and the first blocking message after the disposable worktree is removed', async () => {
    const source = fs.readFileSync(path.join(workspace, problem.projectRelative, tasks[0].proofPath!));
    let artifactText = '';
    diagnostics.mockImplementation(async input => {
      project = input.projectRoot;
      artifactText = canonicalMathJson({ schema: 'theoremos.lean-diagnostics.v1', authority: 'advisory-lean-process',
        sourceDigest: 'fixed-source', environmentDigest: 'fixed-environment', captureComplete: true,
        stdout: 'complete artifact ' + 'x'.repeat(20000), stderr: '' });
      const digest = mathDigest(artifactText), relative = `.lake/diagnostic-artifacts/${digest}.json`;
      fs.mkdirSync(path.dirname(path.join(project, relative)), { recursive: true });
      fs.writeFileSync(path.join(project, relative), artifactText);
      return { exitCode: 1, timedOut: false, stdout: 'warning: bounded preview omitted the error', stderr: '',
        sourceDigest: 'fixed-source', environmentDigest: 'fixed-environment',
        firstBlocking: { format: 'lean-json', severity: 'error', file: 'Submission.lean', line: 80, column: 3,
          message: 'unsolved goals\nn : Nat\n\u22a2 n > 1', goalText: 'n : Nat\n\u22a2 n > 1' },
        diagnosticArtifacts: [{ path: relative, digest, sourceDigest: 'fixed-source', environmentDigest: 'fixed-environment', captureComplete: true }] };
    });
    await expect(capture()).rejects.toThrow('math_statement_elaboration_failed\nSubmission.lean:80:4: error: unsolved goals');
    expect(fs.existsSync(project)).toBe(false);
    const saved = manifest();
    expect(saved.value).toMatchObject({ sourceDigest: 'fixed-source', environmentDigest: 'fixed-environment',
      firstBlocking: { goalText: 'n : Nat\n\u22a2 n > 1' }, diagnosticArtifactErrors: [], diagnosticArtifacts: [{ captureComplete: true }] });
    const reference = saved.value.diagnosticArtifacts[0], copied = fs.readFileSync(path.join(saved.root, reference.path), 'utf8');
    expect(copied).toBe(artifactText); expect(mathDigest(copied)).toBe(reference.digest);
    expect(fs.readFileSync(path.join(workspace, problem.projectRelative, tasks[0].proofPath!))).toEqual(source);
  });

  it('preserves the primary failure when a diagnostic artifact changed instead of publishing that artifact', async () => {
    diagnostics.mockImplementation(async input => {
      project = input.projectRoot;
      const digest = mathDigest('original bytes'), relative = `.lake/diagnostic-artifacts/${digest}.json`;
      fs.mkdirSync(path.dirname(path.join(project, relative)), { recursive: true });
      fs.writeFileSync(path.join(project, relative), 'changed bytes');
      return { exitCode: 1, timedOut: false, stdout: 'Submission.lean:2:3: error: bad type', stderr: '',
        diagnosticArtifacts: [{ path: relative, digest, sourceDigest: 'source', environmentDigest: 'environment' }] };
    });
    await expect(capture()).rejects.toThrow('math_statement_elaboration_failed\nSubmission.lean:2:3: error: bad type');
    expect(fs.existsSync(project)).toBe(false);
    expect(manifest().value).toMatchObject({ diagnosticArtifacts: [],
      diagnosticArtifactErrors: ['math_statement_diagnostic_artifact_changed'] });
  });

  it('preserves raw diagnostic fallback and legacy mocks without structured fields', async () => {
    diagnostics.mockResolvedValue({ exitCode: 1, timedOut: false,
      stdout: 'warning: before\nSubmission.lean:8:4: error: legacy error\nexpected a term', stderr: '' });
    await expect(capture()).rejects.toThrow('math_statement_elaboration_failed\nSubmission.lean:8:4: error: legacy error\nexpected a term');
    expect(manifest().value).toMatchObject({ diagnosticArtifacts: [], diagnosticArtifactErrors: [] });
  });
});
