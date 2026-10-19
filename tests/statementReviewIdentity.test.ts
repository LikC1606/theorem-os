import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { bootstrapLocalExample, LOCAL_EXAMPLE_STATEMENT } from '../src/math/localExample';
import type { LeanStatementContext } from '../src/math/leanStatementContext';
import { commitSolverSources, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { assertStatementSnapshot, statementSnapshot, writeStatementSnapshot, type StatementReview } from '../src/solver/statementReview';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

describe('statement review dependency identity', () => {
  let directory: string, workspace: string, problem: SolverProblem, commit: string, source: string;
  let dependency: CooperativeTask, consumer: CooperativeTask;
  const snapshot = (context?: LeanStatementContext) => statementSnapshot(problem, consumer, workspace, commit, 'fixed-environment',
    [{ task: dependency, taskDigest: taskVersion(dependency) }], context);

  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'statement-review-identity-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    source = LOCAL_EXAMPLE_STATEMENT.replace('theorem add_zero',
      'def reviewBase : Nat := 0\nlemma dependency : True := by trivial\nlemma consumer : True := by trivial\ntheorem add_zero');
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), source);
    commit = commitSolverSources(problem, workspace);
    dependency = { id: 'dependency', kind: 'lemma', objective: 'Establish the supporting fact.', dependsOn: [], revision: 0,
      theoremName: 'Tutorial.dependency', proofPath: 'Submission.lean', type: 'True', premises: [] };
    consumer = { id: 'consumer', kind: 'lemma', objective: 'Use the supporting fact.', dependsOn: ['dependency'], revision: 0,
      theoremName: 'Tutorial.consumer', proofPath: 'Submission.lean', type: 'True', statementReview: true,
      informalStatement: 'The proposition True holds.' };
  });

  afterEach(() => fs.rmSync(directory, { recursive: true, force: true }));

  it.each(['objective', 'revision', 'both'] as const)('keeps the semantic identity after a dependency %s edit', edit => {
    const before = snapshot(), previousVersion = taskVersion(dependency);
    dependency = { ...dependency,
      ...(edit !== 'revision' ? { objective: 'Try a different method for the same supporting fact.' } : {}),
      ...(edit !== 'objective' ? { revision: 1 } : {}) };
    const after = snapshot();
    expect(taskVersion(dependency)).not.toBe(previousVersion);
    expect(after.snapshotDigest).toBe(before.snapshotDigest);
    expect(before.input.dependencies[0]!.taskDigest).toBe(previousVersion);
    expect(after.input.dependencies[0]!.taskDigest).toBe(taskVersion(dependency));
  });

  it.each([
    { field: 'type', change: { type: 'True \u2227 True' } },
    { field: 'premises', change: { premises: ['An additional hypothesis.'] } },
    { field: 'dependencies', change: { dependsOn: ['new-premise'] } },
    { field: 'declaration', change: { theoremName: 'Tutorial.different' } },
    { field: 'conditional contract', change: { conditional: true } },
  ])('invalidates the identity after the dependency $field changes', ({ change }) => {
    const before = snapshot();
    dependency = { ...dependency, ...change };
    expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
  });

  it('writes the current full dependency version even when the semantic snapshot is reused', () => {
    const before = snapshot(), oldVersion = taskVersion(dependency);
    dependency = { ...dependency, objective: 'Explain the same fact more clearly.', revision: 1 };
    const after = snapshot(), reviewWorkspace = path.join(directory, 'review');
    writeStatementSnapshot(reviewWorkspace, after);
    const written = JSON.parse(fs.readFileSync(path.join(reviewWorkspace, 'STATEMENT.json'), 'utf8'));
    expect(written.snapshotDigest).toBe(before.snapshotDigest);
    expect(written.dependencies).toEqual([{ taskId: dependency.id, taskDigest: taskVersion(dependency),
      theoremName: dependency.theoremName, leanType: dependency.type }]);
    expect(written.dependencies[0].taskDigest).not.toBe(oldVersion);
    expect(before.input.dependencies[0]!.taskDigest).toBe(oldVersion);
  });

  it('rejects rewriting frozen provenance even when the replacement has the same semantic identity', () => {
    const before = snapshot(), reviewWorkspace = path.join(directory, 'review');
    const review: StatementReview = { id: 'review', taskId: consumer.id, taskDigest: taskVersion(consumer),
      snapshotDigest: before.snapshotDigest, environmentDigest: 'fixed-environment', commit,
      leanStatement: before.input.leanStatement, intendedStatement: consumer.informalStatement!, premises: [],
      dependencies: before.input.dependencies, workspace: reviewWorkspace, files: writeStatementSnapshot(reviewWorkspace, before), status: 'accepted' };
    expect(() => assertStatementSnapshot(review)).not.toThrow();
    dependency = { ...dependency, objective: 'Explain the same fact more clearly.', revision: 1 };
    const after = snapshot();
    expect(after.snapshotDigest).toBe(before.snapshotDigest);
    writeStatementSnapshot(reviewWorkspace, after);
    expect(() => assertStatementSnapshot(review)).toThrow('math_statement_snapshot_changed');
  });

  it('invalidates the identity when a definition in the blind source changes', () => {
    const before = snapshot();
    dependency = { ...dependency, objective: 'Use the same supporting statement.', revision: 1 };
    fs.writeFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), source.replace('reviewBase : Nat := 0', 'reviewBase : Nat := 1'));
    commit = commitSolverSources(problem, workspace);
    expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
  });

  it('invalidates the identity when a Lean-resolved definition changes', () => {
    const context: LeanStatementContext = { type: 'True', constants: [
      { name: 'Tutorial.reviewBase', module: 'Submission', type: 'Nat', definition: '0' }], omitted: [] };
    const before = snapshot(context);
    dependency = { ...dependency, revision: 1 };
    expect(snapshot({ ...context, constants: [{ ...context.constants[0]!, definition: '1' }] }).snapshotDigest).not.toBe(before.snapshotDigest);
  });

  it('keeps advisory findings sensitive to their objective and version', () => {
    dependency = { id: 'dependency', kind: 'research', objective: 'Investigate one approach.', dependsOn: [], revision: 0 };
    const before = snapshot();
    dependency = { ...dependency, objective: 'Investigate a different approach.', revision: 1 };
    expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
  });
});
