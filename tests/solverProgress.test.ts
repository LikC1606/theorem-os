import { describe, expect, it } from 'vitest';
import { buildProofContinuation, recordedTaskProofStatus } from '../src/solver/progress';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';

function node(id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord {
  return { task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: `Submission.${id}`, proofPath: 'Submission.lean', type: 'True' } : {}) },
    status: 'pending', attempts: 0 };
}
function checked(item: TaskRecord, uses: TaskRecord[] = [], statementOnly = false) {
  item.status = 'integrated';
  const proof = item.integratedCheck = { taskDigest: taskVersion(item.task), passed: true, commit: 'canonical',
    sourceDigest: 'source', seedCommit: 'seed', changes: [],
    verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: 'receipt' },
    ] }, references: { environmentDigest: 'environment', sourceCommit: 'projection', contextDigest: 'context', inputs: [],
      root: { file: item.task.proofPath!, name: item.task.theoremName! },
      tasks: uses.map(input => ({ taskId: input.task.id, taskDigest: taskVersion(input.task) })),
      statement: statementOnly ? uses.map(input => ({ file: input.task.proofPath!, name: input.task.theoremName! })) : [],
      proof: statementOnly ? [] : uses.map(input => ({ file: input.task.proofPath!, name: input.task.theoremName! })) } } as TaskProof;
  return proof;
}

describe('recorded proof continuation', () => {
  it('deduplicates a shared mathematical frontier and exposes checked inputs for the consumer', () => {
    const input = node('input'), core = node('core', 'lemma', ['input']); checked(input);
    const goal1 = node('goal1', 'goal', ['core']), goal2 = node('goal2', 'goal', ['core']);
    const report = buildProofContinuation([input, core, goal1, goal2]);
    expect(report.frontier).toEqual([{ taskId: 'core', kind: 'lemma', status: 'pending', control: 'active',
      attempts: 0, goalIds: ['goal1', 'goal2'], checkedInputs: ['input'] }]);
    expect(report.continuationCandidates).toEqual(['core']);
    expect(report.reuse[0]).toMatchObject({ plannedConsumers: ['core'], plannedGoalIds: ['goal1', 'goal2'], proofConsumers: [] });
    expect(report.goals[0].checkedDependencies).toEqual(['input']);
  });

  it('separates planned use, proof use, statement references and a conditional application', () => {
    const input = node('input'); checked(input);
    const planned = node('planned', 'goal', ['input']);
    const actual = node('actual', 'lemma'); checked(actual, [input]);
    const statement = node('statement', 'lemma'); checked(statement, [input], true);
    const conditional = node('conditional', 'lemma', ['input']);
    const proof = checked(conditional, [input]); conditional.status = 'conditional';
    proof.conditions = [{ taskId: 'open', taskDigest: 'open-version' }];
    const report = buildProofContinuation([input, planned, actual, statement, conditional]);
    expect(report.reuse[0]).toMatchObject({ plannedConsumers: ['planned', 'conditional'], proofConsumers: ['actual'],
      statementConsumers: ['statement'], conditionalConsumers: ['conditional'] });
    expect(report.goals[0].recordedProof).toBe('none');
    expect(report.unconnectedTasks).toEqual(['actual', 'statement', 'conditional']);
  });

  it('excludes stale task versions and environments from recorded reuse', () => {
    const input = node('input'); checked(input);
    const consumer = node('consumer'); const proof = checked(consumer, [input]);
    proof.references!.tasks![0].taskDigest = 'old-version';
    expect(buildProofContinuation([input, consumer]).reuse[0].proofConsumers).toEqual([]);
    proof.references!.tasks![0].taskDigest = taskVersion(input.task);
    proof.references!.environmentDigest = 'different-environment';
    expect(buildProofContinuation([input, consumer], { environmentDigest: 'environment' }).reuse[0].proofConsumers).toEqual([]);
    input.task = { ...input.task, revision: 1 };
    expect(recordedTaskProofStatus(input)).toBe('stale');
    expect(buildProofContinuation([input, consumer]).reuse).toEqual([]);
  });

  it('keeps unavailable reference evidence unknown and does not infer consumption from a planned edge', () => {
    const input = node('input'); delete checked(input).references;
    const consumer = node('consumer', 'goal', ['input']); delete checked(consumer).references;
    const report = buildProofContinuation([input, consumer]);
    expect(report.reuse[0].plannedConsumers).toEqual(['consumer']);
    expect(report.reuse[0].proofConsumers).toEqual([]);
    expect(report.referenceCoverageMissing).toEqual(['input', 'consumer']);
    expect(report.evidence).toBe('recorded-not-replayed');
  });

  it('does not settle nominally integrated tasks without matching receipts or close conditional goals', () => {
    const helper = node('helper'); checked(helper).verification.results = [];
    const goal = node('goal', 'goal', ['helper']);
    const report = buildProofContinuation([helper, goal]);
    expect(report.frontier[0].taskId).toBe('helper');
    expect(report.continuationCandidates).toEqual([]);
    const proof = checked(goal); goal.status = 'conditional';
    proof.conditions = [{ taskId: 'helper', taskDigest: taskVersion(helper.task) }];
    expect(buildProofContinuation([helper, goal]).goals[0].recordedProof).toBe('conditional');
  });

  it('reports missing dependencies and respects paused routes without mutating task versions', () => {
    const goal = node('goal', 'goal', ['absent']), paused = node('paused', 'goal');
    paused.task = { ...paused.task, groupId: 'other' };
    const before = JSON.stringify([goal, paused]);
    const report = buildProofContinuation([goal, paused], { groups: [
      { group: { id: 'main', objective: '', status: 'active', revision: 0 }, turns: 0 },
      { group: { id: 'other', objective: '', status: 'paused', revision: 0 }, turns: 0 },
    ] });
    expect(report.goals).toHaveLength(1);
    expect(report.goals[0].missingDependencies).toEqual(['absent']);
    expect(JSON.stringify([goal, paused])).toBe(before);
  });

  it('retains a checked shared wrapper in a scoped view without exposing its private prerequisite', () => {
    const secret = node('private_implementation'), shared = node('shared'); checked(secret); checked(shared, [secret]);
    const goal = node('goal', 'goal', ['shared']);
    const report = buildProofContinuation([shared, goal]);
    expect(report.continuationCandidates).toEqual(['goal']);
    expect(report.reuse[0].taskId).toBe('shared');
    expect(JSON.stringify(report)).not.toContain('private_implementation');
  });
});
