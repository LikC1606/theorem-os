import { describe, expect, it } from 'vitest';
import { advisoryStagnation, type StagnationWorker } from '../src/solver/advisoryStagnation';
import { CAPACITY_EXPLORATION_FOCUSES, createCapacityExploration } from '../src/solver/capacityExploration';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';

const identity = { environmentDigest: 'original-environment', problemReceiptDigest: 'original-problem' };
const lemma = (id: string, dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind: 'lemma', type: 'True', theoremName: 'Submission.' + id, proofPath: 'Submission.lean',
    objective: 'Prove ' + id, dependsOn, revision: 0, groupId: 'main' }, status: 'running', attempts: 1,
});
const fixture = () => {
  const frontier = lemma('hard'), goal = lemma('goal', ['hard']);
  goal.task.kind = 'goal'; goal.status = 'pending'; delete goal.task.type;
  const research: TaskRecord = { task: { id: 'route_audit', kind: 'research', objective: 'Audit the missing route',
    dependsOn: ['hard'], revision: 0, groupId: 'main' }, status: 'running', attempts: 4 };
  research.assignment = { taskId: research.task.id, taskDigest: taskVersion(research.task),
    workerId: 'researcher', seedCommit: 'unchanged', assignmentId: 'dispatch-a' };
  const worker: StagnationWorker = { id: 'researcher', sessionTaskId: research.task.id,
    sessionTaskVersion: taskVersion(research.task), advisoryCheckpoint: { noProgressStreak: 3 } };
  return { tasks: [goal, frontier, research], workers: [worker], identity, sourceDigest: 'owned-source', evidenceDigest: 'external-evidence' };
};

describe('advisory stagnation is a stable scheduling signal', () => {
  it('identifies the original frontier and matching stalled advisory worker without mutating proof state', () => {
    const input = fixture(), original = structuredClone(input);
    expect(advisoryStagnation(input)).toMatchObject({ taskIds: ['hard'], workerIds: ['researcher'],
      reason: 'advisory-no-durable-progress', inputDigest: expect.stringMatching(/^[a-f0-9]{64}$/u) });
    expect(input).toEqual(original);
  });

  it('does not diagnose a healthy, stale, unrelated or typed assignment as stalled research', () => {
    for (const mode of ['healthy', 'stale-task', 'stale-session', 'other-group', 'unrelated-question', 'typed'] as const) {
      const input = fixture(), research = input.tasks[2];
      if (mode === 'healthy') input.workers[0].advisoryCheckpoint!.noProgressStreak = 2;
      if (mode === 'stale-task') research.assignment!.taskDigest = 'old';
      if (mode === 'stale-session') input.workers[0].sessionTaskVersion = 'old';
      if (mode === 'other-group') { research.task.groupId = 'other'; research.assignment!.taskDigest = taskVersion(research.task);
        input.workers[0].sessionTaskVersion = taskVersion(research.task); }
      if (mode === 'unrelated-question') { research.task.dependsOn = []; research.assignment!.taskDigest = taskVersion(research.task);
        input.workers[0].sessionTaskVersion = taskVersion(research.task); }
      if (mode === 'typed') { research.task.kind = 'lemma'; research.assignment!.taskDigest = taskVersion(research.task);
        input.workers[0].sessionTaskVersion = taskVersion(research.task); }
      expect(advisoryStagnation(input), mode).toBeUndefined();
    }
  });

  it('keeps the same input across dispatches, counters, ownership, ordering and scheduling prose', () => {
    const input = fixture(), before = advisoryStagnation(input)!.inputDigest;
    input.workers[0].advisoryCheckpoint!.noProgressStreak = 19;
    input.tasks[2].assignment!.assignmentId = 'later-dispatch';
    input.tasks[1].attempts = 99; input.tasks[1].feedback = 'Another interrupted turn';
    input.tasks[1].task.ownerId = 'another-prover'; input.tasks[1].task.revision = 52;
    input.tasks[1].task.objective = 'The same mathematical statement, different prose';
    input.tasks.reverse();
    expect(advisoryStagnation(input)!.inputDigest).toBe(before);
  });

  it('reactivates only for new saved evidence, original environment/source or a mathematical contract', () => {
    const initial = advisoryStagnation(fixture())!.inputDigest;
    for (const mode of ['evidence', 'source', 'environment', 'contract'] as const) {
      const input = fixture();
      if (mode === 'evidence') input.evidenceDigest = 'new-external-finding';
      if (mode === 'source') input.sourceDigest = 'new-owned-source';
      if (mode === 'environment') input.identity = { ...identity, environmentDigest: 'new-environment' };
      if (mode === 'contract') input.tasks[1].task.type = 'False';
      expect(advisoryStagnation(input)!.inputDigest, mode).not.toBe(initial);
    }
  });

  it('requests typed decomposition only after every current focus has finished', () => {
    const input = fixture(); input.workers = [];
    const target = input.tasks[1];
    const explored = CAPACITY_EXPLORATION_FOCUSES.map((focus, index) => {
      const node = createCapacityExploration(target, { id: 'prover-' + index }, input.tasks, identity, focus);
      node.status = 'completed'; return node;
    });
    const explorationInputs = explored.map(node => ({ ...node.capacityExploration!, taskId: node.task.id }));
    const completed = { ...input, tasks: [...input.tasks, ...explored], explorationInputs };
    expect(advisoryStagnation(completed)).toMatchObject({ taskIds: ['hard'], workerIds: [], reason: 'frontier-not-decomposed' });
    expect(advisoryStagnation({ ...completed, explorationInputs: explorationInputs.slice(1) })).toBeUndefined();
    explored[0].status = 'running';
    expect(advisoryStagnation(completed)).toBeUndefined();
  });

  it.each(['pending', 'running', 'blocked'] as const)('does not treat issued %s investigations as exhausted', status => {
    const input = fixture(); input.workers = [];
    const explored = CAPACITY_EXPLORATION_FOCUSES.map((focus, index) => {
      const node = createCapacityExploration(input.tasks[1], { id: 'prover-' + index }, input.tasks, identity, focus);
      node.status = index ? status : 'completed'; return node;
    });
    const explorationInputs = explored.map(node => ({ ...node.capacityExploration!, taskId: node.task.id }));
    expect(advisoryStagnation({ ...input, tasks: [...input.tasks, ...explored], explorationInputs })).toBeUndefined();
  });

  it('does not let an issued tombstone substitute for a missing completed investigation', () => {
    const input = fixture(); input.workers = [];
    const explored = CAPACITY_EXPLORATION_FOCUSES.map((focus, index) => {
      const node = createCapacityExploration(input.tasks[1], { id: 'prover-' + index }, input.tasks, identity, focus);
      node.status = 'completed'; return node;
    });
    const explorationInputs = explored.map(node => ({ ...node.capacityExploration!, taskId: node.task.id }));
    expect(advisoryStagnation({ ...input, tasks: [...input.tasks, ...explored.slice(1)], explorationInputs })).toBeUndefined();
  });

  it('keeps legacy archives with no worker metadata healthy and ignores stale exploration identities', () => {
    const input = fixture(); input.workers = [];
    expect(advisoryStagnation(input)).toBeUndefined();
    const explored = CAPACITY_EXPLORATION_FOCUSES.map(focus => createCapacityExploration(input.tasks[1], { id: 'prover' }, input.tasks, identity, focus));
    explored.forEach(node => { node.status = 'completed'; });
    const explorationInputs = explored.map(node => ({ ...node.capacityExploration!, taskId: node.task.id }));
    input.tasks[1].task.type = 'False';
    expect(advisoryStagnation({ ...input, tasks: [...input.tasks, ...explored], explorationInputs })).toBeUndefined();
  });
});
