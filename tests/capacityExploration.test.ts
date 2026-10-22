import { describe, expect, it } from 'vitest';
import { CAPACITY_EXPLORATION_FOCUSES, capacityExplorationInput, capacityExplorationWorkerCanTask,
  createCapacityExploration, currentCapacityExploration, plannedTaskRecords,
  type CapacityExploration, type CapacityExplorationFocus } from '../src/solver/capacityExploration';
import { taskVersion, type TaskRecord } from '../src/solver/tasks';
import { assignSharedResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import { originalGoalTaskFocus, readyResearchTasks, routeAllowsTask } from '../src/solver/modules/search';
import { integratedProof } from './helpers/taskProof';

const identity = { environmentDigest: 'environment', problemReceiptDigest: 'frozen-original-problem' };
const prover = { id: 'prover-2', role: 'prover' };
const node = (id: string, dependsOn: string[] = [], kind: 'lemma' | 'goal' = 'lemma'): TaskRecord => ({
  task: { id, kind, objective: `Prove ${id}`, dependsOn, revision: 0, groupId: 'main',
    theoremName: `Submission.${id}`, proofPath: 'Submission.lean', ...(kind === 'lemma' ? { type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
const exploration = (target: TaskRecord, tasks = [target], focus: CapacityExplorationFocus = CAPACITY_EXPLORATION_FOCUSES[0]) =>
  createCapacityExploration(target, prover, tasks, identity, focus);
const checked = (item: TaskRecord, proof = 'by trivial', receipt = 'receipt') => integratedProof(item, {
  receiptId: receipt, environmentDigest: identity.environmentDigest,
  changes: [{ file: item.task.proofPath!, name: item.task.theoremName!, after: `theorem ${item.task.theoremName} : True := ${proof}\n` }],
  inputs: [{ file: item.task.proofPath!, name: item.task.theoremName!, digest: proof }],
});

describe('capacity exploration mathematical input identity', () => {
  it('is stable across worker ownership, assignment, turn counts, prose and operational revisions', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [target, input];
    const before = capacityExplorationInput(target.task, tasks, identity);
    target.task = { ...target.task, objective: 'Rephrase the same target', revision: 19, ownerId: 'engineer' };
    input.task = { ...input.task, objective: 'New wording for the same interface', revision: 32 };
    target.status = 'running'; target.attempts = 103; target.finding = 'A scheduling note';
    target.assignment = { taskId: target.task.id, taskDigest: taskVersion(target.task), workerId: 'engineer',
      seedCommit: 'different-seed', assignmentId: 'later-dispatch' };
    input.feedback = 'More logs'; input.attempts = 81;
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
  });

  it('ignores unrelated sources, findings and proof receipts outside the declared dependency cone', () => {
    const input = node('input'), target = node('target', ['input']), unrelated = node('other');
    const tasks = [target, input, unrelated], before = capacityExplorationInput(target.task, tasks, identity);
    checked(unrelated); unrelated.finding = 'A different theorem was solved';
    unrelated.task = { ...unrelated.task, type: 'False', revision: 22 };
    tasks.push(node('new-unrelated'));
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
  });

  it('does not self-trigger from host explorations, their status, findings or metadata', () => {
    const target = node('target'), before = capacityExplorationInput(target.task, [target], identity);
    const first = exploration(target), sibling = exploration(target, [target], 'interface');
    first.status = 'completed'; first.finding = 'A new advisory observation';
    sibling.status = 'running'; sibling.feedback = 'More progress'; sibling.attempts = 9;
    const tasks = [first, target, sibling];
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
    target.task = { ...target.task, dependsOn: [first.task.id] };
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
  });

  it('normalizes task order and input ordering across serialization', () => {
    const first = node('first'), second = node('second'), target = node('target', ['second', 'first']);
    checked(first); checked(second);
    const tasks = [first, target, second], before = capacityExplorationInput(target.task, tasks, identity);
    target.task = { ...target.task, dependsOn: ['first', 'second'] };
    const restored: TaskRecord[] = JSON.parse(JSON.stringify(tasks.toReversed()));
    expect(capacityExplorationInput(restored.find(item => item.task.id === target.task.id)!.task, restored, identity)).toBe(before);
  });

  it.each(['target-type', 'target-premise', 'input-type', 'transitive-input', 'environment', 'problem'] as const)(
    'changes for genuinely changed mathematical inputs: %s', change => {
      const root = node('root'), input = node('input', ['root']), target = node('target', ['input']);
      const tasks = [target, input, root], before = capacityExplorationInput(target.task, tasks, identity);
      const nextIdentity = { ...identity };
      if (change === 'target-type') target.task = { ...target.task, type: 'True ∧ True' };
      if (change === 'target-premise') target.task = { ...target.task, premises: ['an exact new premise'] };
      if (change === 'input-type') input.task = { ...input.task, type: 'False' };
      if (change === 'transitive-input') root.task = { ...root.task, type: 'False' };
      if (change === 'environment') nextIdentity.environmentDigest = 'different-lean-environment';
      if (change === 'problem') nextIdentity.problemReceiptDigest = 'different-frozen-statement';
      expect(capacityExplorationInput(target.task, tasks, nextIdentity)).not.toBe(before);
    });

  it('opens another input only for changed checked local evidence, preserving receipt replays', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [target, input];
    const unproved = capacityExplorationInput(target.task, tasks, identity);
    checked(input); const proved = capacityExplorationInput(target.task, tasks, identity);
    expect(proved).not.toBe(unproved);
    const replay = checked(input, 'by trivial', 'another-receipt');
    replay.commit = 'unrelated-commit'; replay.sourceDigest = 'different-whole-file-hash';
    replay.references!.sourceCommit = 'another-run'; replay.verification.targetCommit = 'replayed-projection';
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(proved);
    checked(input, 'by exact True.intro');
    expect(capacityExplorationInput(target.task, tasks, identity)).not.toBe(proved);
  });

  it('does not treat failed, conditional or foreign-environment receipts as new checked inputs', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [target, input];
    const before = capacityExplorationInput(target.task, tasks, identity);
    checked(input).passed = false;
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
    checked(input).conditions = [{ taskId: 'unproven', taskDigest: 'digest' }];
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
    checked(input).references!.environmentDigest = 'foreign-environment';
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
  });

  it('includes every declared proof route while ignoring the route currently assigned to a worker', () => {
    const first = node('first'), second = node('second'), target = node('original', [], 'goal');
    target.alternativeRoutes = [
      { id: 'route_a', targetTaskId: target.task.id, prerequisiteTaskIds: [], closingTaskId: first.task.id },
      { id: 'route_b', targetTaskId: target.task.id, prerequisiteTaskIds: [], closingTaskId: second.task.id },
    ];
    const tasks = [target, first, second], before = capacityExplorationInput(target.task, tasks, identity);
    target.assignment = { taskId: target.task.id, taskDigest: taskVersion(target.task), workerId: 'engineer',
      seedCommit: 'seed', routeId: 'route_a' };
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
    target.assignment.routeId = 'route_b';
    target.alternativeRoutes.reverse();
    expect(capacityExplorationInput(target.task, tasks, identity)).toBe(before);
    checked(first);
    expect(capacityExplorationInput(target.task, tasks, identity)).not.toBe(before);
  });
});

describe('bounded advisory exploration creation', () => {
  it('creates independent focuses and consumer-specific deliverables without touching inputs', () => {
    const target = node('target'), before = structuredClone(target);
    const results = CAPACITY_EXPLORATION_FOCUSES.map(focus => exploration(target, [target], focus));
    expect(new Set(results.map(item => item.task.id)).size).toBe(4);
    expect(new Set(results.map(item => item.task.objective)).size).toBe(4);
    for (const result of results) {
      expect(result).toMatchObject({ status: 'pending', attempts: 0,
        task: { kind: 'research', ownerId: prover.id, groupId: 'main', dependsOn: [target.task.id] },
        capacityExploration: { schema: 'theorem-os.capacity-exploration.v1', targetTaskId: target.task.id,
          targetTaskDigest: taskVersion(target.task), workerId: prover.id, ...identity } });
      expect(result.task.id).toMatch(/^capacity_[a-f0-9]{40}$/u);
      expect(result.task.objective).toContain(target.task.theoremName);
      expect(result.task.objective).toContain('Exact consumer type:\nTrue');
      expect(result.task.objective).toContain('Lean scratch experiments');
      expect(result.task.objective).toContain('do not change owned Lean files');
      expect(result.task.objective).toContain('precise lemmaRequests with full closed Lean types');
      expect(result.task.objective).toContain('this exact consumer');
      expect(result.task).not.toHaveProperty('theoremName');
      expect(result.task).not.toHaveProperty('type');
      expect(currentCapacityExploration(result, [target, ...results], identity)).toBe(true);
    }
    expect(target).toEqual(before);
  });

  it('supports frozen original goals without a duplicated type on the planning task', () => {
    const target = node('original', [], 'goal'), result = exploration(target);
    expect(result.task.objective).toContain('frozen original goal declaration supplied in the mandatory problem context');
    expect(result.task.objective).not.toContain('undefined');
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(true);
    expect(currentCapacityExploration(result, [target, result], { ...identity, problemReceiptDigest: 'edited-problem' })).toBe(false);
  });

  it('has one stable target/input/focus identity across worker choices, restarts and completed findings', () => {
    const target = node('target'), first = exploration(target);
    first.status = 'completed'; first.finding = 'The bounded investigation is finished';
    const restored: TaskRecord[] = JSON.parse(JSON.stringify([first, target]));
    const second = createCapacityExploration(restored[1], { id: 'another-prover' }, restored, identity, 'construction');
    expect(second.task.id).toBe(first.task.id);
    expect(second.capacityExploration!.inputDigest).toBe(first.capacityExploration!.inputDigest);
    expect(second.task.ownerId).toBe('another-prover');
    expect(currentCapacityExploration(restored[0], restored, identity)).toBe(true);
  });

  it('preserves group isolation and accepts an unresolved conditional proof target', () => {
    const target = node('target');
    target.task = { ...target.task, groupId: 'branch_two', sharing: 'group' };
    checked(target).conditions = [{ taskId: 'unproven', taskDigest: 'digest' }];
    const result = exploration(target);
    expect(result.task).toMatchObject({ groupId: 'branch_two', sharing: 'group' });
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(true);
  });

  it.each(['research', 'empty-type', 'placeholder', 'missing-path', 'missing-name', 'completed', 'stopped', 'checked', 'missing'] as const)(
    'refuses to create investigations for unusable targets: %s', state => {
      const target = node('target');
      if (state === 'research') target.task = { ...target.task, kind: 'research' };
      if (state === 'empty-type') target.task = { ...target.task, type: ' ' };
      if (state === 'placeholder') target.task = { ...target.task, type: 'FULL_CLOSED_LEAN_TYPE' };
      if (state === 'missing-path') target.task = { ...target.task, proofPath: undefined };
      if (state === 'missing-name') target.task = { ...target.task, theoremName: undefined };
      if (state === 'completed') target.status = 'completed';
      if (state === 'stopped') target.task = { ...target.task, status: 'stopped' };
      if (state === 'checked') checked(target);
      expect(() => exploration(target, state === 'missing' ? [] : [target])).toThrow('math_capacity_exploration_target_invalid');
    });
});

describe('host marker and worker eligibility', () => {
  it.each(['paused', 'stopped'] as const)('retains a %s exploration identity without granting dispatch permission', control => {
    const target = node('target'), result = exploration(target), originalDigest = taskVersion(result.task);
    const marker = result.capacityExploration;
    result.task = { ...result.task, status: control };
    expect(taskVersion(result.task)).toBe(originalDigest);
    expect(result.capacityExploration).toBe(marker);
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(true);
    expect(capacityExplorationWorkerCanTask(prover, result.task, result)).toBe(false);
    expect(routeAllowsTask(result.task, [target, result])).toBe(false);
    expect(readyResearchTasks([target, result])).not.toContain(result);
    target.task = { ...target.task, status: control };
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(false);
  });

  it('requires the complete record marker and its fixed worker owner', () => {
    const target = node('target'), result = exploration(target);
    expect(capacityExplorationWorkerCanTask(prover, result.task, result)).toBe(true);
    expect(capacityExplorationWorkerCanTask({ ...prover, id: 'other-prover' }, result.task, result)).toBe(false);
    expect(capacityExplorationWorkerCanTask(prover, result.task)).toBe(false);
    expect(capacityExplorationWorkerCanTask(prover, result.task, { ...result, capacityExploration: undefined })).toBe(false);
    for (const role of ['researcher', 'engineer', 'lead', 'reviewer'])
      expect(capacityExplorationWorkerCanTask({ ...prover, role }, result.task, result)).toBe(false);
    expect(capacityExplorationWorkerCanTask(prover, { ...result.task, ownerId: 'other-prover' }, result)).toBe(false);
    expect(capacityExplorationWorkerCanTask(prover, { ...result.task, status: 'paused' }, result)).toBe(false);
  });

  it('does not grant research eligibility from a model task field or a capacity-looking identifier', () => {
    const target = node('target'), result = exploration(target);
    const forged = { ...result.task, capacityExploration: result.capacityExploration };
    const ordinary: TaskRecord = { task: forged, status: 'pending', attempts: 0 };
    expect(capacityExplorationWorkerCanTask(prover, ordinary.task, ordinary)).toBe(false);
    expect(currentCapacityExploration(ordinary, [target, ordinary], identity)).toBe(false);
    expect(plannedTaskRecords([target, ordinary])).toEqual([target, ordinary]);
  });

  it.each(['schema', 'inputDigest', 'taskDigest', 'targetTaskDigest', 'workerId', 'focus'] as const)(
    'rejects a changed host marker field: %s', field => {
      const target = node('target'), result = exploration(target);
      result.capacityExploration = { ...result.capacityExploration, [field]: 'corrupt' } as CapacityExploration;
      expect(currentCapacityExploration(result, [target, result], identity)).toBe(false);
      expect(capacityExplorationWorkerCanTask(prover, result.task, result)).toBe(false);
    });

  it('checks exact task digest and owner separately because taskVersion excludes ownerId', () => {
    const target = node('target'), result = exploration(target), digest = taskVersion(result.task);
    result.task = { ...result.task, ownerId: 'other-prover' };
    expect(taskVersion(result.task)).toBe(digest);
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(false);
    expect(capacityExplorationWorkerCanTask({ ...prover, id: 'other-prover' }, result.task, result)).toBe(false);
    result.task = { ...result.task, ownerId: prover.id, objective: 'An arbitrary unrelated research request' };
    expect(currentCapacityExploration(result, [target, result], identity)).toBe(false);
  });

  it.each(['target-contract', 'target-revision', 'local-input', 'checked-target', 'removed-target', 'environment', 'problem'] as const)(
    'retires stale bindings when %s changes', change => {
      const input = node('input'), target = node('target', ['input']), tasks = [target, input];
      const result = exploration(target, tasks), nextIdentity = { ...identity };
      tasks.push(result);
      if (change === 'target-contract') target.task = { ...target.task, type: 'False' };
      if (change === 'target-revision') target.task = { ...target.task, revision: 1 };
      if (change === 'local-input') checked(input);
      if (change === 'checked-target') checked(target);
      if (change === 'removed-target') tasks.splice(tasks.indexOf(target), 1);
      if (change === 'environment') nextIdentity.environmentDigest = 'changed-environment';
      if (change === 'problem') nextIdentity.problemReceiptDigest = 'changed-problem';
      expect(currentCapacityExploration(result, tasks, nextIdentity)).toBe(false);
    });

  it('excludes host tasks from base planning while retaining every ordinary record by reference', () => {
    const target = node('target'), result = exploration(target);
    const ordinary: TaskRecord = { task: { id: 'capacity_' + 'a'.repeat(40), kind: 'research', revision: 0,
      objective: 'An ordinary Lead research task', dependsOn: [] }, status: 'pending', attempts: 0 };
    const records = [result, ordinary, target], base = plannedTaskRecords(records);
    expect(base).toEqual([ordinary, target]);
    expect(base[0]).toBe(ordinary); expect(base[1]).toBe(target);
    expect(records).toEqual([result, ordinary, target]);
  });
});

describe('optional exploration priority', () => {
  it.each(['last-worker-slot', 'last-group-slot'] as const)(
    'keeps ready typed work ahead of a backup-route exploration at the %s', capacity => {
      const typed = node('preferred_input'), closing = node('preferred_closing', [typed.task.id]);
      const backup = node('backup_input'), backupClosing = node('backup_closing', [backup.task.id]);
      const goal = node('original', [], 'goal');
      goal.alternativeRoutes = [
        { id: 'preferred', targetTaskId: goal.task.id, prerequisiteTaskIds: [typed.task.id], closingTaskId: closing.task.id },
        { id: 'backup', targetTaskId: goal.task.id, prerequisiteTaskIds: [backup.task.id], closingTaskId: backupClosing.task.id },
      ];
      const running: TaskRecord = { task: { id: 'preferred_research', kind: 'research', revision: 0,
        objective: 'Investigate the preferred input independently.', dependsOn: [typed.task.id] }, status: 'running', attempts: 1 };
      running.assignment = { taskId: running.task.id, taskDigest: taskVersion(running.task),
        workerId: 'active-researcher', seedCommit: 'seed' };
      const tasks = [typed, closing, backup, backupClosing, goal, running];
      const optional = exploration(backup, tasks); tasks.push(optional);
      const groups = [{ group: { id: 'main', objective: 'Prove the original goal', status: 'active' as const,
        revision: 0, maxConcurrent: capacity === 'last-group-slot' ? 2 : 7 }, turns: 0, busy: 1 }];
      const worker = (id: string, role: ResearchWorker['role']): ResearchWorker =>
        ({ id, role, worktree: `/unused/${id}`, ownedFiles: ['Submission.lean'] });
      const peer = worker(prover.id, 'prover'), live = [peer, worker('active-researcher', 'researcher'),
        ...(capacity === 'last-group-slot' ? [worker('another-prover', 'prover')] : [])];
      const focus = originalGoalTaskFocus(tasks, groups);
      expect(focus.preferred.support.has(typed.task.id)).toBe(true);
      expect(focus.preferred.support.has(running.task.id)).toBe(true);
      expect(focus.preferred.support.has(optional.task.id)).toBe(false);
      expect(assignSharedResearchTask([optional, typed], peer, live, groups, tasks)).toBe(typed);
      expect(assignSharedResearchTask([optional], peer, live, groups, tasks)).toBe(optional);
    });
});
