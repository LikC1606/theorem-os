import { describe, expect, it } from 'vitest';
import { describeProofRoutes, parseProofRoutes, proofRouteReady, type ProofRoute } from '../src/solver/proofRoutes';
import { markTaskAcceptance, taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';

function node(id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord {
  return { task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: `Submission.${id}`, type: 'True' } : {}) },
    status: 'pending', attempts: 0 };
}

function checked(item: TaskRecord, uses: TaskRecord[] = [], fresh = true) {
  item.status = 'integrated';
  const digest = taskVersion(item.task);
  const proof = item.integratedCheck = { taskDigest: digest, passed: true, commit: 'canonical', sourceDigest: 'source',
    seedCommit: 'seed', changes: [], verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: `receipt-${item.task.id}`, proofPath: item.task.proofPath,
        theoremName: item.task.theoremName, statementHash: digest, leanStatementHash: digest },
    ] }, references: { environmentDigest: 'environment', sourceCommit: 'canonical', contextDigest: 'context', inputs: [],
      root: { file: item.task.proofPath!, name: item.task.theoremName! },
      tasks: uses.map(input => ({ taskId: input.task.id, taskDigest: taskVersion(input.task) })),
      statement: [], proof: uses.map(input => ({ file: input.task.proofPath!, name: input.task.theoremName! })) } } as TaskProof;
  if (fresh) markTaskAcceptance(proof);
  return proof;
}

function fixture() {
  const first = node('first'), second = node('second'), closing = node('closing', 'lemma', ['first', 'second']);
  closing.task = { ...closing.task, type: '∀ n : ℕ, n = n' };
  const goal = node('goal', 'goal');
  const route: ProofRoute = { id: 'route', targetTaskId: 'goal', prerequisiteTaskIds: ['first', 'second'], closingTaskId: 'closing' };
  return { first, second, closing, goal, route, tasks: [first, second, closing, goal] };
}

describe('proof route interfaces', () => {
  it('keeps legacy plans empty and alternatives separate from the frozen goal dependencies', () => {
    const { route, tasks, goal } = fixture(), alternate = node('alternate', 'lemma', ['first']);
    const routes = [route, { ...route, id: 'alternative', closingTaskId: 'alternate', prerequisiteTaskIds: ['first'] }];
    expect(parseProofRoutes(undefined, tasks.map(item => item.task))).toEqual([]);
    expect(parseProofRoutes(routes, [...tasks, alternate].map(item => item.task))).toEqual(routes);
    expect(goal.task.dependsOn).toEqual([]);
  });

  it('copies prerequisite lists and retains the full exact closing interface', () => {
    const { route, tasks, closing } = fixture();
    const parsed = parseProofRoutes([route], tasks.map(item => item.task));
    (route.prerequisiteTaskIds as string[]).push('changed-after-parsing');
    expect(parsed[0].prerequisiteTaskIds).toEqual(['first', 'second']);
    expect(describeProofRoutes(parsed, tasks).routes[0].closingType).toBe(closing.task.type);
  });

  it.each([
    null, {}, 'route', [null], [{ id: 'route' }],
    [{ id: 'route', targetTaskId: 'goal', prerequisiteTaskIds: [], closingTaskId: 'closing', accepted: true }],
    [{ id: 'route', targetTaskId: 'goal', prerequisiteTaskIds: ['first', 'first'], closingTaskId: 'closing' }],
    [{ id: 'route', targetTaskId: 'goal', prerequisiteTaskIds: 'first', closingTaskId: 'closing' }],
  ])('rejects malformed route payload %j', payload => {
    const { tasks } = fixture();
    expect(() => parseProofRoutes(payload, tasks.map(item => item.task))).toThrow(/math_plan_invalid_proof_route/u);
  });

  it('rejects duplicate route IDs and duplicate closure aliases for one target', () => {
    const { route, tasks } = fixture(), plan = tasks.map(item => item.task);
    expect(() => parseProofRoutes([route, route], plan)).toThrow('math_plan_duplicate_proof_route');
    expect(() => parseProofRoutes([route, { ...route, id: 'alias' }], plan)).toThrow('math_plan_duplicate_proof_route');
  });

  it('requires existing original goals and exact mathematical input interfaces', () => {
    const { route, tasks, first, closing } = fixture();
    expect(() => parseProofRoutes([{ ...route, targetTaskId: 'first' }], tasks.map(item => item.task)))
      .toThrow('math_plan_invalid_proof_route_target');
    expect(() => parseProofRoutes([{ ...route, closingTaskId: 'missing' }], tasks.map(item => item.task)))
      .toThrow('math_plan_invalid_proof_route_input');
    first.task = { ...first.task, kind: 'research', type: undefined };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_invalid_proof_route_input');
    first.task = { ...first.task, kind: 'lemma', type: 'True' };
    closing.task = { ...closing.task, type: 'FULL_CLOSED_LEAN_TYPE' };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_invalid_proof_route_input');
    closing.task = { ...closing.task, type: undefined };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_invalid_proof_route_input');
  });

  it('requires the closing task to depend on every prerequisite, allowing transitive inputs', () => {
    const { route, tasks, closing, second } = fixture();
    closing.task = { ...closing.task, dependsOn: ['second'] };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_proof_route_missing_prerequisite');
    second.task = { ...second.task, dependsOn: ['first'] };
    expect(parseProofRoutes([route], tasks.map(item => item.task))).toEqual([route]);
  });

  it('rejects ordinary cycles, hidden target assumptions, and cycles spanning alternative goal connections', () => {
    const { route, tasks, first } = fixture();
    first.task = { ...first.task, dependsOn: ['closing'] };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_proof_route_cycle');
    first.task = { ...first.task, dependsOn: ['goal'] };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_proof_route_cycle');
    first.task = { ...first.task, dependsOn: ['other_goal'] };
    const otherGoal = node('other_goal', 'goal'), otherClosing = node('other_closing', 'lemma', ['goal']);
    expect(() => parseProofRoutes([route, { id: 'other', targetTaskId: 'other_goal', closingTaskId: 'other_closing',
      prerequisiteTaskIds: [] }], [...tasks, otherGoal, otherClosing].map(item => item.task))).toThrow('math_plan_proof_route_cycle');
  });

  it('rejects missing task dependencies and cross-group private route inputs', () => {
    const { route, tasks, first, closing } = fixture();
    first.task = { ...first.task, dependsOn: ['missing'] };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_missing_dependency');
    first.task = { ...first.task, dependsOn: [], groupId: 'other', sharing: 'group' };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_proof_route_input_not_shared');
    first.task = { ...first.task, sharing: 'problem' };
    closing.task = { ...closing.task, groupId: 'other', sharing: 'group' };
    expect(() => parseProofRoutes([route], tasks.map(item => item.task))).toThrow('math_plan_proof_route_input_not_shared');
    closing.task = { ...closing.task, sharing: 'problem' };
    expect(parseProofRoutes([route], tasks.map(item => item.task))).toEqual([route]);
  });
});

describe('proof route evidence boundaries', () => {
  it('requires every prerequisite within a route, while another completed route can be ready', () => {
    const { route, tasks, first, closing } = fixture();
    checked(first); checked(closing, [first]);
    expect(proofRouteReady(route, tasks, 'environment')).toBe(false);
    const alternate = node('alternate'); checked(alternate);
    expect(proofRouteReady({ id: 'alternate', targetTaskId: 'goal', prerequisiteTaskIds: [], closingTaskId: 'alternate' },
      [...tasks, alternate], 'environment')).toBe(true);
    expect(describeProofRoutes([route], tasks).routes[0].remainingPrerequisiteTaskIds).toEqual(['second']);
  });

  it('does not promote complete helper receipts into an original-goal check', () => {
    const { route, tasks, first, second, closing } = fixture();
    checked(first); checked(second); checked(closing, [first, second]);
    expect(proofRouteReady(route, tasks, 'environment')).toBe(true);
    const report = describeProofRoutes([route], tasks, 'environment');
    expect(report).toMatchObject({ evidence: 'recorded-not-replayed', routes: [{ ready: true,
      evidence: 'recorded-not-replayed', closingStatus: 'checked', targetStatus: 'none', connection: 'awaiting-original-check' }] });
  });

  it('requires fresh host acceptance for dispatch even if archived receipts are complete', () => {
    const { route, tasks, first, second, closing } = fixture();
    checked(first); checked(second); checked(closing, [first, second]);
    const restored: TaskRecord[] = JSON.parse(JSON.stringify(tasks));
    expect(proofRouteReady(route, restored, 'environment')).toBe(false);
    expect(proofRouteReady(route, restored, 'environment', false)).toBe(true);
    expect(describeProofRoutes([route], restored, 'environment').routes[0].ready).toBe(true);
  });

  it.each(['empty', 'failed', 'wrong-commit', 'wrong-target', 'wrong-digest', 'missing-id'] as const)
    ('does not accept a %s receipt despite nominal integration', change => {
      const { route, tasks, first, second, closing } = fixture();
      checked(first); checked(second); const proof = checked(closing, [first, second]);
      const receipt = proof.verification.results[0];
      if (change === 'empty') proof.verification.results = [];
      if (change === 'failed') receipt.status = 'failed';
      if (change === 'wrong-commit') receipt.targetCommit = 'different';
      if (change === 'wrong-target') receipt.theoremName = 'Submission.unrelated';
      if (change === 'wrong-digest') receipt.statementHash = 'unrelated-version';
      if (change === 'missing-id') receipt.receiptId = '';
      markTaskAcceptance(proof);
      expect(proofRouteReady(route, tasks)).toBe(false);
      expect(describeProofRoutes([route], tasks).routes[0].closingStatus).toBe('unverified');
    });

  it('rejects changed task and input versions, including omitted reference inputs', () => {
    const { route, tasks, first, second, closing } = fixture();
    checked(first); checked(second); const proof = checked(closing, [first, second]);
    proof.references!.tasks![0].taskDigest = 'old-version';
    expect(proofRouteReady(route, tasks)).toBe(false);
    expect(describeProofRoutes([route], tasks).routes[0].closingStatus).toBe('stale');
    proof.references!.tasks![0].taskDigest = taskVersion(first.task);
    delete proof.references!.tasks;
    expect(proofRouteReady(route, tasks)).toBe(false);
    expect(describeProofRoutes([route], tasks).routes[0].referenceCoverageMissing).toContain('closing');
    proof.references!.tasks = [];
    closing.task = { ...closing.task, revision: 1 };
    expect(describeProofRoutes([route], tasks).routes[0].closingStatus).toBe('stale');
  });

  it('fails closed when a requested environment cannot be matched', () => {
    const { route, tasks, first, second, closing } = fixture();
    checked(first); checked(second); const proof = checked(closing, [first, second]);
    expect(proofRouteReady(route, tasks, 'different')).toBe(false);
    expect(describeProofRoutes([route], tasks, 'different').routes[0].closingStatus).toBe('stale');
    delete proof.references;
    expect(proofRouteReady(route, tasks, 'environment')).toBe(false);
  });

  it('rejects conditional, merely delivered, and proof-only records', () => {
    const { route, tasks, first, second, closing } = fixture();
    checked(first); checked(second); const proof = checked(closing, [first, second]);
    proof.conditions = [{ taskId: 'first', taskDigest: taskVersion(first.task) }];
    expect(proofRouteReady(route, tasks)).toBe(false);
    expect(describeProofRoutes([route], tasks).routes[0].closingStatus).toBe('conditional');
    delete proof.conditions; markTaskAcceptance(proof);
    closing.status = 'delivered';
    expect(proofRouteReady(route, tasks)).toBe(false);
    closing.status = 'integrated'; closing.proof = proof; delete closing.integratedCheck;
    expect(proofRouteReady(route, tasks)).toBe(false);
  });

  it('requires current transitive evidence and forbids actual circular target use omitted from the plan', () => {
    const { route, tasks, first, second, closing, goal } = fixture();
    const inner = node('inner'); checked(inner); checked(first, [inner]); checked(second); checked(closing, [first, second]);
    expect(proofRouteReady(route, [...tasks, inner], 'environment')).toBe(true);
    inner.status = 'pending';
    expect(proofRouteReady(route, [...tasks, inner], 'environment')).toBe(false);
    checked(goal); checked(first, [goal]);
    expect(proofRouteReady(route, tasks, 'environment')).toBe(false);
  });

  it('requires original proof references to the exact closing task and declaration', () => {
    const { route, tasks, first, second, closing, goal } = fixture();
    checked(first); checked(second); checked(closing, [first, second]);
    const proof = checked(goal, [closing]);
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].connection).toBe('closed-by-original-check');
    proof.references!.statement = proof.references!.proof; proof.references!.proof = [];
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].connection).toBe('awaiting-original-check');
    proof.references!.proof = [{ file: 'Submission.lean', name: closing.task.theoremName! }];
    proof.references!.tasks = [];
    expect(describeProofRoutes([route], tasks, 'environment').routes[0].connection).toBe('awaiting-original-check');
    delete proof.references;
    expect(describeProofRoutes([route], tasks, 'environment').routes[0]).toMatchObject({ connection: 'awaiting-original-check',
      referenceCoverageMissing: ['goal'] });
  });

  it('keeps conditional original goals open even when the closing declaration is referenced', () => {
    const { route, tasks, first, second, closing, goal } = fixture();
    checked(first); checked(second); checked(closing, [first, second]);
    checked(goal, [closing]).conditions = [{ taskId: 'first', taskDigest: taskVersion(first.task) }];
    goal.status = 'conditional';
    expect(describeProofRoutes([route], tasks, 'environment').routes[0]).toMatchObject({ targetStatus: 'conditional',
      connection: 'awaiting-original-check' });
  });

  it.each(['receipt', 'root', 'task-references', 'declaration-references'] as const)
    ('fails closed on malformed restored %s data', invalid => {
      const { route, tasks, first, second, closing, goal } = fixture();
      checked(first); checked(second); checked(closing, [first, second]); checked(goal, [closing]);
      const restored: TaskRecord[] = JSON.parse(JSON.stringify(tasks));
      const restoredClosing = restored.find(item => item.task.id === 'closing')!.integratedCheck!;
      const restoredGoal = restored.find(item => item.task.id === 'goal')!.integratedCheck!;
      if (invalid === 'receipt') restoredClosing.verification.results = [null] as any;
      if (invalid === 'root') restoredClosing.references!.root = {} as any;
      if (invalid === 'task-references') restoredClosing.references!.tasks = {} as any;
      if (invalid === 'declaration-references') restoredGoal.references!.proof = {} as any;
      if (invalid !== 'declaration-references') expect(proofRouteReady(route, restored, 'environment', false)).toBe(false);
      expect(describeProofRoutes([route], restored, 'environment').routes[0].connection).toBe('awaiting-original-check');
    });
});
