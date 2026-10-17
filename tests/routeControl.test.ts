import { describe, expect, it } from 'vitest';
import { recordRouteBlockers, refreshRouteBlockers, routeBlockerBasis, validateBlockerProposals,
  type BlockerProposal, type RouteBlocker } from '../src/solver/routeControl';
import { readyResearchTasks, researchCanAdvance, routeAllowsTask } from '../src/solver/modules/search';
import { markTaskAcceptance, taskVersion, type RouteRecord, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';

const environment = 'environment', problem = 'frozen-problem';
const proposal: BlockerProposal = { mechanism: 'missing stable-specific inequality', scope: 'the proposed saturation shortcut',
  evidenceRefs: ['local-counterexample'] };

function node(id: string, dependsOn: string[] = [], kind: TaskRecord['task']['kind'] = 'lemma'): TaskRecord {
  return { task: { id, kind, objective: `Prove ${id}`, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: `Submission.${id}`, proofPath: 'Submission.lean', type: 'True' } : {}) },
    status: 'pending', attempts: 0 };
}

function checked(item: TaskRecord, options: { fresh?: boolean; proofText?: string; environment?: string } = {}): TaskProof {
  const proof = item.integratedCheck = { taskDigest: taskVersion(item.task), passed: true, commit: 'canonical',
    sourceDigest: 'source', seedCommit: 'seed',
    changes: [{ file: item.task.proofPath!, name: item.task.theoremName!,
      after: `theorem ${item.task.theoremName!} : ${item.task.type!} := ${options.proofText ?? 'by trivial'}\n` }],
    verification: { status: 'kernel_verified', targetCommit: 'projection', results: [
      { status: 'kernel_verified', targetCommit: 'projection', receiptId: 'receipt' },
    ] }, references: { environmentDigest: options.environment ?? environment, sourceCommit: 'projection', contextDigest: 'context',
      inputs: [{ file: item.task.proofPath!, name: item.task.theoremName!, digest: options.proofText ?? 'by trivial' }],
      root: { file: item.task.proofPath!, name: item.task.theoremName! }, tasks: [], statement: [], proof: [] } } as TaskProof;
  item.status = 'integrated';
  if (options.fresh !== false) markTaskAcceptance(proof);
  return proof;
}

function report(records: RouteBlocker[], item: TaskRecord, tasks: TaskRecord[], value: BlockerProposal[] = [proposal], at = 10) {
  return recordRouteBlockers(records, validateBlockerProposals(value, item.task, tasks), item.task, tasks, environment, problem, at);
}

function parked(item: TaskRecord, tasks: TaskRecord[], value: BlockerProposal = proposal) {
  const records: RouteBlocker[] = [];
  report(records, item, tasks, [value], 1); report(records, item, tasks, [value], 2);
  refreshRouteBlockers(records, tasks, environment, problem, 3);
  expect(item.routeParking).toEqual([records[0].id]);
  return records;
}

describe('route blocker proposals', () => {
  it('normalizes reports and permits reopen evidence only from the declared dependency cone', () => {
    const root = node('root'), intermediate = node('intermediate', ['root']), target = node('target', ['intermediate']);
    const unrelated = node('unrelated'), tasks = [root, intermediate, target, unrelated];
    const [value] = validateBlockerProposals([{ mechanism: '  missing\n inequality ', scope: ' local   route ' }], target.task, tasks);
    expect(value).toMatchObject({ mechanism: 'missing inequality', scope: 'local route' });
    expect(value.reopenOn).toEqual([{ kind: 'contract-changed' }, { kind: 'environment-changed' },
      { kind: 'dependency-checked', taskId: 'intermediate' }, { kind: 'dependency-checked', taskId: 'root' }]);
    expect(() => validateBlockerProposals([{ ...proposal, reopenOn: [{ kind: 'dependency-checked', taskId: unrelated.task.id }] }],
      target.task, tasks)).toThrow('math_route_blocker_invalid');
  });

  it.each([null, {}, [null], [{ ...proposal, scope: '' }], [{ ...proposal, scope: 12 }],
    [{ ...proposal, scope: 'x'.repeat(2001) }], [{ ...proposal, mechanism: ' ' }],
    [{ ...proposal, evidenceRefs: [42] }], [{ ...proposal, reopenOn: [] }],
    [{ ...proposal, reopenOn: [{ kind: 'model-says-resolved' }] }],
    [{ ...proposal, reopenOn: [{ kind: 'dependency-checked' }] }],
  ])('rejects malformed local scopes and reopening policies (%#)', value => {
    const target = node('target');
    expect(() => validateBlockerProposals(value, target.task, [target])).toThrow('math_route_blocker_invalid');
  });

  it('does not coerce a non-string dependency identifier into a valid reopening condition', () => {
    const input = node('1'), target = node('target', ['1']);
    expect(() => validateBlockerProposals([{ ...proposal, reopenOn: [{ kind: 'dependency-checked', taskId: 1 }] }],
      target.task, [input, target])).toThrow('math_route_blocker_invalid');
  });

  it('handles valid dependency identifiers that coincide with object prototype property names', () => {
    const input = node('__proto__'), target = node('target', ['__proto__']), tasks = [input, target];
    const basis = routeBlockerBasis(target.task, tasks, environment, problem);
    expect(Object.hasOwn(basis.dependencies, '__proto__')).toBe(true);
    const [value] = validateBlockerProposals([proposal], target.task, tasks);
    expect(value.reopenOn).toContainEqual({ kind: 'dependency-checked', taskId: '__proto__' });
  });
});

describe('local recurrence and parking', () => {
  it('counts duplicate proposals in one response once and parks after a second distinct report', () => {
    const target = node('target'), tasks = [target], records: RouteBlocker[] = [];
    report(records, target, tasks, [proposal, { ...proposal, evidenceRefs: ['second-reference'] }]);
    expect(records).toHaveLength(1); expect(records[0]).toMatchObject({ count: 1, status: 'open', evidenceStatus: 'advisory' });
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toEqual([]);
    report(records, target, tasks);
    refreshRouteBlockers(records, tasks, environment, problem);
    expect(records[0]).toMatchObject({ count: 2, status: 'parked' });
    expect(target.routeParking).toEqual([records[0].id]);
  });

  it('keeps separate advisory obligations separate even when their group and blocker wording match', () => {
    const left = node('left', [], 'research'), right = node('right', [], 'research');
    const tasks = [left, right], records: RouteBlocker[] = [];
    report(records, left, tasks); report(records, right, tasks);
    expect(records).toHaveLength(2);
    expect(records.map(item => [item.taskId, item.count, item.status])).toEqual([
      ['left', 1, 'open'], ['right', 1, 'open'],
    ]);
    report(records, left, tasks); refreshRouteBlockers(records, tasks, environment, problem);
    expect(left.routeParking).toHaveLength(1); expect(right.routeParking).toEqual([]);
  });

  it('preserves recurrence through cosmetic task edits and new advisory references or reopen policies', () => {
    const target = node('target'), tasks = [target], records: RouteBlocker[] = [];
    report(records, target, tasks);
    const originalPolicy = records[0].reopenOn;
    target.task = { ...target.task, revision: 4, objective: 'Try the same inference in more detail', ownerId: 'another-worker' };
    report(records, target, tasks, [{ ...proposal, evidenceRefs: ['new-advisory-note'], reopenOn: [{ kind: 'environment-changed' }] }]);
    expect(records).toHaveLength(1);
    expect(records[0]).toMatchObject({ count: 2, status: 'parked', taskDigest: taskVersion(target.task) });
    expect(records[0].reopenOn).toEqual(originalPolicy);
    expect(records[0].evidenceRefs).toEqual(['local-counterexample', 'new-advisory-note']);
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toHaveLength(1);
  });

  it('ignores unrelated helpers, whole-file hashes, commits and receipt IDs', () => {
    const input = node('input'), target = node('target', ['input']); checked(input);
    const tasks = [input, target], records: RouteBlocker[] = [];
    report(records, target, tasks);
    const before = routeBlockerBasis(target.task, tasks, environment, problem);
    const extra = node('unrelated'); checked(extra); tasks.push(extra);
    const proof = input.integratedCheck!;
    proof.commit = 'new-canonical'; proof.sourceDigest = 'changed-whole-file'; proof.seedCommit = 'new-seed';
    proof.verification.targetCommit = 'new-projection';
    proof.verification.results[0] = { ...proof.verification.results[0], targetCommit: 'new-projection', receiptId: 'new-receipt' };
    proof.references!.sourceCommit = 'new-projection'; proof.references!.contextDigest = 'changed-file-context';
    proof.references!.inputs.push({ file: 'Submission.lean', digest: 'whole-file-changed' });
    proof.changes.push({ file: 'Submission.lean', name: 'Submission.unrelated', after: 'theorem unrelated : True := by trivial\n' });
    markTaskAcceptance(proof);
    expect(routeBlockerBasis(target.task, tasks, environment, problem)).toEqual(before);
    report(records, target, tasks);
    expect(records).toHaveLength(1); expect(records[0].count).toBe(2);
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toHaveLength(1);
  });

  it('does not treat invalidation from a dependency prose edit as new mathematical evidence', () => {
    const input = node('input'), target = node('target', ['input']); checked(input);
    const tasks = [input, target], records: RouteBlocker[] = [];
    report(records, target, tasks);
    input.task = { ...input.task, revision: 1, objective: 'A clearer explanation of the same exact lemma' };
    report(records, target, tasks);
    expect(records).toHaveLength(1);
    expect(records[0]).toMatchObject({ count: 2, status: 'parked' });
  });

  it('does not reset recurrence when untrusted restored dependency receipts appear between reports', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [input, target], records: RouteBlocker[] = [];
    report(records, target, tasks);
    checked(input, { fresh: false });
    input.integratedCheck = JSON.parse(JSON.stringify(input.integratedCheck));
    report(records, target, tasks);
    expect(records).toHaveLength(1);
    expect(records[0]).toMatchObject({ count: 2, status: 'parked' });
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toHaveLength(1);
  });

  it('parks only the affected inference and leaves other work schedulable without refuting an original goal', () => {
    const shortcut = node('shortcut', [], 'research'), sibling = node('sibling', [], 'research'), alternative = node('alternative', [], 'research');
    alternative.task = { ...alternative.task, groupId: 'other' };
    const original = node('original', [], 'goal'), tasks = [shortcut, sibling, alternative, original];
    const groups: RouteRecord[] = ['main', 'other'].map(id => ({ group: { id, objective: id, status: 'active', revision: 0 }, turns: 0 }));
    const records = parked(shortcut, tasks);
    expect(records[0]).toMatchObject({ evidenceStatus: 'advisory', taskId: 'shortcut', status: 'parked' });
    expect(original.status).toBe('pending'); expect(original.integratedCheck).toBeUndefined();
    expect(routeAllowsTask(shortcut.task, tasks, groups)).toBe(false);
    expect(routeAllowsTask(sibling.task, tasks, groups)).toBe(true);
    expect(routeAllowsTask(alternative.task, tasks, groups)).toBe(true);
    expect(readyResearchTasks(tasks, groups).map(item => item.task.id)).toEqual(['sibling', 'alternative', 'original']);
    expect(researchCanAdvance([shortcut], groups, new Set(['researcher']))).toBe(false);
    expect(researchCanAdvance(tasks, groups, new Set(['researcher']))).toBe(true);
  });

  it('handles cyclic restored dependency plans without recursion failure or inventing progress', () => {
    const left = node('left', ['right']), right = node('right', ['left']), tasks = [left, right];
    expect(() => routeBlockerBasis(left.task, tasks, environment, problem)).not.toThrow();
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set(['engineer']))).toBe(false);
  });
});

describe('blocker reopening', () => {
  it('requires fresh checked local dependency evidence and rejects restored JSON receipts', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [input, target];
    const records = parked(target, tasks, { ...proposal, reopenOn: [{ kind: 'dependency-checked', taskId: input.task.id }] });
    checked(input, { fresh: false });
    input.integratedCheck = JSON.parse(JSON.stringify(input.integratedCheck));
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(records[0].status).toBe('parked'); expect(target.routeParking).toHaveLength(1);
    markTaskAcceptance(input.integratedCheck!);
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([records[0]]);
    expect(records[0]).toMatchObject({ status: 'reopened', reopenedReason: 'dependency-checked' });
    expect(target.routeParking).toEqual([]);
  });

  it.each(['conditional', 'stale-task', 'stale-environment', 'failed', 'no-fresh-check'] as const)(
    'does not reopen from a %s dependency receipt', invalid => {
      const input = node('input'), target = node('target', ['input']), tasks = [input, target];
      const records = parked(target, tasks, { ...proposal, reopenOn: [{ kind: 'dependency-checked', taskId: input.task.id }] });
      const proof = checked(input, { fresh: false, ...(invalid === 'stale-environment' ? { environment: 'old-environment' } : {}) });
      if (invalid === 'conditional') proof.conditions = [{ taskId: 'open', taskDigest: 'open-version' }];
      if (invalid === 'stale-task') proof.taskDigest = 'previous-task-version';
      if (invalid === 'failed') proof.passed = false;
      if (invalid !== 'no-fresh-check') markTaskAcceptance(proof);
      expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
      expect(target.routeParking).toHaveLength(1);
    });

  it('does not reopen for an unrelated fresh check or for a replay of the same local proof', () => {
    const input = node('input'), unrelated = node('unrelated'), target = node('target', ['input']); checked(input);
    const tasks = [input, unrelated, target], records = parked(target, tasks);
    checked(unrelated); checked(input);
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toHaveLength(1);
  });

  it('reopens when a newly checked local dependency actually changes the relevant proof', () => {
    const input = node('input'), target = node('target', ['input']); checked(input);
    const tasks = [input, target], records = parked(target, tasks);
    checked(input, { proofText: 'by exact True.intro' });
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([records[0]]);
    expect(records[0].reopenedReason).toBe('dependency-checked');
    expect(target.routeParking).toEqual([]);
  });

  it('respects explicit reopen policies for changed contracts and environments', () => {
    const target = node('target'), tasks = [target];
    const records = parked(target, tasks, { ...proposal, reopenOn: [{ kind: 'contract-changed' }] });
    expect(refreshRouteBlockers(records, tasks, 'new-environment', problem)).toEqual([]);
    target.task = { ...target.task, premises: ['a genuinely new mathematical premise'] };
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([records[0]]);
    expect(records[0].reopenedReason).toBe('contract-changed');
    const toolTarget = node('tool_target'), toolTasks = [toolTarget];
    const toolRecords = parked(toolTarget, toolTasks, { ...proposal, reopenOn: [{ kind: 'environment-changed' }] });
    expect(refreshRouteBlockers(toolRecords, toolTasks, 'new-environment', problem)).toEqual([toolRecords[0]]);
    expect(toolRecords[0].reopenedReason).toBe('environment-changed');
  });

  it('recognizes a changed dependency contract or frozen problem identity as material', () => {
    const input = node('input'), target = node('target', ['input']), tasks = [input, target];
    const records = parked(target, tasks);
    input.task = { ...input.task, type: 'True ∧ True' };
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([records[0]]);
    expect(records[0].reopenedReason).toBe('contract-changed');
    const sameTarget = node('same_target'), sameTasks = [sameTarget], sameRecords = parked(sameTarget, sameTasks);
    expect(refreshRouteBlockers(sameRecords, sameTasks, environment, 'different-frozen-problem')).toEqual([sameRecords[0]]);
  });

  it('supersedes a removed or moved scope and never leaks its parking to another task', () => {
    const target = node('target'), sibling = node('sibling'), tasks = [target, sibling], records = parked(target, tasks);
    target.task = { ...target.task, groupId: 'new-route' };
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(records[0].status).toBe('superseded'); expect(target.routeParking).toEqual([]); expect(sibling.routeParking).toEqual([]);
    const removed = node('removed'), removable = [removed, sibling], removedRecords = parked(removed, removable);
    expect(refreshRouteBlockers(removedRecords, [sibling], environment, problem)).toEqual([]);
    expect(removedRecords[0].status).toBe('superseded'); expect(sibling.routeParking).toEqual([]);
  });

  it('clears parking for the assigned obligation only after its own fresh unconditional check', () => {
    const target = node('target'), tasks = [target], records = parked(target, tasks);
    const proof = checked(target, { fresh: false });
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([]);
    expect(target.routeParking).toHaveLength(1);
    markTaskAcceptance(proof);
    expect(refreshRouteBlockers(records, tasks, environment, problem)).toEqual([records[0]]);
    expect(records[0].reopenedReason).toBe('assigned-obligation-checked');
    expect(target.routeParking).toEqual([]);
  });
});
