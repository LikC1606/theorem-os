import { describe, expect, it } from 'vitest';
import { captureObligationSnapshot, diffObligationProgress } from '../src/solver/obligationProgress';
import { finalCandidateReviewReady } from '../src/solver/modules/search';
import { hasTaskAcceptance, markTaskAcceptance, taskVersion, type RouteRecord, type TaskRecord } from '../src/solver/tasks';
import type { ProofRoute } from '../src/solver/proofRoutes';
import type { RouteBlocker } from '../src/solver/routeControl';
import { integratedProof } from './helpers/taskProof';

const environmentDigest = 'environment';
function node(id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord {
  return { task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: `Submission.${id}`, proofPath: 'Submission.lean', type: 'True' } : {}) },
    status: 'pending', attempts: 0 };
}
function checked(item: TaskRecord, uses: TaskRecord[] = []) {
  return integratedProof(item, { uses, accept: false, receiptId: 'receipt', sourceCommit: 'projection', environmentDigest,
    inputs: [{ file: item.task.proofPath!, name: item.task.theoremName!, digest: 'declaration' }] });
}
function blocker(item: TaskRecord): RouteBlocker {
  return { id: 'local-obstruction', taskId: item.task.id, taskDigest: taskVersion(item.task), groupId: 'main',
    mechanism: 'short-vector shortcut fails', scope: 'this intermediate saturation inference', evidenceStatus: 'advisory',
    evidenceRefs: ['counterexample-note'], reopenOn: [{ kind: 'contract-changed' }],
    basis: { contractDigest: 'contract', environmentDigest, dependencies: {} }, fingerprint: 'fingerprint',
    count: 1, status: 'open', createdAt: 1, updatedAt: 1 };
}
const snapshot = (tasks: TaskRecord[], options: Parameters<typeof captureObligationSnapshot>[1] = {}) =>
  captureObligationSnapshot(tasks, { environmentDigest, ...options });

describe('obligation snapshots and observed progress', () => {
  it('starts with a baseline without manufacturing closures from existing checked receipts', () => {
    const input = node('input'), goal = node('goal', 'goal', ['input']); checked(input); checked(goal, [input]);
    const state = snapshot([input, goal]), receipt = diffObligationProgress(undefined, state, 10)!;
    expect(state).toMatchObject({ evidence: 'recorded-not-replayed', acceptance: 'not-assessed' });
    expect(state.obligations.every(item => item.closed)).toBe(true);
    expect(receipt).toMatchObject({ kind: 'baseline', at: 10, afterDigest: state.digest,
      obligations: { new: [], closed: [], reopened: [], removed: [], changed: [] }, goalFrontiers: [], routes: [] });
    expect(hasTaskAcceptance(input.integratedCheck!)).toBe(false);
    expect(finalCandidateReviewReady([input, goal])).toBe(false);
  });

  it('ignores dispatches, attempts, assignment metadata, route turns and mere task ordering', () => {
    const helper = node('helper'), goal = node('goal', 'goal'), tasks = [helper, goal];
    const groups: RouteRecord[] = [{ group: { id: 'main', objective: 'main', revision: 0, status: 'active' }, turns: 0 }];
    const before = snapshot(tasks, { groups });
    helper.status = 'running'; helper.attempts = 8;
    helper.assignment = { taskId: 'helper', taskDigest: taskVersion(helper.task), workerId: 'researcher', seedCommit: 'new-seed' };
    groups[0].turns = 100; groups[0].busy = 3;
    const after = snapshot([...tasks].reverse(), { groups });
    expect(after.digest).toBe(before.digest);
    expect(diffObligationProgress(before, after)).toBeUndefined();
  });

  it('reports a checked unrelated helper locally without moving any original-goal frontier', () => {
    const helper = node('unrelated'), goal = node('goal', 'goal'), tasks = [helper, goal];
    const before = snapshot(tasks); checked(helper);
    const receipt = diffObligationProgress(before, snapshot(tasks))!;
    expect(receipt.obligations.closed.map(change => change.after.taskId)).toEqual(['unrelated']);
    expect(receipt.goalFrontiers).toEqual([]);
    expect(receipt.routes).toEqual([]);
    expect(before.goals[0].frontier.map(item => item.taskId)).toEqual(['goal']);
  });

  it('moves the frontier only when a required mathematical input is actually checked', () => {
    const input = node('input'), goal = node('goal', 'goal', ['input']), tasks = [input, goal];
    const before = snapshot(tasks); checked(input);
    const receipt = diffObligationProgress(before, snapshot(tasks))!;
    expect(receipt.obligations.closed.map(change => change.after.taskId)).toEqual(['input']);
    expect(receipt.goalFrontiers).toHaveLength(1);
    expect(receipt.goalFrontiers[0].before!.frontier.map(item => item.taskId)).toEqual(['input']);
    expect(receipt.goalFrontiers[0].after!.frontier.map(item => item.taskId)).toEqual(['goal']);
    expect(receipt.goalFrontiers[0].after!.closed).toBe(false);
  });

  it('does not close the original obligation from a conditional candidate bridge', () => {
    const input = node('input'), goal = node('goal', 'goal', ['input']), tasks = [input, goal];
    const before = snapshot(tasks), proof = checked(goal, [input]);
    proof.conditions = [{ taskId: 'input', taskDigest: taskVersion(input.task) }]; goal.status = 'conditional';
    const after = snapshot(tasks), receipt = diffObligationProgress(before, after)!;
    expect(after.obligations.find(item => item.taskId === 'goal')).toMatchObject({ recordedProof: 'conditional', closed: false });
    expect(receipt.obligations.closed).toEqual([]);
    expect(receipt.goalFrontiers).toEqual([]);
    expect(after.goals[0].frontier.map(item => item.taskId)).toEqual(['input']);
  });

  it('keeps advisory counterexamples and parking local without declaring mathematical closure or falsity', () => {
    const research = node('shortcut', 'research'), goal = node('goal', 'goal'), tasks = [research, goal];
    const before = snapshot(tasks);
    research.status = 'completed'; research.finding = 'The shortcut fails on the recorded finite example; the original theorem remains open.';
    const local = blocker(research); local.status = 'parked'; local.count = 2;
    const after = snapshot(tasks, { blockers: [local] }), receipt = diffObligationProgress(before, after)!;
    expect(receipt.advisory.completed.map(change => change.after.taskId)).toEqual(['shortcut']);
    expect(receipt.blockers.new[0]).toMatchObject({ taskId: 'shortcut', status: 'parked', evidenceStatus: 'advisory' });
    expect(receipt.obligations.closed).toEqual([]); expect(receipt.goalFrontiers).toEqual([]);
    expect(after.goals[0].closed).toBe(false); expect(after.acceptance).toBe('not-assessed');
  });

  it('does not report a mathematical frontier move when an advisory coordination dependency completes', () => {
    const research = node('research', 'research'), core = node('core', 'lemma', ['research']);
    const goal = node('goal', 'goal', ['core']), tasks = [research, core, goal];
    const before = snapshot(tasks); research.status = 'completed'; research.finding = 'A useful informal route';
    const after = snapshot(tasks), receipt = diffObligationProgress(before, after)!;
    expect(before.goals[0].frontier.map(item => item.taskId)).toEqual(['core']);
    expect(after.goals[0].frontier.map(item => item.taskId)).toEqual(['core']);
    expect(receipt.goalFrontiers).toEqual([]); expect(receipt.obligations.closed).toEqual([]);
    expect(receipt.advisory.completed).toHaveLength(1);
  });

  it('does not report frontier progress when completed research and sketch notes still depend on an open theorem', () => {
    const core = node('core'), finding = node('finding', 'research', ['core']), review = node('review', 'sketch', ['finding']);
    const goal = node('goal', 'goal', ['review']), tasks = [core, finding, review, goal];
    const before = snapshot(tasks);
    finding.status = 'completed'; review.status = 'completed';
    finding.finding = 'The open theorem is still required.'; review.finding = 'The route has the same unproved premise.';
    const after = snapshot(tasks), receipt = diffObligationProgress(before, after)!;

    expect(before.goals[0].frontier.map(item => item.taskId)).toEqual(['core']);
    expect(after.goals[0].frontier.map(item => item.taskId)).toEqual(['core']);
    expect(receipt.goalFrontiers).toEqual([]);
    expect(receipt.obligations.closed).toEqual([]);
    expect(receipt.advisory.completed.map(change => change.after.taskId)).toEqual(['finding', 'review']);
    expect(after.goals[0].closed).toBe(false);
    expect(snapshot(JSON.parse(JSON.stringify(tasks))).digest).toBe(after.digest);

    checked(core);
    const proved = snapshot(tasks), mathematical = diffObligationProgress(after, proved)!;
    expect(mathematical.obligations.closed.map(change => change.after.taskId)).toEqual(['core']);
    expect(mathematical.goalFrontiers[0].after!.frontier.map(item => item.taskId)).toEqual(['goal']);
    expect(proved.goals[0].closed).toBe(false);
  });

  it('keeps a missing input visible beneath completed advisory work after restore', () => {
    const finding = node('finding', 'research', ['absent']), review = node('review', 'sketch', ['finding']);
    finding.status = 'completed'; review.status = 'completed';
    const goal = node('goal', 'goal', ['review']);
    const restored: TaskRecord[] = JSON.parse(JSON.stringify([finding, review, goal]));
    const state = snapshot(restored);

    expect(state.goals[0]).toMatchObject({ closed: false, missingDependencies: ['absent'] });
    expect(state.obligations.find(item => item.taskId === 'goal')).toMatchObject({ recordedProof: 'none', closed: false });
  });

  it('binds exact versions and reopens consumers of an invalidated recorded dependency', () => {
    const input = node('input'), goal = node('goal', 'goal', ['input']); checked(input); checked(goal, [input]);
    const tasks = [input, goal], before = snapshot(tasks);
    input.task = { ...input.task, revision: 1, type: 'True ∧ True' };
    const after = snapshot(tasks), receipt = diffObligationProgress(before, after)!;
    expect(after.obligations.every(item => item.recordedProof === 'stale' && !item.closed)).toBe(true);
    expect(receipt.obligations.reopened.map(change => change.after.taskId)).toEqual(['goal', 'input']);
    expect(receipt.goalFrontiers[0].after!.frontier.map(item => item.taskId)).toEqual(['input']);
    expect(before.obligations.find(item => item.taskId === 'input')!.taskDigest).not.toBe(taskVersion(input.task));
  });

  it('reports environment invalidation as a reopening without treating recorded goal checks as official acceptance', () => {
    const goal = node('goal', 'goal'); checked(goal);
    const before = snapshot([goal]), after = snapshot([goal], { environmentDigest: 'different-toolchain' });
    const receipt = diffObligationProgress(before, after)!;
    expect(receipt.environmentChanged).toBe(true);
    expect(receipt.obligations.reopened[0].after).toMatchObject({ taskId: 'goal', recordedProof: 'stale', closed: false });
    expect(receipt.acceptance).toBe('not-assessed');
  });

  it('preserves recorded progress on resume without authorizing fresh dispatch or acceptance', () => {
    const goal = node('goal', 'goal'), proof = checked(goal); markTaskAcceptance(proof);
    const before = snapshot([goal]), restored: TaskRecord[] = JSON.parse(JSON.stringify([goal]));
    expect(hasTaskAcceptance(restored[0].integratedCheck!)).toBe(false);
    const after = snapshot(restored);
    expect(after.digest).toBe(before.digest); expect(after.obligations[0].closed).toBe(true);
    expect(diffObligationProgress(JSON.parse(JSON.stringify(before)), after)).toBeUndefined();
    expect(hasTaskAcceptance(restored[0].integratedCheck!)).toBe(false);
    expect(finalCandidateReviewReady(restored)).toBe(false);
  });

  it('ignores receipts and commits changing during a replay of the same mathematical checkpoint', () => {
    const goal = node('goal', 'goal'), proof = checked(goal), before = snapshot([goal]);
    proof.commit = 'replayed-canonical'; proof.seedCommit = 'replayed-seed'; proof.sourceDigest = 'replayed-source';
    proof.verification.targetCommit = 'replayed-projection'; proof.verification.results[0].targetCommit = 'replayed-projection';
    proof.verification.results[0].receiptId = 'replayed-receipt';
    proof.references!.sourceCommit = 'replayed-projection'; proof.references!.contextDigest = 'replayed-context';
    expect(snapshot([goal]).digest).toBe(before.digest);
  });

  it('keeps paused goals visible and does not call a scheduling pause removal or mathematical progress', () => {
    const goal = node('goal', 'goal'), before = snapshot([goal]);
    goal.task = { ...goal.task, status: 'paused' };
    const groups: RouteRecord[] = [{ group: { id: 'main', objective: 'main', revision: 0, status: 'paused' }, turns: 100 }];
    const after = snapshot([goal], { groups });
    expect(after.goals).toHaveLength(1); expect(after.digest).toBe(before.digest);
    expect(diffObligationProgress(before, after)).toBeUndefined();
  });

  it('separates newly proposed advisory work from new typed obligations and removals', () => {
    const old = node('old'), goal = node('goal', 'goal'), before = snapshot([old, goal]);
    const proposed = node('proposed', 'research'), exact = node('exact');
    const receipt = diffObligationProgress(before, snapshot([goal, proposed, exact]))!;
    expect(receipt.advisory.proposed.map(item => item.taskId)).toEqual(['proposed']);
    expect(receipt.obligations.new.map(item => item.taskId)).toEqual(['exact']);
    expect(receipt.obligations.removed.map(item => item.taskId)).toEqual(['old']);
    expect(receipt.obligations.closed).toEqual([]); expect(receipt.obligations.reopened).toEqual([]);
    expect(receipt.goalFrontiers).toEqual([]);
  });

  it('does not settle an obligation with missing, malformed or merely statement reference evidence', () => {
    const goal = node('goal', 'goal'), proof = checked(goal);
    proof.verification.results = [];
    expect(snapshot([goal]).obligations[0]).toMatchObject({ recordedProof: 'unverified', closed: false });
    checked(goal).references!.scope = 'statement';
    expect(snapshot([goal]).obligations[0]).toMatchObject({ recordedProof: 'unverified', closed: false });
    delete checked(goal).references;
    expect(snapshot([goal]).obligations[0]).toMatchObject({ recordedProof: 'unverified', closed: false, referenceCoverage: 'missing' });
  });

  it.each(['proofPath', 'theoremName', 'statementHash', 'leanStatementHash'] as const)(
    'does not close an exact obligation with a receipt for a different %s', field => {
      const goal = node('goal', 'goal'), proof = checked(goal);
      proof.verification.results[0][field] = 'different-declaration';
      expect(snapshot([goal]).obligations[0]).toMatchObject({ recordedProof: 'unverified', closed: false });
    });

  it('detaches snapshots and lists local blocker parking/reopening while ignoring repeated-report activity', () => {
    const research = node('research', 'research'), goal = node('goal', 'goal'), tasks = [research, goal], local = blocker(research);
    const before = snapshot(tasks, { blockers: [local] });
    local.status = 'parked'; local.count = 2; local.updatedAt = 2;
    const after = snapshot(tasks, { blockers: [local] }), parked = diffObligationProgress(before, after)!;
    expect(before.blockers[0].status).toBe('open'); expect(parked.blockers.parked).toHaveLength(1);
    expect(parked.goalFrontiers).toEqual([]);
    local.count = 3; local.updatedAt = 10;
    expect(snapshot(tasks, { blockers: [local] }).digest).toBe(after.digest);
    local.status = 'reopened'; local.reopenedReason = 'dependency-checked';
    const reopened = diffObligationProgress(after, snapshot(tasks, { blockers: [local] }))!;
    expect(reopened.blockers.reopened).toHaveLength(1); expect(reopened.obligations.closed).toEqual([]);
    const removed = diffObligationProgress(snapshot(tasks, { blockers: [local] }), snapshot(tasks))!;
    expect(removed.blockers.removed).toHaveLength(1);
  });
});

describe('proof-route progress', () => {
  function routeFixture() {
    const input = node('input'), closing = node('closing', 'lemma', ['input']), goal = node('goal', 'goal');
    const route: ProofRoute = { id: 'route', targetTaskId: 'goal', prerequisiteTaskIds: ['input'], closingTaskId: 'closing' };
    return { input, closing, goal, route, tasks: [input, closing, goal] };
  }

  it('tracks a conditional closing implication without closing the route or original goal', () => {
    const { input, closing, goal, route, tasks } = routeFixture();
    const before = snapshot(tasks, { proofRoutes: [route] }), proof = checked(closing, [input]);
    closing.status = 'conditional'; proof.conditions = [{ taskId: 'input', taskDigest: taskVersion(input.task) }];
    const after = snapshot(tasks, { proofRoutes: [route] }), receipt = diffObligationProgress(before, after)!;
    expect(after.routes[0]).toMatchObject({ closingStatus: 'conditional', ready: false, connection: 'awaiting-original-check',
      remainingPrerequisiteTaskIds: ['input'] });
    expect(after.goals[0].closed).toBe(false); expect(receipt.obligations.closed).toEqual([]);
    expect(receipt.goalFrontiers).toEqual([]); expect(goal.status).toBe('pending');
  });

  it('reports a completed route as awaiting the original check and then records the checked connection', () => {
    const { input, closing, goal, route, tasks } = routeFixture(), before = snapshot(tasks, { proofRoutes: [route] });
    checked(input); checked(closing, [input]);
    const ready = snapshot(tasks, { proofRoutes: [route] }), receipt = diffObligationProgress(before, ready)!;
    expect(ready.routes[0]).toMatchObject({ ready: true, connection: 'awaiting-original-check' });
    expect(receipt.obligations.closed.map(change => change.after.taskId)).toEqual(['closing', 'input']);
    expect(ready.goals[0]).toMatchObject({ closed: false, frontier: [{ taskId: 'goal', taskDigest: taskVersion(goal.task) }] });
    checked(goal, [closing]);
    const connected = snapshot(tasks, { proofRoutes: [route] }), completed = diffObligationProgress(ready, connected)!;
    expect(connected.routes[0].connection).toBe('closed-by-original-check');
    expect(completed.obligations.closed.map(change => change.after.taskId)).toEqual(['goal']);
    expect(completed.routes[0].after!.connection).toBe('closed-by-original-check');
    expect(completed.goalFrontiers[0].after!.frontier).toEqual([]);
    expect(completed.acceptance).toBe('not-assessed'); expect(finalCandidateReviewReady(tasks)).toBe(false);
  });

  it('retains alternative frontiers and does not treat all alternative branches as mandatory', () => {
    const { input, closing, goal, route, tasks } = routeFixture(), otherInput = node('other_input');
    const otherClosing = node('other_closing', 'lemma', ['other_input']);
    const alternative: ProofRoute = { id: 'alternative', targetTaskId: goal.task.id,
      prerequisiteTaskIds: [otherInput.task.id], closingTaskId: otherClosing.task.id };
    tasks.push(otherInput, otherClosing); goal.alternativeRoutes = [route, alternative];
    const before = snapshot(tasks); checked(input); checked(closing, [input]);
    const after = snapshot(tasks), receipt = diffObligationProgress(before, after)!;
    expect(after.goals[0].routeCombination).toBe('any'); expect(after.goals[0].alternatives).toHaveLength(2);
    expect(after.routes.find(item => item.routeId === 'alternative')!.ready).toBe(false);
    expect(after.routes.find(item => item.routeId === 'route')!.ready).toBe(true);
    expect(after.goals[0].frontier.map(item => item.taskId)).toEqual(['goal']);
    expect(receipt.obligations.closed.some(change => change.after.taskId === goal.task.id)).toBe(false);
  });
});
