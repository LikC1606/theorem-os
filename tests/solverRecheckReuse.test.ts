import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { taskReferenceDependencies, taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, solverState } from './helpers/solver';
import { failedBatch, receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const verified = (request: MathematicsVerifierBatchRequest) => {
  const batch = receiptBatch(request, { sessionId: 'recheck-reuse-fixture',
    receiptId: (_, name) => 'receipt-' + request.targetCommit + '-' + name });
  for (const result of batch.results) result.declarationReferences = { statement: [],
    proof: [{ file: 'Submission.lean', name: result.theoremName + '._proof_1' }] };
  return batch;
};

describe('process-local reuse of unchanged integrated projections', () => {
  let directory: string, workspace: string, file: string, problem: SolverProblem, state: SolverRunState;
  let cooperative: CooperativeResearch, controller: AbortController;
  let events: { event: string; details?: Record<string, unknown> }[];
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const source = () => committedSource(workspace, state.cooperation!.canonicalCommit!, problem.projectRelative + '/Submission.lean');
  const update = (change: (source: string) => string) => {
    fs.writeFileSync(file, change(source()));
    state.cooperation!.canonicalCommit = commitSolverSources(problem, workspace);
  };
  const synchronize = async () => {
    const selected = state.cooperation!.tasks.filter(item => item.status === 'integrated');
    (cooperative as any).markPendingValidation(selected, new Set(selected.map(item => item.task.id)));
    await (cooperative as any).schedulePlanSynchronization();
  };
  const recheck = () => (cooperative as any).recheckIntegrated(state.cooperation!.canonicalCommit!, true) as Promise<boolean>;
  const checkedNames = () => host.verify.mock.calls.flatMap(([request]: [MathematicsVerifierBatchRequest]) =>
    request.items.map(item => item.theoremName));
  const reusedIds = () => events.filter(item => item.event === 'task_check_reused').map(item => item.details?.taskId);
  const finishLastGoal = () => update(text => text.replace('by sorry', 'by exact Nat.zero_add n'));

  beforeEach(async () => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-recheck-reuse-');
    ({ directory, workspace, problem } = example);
    file = path.join(workspace, problem.projectRelative, 'Submission.lean');
    const initial = fs.readFileSync(file, 'utf8').replace('theorem add_zero', 'lemma helper : True := by trivial\n\ntheorem add_zero')
      .replace('by sorry', 'by rfl');
    fs.writeFileSync(file, initial);
    const canonical = commitSolverSources(problem, workspace), lead = leadWorker(problem, workspace);
    const helper: CooperativeTask = { id: 'helper', kind: 'lemma', objective: 'Prove the helper.', type: 'True',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.helper', dependsOn: [], revision: 0 };
    const goals: CooperativeTask[] = problem.targets.map((target, index) => ({ id: 'goal_' + index, kind: 'goal',
      objective: 'Prove ' + target.theoremName + '.', proofPath: target.proofPath, theoremName: target.theoremName,
      dependsOn: index === 0 ? ['helper'] : [], revision: 0 }));
    state = solverState(problem, workspace, { runId: 'recheck-reuse-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: canonical,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [helper, ...goals].map(task => ({ task, status: task.id === 'goal_1' ? 'pending' : 'integrated', attempts: 0 })) } });
    events = []; controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers: [lead], retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }) });
    for (const current of [node('helper'), node('goal_0')]) {
      current.integratedCheck = await (cooperative as any).check(current.task,
        { taskId: current.task.id, taskDigest: taskVersion(current.task), workerId: lead.id, seedCommit: canonical }, workspace, canonical);
      expect(current.integratedCheck!.references!.inputs.some(input => !input.name)).toBe(true);
      expect(taskReferenceDependencies(current)).toBeUndefined();
    }
    host.verify.mockClear(); events = [];
  });
  afterEach(async () => {
    controller.abort(); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('keeps receipts for unchanged helpers and goals when Lead completes only the last goal', async () => {
    const helper = node('helper').integratedCheck, goal = node('goal_0').integratedCheck;
    finishLastGoal();

    await synchronize();

    expect(host.verify).not.toHaveBeenCalled();
    expect(reusedIds()).toEqual(['helper', 'goal_0']);
    expect(node('helper').integratedCheck).toBe(helper);
    expect(node('goal_0').integratedCheck).toBe(goal);
    expect(node('helper').pendingValidation).toBeUndefined();
    expect(node('goal_0').pendingValidation).toBeUndefined();
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
    expect(source()).toContain('by exact Nat.zero_add n');
  });

  it('checks changed-only targets with the same full projection in one independent verifier batch', async () => {
    const extra: CooperativeTask = { id: 'extra', kind: 'lemma', objective: 'Prove another helper.', type: 'True',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.extra', dependsOn: [], revision: 0 };
    update(text => text.replace('theorem add_zero', 'lemma extra : True := by trivial\n\ntheorem add_zero'));
    state.cooperation!.tasks.splice(1, 0, { task: extra, status: 'integrated', attempts: 0 });
    finishLastGoal();
    const check = vi.spyOn(cooperative as any, 'check');

    await recheck();

    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName)))
      .toEqual([['Tutorial.helper', 'Tutorial.extra'], ['Tutorial.add_zero']]);
    expect(events.filter(item => item.event === 'task_recheck_batch_started')).toMatchObject([
      { details: { taskIds: ['helper', 'extra'] } },
    ]);
    expect(check).toHaveBeenCalledTimes(3);
    for (const current of [node('helper'), node('extra'), node('goal_0')]) {
      expect(current.integratedCheck).toMatchObject({ passed: true, commit: state.cooperation!.canonicalCommit,
        verification: { results: [{ theoremName: current.task.theoremName }] } });
      expect(current.integratedCheck!.verification.results).toHaveLength(1);
    }
  });

  it('rechecks a batched consumer after a retained goal dependency becomes invalid', async () => {
    const consumer: CooperativeTask = { id: 'consumer', kind: 'lemma', objective: 'Consume the checked goal.', type: 'True',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.consumer', dependsOn: ['goal_0'], revision: 0 };
    update(text => text.replace('theorem add_zero', 'lemma consumer : True := by trivial\n\ntheorem add_zero'));
    state.cooperation!.tasks.push({ task: consumer, status: 'integrated', attempts: 0 });
    node('helper').status = 'blocked';

    await expect(recheck()).resolves.toBe(true);

    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName)))
      .toEqual([['Tutorial.add_zero', 'Tutorial.consumer'], ['Tutorial.consumer']]);
    for (const id of ['goal_0', 'consumer']) expect(node(id)).toMatchObject({
      status: 'blocked', feedback: 'math_task_dependency_invalidated',
      integratedCheck: { passed: true, commit: state.cooperation!.canonicalCommit },
    });
    const requests = host.verify.mock.calls.map(([request]: [MathematicsVerifierBatchRequest]) => request);
    expect(committedSource(workspace, requests[0].targetCommit!, problem.projectRelative + '/Submission.lean'))
      .toContain('theorem add_zero');
    expect(committedSource(workspace, requests[1].targetCommit!, problem.projectRelative + '/Submission.lean'))
      .not.toContain('theorem add_zero');
  });

  it('rechecks a restored receipt without forcing an unchanged live receipt through the verifier', async () => {
    node('helper').integratedCheck = structuredClone(node('helper').integratedCheck);
    const goal = node('goal_0').integratedCheck;
    finishLastGoal();

    await synchronize();

    expect(checkedNames()).toEqual(['Tutorial.helper']);
    expect(reusedIds()).toEqual(['goal_0']);
    expect(node('goal_0').integratedCheck).toBe(goal);
    expect(node('helper').integratedCheck!.commit).toBe(state.cooperation!.canonicalCommit);
  });

  it('never reuses receipts restored from JSON even when every projection is unchanged', async () => {
    for (const current of [node('helper'), node('goal_0')]) current.integratedCheck = structuredClone(current.integratedCheck);
    finishLastGoal();

    await synchronize();

    expect(checkedNames()).toEqual(['Tutorial.helper', 'Tutorial.add_zero']);
    expect(reusedIds()).toEqual([]);
  });

  it('keeps an unchanged goal blocked when its required dependency is invalidated', async () => {
    node('helper').status = 'blocked';
    finishLastGoal();

    await recheck();

    expect(checkedNames()).toEqual(['Tutorial.add_zero']);
    expect(reusedIds()).toEqual([]);
    expect(node('goal_0')).toMatchObject({ status: 'blocked', feedback: 'math_task_dependency_invalidated' });
  });

  it.each(['source', 'environment', 'task', 'receipt'] as const)
  ('rechecks integrated proofs after their %s changes', async change => {
    finishLastGoal();
    if (change === 'source') update(text => text.replace('helper : True := by trivial', 'helper : True := by exact True.intro'));
    if (change === 'environment') state.environmentDigest = 'changed-environment';
    if (change === 'task') node('helper').task = { ...node('helper').task, revision: 1, objective: 'Clarify the helper.' };
    if (change === 'receipt') node('helper').integratedCheck!.verification.results[0]!.receiptId = 'changed-receipt';

    await synchronize();

    expect(checkedNames()).toContain('Tutorial.helper');
    expect(reusedIds()).not.toContain('helper');
    if (['source', 'environment'].includes(change)) {
      expect(checkedNames()).toContain('Tutorial.add_zero');
      expect(reusedIds()).toEqual([]);
    }
    for (const current of [node('helper'), node('goal_0')]) expect(current).toMatchObject({
      status: 'integrated', integratedCheck: { passed: true, taskDigest: taskVersion(current.task) },
    });
  });
  it.each(['live', 'restored', 'new-reference'] as const)
  ('blocks an actual-reference consumer when its later producer fails recheck (%s)', async mode => {
    const peer: CooperativeTask = { id: 'peer', kind: 'lemma', objective: 'Prove peer.', type: 'True',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.peer', dependsOn: [], revision: 0 };
    update(text => text.replace('theorem add_zero', 'lemma peer : True := by trivial\n\ntheorem add_zero'));
    state.cooperation!.tasks.push({ task: peer, status: 'integrated', attempts: 0 });
    if (mode !== 'new-reference') update(text => text.replace('by rfl', 'by have := peer; rfl'));
    let rechecking = false;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = receiptBatch(request, { sessionId: 'actual-order-fixture', receiptId: (_, name) => 'receipt-' + name });
      for (const result of batch.results) result.declarationReferences = { statement: [], proof: result.theoremName === 'Tutorial.add_zero' &&
        (mode !== 'new-reference' || rechecking)
        ? [{ file: 'Submission.lean', name: 'Tutorial.peer' }] : [] };
      return batch;
    });
    for (const current of [node('peer'), node('goal_0')]) current.integratedCheck = await (cooperative as any).check(current.task,
      { taskId: current.task.id, taskDigest: taskVersion(current.task), workerId: 'lead', seedCommit: state.cooperation!.canonicalCommit! },
      workspace, state.cooperation!.canonicalCommit!);
    expect(taskReferenceDependencies(node('goal_0'))).toEqual(mode === 'new-reference' ? [] :
      [{ taskId: 'peer', taskDigest: taskVersion(peer) }]);
    if (mode === 'restored') for (const current of [node('peer'), node('goal_0')]) current.integratedCheck = structuredClone(current.integratedCheck);
    update(text => text.replace('peer : True := by trivial', 'peer : True := by exact True.intro'));
    if (mode === 'new-reference') update(text => text.replace('by rfl', 'by have := peer; rfl'));
    rechecking = true;
    const previous = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = await previous(request);
      return request.items.some(item => item.theoremName === 'Tutorial.peer') ? failedBatch(batch, {
        selected: result => result.theoremName === 'Tutorial.peer', stdoutPreview: () => 'Submission.lean:5:0: error: unsolved goals' }) : batch;
    });
    await synchronize();
    expect(node('peer').status).toBe('blocked');
    expect(node('peer').pendingValidation).toBeUndefined();
    expect(node('goal_0').pendingValidation).toBeUndefined();
    expect(node('goal_0')).toMatchObject({ status: 'blocked', feedback: 'math_task_dependency_invalidated' });
    expect(node('goal_0').integratedCheck!.references!.tasks).toEqual([{ taskId: 'peer', taskDigest: taskVersion(peer) }]);
    expect(node('helper').status).toBe('integrated');
    expect(node('goal_1').status).toBe('pending');
    expect(state.cooperation!.recheck).toMatchObject({ total: 3, completed: 3 });
  });
});
