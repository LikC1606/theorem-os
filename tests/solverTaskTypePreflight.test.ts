import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { git } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { TaskTypePreflightCache, type TaskTypePreflight } from '../src/solver/taskTypePreflight';
import { taskVersion } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('typed helper dispatch admission', () => {
  let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
  let controller: AbortController, emit: ReturnType<typeof vi.fn>, allowed: boolean;
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const result = (status: TaskTypePreflight['status'] = 'elaborated', current = () => true) => ({ current,
    result: { status, inputDigest: 'fixed-input', reason: 'exact closed query error', taskDigest: taskVersion(state.cooperation!.tasks[0].task),
      evidence: 'advisory-type-elaboration', proofAcceptance: 'not-assessed' } as TaskTypePreflight });
  const peer = (index = 1) => (cooperative as any).nextPeer(workers[index], budget, true);
  const holdPreflight = () => {
    type Finish = (status?: TaskTypePreflight['status'], current?: () => boolean) => void;
    let signal!: AbortSignal, finish!: Finish;
    vi.mocked(TaskTypePreflightCache.prototype.check).mockImplementation(input => {
      signal = input.signal!;
      return new Promise(resolve => { finish = (status, current) => resolve(result(status, current)); });
    });
    return { get signal() { return signal; }, finish: ((status, current) => finish(status, current)) as Finish };
  };
  beforeEach(() => {
    budget.maxTurns = Infinity;
    const example = localExample('solver-type-preflight-', 'lead'), { workspace, problem } = example;
    directory = example.directory;
    workers = [leadWorker(problem, workspace, 'lead'), ...['proof', 'other'].map(id => peerWorker(example, id))];
    const parsed = parseCooperationPlan(problem, { tasks: [{ id: 'helper', kind: 'lemma', objective: 'Prove helper',
      theoremName: 'Tutorial.helper', type: 'True', proofPath: 'Submission.lean', ownerId: 'proof' },
    { id: 'independent', kind: 'research', objective: 'Independent question', ownerId: 'other' },
    ...problem.targets.map((target, index) => ({ id: `original_goal_${index + 1}`, kind: 'goal', objective: 'Original',
      theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' }))] });
    state = solverState(problem, workspace, { runId: 'type-fixture', phase: 'running', cooperation: { canonicalCommit: problem.baseCommit,
      tasks: parsed.tasks.map(task => ({ task, status: 'pending', attempts: 0 })) } });
    controller = new AbortController(); emit = vi.fn(); allowed = true;
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal, emit,
      modelDispatchAllowed: () => allowed });
    vi.spyOn(TaskTypePreflightCache.prototype, 'check').mockImplementation(async () => result());
  });
  afterEach(async () => {
    controller.abort(); await cooperative.stop(); vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('preflights before assignment, preserves Infinity and grants no proof evidence', async () => {
    const check = vi.mocked(TaskTypePreflightCache.prototype.check);
    check.mockImplementation(async input => {
      expect(state.cooperation!.tasks[0].status).toBe('pending'); expect(input.timeoutMs).toBe(Infinity);
      return result();
    });
    const action = await peer();
    expect(action).toMatchObject({ kind: 'task', task: { id: 'helper' } });
    expect(state.cooperation!.tasks[0]).toMatchObject({ status: 'running', attempts: 0,
      typePreflight: { status: 'elaborated', proofAcceptance: 'not-assessed' } });
    expect(state.cooperation!.tasks[0].proof).toBeUndefined();
  });

  it('blocks an exact invalid interface without charging a model attempt and gives Lead precise feedback', async () => {
    vi.mocked(TaskTypePreflightCache.prototype.check).mockResolvedValue(result('invalid'));
    expect(typeof await peer()).toBe('symbol');
    const node = state.cooperation!.tasks[0];
    expect(node).toMatchObject({ status: 'blocked', attempts: 0, feedback: expect.stringContaining('exact closed query error') });
    expect(node.assignment).toBeUndefined(); expect(state.lastFailure).toBeUndefined();
    expect((cooperative as any).refreshInvalidTaskTypes()).toBe(false);
    expect(vi.mocked(TaskTypePreflightCache.prototype.check)).toHaveBeenCalledOnce();
  });

  it.each(['deferred', 'unavailable'] as const)('allows work to continue with %s and records no mathematical failure', async status => {
    vi.mocked(TaskTypePreflightCache.prototype.check).mockResolvedValue(result(status));
    expect(await peer()).toMatchObject({ kind: 'task' });
    expect(state.cooperation!.tasks[0].typePreflight?.status).toBe(status);
    expect(state.lastFailure).toBeUndefined();
  });

  it('records an unavailable advisory without starting Lean when the host has no bound worker environment', async () => {
    (cooperative as any).input.access.delete(workers[1].id);
    expect(await peer()).toMatchObject({ kind: 'task', task: { id: 'helper' } });
    expect(state.cooperation!.tasks[0]).toMatchObject({ status: 'running', attempts: 0,
      typePreflight: { status: 'unavailable', reason: 'worker-environment-unavailable', proofAcceptance: 'not-assessed' } });
    expect(vi.mocked(TaskTypePreflightCache.prototype.check)).not.toHaveBeenCalled();
  });

  it('keeps independent work assignable while one type query is awaiting Lean', async () => {
    const held = holdPreflight(), pending = peer();
    expect(await peer(2)).toMatchObject({ kind: 'task', task: { id: 'independent' } });
    held.finish(); expect(await pending).toMatchObject({ kind: 'task', task: { id: 'helper' } });
  });

  it.each(['contract', 'canonical', 'source', 'admission', 'turns', 'owner', 'environment-binding'] as const)
  ('discards awaited preflight after %s changes', async change => {
    let current = true;
    const held = holdPreflight(), pending = peer(), node = state.cooperation!.tasks[0];
    if (change === 'contract') node.task = { ...node.task, type: 'False', revision: 1 };
    if (change === 'canonical') state.cooperation!.canonicalCommit = 'b'.repeat(40);
    if (change === 'source') current = false;
    if (change === 'admission') allowed = false;
    if (change === 'turns') { state.turns = 1; budget.maxTurns = 1; }
    if (change === 'owner') node.task = { ...node.task, ownerId: 'other' };
    if (change === 'environment-binding') (cooperative as any).input.access.set(workers[1].id, { environment: {}, retrievalRoot: directory });
    held.finish('elaborated', () => current);
    expect(typeof await pending).toBe('symbol'); expect(node.status).toBe('pending'); expect(node.assignment).toBeUndefined();
    budget.maxTurns = Infinity;
  });

  it.each(['removed', 'revised', 'dependency-revised', 'canonical'] as const)
  ('cancels a pending preflight after its %s input changes and waits for its cleanup', async change => {
    const node = state.cooperation!.tasks[0];
    if (change === 'dependency-revised') {
      node.task = { ...node.task, dependsOn: ['independent'] };
      state.cooperation!.tasks[1].status = 'completed';
    }
    const held = holdPreflight();
    let settled = false;
    const pending = peer().then(value => { settled = true; return value; });
    expect(held.signal.aborted).toBe(false);
    if (change === 'canonical') {
      git(workers[0].worktree, ['-c', 'user.name=TheoremOS', '-c', 'user.email=theoremos@localhost',
        'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'Update canonical fixture']);
      state.cooperation!.canonicalCommit = git(workers[0].worktree, ['rev-parse', 'HEAD']);
      (cooperative as any).changed();
    } else {
      const tasks = state.cooperation!.tasks.filter(item => change !== 'removed' || item !== node).map(item => {
        if (change === 'revised' && item === node) return { ...item.task, type: 'False', revision: item.task.revision + 1 };
        if (change === 'dependency-revised' && item.task.id === 'independent')
          return { ...item.task, objective: 'Revised research input', revision: item.task.revision + 1 };
        return item.task;
      });
      await (cooperative as any).acceptPlan(parseCooperationPlan(state.problem, { tasks }));
    }
    expect(held.signal.aborted).toBe(true); expect(controller.signal.aborted).toBe(false);
    await new Promise<void>(resolve => setImmediate(resolve));
    expect(settled).toBe(false); expect((cooperative as any).preparingTaskTypes.has(node)).toBe(true);
    let woke = false;
    const waiting = (cooperative as any).waitForDispatch().then(() => { woke = true; });
    await new Promise<void>(resolve => setImmediate(resolve)); expect(woke).toBe(false);
    held.finish('invalid');
    expect(typeof await pending).toBe('symbol'); await waiting;
    expect(woke).toBe(true); expect((cooperative as any).preparingTaskTypes.size).toBe(0);
    expect(node.assignment).toBeUndefined(); expect(node.typePreflight).toBeUndefined();
    expect(node.status).toBe('pending'); expect(state.lastFailure).toBeUndefined();
    expect(emit.mock.calls.some(([event]) => ['task_type_preflight', 'task_assigned'].includes(event))).toBe(false);
  });

  it('preserves an unchanged preflight across unrelated plan, notes and activity changes', async () => {
    const held = holdPreflight(), pending = peer();
    const tasks = state.cooperation!.tasks.map(item => item.task.id === 'independent'
      ? { ...item.task, objective: 'Another independent question', revision: item.task.revision + 1 } : item.task);
    await (cooperative as any).acceptPlan(parseCooperationPlan(state.problem, { tasks }));
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'Independent notes\n');
    (cooperative as any).changed(); cooperative.modelBudgetChanged();
    expect(await peer(2)).toMatchObject({ kind: 'task', task: { id: 'independent' } });
    expect(held.signal.aborted).toBe(false);
    expect(vi.mocked(TaskTypePreflightCache.prototype.check)).toHaveBeenCalledOnce();
    held.finish(); expect(await pending).toMatchObject({ kind: 'task', task: { id: 'helper' } });
  });

  it.each(['admission', 'turns', 'environment', 'environment-binding', 'owner', 'worker-stopped'] as const)
  ('cancels obsolete host work on a %s notification without publishing an invalid type', async change => {
    const held = holdPreflight(), pending = peer(), node = state.cooperation!.tasks[0];
    if (change === 'admission') allowed = false;
    if (change === 'turns') { state.turns = 1; budget.maxTurns = 1; }
    if (change === 'environment') state.environmentDigest = 'updated-environment';
    if (change === 'environment-binding') (cooperative as any).input.access.set(workers[1].id, { environment: {}, retrievalRoot: directory });
    if (change === 'owner') node.task = { ...node.task, ownerId: 'other' };
    if (change === 'worker-stopped') cooperative.stopped(workers[1]);
    else cooperative.modelBudgetChanged();
    expect(held.signal.aborted).toBe(true); expect(controller.signal.aborted).toBe(false);
    held.finish('invalid'); expect(typeof await pending).toBe('symbol');
    expect(node).toMatchObject({ status: 'pending', attempts: 0 });
    expect(node.assignment).toBeUndefined(); expect(node.typePreflight).toBeUndefined();
    expect(state.lastFailure).toBeUndefined();
    budget.maxTurns = Infinity;
  });

  it('passes run cancellation to Lean and retains the preparation until its cleanup completes', async () => {
    const held = holdPreflight();
    let settled = false;
    const pending = peer().then(value => { settled = true; return value; });
    controller.abort();
    expect(held.signal.aborted).toBe(true);
    await new Promise<void>(resolve => setImmediate(resolve)); expect(settled).toBe(false);
    expect((cooperative as any).preparingTaskTypes.size).toBe(1);
    held.finish('invalid'); expect(typeof await pending).toBe('symbol');
    expect((cooperative as any).preparingTaskTypes.size).toBe(0);
    expect(state.cooperation!.tasks[0].assignment).toBeUndefined();
    expect(state.cooperation!.tasks[0].typePreflight).toBeUndefined();
    expect(state.lastFailure).toBeUndefined();
  });

  it('drains a cancelled preflight before stop returns', async () => {
    const held = holdPreflight(), pending = peer();
    let stopped = false;
    const stopping = cooperative.stop().then(() => { stopped = true; });
    expect(held.signal.aborted).toBe(true);
    await new Promise<void>(resolve => setImmediate(resolve)); expect(stopped).toBe(false);
    expect((cooperative as any).preparingTaskTypes.size).toBe(1);
    held.finish('invalid'); expect(typeof await pending).toBe('symbol'); await stopping;
    expect(stopped).toBe(true); expect((cooperative as any).preparingTaskTypes.size).toBe(0);
    expect(state.cooperation!.tasks[0].assignment).toBeUndefined();
    expect(state.cooperation!.tasks[0].typePreflight).toBeUndefined();
    expect(state.lastFailure).toBeUndefined();
  });

  it('does not reopen invalid A when its worker edits independent B, but does reopen on a canonical change', async () => {
    vi.mocked(TaskTypePreflightCache.prototype.check).mockResolvedValue(result('invalid'));
    await peer();
    fs.appendFileSync(path.join(workers[1].worktree, state.problem.projectRelative, 'Submission.lean'), '\n-- independent B work\n');
    expect((cooperative as any).refreshInvalidTaskTypes()).toBe(false);
    expect(state.cooperation!.tasks[0].status).toBe('blocked');
    state.cooperation!.canonicalCommit = 'b'.repeat(40);
    expect((cooperative as any).refreshInvalidTaskTypes()).toBe(true);
    expect(state.cooperation!.tasks[0].status).toBe('pending');
  });

  it('waits for host type work without reporting an idle or finished frontier', async () => {
    const held = holdPreflight();
    state.cooperation!.tasks[1].task = { ...state.cooperation!.tasks[1].task, status: 'paused' };
    const pending = peer();
    (cooperative as any).needsLead = false;
    let settled = false;
    const lead = (cooperative as any).nextLead(workers[0], budget, true).then(() => { settled = true; });
    await new Promise(resolve => setTimeout(resolve, 15));
    expect(settled).toBe(false); expect(emit.mock.calls.some(([event]) => event === 'routes_idle')).toBe(false);
    held.finish(); await pending; await lead;
  });
});
