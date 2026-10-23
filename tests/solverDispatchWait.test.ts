import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { TaskTypePreflightCache } from '../src/solver/taskTypePreflight';
import { taskVersion } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('recorded dispatch waits', () => {
  const budget = { maxTurns: 10, remainingMs: 60_000 };
  let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
  let controller: AbortController, modules: SolverModules, emit: ReturnType<typeof vi.fn>, pending: Promise<unknown>[];
  const node = (id = 'helper') => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const wait = (worker = workers[2]) => state.workers!.find(item => item.id === worker.id)!.scheduling?.wait;
  const track = <T,>(promise: Promise<T>) => { pending.push(promise); void promise.catch(() => {}); return promise; };
  const tick = () => new Promise<void>(resolve => setImmediate(resolve));
  const events = (name: string) => emit.mock.calls.filter(([event]) => event === name).map(([, details]) => details);
  const refresh = () => (cooperative as any).changed();

  beforeEach(() => {
    const example = localExample('solver-dispatch-wait-', 'lead');
    directory = example.directory;
    workers = [leadWorker(example.problem, example.workspace, 'lead'),
      ...['busy', 'idle', 'observer'].map(id => peerWorker(example, id))];
    const plan = parseCooperationPlan(example.problem, { tasks: [
      { id: 'helper', kind: 'lemma', ownerId: 'busy', objective: 'Prove an independently useful helper.',
        theoremName: 'Tutorial.helper', type: 'True', proofPath: 'Submission.lean' },
      { id: 'ongoing', kind: 'research', ownerId: 'busy', objective: 'Investigate a separate construction.' },
      ...example.problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: 'Original target', theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' })),
    ] });
    state = solverState(example.problem, example.workspace, { runId: 'dispatch-wait-fixture', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'running', turns: 0 })),
      cooperation: { canonicalCommit: example.problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    node('ongoing').status = 'running';
    node('ongoing').assignment = { taskId: 'ongoing', taskDigest: taskVersion(node('ongoing').task), workerId: 'busy',
      seedCommit: example.problem.baseCommit, assignmentId: 'ongoing-assignment' };
    pending = []; controller = new AbortController(); emit = vi.fn();
    modules = { ...directSolverModules, M1: { ...directSolverModules.M1,
      open: vi.fn(() => { throw new Error('fixture_real_models_forbidden'); }) }, M5: { ...directSolverModules.M5 } };
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal, emit, modules });
    vi.spyOn(TaskTypePreflightCache.prototype, 'check').mockImplementation(async input => ({ current: () => true,
      result: { status: 'elaborated', inputDigest: 'fixture-input', taskDigest: taskVersion(input.task),
        reason: 'fixture type elaboration', evidence: 'advisory-type-elaboration', proofAcceptance: 'not-assessed' } }));
  });
  afterEach(async () => {
    controller.abort();
    await Promise.allSettled(pending);
    await cooperative.stop();
    expect(modules.M1.open).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('records owner congestion once, then dispatches after an explicit complete plan makes the helper shared', async () => {
    const busyAssignment = node('ongoing').assignment, version = taskVersion(node().task);
    const next = track(cooperative.next(workers[2], budget));
    await tick();
    const observed = wait();
    expect(observed).toMatchObject({ stage: 'm5-no-selection', candidateCount: 1, omittedCandidates: 0,
      candidates: [{ taskId: 'helper', taskDigest: version, reason: 'owner' }] });
    for (let index = 0; index < 3; index++) { refresh(); await tick(); }
    expect(wait()).toBe(observed); expect(events('dispatch_wait')).toHaveLength(1);

    const archive = state.cooperation!;
    await (cooperative as any).acceptPlan(parseCooperationPlan(state.problem, {
      tasks: archive.tasks.map(item => item.task.id === 'helper' ? { ...item.task, ownerId: undefined } : item.task),
      groups: archive.groups!.map(item => item.group),
    }));
    expect(await next).toMatchObject({ kind: 'task', task: { id: 'helper' }, assignment: { workerId: 'idle' } });
    expect(taskVersion(node().task)).toBe(version);
    expect(node('ongoing').assignment).toBe(busyAssignment);
    expect(wait()).toBeUndefined();
    expect(events('dispatch_wait_ended')).toContainEqual(expect.objectContaining({ workerId: 'idle',
      observedAt: observed!.observedAt, reason: 'selected' }));
    expect(node().proof).toBeUndefined(); expect(node().attempts).toBe(0);
  });

  it('retains a saved assignment when ownerId is removed and records its actual reservation', async () => {
    const helper = node(); helper.task = { ...helper.task, ownerId: undefined };
    helper.assignment = { taskId: helper.task.id, taskDigest: taskVersion(helper.task), workerId: 'busy',
      seedCommit: state.problem.baseCommit, assignmentId: 'saved-draft' };
    const assignment = helper.assignment;
    track(cooperative.next(workers[2], budget)); await tick();
    expect(wait()?.candidates).toEqual([{ taskId: helper.task.id, taskDigest: taskVersion(helper.task), reason: 'saved-assignment' }]);
    expect(helper.assignment).toBe(assignment); expect(helper.status).toBe('pending');
  });

  it('reports no M3 candidates without inventing a dependency or Lead cause', async () => {
    node().task = { ...node().task, status: 'paused' };
    track(cooperative.next(workers[2], budget)); await tick();
    expect(wait()).toMatchObject({ stage: 'm3-no-ready', candidateCount: 0, candidates: [], omittedCandidates: 0 });
    expect(node().assignment).toBeUndefined();
  });

  it('records an unknown policy exclusion when a custom M5 declines otherwise eligible work', async () => {
    node().task = { ...node().task, ownerId: undefined };
    modules.M5.assign = vi.fn(() => undefined);
    track(cooperative.next(workers[2], budget)); await tick();
    expect(wait()).toMatchObject({ stage: 'm5-no-selection', candidates: [{ taskId: 'helper', reason: 'policy-no-selection' }] });
    expect(modules.M5.assign).toHaveBeenCalledOnce();
    expect(node().assignment).toBeUndefined();
  });

  it('rejects a custom M5 that ignores ownership instead of treating its suggestion as dispatch authority', async () => {
    modules.M5.assign = vi.fn(() => node());
    await expect(cooperative.next(workers[2], budget)).rejects.toThrow('math_task_assignment_invalid');
    expect(node().assignment).toBeUndefined(); expect(events('task_assigned')).toHaveLength(0);
  });

  it('rechecks ownership before opening a task turn even when its mathematical digest is unchanged', async () => {
    const helper = node(); helper.task = { ...helper.task, ownerId: undefined };
    const action = await cooperative.next(workers[2], budget);
    expect(action?.kind).toBe('task');
    const version = taskVersion(helper.task);
    helper.task = { ...helper.task, ownerId: 'busy' };
    expect(taskVersion(helper.task)).toBe(version);
    expect(cooperative.started(workers[2], action!)).toBe(false);
    expect(helper.attempts).toBe(0); expect(state.cooperation!.groups![0].turns).toBe(0);
    helper.task = { ...helper.task, ownerId: undefined };
    expect(cooperative.started(workers[2], action!)).toBe(true);
    expect(helper.attempts).toBe(1);
  });

  it('explains host preparation while another eligible worker waits and prevents a duplicate claim', async () => {
    node().task = { ...node().task, ownerId: undefined };
    let finish!: () => void;
    vi.mocked(TaskTypePreflightCache.prototype.check).mockImplementation(input => new Promise(resolve => {
      finish = () => resolve({ current: () => true, result: { status: 'elaborated', inputDigest: 'held-input',
        taskDigest: taskVersion(input.task), reason: 'fixture type elaboration',
        evidence: 'advisory-type-elaboration', proofAcceptance: 'not-assessed' } });
    }));
    const preparing = track(cooperative.next(workers[2], budget));
    track(cooperative.next(workers[3], budget)); await tick();
    expect(wait(workers[3])).toMatchObject({ stage: 'host-filtered', candidates: [{ taskId: 'helper', reason: 'preparing-type' }] });
    expect(node().assignment).toBeUndefined();
    finish(); expect(await preparing).toMatchObject({ kind: 'task', assignment: { workerId: 'idle' } });
    await tick();
    expect(wait(workers[3])?.stage).toBe('m3-no-ready');
    expect(events('task_assigned').filter(event => event.taskId === 'helper')).toHaveLength(1);
  });

  it.each(['time-limit', 'model-disabled', 'turn-limit'] as const)('records %s without changing terminal budget behavior', async gate => {
    const dispatchBudget = { ...budget, ...(gate === 'time-limit' ? { remainingMs: 0 } : {}),
      ...(gate === 'turn-limit' ? { maxTurns: 0 } : {}) };
    (cooperative as any).input.modelDispatchAllowed = () => gate !== 'model-disabled';
    expect(await cooperative.next(workers[2], dispatchBudget)).toBeUndefined();
    expect(wait()).toMatchObject({ stage: 'budget-gated', gate, candidateCount: 0 });
    cooperative.stopped(workers[2]);
    expect(wait()).toMatchObject({ stage: 'budget-gated', gate, endedAt: expect.any(Number) });
    cooperative.stopped(workers[2]); await cooperative.stop();
    expect(events('dispatch_wait_ended')).toEqual([expect.objectContaining({ workerId: 'idle', reason: 'stopped' })]);
  });

  it('records Lead unavailability without dispatching a peer turn', async () => {
    cooperative.stopped(workers[0], 'fixture Lead unavailable');
    expect(await cooperative.next(workers[2], budget)).toBeUndefined();
    expect(wait()).toMatchObject({ stage: 'lead-unavailable', candidateCount: 0 });
    expect(events('task_assigned')).toHaveLength(0);
  });

  it('bounds observations and preserves omitted counts in archives and scoped worker views', async () => {
    const helper = node();
    state.cooperation!.tasks.push(...Array.from({ length: 18 }, (_, index) => ({
      task: { ...helper.task, id: `hidden_${index}`, theoremName: `Tutorial.hidden_${index}`,
        objective: `Private helper ${index}`, groupId: 'private', sharing: 'group' as const },
      status: 'pending' as const, attempts: 0,
    })));
    state.cooperation!.groups!.push({ group: { id: 'private', objective: 'Private route', status: 'active', revision: 0 }, turns: 0 });
    state.workers!.find(worker => worker.id === 'observer')!.sessionTaskId = helper.task.id;
    track(cooperative.next(workers[2], budget)); await tick();
    expect(wait()).toMatchObject({ candidateCount: 19, omittedCandidates: 3 });
    expect(wait()!.candidates).toHaveLength(16);
    const view = JSON.parse(fs.readFileSync(path.join(workers[3].worktree, 'COOPERATION.json'), 'utf8'));
    const scoped = view.dispatchWaits.find((record: { workerId: string }) => record.workerId === 'idle');
    expect(scoped.candidates.map((candidate: { taskId: string }) => candidate.taskId)).toEqual(['helper']);
    expect(scoped).toMatchObject({ candidateCount: 19, omittedCandidates: 18 });
    expect(JSON.stringify(scoped)).not.toContain('hidden_');
    const leadView = JSON.parse(fs.readFileSync(path.join(workers[0].worktree, 'COOPERATION.json'), 'utf8'));
    expect(leadView.dispatchWaits[0].candidates).toHaveLength(16);
  });
});
