import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { readSolverRunState, writeSolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { committedSource, commitSolverSources, git } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { assignmentDeliveryFile, parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch, workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { receiptBatch } from './helpers/verifier';
import { buildRunInspection } from '../src/solver/inspection';

const host = vi.hoisted(() => ({ verify: vi.fn() }));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));

type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type StopReceipt = Awaited<ReturnType<NonNullable<MathAgentSession['stopForFreeze']>>>;

describe('runner proof readiness freeze barrier', () => {
  const fixtures: ReturnType<typeof fixture>[] = [];

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => receiptBatch(request, {
      sessionId: 'proof-ready-runner-fixture', receiptId: (_, name) => 'ready-receipt-' + request.targetCommit + '-' + name,
    }));
  });
  afterEach(async () => {
    for (const current of fixtures.splice(0)) {
      current.controller.abort(); current.stopResult.resolve({ status: 'stopped' });
      current.turns.forEach(turn => turn.done.resolve('interrupted'));
      await Promise.allSettled([current.completion]);
      fs.rmSync(current.directory, { recursive: true, force: true });
    }
    vi.useRealTimers(); vi.restoreAllMocks();
  });

  function fixture(options: { stop?: 'missing' | 'unconfirmed' | 'throw'; closeRejects?: boolean; attempts?: number } = {}) {
    const example = localExample('solver-proof-ready-runner-', 'lead');
    const { directory, workspace, problem } = example;
    const writer = peerWorker(example, 'writer', { role: 'engineer' });
    const workers = [leadWorker(problem, workspace, 'lead'), writer];
    const plan = parseCooperationPlan(problem, { tasks: problem.targets.map((target, index) => ({
      id: 'goal_' + index, kind: 'goal', ...target, objective: 'Prove ' + target.theoremName,
      status: index === 0 ? 'active' : 'paused', ownerId: 'writer',
    })) });
    const state = solverState(problem, workspace, { runId: 'proof-ready-runner', phase: 'prepared', failures: [],
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit, tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: options.attempts ?? 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) },
    });
    let cooperation!: CooperativeResearch;
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(function (this: CooperativeResearch) { cooperation = this; });
    const controller = new AbortController(), started = deferred(), stopping = deferred();
    const stopResult = deferred<StopReceipt>();
    const turns: { action: CooperativeAction; done: ReturnType<typeof deferred<string>> }[] = [];
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const eventWaiters = new Map<string, ReturnType<typeof deferred>>();
    const interrupt = vi.fn(async () => {});
    const closed = vi.fn();
    const stopForFreeze = vi.fn(async () => {
      stopping.resolve();
      if (options.stop === 'throw') throw new Error('fixture_shutdown_failed');
      return options.stop === 'unconfirmed' ? { status: 'unconfirmed' as const, reason: 'process-group-active' as const } : stopResult.promise;
    });
    const open = vi.fn(async (access: MathAgentOptions): Promise<MathAgentSession> => {
      if (access.environment.DEEPSCIENTIST_MATH_WORKER_ID !== writer.id) throw new Error('fixture_unexpected_lead_dispatch');
      let active: ReturnType<typeof deferred<string>> | undefined;
      return { threadId: access.threadId ?? 'proof-ready-thread', interrupt, notify: async () => {},
        close: async () => { closed(); active?.resolve('interrupted'); if (options.closeRejects) throw new Error('fixture_close_failed'); },
        ...(options.stop === 'missing' ? {} : { stopForFreeze }),
        run: async (message, _id, _workspace, onStarted) => {
          const action = JSON.parse(message) as CooperativeAction;
          active = deferred<string>(); turns.push({ action, done: active });
          onStarted('ready-turn-' + turns.length); started.resolve(); return active.promise;
        },
      };
    });
    const modules: SolverModules = { ...directSolverModules, M1: { ...directSolverModules.M1, open },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => ({
        instructions: 'Offline proof readiness runner fixture.', message: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
      }) },
    };
    const completion = runResearchWorkers({ state, workers, access: workerAccess(workers, directory), modules, root: directory,
      buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original goals.', executable: 'offline-fixture',
      profile: 'offline-fixture', signal: controller.signal, deadline: Infinity, maxTurns: Infinity, maxTurnMs: Infinity,
      maxTotalTokens: 0, save: () => {}, emit: (event, details) => {
        events.push({ event, details }); eventWaiters.get(event)?.resolve();
      },
    });
    void completion.catch(() => {});
    const wait = async (promise: Promise<unknown>) => Promise.race([promise, completion.then(() => {
      throw new Error('fixture_runner_finished_before_expected_checkpoint');
    })]);
    const waitEvent = (event: string) => {
      if (events.some(item => item.event === event)) return Promise.resolve();
      const pending = eventWaiters.get(event) ?? deferred(); eventWaiters.set(event, pending); return wait(pending.promise);
    };
    const action = () => {
      const value = turns[0]?.action; if (value?.kind !== 'task') throw new Error('fixture_missing_proof_task'); return value;
    };
    const sourceFile = path.join(writer.worktree, problem.projectRelative, 'Submission.lean');
    const writeProof = () => fs.writeFileSync(sourceFile, fs.readFileSync(sourceFile, 'utf8').replace('by sorry', 'by rfl'));
    const appendReady = (id = 'ready-runner-submission') => fs.appendFileSync(path.join(writer.worktree, assignmentDeliveryFile(action().assignment)),
      JSON.stringify({ kind: 'ready', id }) + '\n');
    const current = { directory, problem, state, workers, modules, writer, controller, stopResult, turns, events, interrupt, stopForFreeze,
      open, closed, completion, action, writeProof, appendReady, waitEvent, wait, started, stopping,
      pulse: () => cooperation.pulse(writer.id), head: () => git(writer.worktree, ['rev-parse', 'HEAD']),
      hostCheck: async <T>(check: () => Promise<T>) => {
        const stopChecking = cooperation.beginChecking(writer, action());
        try { return await check(); }
        finally { stopChecking(); }
      },
    };
    fixtures.push(current); return current;
  }

  it('keeps a frozen proof in checking status until the host verifier settles', async () => {
    const entered = deferred(), resume = deferred();
    host.verify.mockImplementation(async request => {
      entered.resolve(); await resume.promise;
      return receiptBatch(request, { sessionId: 'proof-ready-status', receiptId: () => 'ready-status-receipt' });
    });
    const current = fixture();
    try {
      await current.wait(current.started.promise);
      current.writeProof(); current.appendReady(); await current.pulse();
      current.turns[0].done.resolve('interrupted');
      current.stopResult.resolve({ status: 'stopped' }); await current.wait(entered.promise);
      const writer = current.state.workers!.find(worker => worker.id === current.writer.id)!;
      expect(writer.scheduling).toMatchObject({ status: 'checking', action: 'task', taskId: current.action().task.id });
      expect(buildRunInspection(current.state).workers.find(worker => worker.id === writer.id)?.currentStatus).toBe('checking');
      const saved = path.join(current.directory, 'checking-state.json');
      writeSolverRunState(saved, current.state);
      expect(readSolverRunState(saved).workers!.find(worker => worker.id === writer.id)?.scheduling?.status).toBe('checking');
      resume.resolve(); await current.waitEvent('proof_ready_checked');
      await vi.waitFor(() => expect(writer.scheduling?.status).not.toBe('checking'));
    } finally { resume.resolve(); }
  });

  it('keeps overlapping host checks busy until both settle and clears a rejected check', async () => {
    const current = fixture(); await current.wait(current.started.promise);
    const first = deferred(), second = deferred();
    const firstCheck = current.hostCheck(() => first.promise);
    const secondCheck = current.hostCheck(() => second.promise);
    const writer = current.state.workers!.find(worker => worker.id === current.writer.id)!;
    try {
      expect(writer.scheduling?.status).toBe('checking');
      const since = writer.scheduling!.since;
      first.resolve(); await firstCheck;
      expect(writer.scheduling).toMatchObject({ status: 'checking', since });
      second.reject(new Error('fixture_host_check_failed'));
      await expect(secondCheck).rejects.toThrow('fixture_host_check_failed');
      expect(writer.scheduling?.status).toBe('working');
    } finally { first.resolve(); second.resolve(); await Promise.allSettled([firstCheck, secondCheck]); }
  });

  it('shows host verification of a live fixed proof delivery while its model turn is still open', async () => {
    const entered = deferred(), resume = deferred();
    host.verify.mockImplementation(async request => {
      entered.resolve(); await resume.promise;
      return receiptBatch(request, { sessionId: 'live-proof-status', receiptId: () => 'live-status-receipt' });
    });
    const current = fixture(); await current.wait(current.started.promise);
    current.writeProof();
    const commit = commitSolverSources(current.problem, current.writer.worktree);
    fs.appendFileSync(path.join(current.writer.worktree, assignmentDeliveryFile(current.action().assignment)),
      JSON.stringify({ kind: 'proof', commit, summary: 'Fixed source proof' }) + '\n');
    const pulse = current.pulse();
    try {
      await current.wait(entered.promise);
      const writer = current.state.workers!.find(worker => worker.id === current.writer.id)!;
      expect(writer.phase).toBe('running');
      expect(writer.scheduling).toMatchObject({ status: 'checking', action: 'task', taskId: current.action().task.id });
      resume.resolve(); await pulse;
      expect(writer.scheduling?.status).not.toBe('checking');
    } finally { resume.resolve(); await pulse; }
  });

  it('waits for settled turn and confirmed process stop before freezing one checked snapshot', async () => {
    const current = fixture(); await current.wait(current.started.promise);
    const before = current.head(); current.writeProof(); current.appendReady(); await current.pulse();
    expect(current.interrupt).toHaveBeenCalledOnce();
    expect(current.stopForFreeze).not.toHaveBeenCalled();
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'awaiting-freeze' }]);

    current.turns[0].done.resolve('interrupted'); await current.wait(current.stopping.promise);
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    expect(current.state.cooperation!.proofReadyRecords![0].snapshotCommit).toBeUndefined();
    current.stopResult.resolve({ status: 'stopped' }); await current.waitEvent('proof_ready_checked');

    const ready = current.state.cooperation!.proofReadyRecords![0];
    expect(ready).toMatchObject({ status: 'checked', evidence: 'unconditional', conditions: [], receiptIds: [expect.any(String)] });
    expect(ready.snapshotCommit).not.toBe(before); expect(ready.snapshotCommit).toBe(current.head());
    expect(host.verify).toHaveBeenCalled();
    const request = host.verify.mock.calls[0][0];
    // M2 verifies an isolated declaration projection while retaining its frozen source commit.
    expect(current.state.cooperation!.tasks[0].proof?.commit).toBe(ready.snapshotCommit);
    expect(committedSource(current.writer.worktree, request.targetCommit, current.problem.projectRelative + '/Submission.lean'))
      .toContain('by rfl');
    expect(current.state.cooperation!.tasks[0].proof?.passed).toBe(true);
    expect(current.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(current.open.mock.calls.every(([access]) => access.turnTimeoutMs === undefined)).toBe(true);
  });

  it.each(['missing', 'unconfirmed', 'throw'] as const)('quarantines the writer without freezing, checking or reopening when process stop is %s', async stop => {
    const current = fixture({ stop }); await current.wait(current.started.promise);
    const before = current.head(); current.writeProof(); current.appendReady(); await current.pulse();
    current.turns[0].done.resolve('interrupted'); await current.waitEvent('proof_ready_freeze_deferred');
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'failed',
      reason: expect.stringContaining(stop === 'missing' ? 'writer-stop-confirmation-unavailable' :
        stop === 'unconfirmed' ? 'process-group-active' : 'shutdown-failed') }]);
    expect(current.state.cooperation!.proofReadyRecords![0].snapshotCommit).toBeUndefined();
    await expect(current.completion).rejects.toThrow('math_writer_stop_unconfirmed');
    expect(current.open).toHaveBeenCalledOnce(); expect(current.turns).toHaveLength(1);
    expect(current.state.workers!.find(worker => worker.id === current.writer.id)?.writerStopUnconfirmed)
      .toMatchObject({ reason: expect.any(String) });
    const archive = path.join(current.directory, 'quarantined-state.json');
    writeSolverRunState(archive, current.state);
    const restored = readSolverRunState(archive);
    const reopened = vi.fn(async () => { throw new Error('fixture_must_not_reopen_quarantined_writer'); });
    await expect(runResearchWorkers({ state: restored, workers: current.workers,
      access: workerAccess(current.workers, current.directory),
      modules: { ...current.modules, M1: { ...current.modules.M1, open: reopened } }, root: current.directory,
      buildFile: path.join(current.directory, 'build.json'), taskText: 'Prove the original goals.', executable: 'offline-fixture',
      profile: 'offline-fixture', signal: new AbortController().signal, deadline: Infinity, maxTurns: Infinity, maxTurnMs: Infinity,
      maxTotalTokens: 0, save: () => {}, emit: () => {},
    })).rejects.toThrow('math_writer_stop_unconfirmed');
    expect(reopened).not.toHaveBeenCalled();
  });

  it('quarantines before a failing close when writer stop is unconfirmed', async () => {
    const current = fixture({ stop: 'unconfirmed', closeRejects: true }); await current.wait(current.started.promise);
    const before = current.head(); current.writeProof(); current.appendReady(); await current.pulse();
    current.turns[0].done.resolve('interrupted'); await current.waitEvent('proof_ready_freeze_deferred');
    expect(current.head()).toBe(before);
    expect(current.state.workers!.find(worker => worker.id === current.writer.id)?.writerStopUnconfirmed)
      .toMatchObject({ reason: 'process-group-active' });
    await expect(current.completion).rejects.toThrow('math_writer_stop_unconfirmed');
    expect(host.verify).not.toHaveBeenCalled();
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'failed' }]);
    const archive = path.join(current.directory, 'failed-close-state.json');
    writeSolverRunState(archive, current.state);
    const reopened = vi.fn(async () => { throw new Error('fixture_must_not_reopen_quarantined_writer'); });
    await expect(runResearchWorkers({ state: readSolverRunState(archive), workers: current.workers,
      access: workerAccess(current.workers, current.directory),
      modules: { ...current.modules, M1: { ...current.modules.M1, open: reopened } }, root: current.directory,
      buildFile: path.join(current.directory, 'build.json'), taskText: 'Prove the original goals.', executable: 'offline-fixture',
      profile: 'offline-fixture', signal: new AbortController().signal, deadline: Infinity, maxTurns: Infinity, maxTurnMs: Infinity,
      maxTotalTokens: 0, save: () => {}, emit: () => {},
    })).rejects.toThrow('math_writer_stop_unconfirmed');
    expect(reopened).not.toHaveBeenCalled();
  });

  it('closes an acknowledged ready turn that never settles and still waits for a confirmed process stop', async () => {
    vi.useFakeTimers();
    const current = fixture(); await current.wait(current.started.promise);
    const before = current.head(); current.writeProof(); current.appendReady(); await current.pulse();
    expect(current.interrupt).toHaveBeenCalledOnce();
    await vi.advanceTimersByTimeAsync(9_999);
    expect(current.closed).not.toHaveBeenCalled(); expect(current.stopForFreeze).not.toHaveBeenCalled();
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    await vi.advanceTimersByTimeAsync(1); await current.wait(current.stopping.promise);
    expect(current.closed).toHaveBeenCalledOnce();
    expect(current.events).toContainEqual({ event: 'proof_ready_session_closed',
      details: expect.objectContaining({ workerId: 'writer', reason: 'interrupt-not-settled' }) });
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    current.stopResult.resolve({ status: 'stopped' }); await current.waitEvent('proof_ready_checked');
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'checked' }]);
    expect(host.verify).toHaveBeenCalled();
    expect(current.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    current.controller.abort(); await Promise.allSettled([current.completion]);
    expect(vi.getTimerCount()).toBe(0);
  });

  it('consumes readiness written at natural completion through the final pulse', async () => {
    const current = fixture(); await current.wait(current.started.promise);
    current.writeProof(); current.appendReady(); current.turns[0].done.resolve('completed');
    await current.wait(current.stopping.promise);
    expect(host.verify).not.toHaveBeenCalled(); current.stopResult.resolve({ status: 'stopped' });
    await current.waitEvent('proof_ready_checked');
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'checked' }]);
    expect(host.verify).toHaveBeenCalled();
  });

  it('reopens the same late proof assignment after a rejected ownership freeze and checks only the corrected snapshot', async () => {
    const current = fixture({ attempts: 2 }); await current.wait(current.started.promise);
    const first = current.action(), before = current.head();
    const relative = path.join(current.problem.projectRelative, current.problem.projectRelative, '.scratch/tmp/Bridge.lean');
    const misplaced = path.join(current.writer.worktree, relative), content = 'lemma saved_bridge : True := by trivial\n';
    fs.mkdirSync(path.dirname(misplaced), { recursive: true }); fs.writeFileSync(misplaced, content);
    current.writeProof();
    const proofFile = path.join(current.writer.worktree, current.problem.projectRelative, 'Submission.lean');
    const savedProof = fs.readFileSync(proofFile, 'utf8');
    current.appendReady(); await current.pulse(); current.turns[0].done.resolve('interrupted');
    await current.wait(current.stopping.promise); current.stopResult.resolve({ status: 'stopped' });
    await current.waitEvent('source_rejected');
    await vi.waitFor(() => expect(current.turns).toHaveLength(2), { timeout: 5000 });
    expect(current.turns[1].action).toMatchObject({ kind: 'task', assignment: first.assignment });
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    expect(fs.readFileSync(misplaced, 'utf8')).toBe(content); expect(fs.readFileSync(proofFile, 'utf8')).toBe(savedProof);
    expect(current.state.cooperation!.tasks[0].feedback).toContain(`File: ${relative}\nError: math_source_outside_ownership`);
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'failed' }]);
    expect(current.state.cooperation!.proofReadyRecords![0].snapshotCommit).toBeUndefined();
    expect(current.state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(current.events.some(item => item.event === 'worker_failed')).toBe(false);
    const corrected = path.join(current.writer.worktree, current.problem.projectRelative, '.scratch/tmp/Bridge.lean');
    fs.mkdirSync(path.dirname(corrected), { recursive: true }); fs.renameSync(misplaced, corrected);
    current.appendReady('corrected-ready-submission'); await current.pulse(); current.turns[1].done.resolve('interrupted');
    await current.waitEvent('proof_ready_checked');
    expect(current.state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'failed' }, { status: 'checked' }]);
    expect(current.state.cooperation!.tasks[0].proof?.passed).toBe(true);
    expect(fs.readFileSync(corrected, 'utf8')).toBe(content);
    expect(host.verify).toHaveBeenCalled();
  });

  it('restores a frozen snapshot without opening a writer and ignores subsequent live source edits', async () => {
    const example = localExample('solver-proof-ready-restored-', 'lead');
    const { directory, workspace, problem } = example;
    const writer = peerWorker(example, 'writer', { role: 'engineer' });
    const workers = [leadWorker(problem, workspace, 'lead'), writer];
    const plan = parseCooperationPlan(problem, { tasks: problem.targets.map((target, index) => ({
      id: 'goal_' + index, kind: 'goal', ...target, objective: 'Prove ' + target.theoremName,
      status: index === 0 ? 'active' : 'paused', ownerId: writer.id,
    })) });
    let state = solverState(problem, workspace, { runId: 'proof-ready-restored', phase: 'prepared', failures: [],
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit, tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) },
    });
    const preparedController = new AbortController(), controller = new AbortController();
    const prepared = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: preparedController.signal });
    let completion: Promise<unknown> | undefined;
    try {
      const action = await prepared.next(writer, { maxTurns: Infinity, remainingMs: Infinity });
      if (action?.kind !== 'task') throw new Error('fixture_missing_restore_assignment');
      expect(prepared.started(writer, action)).toBe(true);
      prepared.activate(writer, action, async () => {}, async () => {}, async () => {});
      const sourceFile = path.join(writer.worktree, problem.projectRelative, 'Submission.lean');
      fs.writeFileSync(sourceFile, fs.readFileSync(sourceFile, 'utf8').replace('by sorry', 'by rfl'));
      fs.appendFileSync(path.join(writer.worktree, assignmentDeliveryFile(action.assignment)),
        JSON.stringify({ kind: 'ready', id: 'persisted-ready' }) + '\n');
      await prepared.pulse(writer.id);
      const snapshot = commitSolverSources(problem, writer.worktree);
      expect(prepared.proofReadyFrozen(writer, action, snapshot)?.status).toBe('frozen');
      prepared.deactivate(writer); preparedController.abort(); await prepared.stop();
      const archive = path.join(directory, 'frozen-state.json'); writeSolverRunState(archive, state);
      state = readSolverRunState(archive);
      fs.writeFileSync(sourceFile, fs.readFileSync(sourceFile, 'utf8').replace('by rfl', 'by exact rfl'));
      const liveCommit = commitSolverSources(problem, writer.worktree);
      expect(liveCommit).not.toBe(snapshot);
      const open = vi.fn(async () => { throw new Error('fixture_restored_snapshot_must_not_open_model'); });
      vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
      completion = runResearchWorkers({ state, workers, access: workerAccess(workers, directory),
        modules: { ...directSolverModules, M1: { ...directSolverModules.M1, open } }, root: directory,
        buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original goals.', executable: 'offline-fixture',
        profile: 'offline-fixture', signal: controller.signal, deadline: Infinity, maxTurns: Infinity, maxTurnMs: Infinity,
        maxTotalTokens: 0, save: () => {}, emit: event => { if (event === 'proof_ready_checked') controller.abort(); },
      });
      await Promise.allSettled([completion]);
      expect(open).not.toHaveBeenCalled();
      expect(state.cooperation!.proofReadyRecords).toMatchObject([{ status: 'checked', snapshotCommit: snapshot }]);
      expect(state.cooperation!.tasks[0].proof).toMatchObject({ passed: true, commit: snapshot });
      expect(host.verify).toHaveBeenCalled();
      const request = host.verify.mock.calls[0][0];
      expect(committedSource(writer.worktree, request.targetCommit, problem.projectRelative + '/Submission.lean'))
        .toContain('by rfl');
      expect(committedSource(writer.worktree, request.targetCommit, problem.projectRelative + '/Submission.lean'))
        .not.toContain('by exact rfl');
      expect(state.turns).toBe(0);
      expect(state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    } finally {
      preparedController.abort(); controller.abort(); await prepared.stop();
      if (completion) await Promise.allSettled([completion]);
      fs.rmSync(directory, { recursive: true, force: true });
    }
  });

  it.each(['environment', 'task'] as const)('does not freeze old readiness after the %s changes during process shutdown', async change => {
    const current = fixture(); await current.wait(current.started.promise);
    const before = current.head(); current.writeProof(); current.appendReady(); await current.pulse();
    current.turns[0].done.resolve('interrupted'); await current.wait(current.stopping.promise);
    if (change === 'environment') current.state.environmentDigest = 'replacement-environment';
    else current.state.cooperation!.tasks[0].task.revision++;
    current.stopResult.resolve({ status: 'stopped' });
    await vi.waitFor(() => expect(current.state.cooperation!.proofReadyRecords![0].status).toBe('superseded'));
    expect(current.head()).toBe(before); expect(host.verify).not.toHaveBeenCalled();
    expect(current.state.cooperation!.proofReadyRecords![0].snapshotCommit).toBeUndefined();
  });
});
