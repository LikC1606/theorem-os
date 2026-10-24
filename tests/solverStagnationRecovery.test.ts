import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { readSolverRunState, writeSolverRunState } from '../src/solver/archive';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { committedSource, git } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { assignmentDeliveryFile, parseCooperationPlan } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('durable checkpoint before context rotation', () => {
  let directory: string;
  let controllers: AbortController[], running: Promise<unknown>[];

  beforeEach(() => {
    vi.useFakeTimers();
    controllers = []; running = [];
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
  });
  afterEach(async () => {
    controllers.forEach(controller => controller.abort());
    await Promise.allSettled(running);
    vi.useRealTimers(); vi.restoreAllMocks();
    if (directory) fs.rmSync(directory, { recursive: true, force: true });
  });

  function fixture() {
    const example = localExample('solver-stagnation-checkpoint-', 'lead');
    directory = example.directory;
    const { workspace, problem } = example;
    const workers = [leadWorker(problem, workspace), peerWorker(example, 'researcher')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index + 1}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, ...target, status: 'paused' })),
      { id: 'investigate', kind: 'research', ownerId: 'researcher',
        objective: 'Identify and save the precise missing mathematical inference.' },
    ] });
    const state = solverState(problem, workspace, { runId: 'stagnation-checkpoint-fixture', phase: 'prepared',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    const check = vi.fn(async () => { throw new Error('fixture_unexpected_proof_acceptance'); });
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const modules = (open: (options: MathAgentOptions) => Promise<MathAgentSession>): SolverModules => ({
      ...directSolverModules, M1: { ...directSolverModules.M1, open },
      M2: { ...directSolverModules.M2, check, checkTask: check },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => ({
        instructions: 'Offline durable checkpoint fixture.', message: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
      }) },
    });
    const run = (open: (options: MathAgentOptions) => Promise<MathAgentSession>, maxTurns = 2) => {
      const controller = new AbortController(); controllers.push(controller);
      const completion = runResearchWorkers({ state, workers, modules: modules(open),
        access: workerAccess(workers, directory), root: directory, buildFile: path.join(directory, 'build.json'),
        taskText: 'Prove the original targets.', executable: 'offline-fixture', profile: 'offline-fixture',
        signal: controller.signal, deadline: Infinity, maxTurnMs: Infinity, maxTurns, maxTotalTokens: 0,
        save: () => {}, emit: (event, details) => events.push({ event, details }),
      });
      running.push(completion); void completion.catch(() => {}); return completion;
    };
    const publishCheckpoint = () => {
      const request = state.workers![1].contextCheckpoint!;
      expect(request.requestId).toBeTypeOf('string');
      const assignment = state.cooperation!.tasks.find(node => node.task.id === 'investigate')!.assignment!;
      const log = path.join(workers[1].worktree, assignmentDeliveryFile(assignment));
      fs.appendFileSync(log, JSON.stringify({ kind: 'progress',
        summary: 'The exact unresolved inference is retained in the saved mathematical checkpoint.' }) + '\n');
      fs.appendFileSync(log, JSON.stringify({ kind: 'checkpoint', requestId: request.requestId,
        notesDigest: mathDigest(fs.readFileSync(path.join(workers[1].worktree, 'RESEARCH.md'))) }) + '\n');
    };
    return { state, workers, problem, check, events, run, publishCheckpoint };
  }

  function sessions(firstOutput: (workspace: string) => void = () => {}, inheritedNotes?: string) {
    const secondStarted = deferred(), finish = deferred<string>();
    const executedThreads: string[] = [], messages: string[] = [];
    const notify = vi.fn(async (_message: string) => {});
    let turns = 0, threads = 0;
    const close = vi.fn(async () => { if (turns >= 2) finish.resolve('interrupted'); });
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      expect(options.environment?.DEEPSCIENTIST_MATH_WORKER_ID).toBe('researcher');
      if (open.mock.calls.length === 1 && inheritedNotes !== undefined)
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), inheritedNotes);
      const threadId = options.threadId ?? `checkpoint-thread-${++threads}`;
      return { threadId, lastInputTokens: 100_000, close, notify, interrupt: async () => { finish.resolve('interrupted'); },
        run: async (message, _messageId, _workspace, onStarted) => {
          messages.push(message);
          executedThreads.push(threadId); onStarted(`checkpoint-turn-${++turns}`);
          if (turns === 1) {
            options.onActivity?.({ event: 'reasoning' });
            firstOutput(options.workspace); return 'checkpoint';
          }
          if (turns !== 2) throw new Error('fixture_unexpected_extra_turn');
          secondStarted.resolve(); return finish.promise;
        } };
    });
    const waitSecond = (completion: Promise<unknown>) => Promise.race([secondStarted.promise,
      completion.then(() => { throw new Error('fixture_finished_before_second_turn'); })]);
    return { open, notify, close, executedThreads, messages, finish, waitSecond };
  }

  it.each(['none', 'metadata', 'scratch', 'notes'] as const)(
    'retains the same over-threshold thread when the checkpoint saves only %s output', async output => {
      const { state, workers, problem, check, events, run } = fixture();
      const held = sessions(workspace => {
        if (output === 'metadata') {
          const notes = path.join(workspace, 'RESEARCH.md');
          fs.writeFileSync(notes, ''); fs.utimesSync(notes, new Date(), new Date(Date.now() + 1_000));
        }
        if (output === 'scratch') {
          const scratch = path.join(workspace, problem.projectRelative, '.scratch/tmp/Probe.lean');
          fs.mkdirSync(path.dirname(scratch), { recursive: true });
          fs.writeFileSync(scratch, '-- Unchecked exploration, not a durable mathematical checkpoint.\n#check Nat.add_zero\n');
        }
        if (output === 'notes') fs.writeFileSync(path.join(workspace, 'RESEARCH.md'),
          'The current argument is saved, but the report and checkpoint control event have not been published.\n');
      });
      const completion = run(held.open); await held.waitSecond(completion);
      expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-1']);
      expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
      expect(state.workers![1].previousThreadIds ?? []).toEqual([]);
      expect(state.workers![1].lastInputTokens).toBe(100_000);
      expect(events.filter(item => item.event === 'context_checkpoint_requested')).toEqual([{
        event: 'context_checkpoint_requested', details: { workerId: 'researcher', threadId: 'checkpoint-thread-1',
          reason: 'context-threshold', lastInputTokens: 100_000 },
      }]);
      expect(events).toContainEqual({ event: 'context_rotation_deferred', details: { workerId: 'researcher',
        threadId: 'checkpoint-thread-1', reason: 'checkpoint-not-published', lastInputTokens: 100_000 } });
      expect(held.messages[1]).toMatch(/RESEARCH\.md/u);
      expect(held.messages[1]).toMatch(/needsDecision/u);
      expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
      expect(state.cooperation!.tasks.find(node => node.task.id === 'investigate')?.proof).toBeUndefined();
      held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
      if (output === 'scratch') {
        const relative = path.join(problem.projectRelative, '.scratch/tmp/Probe.lean');
        expect(fs.readFileSync(path.join(workers[1].worktree, relative), 'utf8')).toContain('Unchecked exploration');
        expect(git(workers[1].worktree, ['ls-files', '--', relative])).toBe('');
      }
      expect(state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    });

  it('rotates only after the exact mathematical checkpoint is committed and available to the replacement thread', async () => {
    const { state, workers, problem, check, events, run, publishCheckpoint } = fixture();
    const notes = 'The existing reduction preserves positive definiteness and integral representation.\n' +
      'The unresolved step is a least-truant classification; the conditional bridge does not prove it.\n';
    const held = sessions(workspace => {
      fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), notes); publishCheckpoint();
    });
    const completion = run(held.open); await held.waitSecond(completion);
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-2']);
    expect(state.workers![1].previousThreadIds).toEqual(['checkpoint-thread-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toHaveLength(1);
    const published = events.findIndex(item => item.event === 'context_checkpoint_published');
    expect(published).toBeGreaterThan(events.findIndex(item => item.event === 'delivery_published' && item.details?.kind === 'progress'));
    expect(events.findIndex(item => item.event === 'context_restarted')).toBeGreaterThan(published);
    expect(state.cooperation!.deliveries).toContainEqual(expect.objectContaining({ kind: 'progress',
      summary: 'The exact unresolved inference is retained in the saved mathematical checkpoint.' }));
    expect(events).toContainEqual({ event: 'context_checkpoint_ready', details: { workerId: 'researcher',
      threadId: 'checkpoint-thread-1', notesDigest: expect.stringMatching(/^[a-f0-9]{64}$/u) } });
    const draft = state.cooperation!.researchDrafts!.investigate;
    expect(committedSource(workers[1].worktree, draft.commit, 'RESEARCH.md')).toBe(notes);
    expect(fs.readFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), 'utf8')).toBe(notes);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    const node = state.cooperation!.tasks.find(node => node.task.id === 'investigate')!;
    expect(node.proof).toBeUndefined(); expect(node.integratedCheck).toBeUndefined();
    expect(committedSource(workers[0].worktree, state.cooperation!.canonicalCommit ?? problem.baseCommit,
      path.join(problem.projectRelative, 'Submission.lean'))).toContain('sorry');
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('does not treat inherited nonempty notes as a new handoff from the current thread', async () => {
    const { state, workers, check, events, run } = fixture();
    const inherited = 'Previous assignment: a reduction exists, but its exact classification gap was not investigated here.\n';
    const held = sessions(() => {}, inherited);
    const completion = run(held.open); await held.waitSecond(completion);
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(held.messages[1]).toMatch(/RESEARCH\.md/u);
    expect(held.messages[1]).toMatch(/needsDecision/u);
    expect(state.workers![1].previousThreadIds ?? []).toEqual([]);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('accepts a current-thread update to inherited notes while retaining the actual saved draft', async () => {
    const { state, workers, check, events, run, publishCheckpoint } = fixture();
    const revised = 'Current assignment: searched the pinned declaration corpus without a classification theorem.\n' +
      'The remaining input is least-truant classification, and the wrapper only consumes that input.\n';
    const held = sessions(workspace => {
      fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), revised); publishCheckpoint();
    },
      'An inherited earlier mathematical checkpoint.\n');
    const completion = run(held.open); await held.waitSecond(completion);
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-2']);
    expect(events.filter(item => item.event === 'context_restarted')).toHaveLength(1);
    expect(committedSource(workers[1].worktree, state.cooperation!.researchDrafts!.investigate.commit, 'RESEARCH.md')).toBe(revised);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('preserves the same unsaved high-context thread across a saved run and resume', async () => {
    const { state, check, events, run } = fixture();
    const held = sessions();
    await expect(run(held.open, 1)).resolves.toBeUndefined();
    const file = path.join(directory, 'resumable-state.json');
    writeSolverRunState(file, state); Object.assign(state, readSolverRunState(file));
    expect(state.workers![1]).toMatchObject({ threadId: 'checkpoint-thread-1', lastInputTokens: 100_000 });
    const completion = run(held.open, 2); await held.waitSecond(completion);
    expect(held.open.mock.calls.at(-1)![0].threadId).toBe('checkpoint-thread-1');
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('deduplicates checkpoint requests across repeated turns and a persisted run', async () => {
    const { state, check, events, run } = fixture();
    const started = Array.from({ length: 3 }, () => deferred());
    const done = Array.from({ length: 3 }, () => deferred<string>());
    let turns = 0;
    const messages: string[] = [];
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({
      threadId: options.threadId ?? 'deduplicated-thread', lastInputTokens: 100_000,
      close: async () => { done[turns - 1]?.resolve('interrupted'); },
      interrupt: async () => { done[turns - 1]?.resolve('interrupted'); },
      run: async (message, _messageId, _workspace, onStarted) => {
        const turn = turns++;
        if (turn >= 3) throw new Error('fixture_unexpected_fourth_turn');
        messages.push(message); onStarted(`deduplicated-turn-${turn}`);
        started[turn].resolve(); return done[turn].promise;
      },
    }));
    const first = run(open, 2); await started[0].promise;
    await vi.advanceTimersByTimeAsync(120_000); await started[1].promise;
    await vi.advanceTimersByTimeAsync(240_000); await expect(first).resolves.toBeUndefined();
    const file = path.join(directory, 'pending-checkpoint.json');
    writeSolverRunState(file, state);
    const persisted = readSolverRunState(file);
    expect(persisted.workers![1]).toMatchObject({ contextCheckpoint: { threadId: 'deduplicated-thread',
      requestedAt: expect.any(Number) } });
    Object.assign(state, persisted);
    const completion = run(open, 3);
    await Promise.race([started[2].promise, completion.then(() => { throw new Error('fixture_missing_third_turn'); })]);
    expect(open.mock.calls.at(-1)![0].threadId).toBe('deduplicated-thread');
    expect(events.filter(item => item.event === 'context_checkpoint_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(messages.slice(1).every(message => /RESEARCH\.md/u.test(message) && /needsDecision/u.test(message))).toBe(true);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    done[2].resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('still replaces an unsaved thread after an actual provider context overflow', async () => {
    const { state, check, events, run } = fixture();
    const recovered = deferred(), finish = deferred<string>();
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const overflow = open.mock.calls.length === 1;
      return { threadId: overflow ? 'overflow-thread' : 'fresh-overflow-recovery', lastInputTokens: 100_000,
        ...(overflow ? { lastError: 'contextWindowExceeded', lastFailureDiagnostic: { code: 'contextWindowExceeded' } } : {}),
        close: async () => { if (!overflow) finish.resolve('interrupted'); }, interrupt: async () => {},
        run: async (_message, _messageId, _workspace, onStarted) => {
          onStarted(overflow ? 'overflow-turn' : 'recovered-turn');
          if (overflow) return 'failed';
          expect(options.threadId).toBeUndefined(); recovered.resolve(); return finish.promise;
        } };
    });
    const completion = run(open);
    await Promise.race([recovered.promise, completion.then(() => { throw new Error('fixture_overflow_not_recovered'); })]);
    expect(open).toHaveBeenCalledTimes(2);
    expect(state.workers![1].previousThreadIds).toEqual(['overflow-thread']);
    expect(events.filter(item => item.event === 'worker_context_recovering')).toHaveLength(1);
    expect(events.filter(item => item.event === 'context_restarted')).toHaveLength(1);
    expect(state.workers![1].contextOverflow).toMatchObject({ maxOptionalContextBytes: 0 });
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('requests a portable argument once during a live high-context turn without interrupting it', async () => {
    const { state, check, events, run } = fixture();
    const started = deferred(), finish = deferred<string>();
    let inputTokens = 89_000;
    let activity: MathAgentOptions['onActivity'];
    const notify = vi.fn(async (_message: string) => {}), interrupt = vi.fn(async () => {});
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      activity = options.onActivity;
      return { threadId: 'live-reasoning-thread', get lastInputTokens() { return inputTokens; }, notify, interrupt,
        close: async () => { finish.resolve('interrupted'); },
        run: async (_message, _messageId, _workspace, onStarted) => {
          onStarted('live-reasoning-turn'); started.resolve(); return finish.promise;
        } };
    });
    const completion = run(open, 1); await started.promise;
    activity!({ event: 'reasoning' }); await Promise.resolve();
    expect(events.filter(item => item.event === 'context_checkpoint_requested')).toEqual([]);
    inputTokens = 91_000;
    activity!({ event: 'reasoning' }); await Promise.resolve(); await Promise.resolve();
    expect(events.filter(item => item.event === 'context_checkpoint_requested')).toEqual([{
      event: 'context_checkpoint_requested', details: { workerId: 'researcher', threadId: 'live-reasoning-thread',
        reason: 'context-threshold', lastInputTokens: 91_000 },
    }]);
    expect(notify).toHaveBeenCalledOnce();
    expect(notify.mock.calls[0][0]).toMatch(/RESEARCH\.md/u);
    expect(notify.mock.calls[0][0]).toMatch(/needsDecision/u);
    inputTokens = 105_000;
    activity!({ event: 'reasoning' }); await Promise.resolve();
    expect(notify).toHaveBeenCalledOnce(); expect(interrupt).not.toHaveBeenCalled();
    expect(open).toHaveBeenCalledOnce(); expect(state.workers![1].threadId).toBe('live-reasoning-thread');
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('retains early and updated notes until the report and current checkpoint are explicitly published', async () => {
    const { state, workers, check, events, run, publishCheckpoint } = fixture();
    const started = Array.from({ length: 3 }, () => deferred());
    const done = Array.from({ length: 3 }, () => deferred<string>());
    const executedThreads: string[] = [], messages: string[] = [];
    const early = 'An early reduction, before the later classification argument.\n';
    const current = early + 'Current gap: the classification argument still needs an independent finite certificate.\n';
    const notes = path.join(workers[1].worktree, 'RESEARCH.md');
    let inputTokens = 89_000, turns = 0, threads = 0;
    let activity: MathAgentOptions['onActivity'];
    const notify = vi.fn(async (_message: string) => {}), interrupt = vi.fn(async () => {});
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      activity = options.onActivity;
      const threadId = options.threadId ?? `checkpoint-window-${++threads}`;
      return { threadId, get lastInputTokens() { return inputTokens; }, notify, interrupt,
        close: async () => { done[turns - 1]?.resolve('interrupted'); },
        run: async (message, _messageId, _workspace, onStarted) => {
          const turn = turns++;
          if (turn >= 3) throw new Error('fixture_unexpected_fourth_turn');
          executedThreads.push(threadId); messages.push(message); onStarted(`checkpoint-window-turn-${turn}`);
          started[turn].resolve(); return done[turn].promise;
        } };
    });
    const completion = run(open, 3); await started[0].promise;
    fs.writeFileSync(notes, early);
    inputTokens = 91_000; activity!({ event: 'reasoning' }); await Promise.resolve();
    expect(notify).toHaveBeenCalledOnce();
    expect(state.workers![1].contextCheckpoint).toMatchObject({ threadId: 'checkpoint-window-1', notesDigest: mathDigest(early) });
    inputTokens = 96_000; done[0].resolve('checkpoint');
    await Promise.race([started[1].promise, completion.then(() => { throw new Error('fixture_missing_second_turn'); })]);
    expect(executedThreads).toEqual(['checkpoint-window-1', 'checkpoint-window-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(messages[1]).toMatch(/RESEARCH\.md/u);
    expect(state.workers![1].threadId).toBe('checkpoint-window-1');
    fs.writeFileSync(notes, current);
    await vi.advanceTimersByTimeAsync(5_000);
    expect(interrupt).not.toHaveBeenCalled();
    expect(executedThreads).toEqual(['checkpoint-window-1', 'checkpoint-window-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(state.workers![1].contextCheckpoint?.publishedNotesDigest).toBeUndefined();
    publishCheckpoint(); done[1].resolve('checkpoint');
    await Promise.race([started[2].promise, completion.then(() => { throw new Error('fixture_missing_replacement_turn'); })]);
    expect(executedThreads).toEqual(['checkpoint-window-1', 'checkpoint-window-1', 'checkpoint-window-2']);
    expect(events.filter(item => item.event === 'context_restarted')).toHaveLength(1);
    expect(events).toContainEqual({ event: 'context_checkpoint_ready', details: { workerId: 'researcher',
      threadId: 'checkpoint-window-1', notesDigest: mathDigest(current) } });
    expect(committedSource(workers[1].worktree, state.cooperation!.researchDrafts!.investigate.commit, 'RESEARCH.md')).toBe(current);
    expect(interrupt).not.toHaveBeenCalled(); expect(check).not.toHaveBeenCalled();
    expect(state.cooperation!.tasks.find(node => node.task.id === 'investigate')?.proof).toBeUndefined();
    done[2].resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it('honors a persisted checkpoint request even when an older archive has no session baseline', async () => {
    const { state, workers, check, events, run } = fixture();
    const inherited = 'A saved earlier reduction, without the later argument.\n';
    const held = sessions(() => {}, inherited);
    await expect(run(held.open, 1)).resolves.toBeUndefined();
    const worker = state.workers![1];
    delete worker.contextCheckpointBaseline;
    worker.contextCheckpoint = { threadId: worker.threadId!, requestedAt: Date.now(), notesDigest: mathDigest(inherited) };
    const file = path.join(directory, 'legacy-checkpoint-request.json');
    writeSolverRunState(file, state); Object.assign(state, readSolverRunState(file));
    expect(state.workers![1].contextCheckpointBaseline).toBeUndefined();
    const completion = run(held.open, 2); await held.waitSecond(completion);
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(fs.readFileSync(path.join(workers[1].worktree, 'RESEARCH.md'), 'utf8')).toBe(inherited);
    expect(held.messages[1]).toMatch(/RESEARCH\.md/u); expect(check).not.toHaveBeenCalled();
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
  });

  it.each([false, true])('preserves a legacy thread without checkpoint metadata until a requested handoff is saved (%s)', async hasNotes => {
    const { state, workers, check, events, run, publishCheckpoint } = fixture();
    const held = sessions();
    await expect(run(held.open, 1)).resolves.toBeUndefined();
    const notes = path.join(workers[1].worktree, 'RESEARCH.md');
    if (hasNotes) fs.writeFileSync(notes, 'Legacy notes do not establish when the last argument was saved.\n');
    delete state.workers![1].contextCheckpoint; delete state.workers![1].contextCheckpointBaseline;
    const file = path.join(directory, 'legacy-context-state.json');
    writeSolverRunState(file, state); Object.assign(state, readSolverRunState(file));
    const completion = run(held.open, 2); await held.waitSecond(completion);
    expect(held.open.mock.calls.at(-1)![0].threadId).toBe('checkpoint-thread-1');
    expect(held.executedThreads).toEqual(['checkpoint-thread-1', 'checkpoint-thread-1']);
    expect(events.filter(item => item.event === 'context_restarted')).toEqual([]);
    expect(state.workers![1].contextCheckpoint).toMatchObject({ threadId: 'checkpoint-thread-1' });
    expect(check).not.toHaveBeenCalled();
    fs.writeFileSync(notes, 'A requested current handoff preserves the precise unresolved classification step.\n');
    publishCheckpoint();
    held.finish.resolve('checkpoint'); await expect(completion).resolves.toBeUndefined();
    const reopened = deferred(), finish = deferred<string>();
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      expect(options.threadId).toBeUndefined();
      return { threadId: 'legacy-replacement-thread', lastInputTokens: 1,
        close: async () => { finish.resolve('interrupted'); }, interrupt: async () => {},
        run: async (_message, _messageId, _workspace, onStarted) => {
          onStarted('legacy-replacement-turn'); reopened.resolve(); return finish.promise;
        } };
    });
    const resumed = run(open, 3);
    await Promise.race([reopened.promise, resumed.then(() => { throw new Error('fixture_missing_legacy_replacement'); })]);
    expect(events.filter(item => item.event === 'context_restarted')).toHaveLength(1);
    expect(state.workers![1].threadId).toBe('legacy-replacement-thread');
    expect(check).not.toHaveBeenCalled(); finish.resolve('checkpoint'); await expect(resumed).resolves.toBeUndefined();
  });

  it.each([
    { contextCheckpoint: { threadId: '', requestedAt: 0 } },
    { contextCheckpoint: { threadId: 'thread', requestedAt: -1 } },
    { contextCheckpoint: { threadId: 'thread', requestedAt: 0, deferredAt: -1 } },
    { contextCheckpoint: { threadId: 'thread', requestedAt: 0, notesDigest: 'not-a-digest' } },
    { contextCheckpointBaseline: { threadId: '', notesDigest: 'a'.repeat(64) } },
    { contextCheckpointBaseline: { threadId: 'thread', notesDigest: 'not-a-digest' } },
  ])('rejects malformed persisted context checkpoint metadata: %j', invalid => {
    const { state } = fixture();
    Object.assign(state.workers![1], invalid);
    const file = path.join(directory, 'invalid-checkpoint.json');
    writeSolverRunState(file, state);
    expect(() => readSolverRunState(file)).toThrow('math_resume_state_invalid:workers.1.contextCheckpoint');
  });
});
