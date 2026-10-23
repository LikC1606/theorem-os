import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { readSolverRunState, writeSolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { createCapacityExploration } from '../src/solver/capacityExploration';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { committedSource, git } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('cooperative advisory continuation and event driven handoffs', () => {
  let directory: string;
  let controllers: AbortController[], running: Promise<unknown>[];

  beforeEach(() => {
    vi.useFakeTimers();
    controllers = []; running = [];
    // Exercise the ordinary explicit pulse/delivery path without advancing the unrelated poller 600 times.
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
  });
  afterEach(async () => {
    controllers.forEach(controller => controller.abort()); await Promise.allSettled(running);
    vi.useRealTimers(); vi.restoreAllMocks();
    if (directory) fs.rmSync(directory, { recursive: true, force: true });
  });

  function fixture(initial = false, projectRelative?: string, continuation?: 'lead' | 'lead-capacity' | 'custom-full' | 'peer', capacity = false) {
    const example = localExample('solver-advisory-checkpoint-', 'lead');
    directory = example.directory;
    if (projectRelative) {
      git(example.workspace, ['mv', '--', example.problem.projectRelative, projectRelative]);
      git(example.workspace, ['-c', 'user.name=Offline fixture', '-c', 'user.email=fixture@localhost',
        'commit', '--no-gpg-sign', '--quiet', '-m', 'Relocate disposable scheduling fixture']);
      example.problem = { ...example.problem, projectRelative, baseCommit: git(example.workspace, ['rev-parse', 'HEAD']) };
    }
    const { workspace, problem } = example;
    const workers = [leadWorker(problem, workspace), peerWorker(example, initial ? 'engineer' : 'researcher',
      { role: initial ? 'engineer' : capacity || continuation === 'lead-capacity' ? 'prover' : 'researcher' })];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index + 1}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, ...target, status: capacity ? 'active' : 'paused',
        ...(capacity ? { ownerId: 'unavailable-prover' } : {}) })),
      { id: 'investigate', kind: 'research', ownerId: 'researcher', objective: 'Resolve the precise missing construction.' },
    ] });
    const state = solverState(problem, workspace, { runId: 'advisory-checkpoint-fixture', phase: 'prepared',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      ...initial ? {} : { cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } } });
    if (capacity) {
      const nodes = state.cooperation!.tasks;
      const exploration = createCapacityExploration(nodes[0], workers[1], nodes, {
        environmentDigest: state.environmentDigest!, problemReceiptDigest: problem.receiptDigest,
      }, 'interface');
      state.cooperation!.tasks = nodes.filter(node => node.task.id !== 'investigate').concat(exploration);
    }
    if (continuation && continuation !== 'peer') {
      state.cooperation!.error = 'offline_lead_replanning_required';
      state.cooperation!.tasks.find(node => node.task.id === 'investigate')!.task.status = 'paused';
      if (continuation === 'lead-capacity') {
        state.cooperation!.tasks.find(node => node.task.id === 'investigate')!.task.status = 'active';
        for (const node of state.cooperation!.tasks.filter(node => node.task.kind === 'goal')) {
          node.task.status = 'active'; node.task.dependsOn = ['investigate'];
        }
      }
    }
    const check = vi.fn(async () => { throw new Error('fixture_unexpected_proof_acceptance'); });
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const controller = new AbortController();
    controllers.push(controller);
    const contextSettings = { instructionsSuffix: '' };
    const modules = (open: (options: MathAgentOptions) => Promise<MathAgentSession>): SolverModules => ({
      ...directSolverModules, M1: { ...directSolverModules.M1, open },
      M2: { ...directSolverModules.M2, check, checkTask: check },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => {
        const assignment = access.assignment!;
        const current = { assignment, receipt: leadPlanDeliveryFile(assignment),
          feedback: assignment.kind === 'task' ? _state.cooperation?.tasks.find(node => node.task.id === assignment.task.id)?.feedback : undefined,
          inbox: _state.cooperation?.deliveries?.map(delivery => delivery.summary) ?? [] };
        return {
          instructions: 'Offline scheduling fixture.' + contextSettings.instructionsSuffix +
            (continuation && assignment.kind === 'lead' ? assignment.planNonce : ''),
          message: continuation ? JSON.stringify({ ...current, mode: 'full',
            exactTasks: state.cooperation!.tasks.map(node => node.task), sentinel: 'full-context-exact-types-'.repeat(300) })
            : JSON.stringify(assignment),
          ...(continuation && continuation !== 'custom-full' ? { continuationMessage: JSON.stringify({ ...current, mode: 'short' }) } : {}),
          scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest },
        };
      } },
    });
    const run = (open: (options: MathAgentOptions) => Promise<MathAgentSession>, maxTurns = 2) => {
      const completion = runResearchWorkers({
        state, workers, modules: modules(open), access: workerAccess(workers, directory),
        root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
        executable: 'offline-fixture', profile: 'offline-fixture', signal: controller.signal,
        deadline: Infinity, maxTurnMs: Infinity, maxTurns, maxTotalTokens: 0,
        save: () => {}, emit: (event, details) => events.push({ event, details }),
      });
      running.push(completion); return completion;
    };
    return { state, workers, problem, check, events, controller, run, contextSettings };
  }

  function heldAdvisoryTurns(count: number) {
    const started = Array.from({ length: count }, () => deferred());
    const done = Array.from({ length: count }, () => deferred<string>());
    const actions: Extract<CooperativeAction, { kind: 'task' }>[] = [];
    let index = 0, active: ReturnType<typeof deferred<string>> | undefined;
    const interrupt = vi.fn(async () => { active?.resolve('interrupted'); });
    const notify = vi.fn(async () => {});
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({
      threadId: options.threadId ?? 'persistent-backoff-thread', interrupt, notify,
      close: async () => { active?.resolve('interrupted'); },
      run: async (message, _messageId, _workspace, onStarted) => {
        const turn = index++;
        if (turn >= count) throw new Error('fixture_unexpected_extra_turn');
        const action = JSON.parse(message) as CooperativeAction;
        if (action.kind !== 'task' || action.task.id !== 'investigate') throw new Error('fixture_unexpected_responsibility:' + action.kind);
        actions.push(action); active = done[turn];
        onStarted(`backoff-turn-${turn}`); started[turn].resolve();
        return done[turn].promise;
      },
    }));
    const wait = (turn: number, completion: Promise<unknown>) => Promise.race([started[turn].promise,
      completion.then(() => { throw new Error('fixture_finished_before_expected_turn:' + turn); })]);
    return { started, done, actions, interrupt, notify, open, wait };
  }

  function heldContinuationTurns(options: { saveNotes?: boolean; highContext?: boolean } = {}) {
    const started = [deferred(), deferred()], done = [deferred<string>(), deferred<string>()];
    const messages: { assignment: CooperativeAction; receipt?: string; mode: string; exactTasks?: unknown[]; sentinel?: string;
      feedback?: string; inbox?: string[] }[] = [];
    const threads: string[] = [];
    let turns = 0, newThreads = 0, active: ReturnType<typeof deferred<string>> | undefined;
    const interrupt = vi.fn(async () => { active?.resolve('interrupted'); });
    const close = vi.fn(async () => { active?.resolve('interrupted'); });
    const open = vi.fn(async (access: MathAgentOptions): Promise<MathAgentSession> => {
      const threadId = access.threadId ?? `continuation-thread-${++newThreads}`;
      return { threadId, close, interrupt, notify: async () => {},
        ...(options.highContext ? { lastInputTokens: 100_000 } : {}),
        run: async (message, _messageId, _workspace, onStarted) => {
          const turn = turns++;
          if (turn > 1) throw new Error('fixture_unexpected_third_continuation_turn');
          messages.push(JSON.parse(message)); threads.push(threadId); active = done[turn];
          onStarted(`continuation-turn-${turn}`);
          if (turn === 0 && options.saveNotes)
            fs.writeFileSync(path.join(access.workspace, 'RESEARCH.md'), 'The current mathematical argument and exact unresolved inference are saved.\n');
          started[turn].resolve(); return done[turn].promise;
        } };
    });
    const wait = (turn: number, completion: Promise<unknown>) => Promise.race([started[turn].promise,
      completion.then(() => { throw new Error('fixture_finished_before_continuation:' + turn); })]);
    return { open, close, interrupt, messages, threads, wait, done };
  }

  it.each(['lead', 'peer'] as const)('does not interrupt unlimited %s work after two minutes or after saving progress', async role => {
    const { workers, check, events, controller, run } = fixture(false, undefined, role);
    const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    await vi.advanceTimersByTimeAsync(120_000);
    expect(held.interrupt).not.toHaveBeenCalled();
    expect(held.open).toHaveBeenCalledOnce();
    fs.writeFileSync(path.join(workers[role === 'lead' ? 0 : 1].worktree, 'RESEARCH.md'),
      'Durable mathematical progress; the exact remaining inference is still being investigated.\n');
    await vi.advanceTimersByTimeAsync(3_600_000);
    expect(held.interrupt).not.toHaveBeenCalled();
    expect(held.open).toHaveBeenCalledOnce();
    expect(events.some(item => item.event === 'cooperative_checkpoint_scheduled' ||
      item.event === 'cooperative_checkpoint_interrupted' || item.event === 'plan_rejected')).toBe(false);
    expect(check).not.toHaveBeenCalled();
    controller.abort(new Error('fixture_complete'));
    await expect(completion).rejects.toThrow('fixture_complete');
    expect(vi.getTimerCount()).toBe(0);
  });

  it.each(['lead', 'custom-full'] as const)(
    'keeps first Lead dispatch full and resumes %s with the current nonce and receipt', async mode => {
      const { state, check, events, controller, run } = fixture(false, undefined, mode);
      const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
      await held.wait(0, completion);
      expect(held.messages[0].assignment.kind).toBe('lead');
      expect(held.messages[0].mode).toBe('full');
      expect(held.messages[0].sentinel).toContain('full-context-exact-types');
      held.done[0].resolve('interrupted'); await held.wait(1, completion);
      const [first, latest] = held.messages;
      expect(latest.assignment.kind).toBe('lead');
      if (first.assignment.kind !== 'lead' || latest.assignment.kind !== 'lead') throw new Error('fixture_not_lead');
      expect(latest.assignment.planVersion).toBe(first.assignment.planVersion);
      expect(latest.assignment.planNonce).not.toBe(first.assignment.planNonce);
      expect(latest.receipt).toBe(leadPlanDeliveryFile(latest.assignment));
      expect(latest.receipt).not.toBe(first.receipt);
      expect(JSON.stringify(latest)).not.toContain(first.assignment.planNonce);
      expect(latest.mode).toBe(mode === 'lead' ? 'short' : 'full');
      expect(held.threads).toEqual(['continuation-thread-1', 'continuation-thread-1']);
      expect(held.open).toHaveBeenCalledTimes(2);
      expect(held.open.mock.calls[1][0].threadId).toBe('continuation-thread-1');
      expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode))
        .toEqual(['full', mode === 'lead' ? 'continuation' : 'full']);
      expect(events.some(item => item.event === 'capacity_refill_assessed' || item.event === 'stagnation_recovery_assessed')).toBe(false);
      expect(state.cooperation!.planPublication).toBeUndefined();
      expect(state.cooperation!.lastLeadInputDigest).toBeUndefined();
      expect(state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
      expect(held.open.mock.calls.every(([access]) => access.turnTimeoutMs === undefined)).toBe(true);
      expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
      controller.abort(new Error('fixture_complete'));
      await expect(completion).rejects.toThrow('fixture_complete');
      expect(check).not.toHaveBeenCalled(); expect(vi.getTimerCount()).toBe(0);
    });

  it('sends full context again after a saved Lead checkpoint rotates to a fresh thread', async () => {
    const { state, check, events, controller, run } = fixture(false, undefined, 'lead');
    const held = heldContinuationTurns({ saveNotes: true, highContext: true });
    const completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    held.done[0].resolve('interrupted'); await held.wait(1, completion);
    expect(held.threads).toEqual(['continuation-thread-1', 'continuation-thread-2']);
    expect(held.messages.map(message => message.mode)).toEqual(['full', 'full']);
    expect(held.messages[1].sentinel).toContain('full-context-exact-types');
    expect(held.messages[1].exactTasks).toEqual(state.cooperation!.tasks.map(node => node.task));
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode)).toEqual(['full', 'full']);
    expect(events).toContainEqual({ event: 'context_restarted', details: expect.objectContaining({ workerId: 'solver',
      previousThreadId: 'continuation-thread-1', reason: 'context' }) });
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
  });

  it('retains a real capacity request as requested when an unfinished Lead checkpoint has no saved decision', async () => {
    const { state, check, events, controller, run } = fixture(false, undefined, 'lead-capacity');
    const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    const first = held.messages[0].assignment;
    if (first.kind !== 'lead') throw new Error('fixture_not_lead');
    expect(first.capacityRefill).toMatchObject({ workerIds: ['researcher'] });
    expect(state.cooperation!.lastCapacityRefill?.status).toBe('requested');
    held.done[0].resolve('interrupted'); await held.wait(1, completion);
    const latest = held.messages[1].assignment;
    if (latest.kind !== 'lead') throw new Error('fixture_not_lead');
    expect(held.messages[1].mode).toBe('short');
    expect(latest.capacityRefill).toEqual(state.cooperation!.lastCapacityRefill && {
      requestId: state.cooperation!.lastCapacityRefill.requestId,
      inputDigest: state.cooperation!.lastCapacityRefill.inputDigest,
      workerIds: state.cooperation!.lastCapacityRefill.workerIds,
      requestedAt: state.cooperation!.lastCapacityRefill.requestedAt,
    });
    expect(state.cooperation!.lastCapacityRefill?.status).toBe('requested');
    expect(events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
  });

  it('sends the complete revised mathematical graph when the Lead plan version changes in the same thread', async () => {
    const { state, check, events, controller, run } = fixture(false, undefined, 'lead');
    const exactType = '∀ (n : Nat), ' + 'True ∧ '.repeat(250) + 'True';
    const next = CooperativeResearch.prototype.next;
    let leadDispatches = 0;
    vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function (this: CooperativeResearch, worker, budget) {
      const action = await next.call(this, worker, budget);
      if (action?.kind === 'lead' && ++leadDispatches === 2) {
        // A scheduler graph replacement occurs between accepted dispatches, without rotating the model thread.
        state.cooperation!.planVersion = 'revised-plan-version';
        state.cooperation!.tasks.find(node => node.task.kind === 'goal')!.task.type = exactType;
        action.planVersion = state.cooperation!.planVersion;
      }
      return action;
    });
    const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    held.done[0].resolve('interrupted'); await held.wait(1, completion);
    const [first, revised] = held.messages;
    expect(first.assignment.kind).toBe('lead'); expect(revised.assignment.kind).toBe('lead');
    if (first.assignment.kind !== 'lead' || revised.assignment.kind !== 'lead') throw new Error('fixture_not_lead');
    expect(revised.assignment.planVersion).not.toBe(first.assignment.planVersion);
    expect(held.threads).toEqual(['continuation-thread-1', 'continuation-thread-1']);
    expect(revised.mode).toBe('full');
    expect(JSON.stringify(revised.exactTasks)).toContain(exactType);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode)).toEqual(['full', 'full']);
    expect(events.some(item => item.event === 'context_restarted')).toBe(false);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
  });

  it('resumes a same-thread advisory assignment with its current short message', async () => {
    const { state, check, events, controller, run } = fixture(false, undefined, 'peer');
    const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    held.done[0].resolve('interrupted'); await held.wait(1, completion);
    expect(held.messages.every(message => message.assignment.kind === 'task')).toBe(true);
    expect(held.messages.map(message => message.mode)).toEqual(['full', 'short']);
    expect(held.threads).toEqual(['continuation-thread-1', 'continuation-thread-1']);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode)).toEqual(['full', 'continuation']);
    expect(state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
  });

  it('sends new feedback and inbox findings in a same-thread short advisory continuation', async () => {
    const { state, check, events, controller, run } = fixture(false, undefined, 'peer');
    const next = CooperativeResearch.prototype.next;
    let peerDispatches = 0;
    vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function (this: CooperativeResearch, worker, budget) {
      const action = await next.call(this, worker, budget);
      if (action?.kind === 'task' && action.task.id === 'investigate' && ++peerDispatches === 2) {
        const node = state.cooperation!.tasks.find(node => node.task.id === action.task.id)!;
        node.feedback = 'Use the newly saved exact coercion lemma before another library search.';
        (state.cooperation!.deliveries ??= []).push({ id: 'fresh-peer-input', producer: 'solver',
          taskId: node.task.id, taskDigest: action.assignment.taskDigest, kind: 'research', status: 'advisory',
          summary: 'A saved finding identifies the exact missing library interface.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: Date.now() });
      }
      return action;
    });
    const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
    await held.wait(0, completion);
    held.done[0].resolve('interrupted'); await held.wait(1, completion);
    expect(held.messages.map(message => message.mode)).toEqual(['full', 'short']);
    expect(held.messages[1].feedback).toContain('newly saved exact coercion lemma');
    expect(held.messages[1].inbox).toContain('A saved finding identifies the exact missing library interface.');
    expect(held.threads).toEqual(['continuation-thread-1', 'continuation-thread-1']);
    expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode)).toEqual(['full', 'continuation']);
    expect(check).not.toHaveBeenCalled();
    controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
  });

  it.each(['task', 'environment', 'seed', 'instructions'] as const)(
    'sends full advisory context when its %s responsibility changes', async change => {
      const { state, workers, check, events, controller, run, contextSettings } = fixture(false, undefined, 'peer');
      const next = CooperativeResearch.prototype.next;
      let peerDispatches = 0;
      vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function (this: CooperativeResearch, worker, budget) {
        const action = await next.call(this, worker, budget);
        if (action?.kind === 'task' && action.task.id === 'investigate' && ++peerDispatches === 2) {
          const node = state.cooperation!.tasks.find(node => node.task.id === action.task.id)!;
          if (change === 'task') {
            node.task = { ...node.task, objective: 'Resolve the distinct finite-dimensional construction.', revision: node.task.revision + 1 };
            action.task = node.task; action.assignment.taskDigest = taskVersion(node.task);
          }
          if (change === 'environment') state.environmentDigest = 'revised-offline-environment';
          if (change === 'seed') {
            git(workers[1].worktree, ['-c', 'user.name=Offline fixture', '-c', 'user.email=fixture@localhost',
              'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'Revise disposable continuation seed']);
            action.assignment.seedCommit = git(workers[1].worktree, ['rev-parse', 'HEAD']);
          }
          if (change === 'instructions') contextSettings.instructionsSuffix = ' Revised offline role instructions.';
        }
        return action;
      });
      const held = heldContinuationTurns(), completion = run(held.open, Infinity); void completion.catch(() => {});
      await held.wait(0, completion);
      held.done[0].resolve('interrupted'); await held.wait(1, completion);
      expect(held.messages.map(message => message.mode)).toEqual(['full', 'full']);
      expect(held.messages[1].sentinel).toContain('full-context-exact-types');
      expect(held.threads).toEqual(['continuation-thread-1', change === 'task' ? 'continuation-thread-2' : 'continuation-thread-1']);
      expect(events.filter(item => item.event === 'context_dispatched').map(item => item.details?.mode)).toEqual(['full', 'full']);
      if (change === 'task') {
        const revised = held.messages[1].assignment;
        expect(revised.kind === 'task' && revised.task.objective).toContain('distinct finite-dimensional construction');
      }
      if (change === 'seed') {
        const first = held.messages[0].assignment, revised = held.messages[1].assignment;
        expect(first.kind === 'task' && revised.kind === 'task' && revised.assignment.seedCommit).not.toBe(
          first.kind === 'task' && first.assignment.seedCommit);
      }
      expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
      controller.abort(new Error('fixture_complete')); await expect(completion).rejects.toThrow('fixture_complete');
    });

  it.each(['acknowledged', 'stalled'] as const)(
    'yields a %s capacity exploration only when typed work is ready and preserves its exact draft', async interruptKind => {
      const { state, workers, problem, check, events, run } = fixture(false, undefined, undefined, true);
      const explorationId = state.cooperation!.tasks.find(node => node.capacityExploration)!.task.id;
      const firstStarted = deferred(), resumed = deferred(), interrupted = deferred<string>(), finish = deferred<string>();
      let typedWorkReady = false;
      vi.spyOn(CooperativeResearch.prototype, 'shouldYieldCapacityExploration')
        .mockImplementation(() => typedWorkReady);
      const teardown = deferred();
      const actions: Extract<CooperativeAction, { kind: 'task' }>[] = [];
      let turns = 0, active: ReturnType<typeof deferred<string>> | undefined, lastError: string | undefined;
      const close = vi.fn(async () => {
        lastError = 'math_codex_transport_closed'; active?.reject(new Error(lastError));
        if (interruptKind === 'stalled' && turns === 1) await teardown.promise;
      });
      const interrupt = vi.fn(async () => { if (interruptKind === 'acknowledged') interrupted.resolve('interrupted'); });
      const notify = vi.fn(async () => {});
      const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => ({
        threadId: options.threadId ?? 'saved-advisory-thread', close, interrupt, notify,
        get lastError() { return lastError; },
        run: async (message, _messageId, _workspace, onStarted) => {
          lastError = undefined;
          const action = JSON.parse(message) as Extract<CooperativeAction, { kind: 'task' }>;
          actions.push(action);
          onStarted(`advisory-turn-${++turns}`);
          const notes = path.join(options.workspace, 'RESEARCH.md');
          if (turns === 1) {
            fs.writeFileSync(notes, 'A partial construction and its exact remaining quantitative gap.\n');
            active = interrupted; firstStarted.resolve();
            return interrupted.promise;
          }
          expect(fs.readFileSync(notes, 'utf8')).toContain('exact remaining quantitative gap');
          const draft = state.cooperation!.researchDrafts![explorationId];
          expect(draft).toMatchObject({ workerId: 'researcher', assignmentId: actions[0].assignment.assignmentId });
          expect(committedSource(workers[1].worktree, draft.commit, 'RESEARCH.md')).toContain('partial construction');
          const node = state.cooperation!.tasks.find(node => node.task.id === explorationId)!;
          expect(node.status).toBe('running'); expect(node.proof).toBeUndefined(); expect(node.integratedCheck).toBeUndefined();
          expect(state.check).toBeUndefined(); expect(check).not.toHaveBeenCalled();
          fs.writeFileSync(notes, 'A completed advisory construction with its precise assumptions and unresolved quantitative gap.\n');
          active = finish; resumed.resolve();
          return finish.promise;
        },
      }));
      const completion = run(open); void completion.catch(() => {});
      const stopped = completion.then(() => { throw new Error('fixture_stopped_before_next_checkpoint:' + JSON.stringify(events)); });
      void stopped.catch(() => {});
      await Promise.race([firstStarted.promise, stopped]);
      expect(open.mock.calls[0][0].turnTimeoutMs).toBeUndefined();
      await vi.advanceTimersByTimeAsync(3_600_000);
      expect(notify).not.toHaveBeenCalled(); expect(interrupt).not.toHaveBeenCalled();
      typedWorkReady = true;
      await vi.advanceTimersByTimeAsync(5_000);
      typedWorkReady = false;
      expect(interrupt).toHaveBeenCalledOnce();
      if (interruptKind === 'stalled') {
        expect(close).not.toHaveBeenCalled();
        await vi.advanceTimersByTimeAsync(10_000);
        expect(close).toHaveBeenCalledOnce(); expect(open).toHaveBeenCalledOnce();
        expect(state.cooperation!.researchDrafts?.[explorationId]).toBeUndefined();
        expect(state.workers![1].candidate).toBeUndefined();
        teardown.resolve();
      }
      await Promise.race([resumed.promise, stopped]);
      expect(actions[1].assignment).toEqual(actions[0].assignment);
      expect(open).toHaveBeenCalledTimes(interruptKind === 'stalled' ? 2 : 1);
      if (interruptKind === 'stalled') expect(open.mock.calls[1][0].threadId).toBe('saved-advisory-thread');
      expect(vi.getTimerCount()).toBe(1);
      await vi.advanceTimersByTimeAsync(15_000);
      expect(interrupt).toHaveBeenCalledOnce();
      expect(close).toHaveBeenCalledTimes(interruptKind === 'stalled' ? 1 : 0);
      finish.resolve('completed'); await expect(completion).resolves.toBeUndefined();
      expect(vi.getTimerCount()).toBe(0);
      expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
      expect(state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
      expect(state.workers![1]).toMatchObject({ threadId: 'saved-advisory-thread', sessionTaskId: explorationId });
      expect(state.cooperation!.tasks.find(node => node.task.id === explorationId)?.status).toBe('completed');
      expect(state.cooperation!.deliveries?.some(delivery => delivery.kind === 'proof' || delivery.kind === 'failure')).toBeFalsy();
      expect(events).toContainEqual({ event: 'turn_checkpoint', details: {
        workerId: 'researcher', turn: 1, reason: 'math_cooperative_scheduling_checkpoint',
      } });
      expect(events.some(item => item.event === 'worker_failed' || item.event === 'turn_failed')).toBe(false);
      for (const target of problem.targets) expect(committedSource(workers[0].worktree,
        state.cooperation!.canonicalCommit!, path.join(problem.projectRelative, target.proofPath))).toContain('sorry');
    });

  it('preserves project scratch through a natural checkpoint without committing it or changing the assignment', async () => {
    const { state, workers, problem, check, events, run } = fixture(false, 'generated/project');
    const held = heldAdvisoryTurns(2), completion = run(held.open); void completion.catch(() => {});
    await held.wait(0, completion);
    const worktree = workers[1].worktree;
    const relative = path.join(problem.projectRelative, '.scratch', 'tmp', 'LibProbe.lean');
    const scratch = path.join(worktree, relative), notes = path.join(worktree, 'RESEARCH.md');
    const probe = '-- Advisory library probe, never accepted proof content.\n#check Nat.add_zero\n';
    fs.mkdirSync(path.dirname(scratch), { recursive: true }); fs.writeFileSync(scratch, probe);
    fs.writeFileSync(notes, 'A saved construction with its exact remaining quantitative gap.\n');
    held.done[0].resolve('interrupted'); await held.wait(1, completion);

    expect(held.interrupt).not.toHaveBeenCalled(); expect(held.open).toHaveBeenCalledOnce();
    expect(held.actions[1].task.id).toBe(held.actions[0].task.id);
    expect(held.actions[1].assignment).toEqual(held.actions[0].assignment);
    expect(state.workers![1]).toMatchObject({ threadId: 'persistent-backoff-thread', sessionTaskId: 'investigate' });
    expect(fs.readFileSync(notes, 'utf8')).toContain('exact remaining quantitative gap');
    expect(fs.lstatSync(scratch).isFile()).toBe(true); expect(fs.readFileSync(scratch, 'utf8')).toBe(probe);
    expect(git(worktree, ['ls-files', '--', relative])).toBe('');
    expect(git(worktree, ['ls-files', '--others', '--exclude-standard', '--', relative])).toBe(relative);
    const draft = state.cooperation!.researchDrafts!.investigate;
    expect(draft).toMatchObject({ workerId: 'researcher', assignmentId: held.actions[0].assignment.assignmentId });
    expect(committedSource(worktree, draft.commit, 'RESEARCH.md')).toContain('exact remaining quantitative gap');
    expect(git(worktree, ['ls-tree', '-r', '--name-only', draft.commit, '--', relative])).toBe('');
    const node = state.cooperation!.tasks.find(node => node.task.id === 'investigate')!;
    expect(node.status).toBe('running'); expect(node.proof).toBeUndefined(); expect(node.integratedCheck).toBeUndefined();

    fs.writeFileSync(notes, 'A completed advisory investigation with the quantitative gap still explicit.\n');
    held.done[1].resolve('completed'); await expect(completion).resolves.toBeUndefined();
    expect(fs.readFileSync(scratch, 'utf8')).toBe(probe);
    expect(git(worktree, ['ls-files', '--', relative])).toBe('');
    expect(git(worktree, ['ls-tree', '-r', '--name-only', 'HEAD', '--', relative])).toBe('');
    expect(git(workers[0].worktree, ['ls-tree', '-r', '--name-only', state.cooperation!.canonicalCommit!, '--', relative])).toBe('');
    expect(events).toContainEqual({ event: 'turn_checkpoint', details: {
      workerId: 'researcher', turn: 1,
    } });
    expect(events.some(item => item.event === 'worker_failed' || item.event === 'turn_failed')).toBe(false);
    expect(state.cooperation!.deliveries?.some(delivery => delivery.kind === 'proof' || delivery.kind === 'failure')).toBeFalsy();
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined(); expect(vi.getTimerCount()).toBe(0);
    for (const target of problem.targets) expect(committedSource(workers[0].worktree,
      state.cooperation!.canonicalCommit!, path.join(problem.projectRelative, target.proofPath))).toContain('sorry');
  });

  it('keeps a genuine tool failure after long reasoning as a failure', async () => {
    const { check, events, run } = fixture();
    const started = deferred(), done = deferred<string>();
    let lastError: string | undefined;
    const open = async (): Promise<MathAgentSession> => ({ threadId: 'failed-advisory-thread',
      get lastError() { return lastError; }, close: async () => {}, interrupt: async () => {},
      run: async (_message, _messageId, _workspace, onStarted) => {
        onStarted('failed-turn'); started.resolve(); return done.promise;
      } });
    const completion = run(open, 1); void completion.catch(() => {});
    await started.promise;
    await vi.advanceTimersByTimeAsync(3_600_000);
    lastError = 'math_model_tool_failed'; done.resolve('failed');
    await expect(completion).rejects.toThrow('math_model_tool_failed');
    expect(events.some(item => item.event === 'turn_checkpoint')).toBe(false);
    expect(events).toContainEqual({ event: 'turn_failed', details: {
      workerId: 'researcher', reason: 'math_model_tool_failed',
    } });
    expect(check).not.toHaveBeenCalled(); expect(vi.getTimerCount()).toBe(0);
  });

  it('restores saved progress without reviving legacy time slicing or interrupting new source edits', async () => {
    const { state, workers, problem, check, events, controller, run } = fixture();
    const held = heldAdvisoryTurns(2), first = run(held.open, 1); void first.catch(() => {});
    await held.wait(0, first); held.done[0].resolve('interrupted');
    await expect(first).resolves.toBeUndefined();
    expect(state.workers![1].advisoryCheckpoint?.noProgressStreak).toBe(1);
    const checkpointFile = path.join(directory, 'checkpoint-state.json');
    writeSolverRunState(checkpointFile, state);
    Object.assign(state, readSolverRunState(checkpointFile));
    const second = run(held.open, Infinity); void second.catch(() => {});
    await held.wait(1, second);
    expect(held.open.mock.calls[1][0].threadId).toBe('persistent-backoff-thread');
    await vi.advanceTimersByTimeAsync(3_600_000);
    const source = path.join(workers[1].worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(source, fs.readFileSync(source, 'utf8').replace('theorem add_zero',
      'lemma partial_construction : True := by trivial\ntheorem add_zero'));
    await vi.advanceTimersByTimeAsync(3_600_000);
    expect(held.interrupt).not.toHaveBeenCalled(); expect(held.notify).not.toHaveBeenCalled();
    expect(held.open).toHaveBeenCalledTimes(2);
    expect(events.some(item => item.event === 'cooperative_checkpoint_scheduled')).toBe(false);
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    controller.abort(new Error('fixture_complete'));
    await expect(second).rejects.toThrow('fixture_complete');
    expect(vi.getTimerCount()).toBe(0);
  });

  it('handles a natural unfinished Lead checkpoint and leaves the proof writer unlimited', async () => {
    const { state, workers, check, events, controller, run } = fixture(true);
    const leadStarted = deferred(), proofStarted = deferred();
    const leadDone = deferred<string>(), proofDone = deferred<string>();
    const sessions = new Map<string, { interrupt: ReturnType<typeof vi.fn>; notify: ReturnType<typeof vi.fn> }>();
    const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
      const id = options.environment!.DEEPSCIENTIST_MATH_WORKER_ID!;
      const done = id === 'solver' ? leadDone : proofDone;
      const interrupt = vi.fn(async () => { done.resolve('interrupted'); }), notify = vi.fn(async () => {});
      sessions.set(id, { interrupt, notify });
      return { threadId: `thread-${id}`, interrupt, notify, close: async () => { done.resolve('interrupted'); },
        run: async (_message, _messageId, _workspace, onStarted) => {
          onStarted(`turn-${id}`);
          if (id === 'solver') {
            fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'The first construction is incomplete; a quantifier bridge remains open.\n');
            leadStarted.resolve();
          } else proofStarted.resolve();
          return done.promise;
        } };
    });
    const completion = run(open); void completion.catch(() => {});
    await leadStarted.promise;
    await vi.advanceTimersByTimeAsync(3_600_000);
    expect(sessions.get('solver')!.notify).not.toHaveBeenCalled();
    expect(sessions.get('solver')!.interrupt).not.toHaveBeenCalled();
    leadDone.resolve('interrupted'); await proofStarted.promise;
    expect(state.cooperation!.initialPlanFallback).toBeDefined();
    expect(fs.readFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'utf8')).toContain('a quantifier bridge remains open');
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'goal')).toHaveLength(state.problem.targets.length);
    expect(state.check).toBeUndefined(); expect(check).not.toHaveBeenCalled();
    expect(workers[1].role).toBe('engineer');
    await vi.advanceTimersByTimeAsync(180_000);
    expect(sessions.get('engineer')!.interrupt).not.toHaveBeenCalled();
    expect(sessions.get('engineer')!.notify).not.toHaveBeenCalled();
    expect(open.mock.calls.every(([options]) => options.turnTimeoutMs === undefined)).toBe(true);
    expect(events.some(item => item.event === 'turn_checkpoint')).toBe(true);
    expect(events.some(item => item.event === 'cooperative_checkpoint_scheduled')).toBe(false);
    controller.abort(new Error('fixture_complete'));
    await expect(completion).rejects.toThrow('fixture_complete');
    expect(check).not.toHaveBeenCalled(); expect(state.check).toBeUndefined();
    expect(vi.getTimerCount()).toBe(0);
  });
});
