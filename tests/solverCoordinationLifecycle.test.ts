import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { advisoryCheckpointScope, runResearchWorkers } from '../src/solver/research';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

type LeadAction = Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>;

describe('bounded coordination completion in the worker loop', () => {
  let directory: string;
  let controllers: AbortController[], running: Promise<unknown>[], releases: (() => void)[];

  beforeEach(() => {
    vi.useFakeTimers(); controllers = []; running = []; releases = [];
    // Publish through explicit pulses; the ordinary worker loop and its timers remain live.
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
  });
  afterEach(async () => {
    controllers.forEach(controller => controller.abort()); releases.forEach(release => release());
    await Promise.allSettled(running);
    vi.useRealTimers(); vi.restoreAllMocks();
    if (directory) fs.rmSync(directory, { recursive: true, force: true });
  });

  function fixture(options: { challenges?: number; initialStreak?: number; stalled?: boolean } = {}) {
    const example = localExample('solver-coordination-lifecycle-', 'lead');
    directory = example.directory;
    const { problem, workspace } = example;
    const workers = [leadWorker(problem, workspace), peerWorker(example, 'researcher')];
    const plan = parseCooperationPlan(problem, { tasks: [
      ...problem.targets.map((target, index) => ({ id: `goal_${index + 1}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, ...target, status: options.challenges === 0 ? 'active' : 'paused' })),
      { id: 'question', kind: 'research', objective: 'Find the exact remaining construction.', status: 'paused' },
    ] });
    const question = plan.tasks.find(task => task.id === 'question')!;
    const state = solverState(problem, workspace, { runId: 'coordination-lifecycle-fixture', phase: 'prepared',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: task.id === question.id ? 'completed' :
          options.challenges === 0 ? 'blocked' : 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })),
        deliveries: Array.from({ length: options.challenges ?? 4 }, (_, index) => {
          const finding = JSON.stringify({ needsDecision: true, conclusion: 'inconclusive',
            summary: `Construction ${index} needs its exact quantified argument.` });
          return { id: `challenge-${index}`, producer: workers[1].id, taskId: question.id, taskDigest: taskVersion(question),
            kind: 'research' as const, status: 'advisory' as const, finding, findingDigest: mathDigest(finding),
            summary: `Review construction ${index}.`, statement: '', premises: [], dependencies: [],
            remainingObligations: [], evidenceRefs: [], createdAt: index + 1 };
        }) } });
    let cooperation: CooperativeResearch | undefined, activeDispatch: LeadAction | undefined, firstActivation = true;
    const activate = CooperativeResearch.prototype.activate;
    vi.spyOn(CooperativeResearch.prototype, 'activate').mockImplementation(function (this: CooperativeResearch, ...args) {
      cooperation = this;
      if (args[1].kind === 'lead') activeDispatch = args[1];
      if (firstActivation && options.initialStreak !== undefined) {
        state.workers![0].advisoryCheckpoint = { scope: advisoryCheckpointScope(args[1])!, noProgressStreak: options.initialStreak };
        firstActivation = false;
      }
      return activate.apply(this, args);
    });
    const controller = new AbortController(); controllers.push(controller);
    const events: { event: string; details?: Record<string, unknown> }[] = [];
    const saved: { decisions: number; offsets: Record<string, number> | undefined }[] = [];
    const check = vi.fn(async () => { throw new Error('fixture_unexpected_proof_acceptance'); });
    const started = Array.from({ length: 4 }, () => deferred());
    const done = Array.from({ length: 4 }, () => deferred<string>()), teardown = deferred();
    releases.push(() => { teardown.resolve(); done.forEach(turn => turn.resolve('interrupted')); });
    const actions: LeadAction[] = [], turnsAt: number[] = [];
    let active: ReturnType<typeof deferred<string>> | undefined, lastError: string | undefined;
    const interrupt = vi.fn(async () => { if (!options.stalled) active?.resolve('interrupted'); });
    const close = vi.fn(async () => {
      if (options.stalled && actions.length === 1) {
        lastError = 'math_codex_transport_closed'; active?.reject(new Error(lastError));
        await teardown.promise;
      } else active?.resolve('interrupted');
    });
    const open = vi.fn(async (access: MathAgentOptions): Promise<MathAgentSession> => ({
      threadId: access.threadId ?? 'coordination-thread', interrupt, close, notify: async () => {},
      get lastError() { return lastError; },
      run: async (message, _messageId, _worktree, onStarted) => {
        lastError = undefined;
        const dispatched = JSON.parse(message) as CooperativeAction;
        if (dispatched.kind !== 'lead' || !dispatched.coordination || !activeDispatch)
          throw new Error('fixture_expected_coordination:' + JSON.stringify(dispatched));
        const action = activeDispatch;
        expect(dispatched.planNonce).toBe(action.planNonce);
        const index = actions.length;
        if (index >= started.length) throw new Error('fixture_unexpected_coordination_turn');
        actions.push(action); turnsAt.push(Date.now()); active = done[index];
        onStarted(`coordination-turn-${index}`); started[index].resolve(); return done[index].promise;
      },
    }));
    const modules: SolverModules = { ...directSolverModules, M1: { ...directSolverModules.M1, open },
      M2: { ...directSolverModules.M2, check, checkTask: check },
      M4: { ...directSolverModules.M4, build: (_problem, _view, access) => ({ instructions: 'Offline coordination fixture.',
        message: JSON.stringify(access.assignment), continuationMessage: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest } }) } };
    const completion = runResearchWorkers({ state, workers, modules, access: workerAccess(workers, directory), root: directory,
      buildFile: path.join(directory, 'build.json'), taskText: 'Resolve only the current bounded coordination batch.',
      executable: 'offline-fixture', profile: 'offline-fixture', signal: controller.signal,
      deadline: Infinity, maxTurnMs: Infinity, maxTurns: Infinity, maxTotalTokens: 0,
      save: () => saved.push({ decisions: state.cooperation!.challengeDecisions?.length ?? 0,
        offsets: structuredClone(state.cooperation!.cursors) }),
      emit: (event, details) => events.push({ event, details }) });
    running.push(completion); void completion.catch(() => {});
    const wait = (turn: number) => Promise.race([started[turn].promise,
      completion.then(() => { throw new Error('fixture_finished_before_coordination_turn:' + turn); })]);
    const append = async (action: LeadAction, response: unknown) => {
      fs.appendFileSync(path.join(workspace, leadPlanDeliveryFile(action)!), JSON.stringify(response) + '\n');
      await cooperation!.pulse(workers[0].id);
    };
    const decide = (action: LeadAction) => ({ kind: 'handoff', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      challengeDecisions: action.challengeIds!.map(id => ({ id, status: 'deferred',
        reason: 'The exact quantified construction is still missing.', reopenOn: 'A checked construction supplies the missing inference.' })) });
    const schedules = () => events.filter(item => item.event === 'cooperative_checkpoint_scheduled');
    const checkpoints = () => events.filter(item => item.event === 'cooperative_checkpoint_saved');
    return { state, problem, workspace, workers, events, saved, check, open, interrupt, close, done, teardown, actions, turnsAt,
      wait, append, decide, schedules, checkpoints, options: open.mock.calls,
      pulse: () => cooperation!.pulse(workers[0].id),
      addChallenge: () => {
        const finding = JSON.stringify({ needsDecision: true, summary: 'A later construction has an unreviewed exact inference.' });
        state.cooperation!.deliveries!.push({ id: 'later-challenge', producer: workers[1].id, taskId: question.id,
          taskDigest: taskVersion(question), kind: 'research', status: 'advisory', finding, findingDigest: mathDigest(finding),
          summary: 'Review the later exact construction.', statement: '', premises: [], dependencies: [],
          remainingObligations: [], evidenceRefs: [], createdAt: Date.now() });
        // Materialize the arrival exactly as worker intake does after appending its accepted record.
        (cooperation as unknown as { changed: () => void }).changed();
      },
      result: (action: LeadAction) => cooperation!.coordinationResult(action) };
  }

  it('ends an accepted batch within one poll while compaction is active and starts the next inbox batch', async () => {
    const current = fixture(); await current.wait(0);
    const action = current.actions[0], response = current.decide(action);
    expect(action.challengeIds).toHaveLength(2);
    current.options[0][0].onActivity!({ event: 'item_started', itemType: 'contextCompaction' });
    await current.append(action, response);
    await current.append(action, response);
    expect(current.result(action)).toEqual({ progress: true });
    expect(current.state.cooperation!.challengeDecisions).toHaveLength(2);
    const cursor = `${current.workers[0].id}/${leadPlanDeliveryFile(action)}`;
    expect(current.saved.some(item => item.decisions === 2 && (item.offsets?.[cursor] ?? 0) > 0)).toBe(true);
    await vi.advanceTimersByTimeAsync(4_999);
    expect(current.interrupt).not.toHaveBeenCalled();
    await vi.advanceTimersByTimeAsync(1); await current.wait(1);
    expect(current.interrupt).toHaveBeenCalledOnce();
    expect(current.close).not.toHaveBeenCalled();
    expect(current.turnsAt[1] - current.turnsAt[0]).toBe(5_000);
    expect(current.actions[1].planNonce).not.toBe(action.planNonce);
    expect(current.actions[1].challengeIds).not.toEqual(action.challengeIds);
    expect(pendingResearchChallenges(current.state.cooperation!)).toHaveLength(2);
    expect(current.events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(current.events.filter(item => item.event === 'lead_coordination_completed')).toHaveLength(1);
    expect(current.check).not.toHaveBeenCalled();
  });

  it('closes a writer that ignores the accepted-decision interrupt and waits for teardown before opening another', async () => {
    const current = fixture({ stalled: true }); await current.wait(0);
    const action = current.actions[0], response = current.decide(action);
    await current.append(action, response);
    await vi.advanceTimersByTimeAsync(5_000);
    expect(current.interrupt).toHaveBeenCalledOnce();
    await vi.advanceTimersByTimeAsync(9_999);
    expect(current.close).not.toHaveBeenCalled();
    await vi.advanceTimersByTimeAsync(1);
    expect(current.close).toHaveBeenCalledOnce();
    expect(current.actions).toHaveLength(1); expect(current.open).toHaveBeenCalledOnce();
    await vi.advanceTimersByTimeAsync(5_000);
    expect(current.actions).toHaveLength(1); expect(current.open).toHaveBeenCalledOnce();
    expect(current.state.cooperation!.challengeDecisions).toHaveLength(2);
    current.teardown.resolve(); await current.wait(1);
    expect(current.open).toHaveBeenCalledTimes(2);
    expect(current.state.cooperation!.challengeDecisions).toHaveLength(2);
    expect(current.events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(current.events.filter(item => item.event === 'turn_failed' || item.event === 'plan_rejected')).toEqual([]);
    expect(current.check).not.toHaveBeenCalled();
  });

  it('counts an accepted short decision without source or notes changes and resets the next scheduling slice', async () => {
    const current = fixture({ initialStreak: 2 }); await current.wait(0);
    const notesFile = path.join(current.workspace, 'RESEARCH.md');
    const notes = fs.existsSync(notesFile) ? fs.readFileSync(notesFile) : undefined;
    const source = fs.readFileSync(path.join(current.workspace, current.problem.projectRelative, 'Submission.lean'));
    expect(current.schedules()[0].details).toMatchObject({ noProgressStreak: 2, checkpointAfterMs: 480_000 });
    await current.append(current.actions[0], current.decide(current.actions[0]));
    await vi.advanceTimersByTimeAsync(5_000); await current.wait(1);
    expect(current.checkpoints()).toContainEqual({ event: 'cooperative_checkpoint_saved',
      details: expect.objectContaining({ workerId: current.workers[0].id, progress: true, noProgressStreak: 0 }) });
    expect(current.schedules()[1].details).toMatchObject({ noProgressStreak: 0, checkpointAfterMs: 120_000 });
    expect(fs.existsSync(notesFile) ? fs.readFileSync(notesFile) : undefined).toEqual(notes);
    expect(fs.readFileSync(path.join(current.workspace, current.problem.projectRelative, 'Submission.lean'))).toEqual(source);
    expect(current.check).not.toHaveBeenCalled();
  });

  it('does not reset coordination backoff for rejected input, new nonces, saved notes or a completed model response', async () => {
    const current = fixture({ initialStreak: 1 }); await current.wait(0);
    const first = current.actions[0];
    await current.append(first, { ...current.decide(first), dispatchNonce: 'stale-nonce' });
    fs.writeFileSync(path.join(current.workspace, 'RESEARCH.md'), 'The missing quantified inference remains unresolved; these are saved notes.\n');
    expect(current.result(first)).toBeUndefined();
    await vi.advanceTimersByTimeAsync(5_000);
    expect(current.interrupt).not.toHaveBeenCalled();
    current.done[0].resolve('completed'); await current.wait(1);
    expect(current.actions[1].planNonce).not.toBe(first.planNonce);
    expect(current.schedules()[1].details).toMatchObject({ noProgressStreak: 1, checkpointAfterMs: 240_000 });
    fs.appendFileSync(path.join(current.workspace, 'RESEARCH.md'), '\nAnother saved observation does not resolve the decision.\n');
    await current.append(current.actions[1], current.decide(first));
    expect(current.result(current.actions[1])).toBeUndefined();
    await vi.advanceTimersByTimeAsync(240_000); await current.wait(2);
    expect(current.checkpoints()).toContainEqual({ event: 'cooperative_checkpoint_saved',
      details: expect.objectContaining({ progress: false, noProgressStreak: 2 }) });
    expect(current.schedules()[2].details).toMatchObject({ noProgressStreak: 2, checkpointAfterMs: 480_000 });
    expect(current.events.some(item => item.event === 'lead_coordination_completed')).toBe(false);
    expect(current.state.cooperation!.challengeDecisions).toBeUndefined();
    expect(current.check).not.toHaveBeenCalled();
  });

  it('does not count unchanged graph publications or their duplicate lines as coordination progress', async () => {
    const current = fixture({ challenges: 0, initialStreak: 1 }); await current.wait(0);
    const publishUnchanged = async (action: LeadAction) => {
      const response = { kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
        tasks: current.state.cooperation!.tasks.map(node => node.task),
        groups: current.state.cooperation!.groups!.map(route => route.group) };
      await current.append(action, response); await current.append(action, response);
    };
    const first = current.actions[0];
    expect(first.capacityRefill).toBeDefined();
    await publishUnchanged(first);
    expect(current.result(first)).toEqual({ progress: false });
    await vi.advanceTimersByTimeAsync(5_000); await current.wait(1);
    expect(current.checkpoints()[0].details).toMatchObject({ progress: false, noProgressStreak: 2 });
    expect(current.schedules()[1].details).toMatchObject({ noProgressStreak: 2, checkpointAfterMs: 480_000 });
    expect(current.actions[1].planNonce).not.toBe(first.planNonce);
    await publishUnchanged(current.actions[1]);
    await vi.advanceTimersByTimeAsync(5_000); await current.wait(2);
    expect(current.checkpoints()[1].details).toMatchObject({ progress: false, noProgressStreak: 3 });
    expect(current.state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(current.events.filter(item => item.event === 'plan_published')).toHaveLength(2);
    expect(current.check).not.toHaveBeenCalled();
  });

  it('retains accepted assessment progress when new inbox input supersedes its writer before the completion poll', async () => {
    const current = fixture({ challenges: 0, initialStreak: 2 }); await current.wait(0);
    const first = current.actions[0];
    const requests = [['capacity', first.capacityRefill], ['stagnation', first.stagnationRecovery]] as const;
    await current.append(first, { kind: 'assessment', dispatchNonce: first.planNonce, baseVersion: first.planVersion,
      assessments: requests.flatMap(([kind, request]) => request ? [{ kind, requestId: request.requestId,
        inputDigest: request.inputDigest, outcome: 'no-independent-work',
        reason: 'The quantified construction is missing until a checked exact construction arrives.' }] : []) });
    expect(current.result(first)).toEqual({ progress: true });
    current.addChallenge(); await current.pulse();
    await current.wait(1);
    expect(current.turnsAt[1] - current.turnsAt[0]).toBeLessThan(5_000);
    expect(current.actions[1].challengeIds).toHaveLength(1);
    expect(current.schedules()[1].details).toMatchObject({ noProgressStreak: 0, checkpointAfterMs: 120_000 });
    expect(current.state.workers![0].advisoryCheckpoint!.noProgressStreak).toBe(0);
    expect(current.events.some(item => item.event === 'assignment_superseded')).toBe(true);
    expect(current.check).not.toHaveBeenCalled();
  });
});
