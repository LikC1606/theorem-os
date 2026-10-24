import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { MathAgentOptions, MathAgentSession } from '../src/runtime/codexSession';
import { readSolverRunState, writeSolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import { runResearchWorkers } from '../src/solver/research';
import { assignmentDeliveryFile, leadPlanDeliveryFile, parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('Lead coordination liveness across checkpoints and restore', () => {
  let directory: string;
  let controllers: AbortController[], running: Promise<unknown>[];

  beforeEach(() => {
    vi.useFakeTimers();
    controllers = []; running = [];
    // Intake is pulsed explicitly; advancing hours must not run the unrelated 200 ms file poller.
    vi.spyOn(CooperativeResearch.prototype, 'start').mockImplementation(() => {});
  });
  afterEach(async () => {
    controllers.forEach(controller => controller.abort());
    await Promise.allSettled(running);
    vi.useRealTimers(); vi.restoreAllMocks();
    if (directory) fs.rmSync(directory, { recursive: true, force: true });
  });

  function fixture() {
    const example = localExample('solver-liveness-recovery-', 'lead');
    directory = example.directory;
    const { problem, workspace } = example;
    const workers = [leadWorker(problem, workspace), peerWorker(example, 'idle-prover', { role: 'prover' }),
      peerWorker(example, 'researcher')];
    const plan = parseCooperationPlan(problem, { tasks: [
      { id: 'investigate', kind: 'research', ownerId: 'researcher', objective: 'Find the precise missing construction.' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}`, ...target, dependsOn: ['investigate'] })),
    ] });
    const check = vi.fn(async () => { throw new Error('fixture_unexpected_proof_acceptance'); });
    const fixture = {
      state: solverState(problem, workspace, { runId: 'liveness-recovery-fixture', phase: 'prepared',
        environmentDigest: mathDigest('offline-liveness-environment'),
        workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
        cooperation: { canonicalCommit: problem.baseCommit,
          tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
          groups: plan.groups.map(group => ({ group, turns: 0 })) } }),
      workers, check,
    };
    const start = (leadModes?: readonly ('planning' | 'coordination')[],
      behavior: { stallLeadInterrupt?: boolean; saveResearchProgress?: boolean } = {}) => {
      const controller = new AbortController(); controllers.push(controller);
      const events: { event: string; details?: Record<string, unknown> }[] = [];
      const messages: { assignment: CooperativeAction; inbox: string[]; threadId: string }[] = [];
      const notifications: { workerId: string; message: string }[] = [];
      const sessionInterrupts: { workerId: string; threadId: string }[] = [], sessionCloses: typeof sessionInterrupts = [];
      const firstLead = deferred(), firstResearch = deferred();
      let cooperation: CooperativeResearch | undefined;
      const next = CooperativeResearch.prototype.next;
      let leadDispatches = 0;
      const capture = vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function(worker, budget) {
        cooperation = this;
        const action = await next.call(this, worker, budget);
        if (action?.kind === 'lead' && leadModes?.length) {
          const mode = leadModes[Math.min(leadDispatches++, leadModes.length - 1)];
          if (mode === 'coordination') action.coordination = true;
          else delete action.coordination;
        }
        return action;
      });
      let sessionsOpened = 0, researchSlices = 0;
      const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
        let active: ReturnType<typeof deferred<string>> | undefined;
        const threadId = options.threadId ?? `${path.basename(options.workspace)}-offline-thread-${++sessionsOpened}`;
        const workerId = options.environment!.DEEPSCIENTIST_MATH_WORKER_ID!;
        return { threadId,
          interrupt: async () => {
            sessionInterrupts.push({ workerId, threadId });
            if (behavior.stallLeadInterrupt && workerId === workers[0].id) return new Promise<void>(() => {});
            // Keep the research peer active without publishing a new Lead input on every slice.
            if (behavior.saveResearchProgress && workerId === workers[2].id && ++researchSlices % 2 === 0)
              fs.appendFileSync(path.join(workers[2].worktree, 'RESEARCH.md'),
                `Construction candidate ${researchSlices / 2}: the draft is saved; its exact remaining case is unproved.\n`);
            active?.resolve('interrupted');
          },
          close: async () => { sessionCloses.push({ workerId, threadId }); active?.resolve('interrupted'); }, notify: async message => {
            notifications.push({ workerId: options.environment!.DEEPSCIENTIST_MATH_WORKER_ID!, message });
          },
          run: async (message, _messageId, _workspace, onStarted) => {
            const parsed = JSON.parse(message) as (typeof messages)[number];
            messages.push({ ...parsed, threadId }); active = deferred<string>();
            onStarted(`offline-turn-${messages.length}`);
            if (parsed.assignment.kind === 'lead') firstLead.resolve();
            else if (parsed.assignment.kind === 'task' && parsed.assignment.task.id === 'investigate') firstResearch.resolve();
            else throw new Error('fixture_unexpected_assignment');
            return active.promise;
          } };
      });
      const modules: SolverModules = { ...directSolverModules, M1: { ...directSolverModules.M1, open },
        M2: { ...directSolverModules.M2, check, checkTask: check },
        M4: { ...directSolverModules.M4, build: (_problem, state, access) => {
          const message = JSON.stringify({ assignment: access.assignment,
            inbox: state.cooperation?.deliveries?.map(delivery => delivery.summary) ?? [] });
          return { instructions: 'Offline coordination fixture.', message, continuationMessage: message,
            scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest } };
        } } };
      const completion = runResearchWorkers({ state: fixture.state, workers, modules,
        access: workerAccess(workers, directory), root: directory, buildFile: path.join(directory, 'unused-build.json'),
        taskText: 'Prove the frozen original targets.', executable: 'offline-fixture', profile: 'offline-fixture',
        signal: controller.signal, deadline: Infinity, maxTurns: Infinity, maxTurnMs: Infinity, maxTotalTokens: 0,
        save: () => {}, emit: (event, details) => events.push({ event, details }) });
      running.push(completion); void completion.catch(() => {});
      const leads = () => messages.filter(message => message.assignment.kind === 'lead');
      const latestLead = () => {
        const message = leads().at(-1)!;
        if (message.assignment.kind !== 'lead') throw new Error('fixture_expected_lead');
        return { ...message, assignment: message.assignment };
      };
      const publish = async (summary: string, needsDecision = false) => {
        const action = messages.findLast(message => message.assignment.kind === 'task')!.assignment;
        if (action.kind !== 'task') throw new Error('fixture_expected_research');
        fs.appendFileSync(path.join(workers[2].worktree, assignmentDeliveryFile(action.assignment)), JSON.stringify({
          kind: 'research', finding: { summary, conclusion: 'inconclusive', needsDecision,
            remainingObligations: ['The exact missing construction still needs a proof.'], evidenceRefs: [] },
        }) + '\n');
        await cooperation!.pulse(workers[2].id);
        expect(fixture.state.cooperation!.deliveries).toContainEqual(expect.objectContaining({
          kind: 'research', summary, producer: workers[2].id }));
      };
      const assess = async (action = latestLead().assignment) => {
        const request = action.capacityRefill!;
        expect(request).toBeDefined();
        fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify({
          kind: 'assessment', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
          assessments: [{ kind: 'capacity', requestId: request.requestId, inputDigest: request.inputDigest,
            outcome: 'no-independent-work', reason: 'The exact missing construction has no independent typed split yet.' }],
        }) + '\n');
        await cooperation!.pulse(workers[0].id);
      };
      const decideChallenges = async (kind: 'plan' | 'handoff' = 'plan', noWork = false) => {
        const action = latestLead().assignment;
        expect(action.challengeIds?.length).toBeGreaterThan(0);
        fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify({
          kind, dispatchNonce: action.planNonce, baseVersion: action.planVersion,
          ...(kind === 'plan' ? { tasks: fixture.state.cooperation!.tasks.map(node => node.task),
            groups: fixture.state.cooperation!.groups!.map(route => route.group) } : {}),
          challengeDecisions: action.challengeIds!.map(id => ({ id, status: 'deferred',
            reason: 'The missing construction still requires a new mathematical input.',
            reopenOn: 'A concrete construction or independently checked smaller obligation becomes available.' })),
          ...(noWork ? { assessments: [{ kind: 'capacity', requestId: action.capacityRefill!.requestId,
            inputDigest: action.capacityRefill!.inputDigest, outcome: 'no-independent-work',
            reason: 'The exact missing construction has no independent typed split yet.' }] } : {}),
        }) + '\n');
        await cooperation!.pulse(workers[0].id);
      };
      const stop = async () => {
        controller.abort(new Error('fixture_complete'));
        await expect(completion).rejects.toThrow('fixture_complete');
        capture.mockRestore();
      };
      return { completion, controller, events, messages, notifications, sessionInterrupts, sessionCloses,
        leads, latestLead, publish, assess, decideChallenges, stop, open,
        current: (action: CooperativeAction) => cooperation!.current(action),
        ready: ({ research = true } = {}) => Promise.race([Promise.all(research
          ? [firstLead.promise, firstResearch.promise] : [firstLead.promise]), completion.then(() => {
          throw new Error('fixture_finished_before_dispatch');
        })]) };
    };
    return { ...fixture, get state() { return fixture.state; }, set state(value) { fixture.state = value; }, start };
  }

  it('enters coordination from a legacy planning thread once, preserves its draft and resumes the saved coordination mode', async () => {
    const fixtureState = fixture(), lead = fixtureState.state.workers![0];
    lead.threadId = 'legacy-mathematical-planning'; lead.sessionRole = 'lead';
    const draft = path.join(lead.worktree, 'RESEARCH.md');
    fs.writeFileSync(draft, 'Saved mathematical construction and precise unresolved inference.\n');
    const run = fixtureState.start(); await run.ready();
    const first = run.latestLead().threadId;
    expect(first).not.toBe('legacy-mathematical-planning');
    expect(lead.previousThreadIds).toContain('legacy-mathematical-planning');
    expect(lead.sessionLeadMode).toBe('coordination');
    expect(fs.readFileSync(draft, 'utf8')).toContain('Saved mathematical construction');
    await vi.advanceTimersByTimeAsync(14 * 60_000);
    expect(run.leads().length).toBeGreaterThanOrEqual(4);
    expect(new Set(run.leads().map(item => item.threadId))).toEqual(new Set([first]));
    expect(new Set(run.leads().map(item => (item.assignment as Extract<CooperativeAction, { kind: 'lead' }>).planNonce)).size)
      .toBe(run.leads().length);
    expect(run.events.filter(item => item.event === 'context_restarted' && item.details?.workerId === lead.id &&
      item.details?.reason === 'responsibility')).toHaveLength(1);
    const saved = path.join(directory, 'coordination-mode-state.json');
    writeSolverRunState(saved, fixtureState.state);
    await run.stop(); fixtureState.state = readSolverRunState(saved);
    expect(fixtureState.state.workers![0].sessionLeadMode).toBe('coordination');
    const paused = fixtureState.state.cooperation!.tasks.find(node => node.task.id === 'investigate')!;
    expect(paused).toMatchObject({ status: 'blocked', feedback: expect.stringContaining('math_research_checkpoint_unchanged') });
    expect(fixtureState.state.cooperation!.researchCheckpoints!.investigate).toMatchObject({ count: 3, paused: true });
    const resumed = fixtureState.start(); await resumed.ready({ research: false });
    expect(resumed.latestLead().threadId).toBe(first);
    expect(resumed.events.some(item => item.event === 'context_restarted' && item.details?.workerId === lead.id &&
      item.details?.reason === 'responsibility')).toBe(false);
    expect(fs.readFileSync(draft, 'utf8')).toContain('Saved mathematical construction');
    expect(paused.status).toBe('blocked');
    expect(resumed.messages.every(message => message.assignment.kind === 'lead')).toBe(true);
    expect(fixtureState.check).not.toHaveBeenCalled();
    await resumed.stop();
  });

  it('changes the Lead thread only when entering or leaving coordination', async () => {
    const fixtureState = fixture(), lead = fixtureState.state.workers![0];
    lead.threadId = 'legacy-planning'; lead.sessionRole = 'lead';
    const run = fixtureState.start(['coordination', 'coordination', 'planning', 'planning', 'coordination']);
    await run.ready();
    await vi.advanceTimersByTimeAsync(10 * 60_000);
    const threads = run.leads().slice(0, 5).map(item => item.threadId);
    expect(threads).toHaveLength(5);
    expect(threads[0]).toBe(threads[1]); expect(threads[2]).toBe(threads[3]);
    expect(new Set(threads).size).toBe(3);
    expect(lead.previousThreadIds).toEqual(['legacy-planning', threads[0], threads[2]]);
    expect(lead.sessionLeadMode).toBe('coordination');
    expect(fixtureState.check).not.toHaveBeenCalled();
    await run.stop();
  });

  it('gives unchanged coordination decisions two, four and at most eight minutes without ending the solving budget', async () => {
    const fixtureState = fixture(), run = fixtureState.start(); await run.ready();
    const scheduled = () => run.events.filter(item => item.event === 'cooperative_checkpoint_scheduled' &&
      item.details?.workerId === fixtureState.workers[0].id).map(item => item.details!);
    await vi.advanceTimersByTimeAsync(90_000);
    const notice = run.notifications.find(item => item.workerId === fixtureState.workers[0].id)!.message;
    expect(notice).toContain('short handoff or assessment protocol');
    expect(notice).not.toContain('complete task graph');
    await vi.advanceTimersByTimeAsync(30_000);
    await vi.advanceTimersByTimeAsync(4 * 60_000);
    await vi.advanceTimersByTimeAsync(8 * 60_000);
    expect(scheduled().slice(0, 4).map(item => item.checkpointAfterMs)).toEqual([120_000, 240_000, 480_000, 480_000]);
    expect(scheduled().at(-1)).toMatchObject({ protected: false, backoffCapped: true });
    expect(fixtureState.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(fixtureState.state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(run.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    expect(fixtureState.check).not.toHaveBeenCalled(); await run.stop();
  });

  it('keeps ordinary Lead planning on its two-minute cadence and reuses a legacy planning thread', async () => {
    const fixtureState = fixture(), lead = fixtureState.state.workers![0];
    lead.threadId = 'legacy-planning'; lead.sessionRole = 'lead';
    const run = fixtureState.start(['planning']); await run.ready();
    await vi.advanceTimersByTimeAsync(6 * 60_000);
    expect(run.leads()).toHaveLength(4);
    expect(new Set(run.leads().map(item => item.threadId))).toEqual(new Set(['legacy-planning']));
    expect(lead.previousThreadIds ?? []).toEqual([]); expect(lead.sessionLeadMode).toBe('planning');
    const slices = run.events.filter(item => item.event === 'cooperative_checkpoint_scheduled' &&
      item.details?.workerId === lead.id).map(item => item.details!.checkpointAfterMs);
    expect(slices).toEqual([120_000, 120_000, 120_000, 120_000]);
    expect(fixtureState.check).not.toHaveBeenCalled(); await run.stop();
  });

  it('keeps coordinating for hours without inventing an assessment, then reconsiders evidence arriving before an acknowledgement', async () => {
    const fixtureState = fixture(), run = fixtureState.start(undefined, { saveResearchProgress: true }); await run.ready();
    const original = structuredClone(fixtureState.state.cooperation!.lastCapacityRefill!);
    expect(original).toMatchObject({ status: 'requested', workerIds: ['idle-prover'] });
    await vi.advanceTimersByTimeAsync(3 * 60 * 60_000);
    expect(run.leads().length).toBeGreaterThanOrEqual(24);
    const nonces = run.leads().map(message => (message.assignment as Extract<CooperativeAction, { kind: 'lead' }>).planNonce);
    expect(new Set(nonces).size).toBe(nonces.length);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({
      requestId: original.requestId, inputDigest: original.inputDigest, requestedAt: original.requestedAt, status: 'requested' });
    expect(run.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    expect(fixtureState.state.cooperation!.tasks.find(node => node.task.id === 'investigate')!.status).toBe('running');
    expect(fixtureState.state.cooperation!.researchCheckpoints?.investigate?.paused).not.toBe(true);

    const summary = 'A new scoped negative result identifies the exact missing construction.';
    await run.publish(summary);
    await run.assess();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({
      requestId: original.requestId, status: 'assessed', outcome: 'no-independent-work' });
    // The old acknowledgement is valid only for its frozen inputs; the new finding still needs a decision.
    await vi.advanceTimersByTimeAsync(8 * 60_000);
    expect(run.latestLead().inbox).toContain(summary);
    expect(run.latestLead().assignment.capacityRefill!.inputDigest).not.toBe(original.inputDigest);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    await run.assess();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'assessed', outcome: 'no-independent-work' });
    expect(fixtureState.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(run.open.mock.calls.every(([options]) => options.turnTimeoutMs === undefined)).toBe(true);
    expect(fixtureState.check).not.toHaveBeenCalled(); expect(fixtureState.state.check).toBeUndefined();
    expect(fixtureState.state.cooperation!.tasks.every(node => !['integrated', 'conditional'].includes(node.status))).toBe(true);
    await run.stop();
  });

  it('routes a new needs-decision finding to the next Lead slice instead of letting a short acknowledgement swallow it', async () => {
    const fixtureState = fixture(), run = fixtureState.start(undefined, { saveResearchProgress: true }); await run.ready();
    await vi.advanceTimersByTimeAsync(4 * 120_000);
    const superseded = run.latestLead().assignment;
    const summary = 'The new scoped obstruction requires an explicit route decision.';
    await run.publish(summary, true);
    expect(run.current(superseded)).toBe(false);
    await run.assess(superseded);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    expect(run.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    expect(fixtureState.state.cooperation!.planPublication).toBeUndefined();
    await vi.advanceTimersByTimeAsync(8 * 60_000);
    expect(run.latestLead().assignment.planNonce).not.toBe(superseded.planNonce);
    expect(run.latestLead().assignment.challengeIds?.length).toBeGreaterThan(0);
    expect(run.latestLead().assignment.capacityRefill!.inputDigest).not.toBe(superseded.capacityRefill!.inputDigest);
    expect(run.latestLead().inbox).toContain(summary);
    await run.decideChallenges();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    expect(fixtureState.state.cooperation!.challengeDecisions).toContainEqual(expect.objectContaining({ status: 'deferred' }));
    expect(fixtureState.state.cooperation!.lastLeadInputDigest).toBeTruthy();
    await vi.advanceTimersByTimeAsync(8 * 60_000);
    expect(run.latestLead().assignment.challengeIds ?? []).toEqual([]);
    await run.assess();
    const settledTurns = run.leads().length;
    await vi.advanceTimersByTimeAsync(60 * 60_000);
    expect(run.leads()).toHaveLength(settledTurns);
    expect(fixtureState.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(fixtureState.check).not.toHaveBeenCalled(); expect(fixtureState.state.check).toBeUndefined();
    await run.stop();
  });

  it('settles a short challenge decision with an explicit no-work reason, waits, then wakes for new evidence', async () => {
    const fixtureState = fixture(), run = fixtureState.start(undefined, { saveResearchProgress: true }); await run.ready();
    const superseded = run.latestLead().assignment;
    await run.publish('The scoped obstruction needs an explicit decision.', true);
    expect(run.current(superseded)).toBe(false);
    await vi.advanceTimersByTimeAsync(8 * 60_000);
    expect(run.latestLead().assignment.planNonce).not.toBe(superseded.planNonce);
    expect(run.latestLead().assignment.challengeIds?.length).toBeGreaterThan(0);
    const version = fixtureState.state.cooperation!.planVersion;
    await run.decideChallenges('handoff', true);
    expect(fixtureState.state.cooperation!.planVersion).toBe(version);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'assessed', outcome: 'no-independent-work' });
    const settledTurns = run.leads().length;
    await vi.advanceTimersByTimeAsync(60 * 60_000);
    expect(run.leads()).toHaveLength(settledTurns);
    const finding = 'A new finite construction changes the available mathematical input.';
    await run.publish(finding);
    await vi.advanceTimersByTimeAsync(120_000);
    expect(run.leads().length).toBeGreaterThan(settledTurns);
    expect(run.latestLead().inbox).toContain(finding);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    expect(fixtureState.check).not.toHaveBeenCalled();
    await run.stop();
  });

  it('closes a superseded Lead after ten seconds when interrupt stalls and dispatches the saved inbox without losing its draft', async () => {
    const fixtureState = fixture(), run = fixtureState.start(undefined, { stallLeadInterrupt: true });
    await run.ready();
    const old = run.latestLead(), draft = path.join(fixtureState.workers[0].worktree, 'RESEARCH.md');
    fs.writeFileSync(draft, 'Saved mathematical construction with the precise unresolved inference.\n');
    await run.publish('A new scoped obstruction requires the next explicit coordination decision.', true);
    expect(run.current(old.assignment)).toBe(false);
    expect(run.sessionInterrupts).toContainEqual({ workerId: fixtureState.workers[0].id, threadId: old.threadId });
    await vi.advanceTimersByTimeAsync(9_999);
    expect(run.latestLead().assignment.planNonce).toBe(old.assignment.planNonce);
    expect(run.sessionCloses).not.toContainEqual({ workerId: fixtureState.workers[0].id, threadId: old.threadId });
    await vi.advanceTimersByTimeAsync(1);
    expect(run.sessionCloses).toContainEqual({ workerId: fixtureState.workers[0].id, threadId: old.threadId });
    expect(run.latestLead().assignment.planNonce).not.toBe(old.assignment.planNonce);
    expect(run.latestLead().assignment.challengeIds?.length).toBeGreaterThan(0);
    expect(fs.readFileSync(draft, 'utf8')).toContain('Saved mathematical construction with the precise unresolved inference.');
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    expect(run.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    expect(fixtureState.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(fixtureState.check).not.toHaveBeenCalled(); expect(fixtureState.state.check).toBeUndefined();
    expect(fixtureState.state.cooperation!.tasks.every(node => !['integrated', 'conditional'].includes(node.status))).toBe(true);
    await run.stop();
  });

  it.each([false, true])('restores a pending refill without losing a newly arrived finding (%s)', async newFinding => {
    const fixtureState = fixture(), first = fixtureState.start(); await first.ready();
    await vi.advanceTimersByTimeAsync(4 * 120_000);
    const original = structuredClone(fixtureState.state.cooperation!.lastCapacityRefill!);
    expect(original.status).toBe('requested');
    const summary = 'Saved external evidence remains unassessed when the process stops.';
    if (newFinding) await first.publish(summary);
    const saved = path.join(directory, 'pending-refill-state.json');
    writeSolverRunState(saved, fixtureState.state);
    await first.stop();
    fixtureState.state = readSolverRunState(saved);
    const resumed = fixtureState.start(); await resumed.ready();
    expect(fixtureState.state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(resumed.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
    const current = resumed.latestLead().assignment.capacityRefill!;
    if (newFinding) {
      expect(resumed.latestLead().inbox).toContain(summary);
      expect(current.inputDigest).not.toBe(original.inputDigest);
    } else {
      expect(current).toMatchObject({ requestId: original.requestId, inputDigest: original.inputDigest,
        requestedAt: original.requestedAt });
    }
    await resumed.assess();
    expect(fixtureState.state.cooperation!.lastCapacityRefill!.status).toBe('assessed');
    expect(fixtureState.state.tokenBudget).toMatchObject({ maxTotalTokens: 0, status: 'unlimited' });
    expect(fixtureState.check).not.toHaveBeenCalled(); expect(fixtureState.state.check).toBeUndefined();
    await resumed.stop();
  });
});
