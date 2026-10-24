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
    const start = () => {
      const controller = new AbortController(); controllers.push(controller);
      const events: { event: string; details?: Record<string, unknown> }[] = [];
      const messages: { assignment: CooperativeAction; inbox: string[] }[] = [];
      const firstLead = deferred(), firstResearch = deferred();
      let cooperation: CooperativeResearch | undefined;
      const next = CooperativeResearch.prototype.next;
      const capture = vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(function(worker, budget) {
        cooperation = this;
        return next.call(this, worker, budget);
      });
      const open = vi.fn(async (options: MathAgentOptions): Promise<MathAgentSession> => {
        let active: ReturnType<typeof deferred<string>> | undefined;
        return { threadId: options.threadId ?? `${path.basename(options.workspace)}-offline-thread`,
          interrupt: async () => { active?.resolve('interrupted'); },
          close: async () => { active?.resolve('interrupted'); }, notify: async () => {},
          run: async (message, _messageId, _workspace, onStarted) => {
            const parsed = JSON.parse(message) as (typeof messages)[number];
            messages.push(parsed); active = deferred<string>();
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
      const assess = async () => {
        const action = latestLead().assignment, request = action.capacityRefill!;
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
      return { completion, controller, events, messages, leads, latestLead, publish, assess, decideChallenges, stop, open,
        ready: () => Promise.race([Promise.all([firstLead.promise, firstResearch.promise]), completion.then(() => {
          throw new Error('fixture_finished_before_dispatch');
        })]) };
    };
    return { ...fixture, get state() { return fixture.state; }, set state(value) { fixture.state = value; }, start };
  }

  it('keeps coordinating for hours without inventing an assessment, then reconsiders evidence arriving before an acknowledgement', async () => {
    const fixtureState = fixture(), run = fixtureState.start(); await run.ready();
    const original = structuredClone(fixtureState.state.cooperation!.lastCapacityRefill!);
    expect(original).toMatchObject({ status: 'requested', workerIds: ['idle-prover'] });
    await vi.advanceTimersByTimeAsync(3 * 60 * 60_000);
    expect(run.leads().length).toBeGreaterThanOrEqual(90);
    const nonces = run.leads().map(message => (message.assignment as Extract<CooperativeAction, { kind: 'lead' }>).planNonce);
    expect(new Set(nonces).size).toBe(nonces.length);
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({
      requestId: original.requestId, inputDigest: original.inputDigest, requestedAt: original.requestedAt, status: 'requested' });
    expect(run.events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);

    const summary = 'A new scoped negative result identifies the exact missing construction.';
    await run.publish(summary);
    await run.assess();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({
      requestId: original.requestId, status: 'assessed', outcome: 'no-independent-work' });
    // The old acknowledgement is valid only for its frozen inputs; the new finding still needs a decision.
    await vi.advanceTimersByTimeAsync(120_000);
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
    const fixtureState = fixture(), run = fixtureState.start(); await run.ready();
    await vi.advanceTimersByTimeAsync(4 * 120_000);
    const before = structuredClone(fixtureState.state.cooperation!.lastCapacityRefill!);
    const summary = 'The new scoped obstruction requires an explicit route decision.';
    await run.publish(summary, true);
    await run.assess();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({
      requestId: before.requestId, status: 'requested' });
    expect(run.events).toContainEqual(expect.objectContaining({ event: 'plan_publication_rejected',
      details: expect.objectContaining({ reason: 'math_plan_assessment_inbox_unresolved' }) }));
    await vi.advanceTimersByTimeAsync(120_000);
    expect(run.latestLead().inbox).toContain(summary);
    await run.decideChallenges();
    expect(fixtureState.state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
    expect(fixtureState.state.cooperation!.challengeDecisions).toContainEqual(expect.objectContaining({ status: 'deferred' }));
    expect(fixtureState.state.cooperation!.lastLeadInputDigest).toBeTruthy();
    await vi.advanceTimersByTimeAsync(120_000);
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
    const fixtureState = fixture(), run = fixtureState.start(); await run.ready();
    await run.publish('The scoped obstruction needs an explicit decision.', true);
    await vi.advanceTimersByTimeAsync(120_000);
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
