import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import * as contextCompiler from '../src/solver/contextCompiler';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('automatic typed proof capacity refill', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let pending: Promise<unknown>[], events: { event: string; details?: Record<string, unknown> }[];
  let busyInterrupt: ReturnType<typeof vi.fn>, model: ReturnType<typeof vi.fn>;
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const track = <T,>(promise: Promise<T>) => { pending.push(promise); void promise.catch(() => {}); return promise; };
  const create = () => {
    const controller = new AbortController();
    const instance = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }),
      modules: { ...directSolverModules, M1: { ...directSolverModules.M1, open: model } } });
    instances.push({ cooperative: instance, controller });
    return instance;
  };
  const plan = () => ({ tasks: state.cooperation!.tasks.map(item => item.task),
    groups: state.cooperation!.groups!.map(item => item.group) });
  const refresh = () => (cooperative as any).changed();
  const nextLead = (dispatchBudget = budget) => track(cooperative.next(workers[0], dispatchBudget));
  const planning = (action: CooperativeAction | undefined) => {
    if (action?.kind !== 'lead') throw new Error('fixture_expected_lead');
    return action;
  };
  const requestFor = (action: CooperativeAction | undefined) => {
    const request = planning(action).capacityRefill;
    expect(request).toBeDefined();
    return request!;
  };
  const contextFor = (action: CooperativeAction, worker = workers[0]) => directSolverModules.M4.build(problem,
    { ...state, cooperation: cooperative.contextState(action, worker),
      workers: workers.map(peer => ({ id: peer.id, role: peer.role, worktree: peer.worktree, phase: 'running', turns: 0 })) },
    { root: directory, worktree: worker.worktree, retrievalRoot: directory, environment: {},
      taskText: 'Prove the original targets using useful independently checked steps.', assignment: action,
      maxOptionalContextBytes: 0 });
  const archivedRequest = () => {
    const { requestId, inputDigest, workerIds, requestedAt } = state.cooperation!.lastCapacityRefill!;
    return { requestId, inputDigest, workerIds: [...workerIds], requestedAt };
  };
  const waitsForInput = async (dispatchBudget = budget) => {
    let settled = false;
    const waiting = nextLead(dispatchBudget);
    void waiting.then(() => { settled = true; }, () => {});
    for (let index = 0; index < 6; index++) { refresh(); await Promise.resolve(); }
    expect(settled).toBe(false);
    return { waiting, settled: () => settled };
  };
  const assess = async (action: CooperativeAction) => {
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(plan()) + '\n```\n');
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(state.cooperation!.lastCapacityRefill?.status).toBe('assessed');
  };
  const noIndependentWork = (action: CooperativeAction) => {
    const lead = planning(action), request = requestFor(action);
    return { kind: 'assessment', dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
      summary: 'The unresolved mathematical frontier does not currently split into independent typed work.',
      assessments: [{ kind: 'capacity', requestId: request.requestId, inputDigest: request.inputDigest,
        outcome: 'no-independent-work', reason: 'The exact classification argument is still needed.' }] };
  };
  const publish = (kind: 'research' | 'progress', summary: string) => (cooperative as any).record(workers[2], node('busy_helper').task,
    kind, 'advisory', summary, kind === 'research' ? { finding: summary, findingDigest: mathDigest(summary) } : {});
  const newLemma = (): TaskRecord => {
    const task: CooperativeTask = { id: 'new_helper', kind: 'lemma', ownerId: workers[1].id,
      objective: 'Prove an independent newly identified step.', proofPath: 'Submission.lean', theoremName: 'Tutorial.new_helper',
      type: 'True', dependsOn: [], revision: 0 };
    return { task, status: 'pending', attempts: 0 };
  };
  const moveBusyTaskToEngineer = () => {
    const busy = node('busy_helper');
    cooperative.deactivate(workers[2]);
    busy.assignment!.workerId = workers[3].id;
    cooperative.activate(workers[3], { kind: 'task', task: busy.task, assignment: busy.assignment! },
      busyInterrupt, async () => {});
  };

  beforeEach(() => {
    const example = localExample('solver-capacity-refill-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'idle-prover', { role: 'prover' }),
      peerWorker(example, 'busy-prover', { role: 'prover' }), peerWorker(example, 'engineer', { role: 'engineer' })];
    const initial = parseCooperationPlan(problem, { tasks: [
      { id: 'busy_helper', kind: 'lemma', ownerId: workers[2].id, objective: 'Prove the current original-goal frontier.',
        proofPath: 'Submission.lean', theoremName: 'Tutorial.busy_helper', type: 'True' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
        dependsOn: ['busy_helper'] })),
    ], groups: [{ id: 'main', objective: 'Prove the original targets.', engineerId: workers[3].id, maxConcurrent: 3 }] });
    state = solverState(problem, example.workspace, { runId: 'capacity-refill-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit, tasks: initial.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: initial.groups.map(group => ({ group, turns: 0 })) } });
    pending = []; events = []; instances = [];
    model = vi.fn(() => { throw new Error('fixture_real_models_forbidden'); });
    cooperative = create();
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    const busy = node('busy_helper');
    busy.status = 'running';
    busy.assignment = { taskId: busy.task.id, taskDigest: taskVersion(busy.task), workerId: workers[2].id,
      seedCommit: problem.baseCommit, assignmentId: 'long-running-frontier' };
    busyInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[2], { kind: 'task', task: busy.task, assignment: busy.assignment }, busyInterrupt, async () => {});
  });
  afterEach(async () => {
    for (const instance of instances) instance.controller.abort();
    await Promise.allSettled(pending);
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    expect(model).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('requests one Lead decision for an idle Prover while another original-goal task keeps running', async () => {
    const assignment = node('busy_helper').assignment;
    const action = await nextLead();
    expect(action).toMatchObject({ kind: 'lead', planNonce: expect.any(String) });
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested', workerIds: ['idle-prover'] });
    expect(node('busy_helper').assignment).toBe(assignment);
    expect(node('busy_helper').status).toBe('running');
    expect(busyInterrupt).not.toHaveBeenCalled();
    cooperative.activate(workers[0], action!, async () => {}, async () => {});
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  it('delivers the actual capacity request through default M4 as mandatory assignment context with no optional allowance', async () => {
    const action = planning(await nextLead()), request = requestFor(action);
    expect(request).toEqual(archivedRequest());
    const compile = vi.spyOn(contextCompiler, 'compileTaskContext');
    const context = contextFor(action);
    const section = compile.mock.calls.at(-1)![0].mandatory?.find(item => item.id === 'capacity-refill');
    expect(section).toMatchObject({ kind: 'assignment' });
    expect(section!.text).toContain(JSON.stringify(request));
    expect(section!.text).toContain('these Provers had no assignable typed lemma work');
    expect(section!.text).toContain('Save and publish that graph promptly');
    expect(section!.text).toContain('waiting is valid');
    expect(section!.text).toContain('Do not manufacture helpers or duplicate in-flight questions');
    expect(context.message).toContain(section!.text);
    expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({
      id: 'capacity-refill', kind: 'assignment', required: true,
    }));
    expect(context.manifest!.omitted).not.toContainEqual(expect.objectContaining({ id: 'capacity-refill' }));
    expect(context.workContract).toHaveProperty('capacityRefill', request);
    expect(context.instructions).toContain('let Provers wait');
    expect(context.instructions).toContain('Do not manufacture helpers.');
    expect(context.instructions).toContain('Once a complete plan has useful executable work');
    expect(context.instructions).toContain('dispatchNonce');
  });

  it('freezes a separate dispatch snapshot rather than letting the mutable request journal rewrite the prompt', async () => {
    const action = planning(await nextLead()), request = requestFor(action), expected = structuredClone(request);
    const receipt = state.cooperation!.lastCapacityRefill!;
    expect(request).not.toBe(receipt);
    expect(request.workerIds).not.toBe(receipt.workerIds);
    expect(Object.isFrozen(request)).toBe(true);
    expect(Object.isFrozen(request.workerIds)).toBe(true);
    receipt.workerIds[0] = 'journal-only-worker';
    receipt.inputDigest = mathDigest('a later journal value');
    receipt.requestedAt++;
    receipt.status = 'assessed';
    const context = contextFor(action);
    expect(action.capacityRefill).toEqual(expected);
    expect(context.workContract).toHaveProperty('capacityRefill', expected);
    expect(context.message).not.toContain('journal-only-worker');
  });

  it('retains the frozen request on its active Lead dispatch after a live plan publication assesses the journal', async () => {
    const action = planning(await nextLead()), request = requestFor(action), snapshot = structuredClone(request);
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    const proposal = plan(); proposal.tasks.push(newLemma().task);
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify({
      kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      summary: 'An independent typed step is ready for the waiting Prover.', ...proposal,
    }) + '\n');
    await cooperative.pulse();
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('assessed');
    expect(node('new_helper').status).toBe('pending');
    expect(cooperative.current(action)).toBe(true);
    expect(requestFor(action)).toEqual(snapshot);
    const context = contextFor(action);
    expect(context.workContract).toHaveProperty('capacityRefill', snapshot);
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'capacity-refill', required: true }));
    expect(context.message).toContain('frozen at this Lead dispatch');
    expect(context.message).toContain(JSON.stringify(snapshot));
  });

  it.each(['requested', 'assessed'] as const)('does not attach a global %s receipt to an unrelated Lead decision', async status => {
    state.cooperation!.lastCapacityRefill = { inputDigest: mathDigest('stale unrelated request'),
      workerIds: ['stale-refill-worker'], requestedAt: 1, status };
    cooperative.interrupted(workers[0], { kind: 'lead', seedCommit: problem.baseCommit });
    const action = planning(await nextLead({ maxTurns: 12, remainingMs: Infinity }));
    expect(action).not.toHaveProperty('capacityRefill');
    const context = contextFor(action);
    expect(context.workContract).not.toHaveProperty('capacityRefill');
    expect(context.manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'capacity-refill' }));
    expect(context.message).not.toContain('stale-refill-worker');
  });

  it('keeps request details in the Lead journal without adding them to a peer file or task context', async () => {
    await nextLead();
    const busy = node('busy_helper');
    const action: CooperativeAction = { kind: 'task', task: busy.task, assignment: busy.assignment! };
    const context = contextFor(action, workers[2]);
    expect(context.workContract).not.toHaveProperty('capacityRefill');
    expect(context.manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'capacity-refill' }));
    refresh();
    const leadJournal = JSON.parse(fs.readFileSync(path.join(workers[0].worktree, 'COOPERATION.json'), 'utf8'));
    expect(leadJournal.lastCapacityRefill).toEqual(state.cooperation!.lastCapacityRefill);
    for (const worker of workers.slice(1)) {
      const journal = JSON.parse(fs.readFileSync(path.join(worker.worktree, 'COOPERATION.json'), 'utf8'));
      expect(journal).not.toHaveProperty('lastCapacityRefill');
    }
  });

  it.each(['assemble', 'review'] as const)('does not give a %s action the global pending capacity request', async kind => {
    await nextLead();
    const action: CooperativeAction = kind === 'assemble' ? { kind, seedCommit: problem.baseCommit }
      : { kind, seedCommit: problem.baseCommit, sourceDigest: mathDigest('fixed review sources') };
    const context = contextFor(action);
    expect(context.workContract).not.toHaveProperty('capacityRefill');
    expect(context.manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'capacity-refill' }));
    expect(context.message).not.toContain('Host capacity refill request');
  });

  it.each([
    { control: 'finite turns', maxTurns: 12, remainingMs: Infinity },
    { control: 'finite time', maxTurns: Infinity, remainingMs: 10_000 },
  ])('preserves the original Lead cadence with $control while still honoring an explicit replan', async limited => {
    const refill = vi.spyOn(cooperative as any, 'capacityRefill');
    const assignment = node('busy_helper').assignment;
    const waiting = await waitsForInput(limited);
    expect(refill).not.toHaveBeenCalled();
    expect(state.cooperation!.lastCapacityRefill).toBeUndefined();
    expect(node('busy_helper').assignment).toBe(assignment);
    cooperative.interrupted(workers[0], { kind: 'lead', seedCommit: problem.baseCommit });
    const action = planning(await waiting.waiting);
    expect(action).not.toHaveProperty('capacityRefill');
    expect(contextFor(action).manifest!.included).not.toContainEqual(expect.objectContaining({ id: 'capacity-refill' }));
    expect(refill).not.toHaveBeenCalled();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(0);
    expect(busyInterrupt).not.toHaveBeenCalled();
  });

  it('retries an unfinished refill after its selected action fails final admission', async () => {
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const action = (await nextLead())!, receipt = state.cooperation!.lastCapacityRefill!;
    const firstRequest = requestFor(action), snapshot = structuredClone(firstRequest);
    cooperative.reserveTurn(workers[0]);
    state.cooperation!.planVersion = 'superseded-before-admission';
    expect(cooperative.started(workers[0], action)).toBe(false);
    cooperative.settleTurn(workers[0]); cooperative.release(workers[0], action);
    expect((cooperative as any).capacityRefill()?.inputDigest).toBe(receipt.inputDigest);
    const retry = (await nextLead())!;
    expect(retry.kind).toBe('lead');
    expect(retry).not.toBe(action);
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested', inputDigest: receipt.inputDigest });
    expect(state.cooperation!.lastCapacityRefill).not.toBe(receipt);
    expect(state.cooperation!.lastCapacityRefill!.requestId).toBe(receipt.requestId);
    expect(state.cooperation!.lastCapacityRefill!.requestedAt).toBe(receipt.requestedAt);
    expect(requestFor(retry)).toEqual(archivedRequest());
    expect(requestFor(retry)).not.toBe(firstRequest);
    expect(requestFor(action)).toEqual(snapshot);
    expect(contextFor(retry).workContract).toHaveProperty('capacityRefill', archivedRequest());
    // A delayed callback from the failed action cannot assess the replacement request.
    (cooperative as any).markCapacityRefillAssessed(action);
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    await assess(retry);
    expect(requestFor(action)).toEqual(snapshot);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_refill_resumed')).toHaveLength(1);
  });

  it.each(['request-failure', 'checkpoint', 'scheduling-checkpoint'] as const)('retries a %s Lead that only retained the previously seeded plan', async recovery => {
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const action = (await nextLead())!, receipt = state.cooperation!.lastCapacityRefill!;
    const firstRequest = requestFor(action), snapshot = structuredClone(firstRequest);
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    cooperative.deactivate(workers[0]);
    const result = await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree), true, recovery);
    expect(result.savedPlan).not.toBe(true);
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested', inputDigest: receipt.inputDigest });
    expect((cooperative as any).capacityRefill()).toBeDefined();
    const retry = (await nextLead())!;
    expect(retry.kind).toBe('lead');
    expect(requestFor(retry)).toEqual(archivedRequest());
    expect(requestFor(retry)).not.toBe(firstRequest);
    expect(contextFor(retry).workContract).toHaveProperty('capacityRefill', archivedRequest());
    await assess(retry);
    expect(requestFor(action)).toEqual(snapshot);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_refill_resumed')).toHaveLength(1);
  });

  it.each(['request-failure', 'checkpoint', 'scheduling-checkpoint'] as const)('accepts a complete new plan saved before %s as one assessed decision', async recovery => {
    const action = (await nextLead())!;
    const proposal = plan(), added = newLemma(); added.task.ownerId = workers[2].id;
    proposal.tasks.push(added.task);
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(proposal) + '\n```\n');
    const result = await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree), true, recovery);
    expect(result.savedPlan).toBe(recovery === 'request-failure' ? true : undefined);
    expect(node('new_helper').status).toBe('pending');
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('assessed');
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  describe.each(['request-failure', 'checkpoint', 'scheduling-checkpoint'] as const)('%s interrupted planning', recovery => {
    const expectDraftOutcome = (attempt: number, action: CooperativeAction, commit: string, since: number) => {
      const unchangedSchedulingDraft = recovery === 'scheduling-checkpoint' && attempt > 0;
      const currentEvents = events.slice(since);
      expect(currentEvents.filter(item => ['plan_rejected', 'lead_checkpoint_saved', 'plan_updated', 'plan_published'].includes(item.event)))
        .toEqual([unchangedSchedulingDraft
          ? { event: 'lead_checkpoint_saved', details: { commit, seedCommit: action.seedCommit, reason: 'unchanged-control-response' } }
          : { event: 'plan_rejected', details: expect.objectContaining({ incomplete: true, stalled: false, recoveryKind: recovery,
            error: expect.any(String), proposalDigest: expect.any(String), inputDigest: expect.any(String) }) }]);
      expect(currentEvents.filter(item => item.event === 'lead_draft_preserved')).toHaveLength(unchangedSchedulingDraft ? 0 : 1);
      expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(recovery === 'scheduling-checkpoint' ? 1 : attempt + 1);
      expect(events.filter(item => item.event === 'lead_checkpoint_saved')).toHaveLength(recovery === 'scheduling-checkpoint' ? attempt : 0);
      expect(events.filter(item => item.event === 'capacity_refill_assessed')).toEqual([]);
      expect(state.cooperation!.planRejection).toBeUndefined();
      expect(state.cooperation!.planPublication).toBeUndefined();
      expect(state.cooperation!.researchDecisions).toBeUndefined();
      expect(state.cooperation!.challengeDecisions).toBeUndefined();
      expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
      expect(state.check).toBeUndefined();
      expect(state.cooperation!.deliveries).toContainEqual(expect.objectContaining({
        producer: workers[0].id, kind: 'progress', status: 'advisory', commit,
        summary: expect.stringContaining('Saved Lead draft pending integration:'),
      }));
    };

    it.each(['malformed', 'missing'] as const)('retries the same %s graph after consecutive interrupted turns', async kind => {
      const notes = kind === 'malformed' ? 'A useful partial construction.\n```math-plan\n{"tasks": [\n'
        : 'A useful partial construction; its exact remaining inference still needs a complete graph.\n';
      const file = path.join(workers[0].worktree, 'RESEARCH.md');
      const originalPlan = structuredClone(plan()), version = state.cooperation!.planVersion, canonical = state.cooperation!.canonicalCommit;
      const busy = node('busy_helper'), assignment = structuredClone(busy.assignment);
      for (let attempt = 0; attempt < 3; attempt++) {
        const action = (await nextLead())!;
        expect(action.kind).toBe('lead');
        fs.writeFileSync(file, notes);
        const commit = commitSolverSources(problem, workers[0].worktree), since = events.length;
        const result = await cooperative.deliver(workers[0], action, commit, true, recovery);
        expect(result).toEqual({ checkWhole: false });
        expectDraftOutcome(attempt, action, commit, since);
        expect(committedSource(workers[0].worktree, commit, 'RESEARCH.md')).toBe(notes);
        expect(plan()).toEqual(originalPlan);
        expect(state.cooperation!.planVersion).toBe(version); expect(state.cooperation!.canonicalCommit).toBe(canonical);
        expect(node('busy_helper')).toBe(busy); expect(busy.assignment).toEqual(assignment);
        expect(busy.status).toBe('running'); expect(busyInterrupt).not.toHaveBeenCalled();
        expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
        expect(state.cooperation!.planRejection?.stalled).not.toBe(true);
        expect(fs.readFileSync(file, 'utf8')).toBe(notes);
        expect((cooperative as any).capacityRefill()).toBeDefined();
      }
      expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(recovery === 'scheduling-checkpoint' ? 1 : 3);
      expect(events.filter(item => item.event === 'lead_checkpoint_saved')).toHaveLength(recovery === 'scheduling-checkpoint' ? 2 : 0);
      expect(events.filter(item => item.event === 'plan_rejected').every(item =>
        item.details?.incomplete === true && item.details.stalled === false)).toBe(true);
      expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
      expect(events.filter(item => item.event === 'capacity_refill_resumed')).toHaveLength(2);
      await assess((await nextLead())!);
      await waitsForInput();
    });

    it.each(['malformed', 'missing'] as const)('retains and retries the same %s draft through repeated process restores', async kind => {
      const notes = kind === 'malformed' ? 'A useful saved argument.\n```math-plan\n{"tasks": [\n'
        : 'A useful saved argument without a complete task graph.\n';
      const file = path.join(workers[0].worktree, 'RESEARCH.md');
      const originalPlan = structuredClone(plan()), version = state.cooperation!.planVersion;
      const canonicalSources = () => problem.ownedFiles.map(relative => committedSource(workers[0].worktree,
        state.cooperation!.canonicalCommit!, path.join(problem.projectRelative, relative)));
      const originalSources = canonicalSources();
      for (let attempt = 0; attempt < 3; attempt++) {
        const action = (await nextLead())!;
        fs.writeFileSync(file, notes);
        const commit = commitSolverSources(problem, workers[0].worktree), since = events.length;
        expect(await cooperative.deliver(workers[0], action, commit, true, recovery)).toEqual({ checkWhole: false });
        expectDraftOutcome(attempt, action, commit, since);
        const saved = path.join(directory, `unfinished-${attempt}.json`);
        writeSolverRunState(saved, state);
        const current = instances.at(-1)!; current.controller.abort(); await cooperative.stop();
        const rejectedBeforeRestore = events.filter(item => item.event === 'plan_rejected').length;
        const checkpointsBeforeRestore = events.filter(item => item.event === 'lead_checkpoint_saved').length;
        state = readSolverRunState(saved); cooperative = create(); await cooperative.restore();
        expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(rejectedBeforeRestore);
        expect(events.filter(item => item.event === 'lead_checkpoint_saved')).toHaveLength(checkpointsBeforeRestore);
        expect(committedSource(workers[0].worktree, commit, 'RESEARCH.md')).toBe(notes);
        expect(plan()).toEqual(originalPlan);
        expect(state.cooperation!.planVersion).toBe(version); expect(canonicalSources()).toEqual(originalSources);
        expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
        expect(state.cooperation!.planPublication).toBeUndefined(); expect(state.check).toBeUndefined();
        expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
        expect(state.cooperation!.planRejection?.stalled).not.toBe(true);
        expect(fs.readFileSync(file, 'utf8')).toBe(notes);
        expect((cooperative as any).capacityRefill()).toBeDefined();
      }
      expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(recovery === 'scheduling-checkpoint' ? 1 : 3);
      expect(events.filter(item => item.event === 'lead_checkpoint_saved')).toHaveLength(recovery === 'scheduling-checkpoint' ? 2 : 0);
      expect(events.filter(item => item.event === 'plan_rejected').every(item =>
        item.details?.incomplete === true && item.details.stalled === false)).toBe(true);
      await assess((await nextLead())!);
      await waitsForInput();
    });
  });

  it('retains ordinary completed invalid-plan rejection and its repeated-input stalled state', async () => {
    const file = path.join(workers[0].worktree, 'RESEARCH.md');
    const incomplete = 'A completed response still omitted its required task graph.\n';
    for (let attempt = 0; attempt < 2; attempt++) {
      const action = (await nextLead())!;
      fs.writeFileSync(file, incomplete);
      await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
      expect(state.cooperation!.planRejection?.stalled).toBe(attempt === 1);
    }
    expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(2);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_refill_resumed')).toHaveLength(1);
  });

  it('keeps native scheduling drafts resumable while ordinary repeated checkpoints still pause unchanged research', async () => {
    const task: CooperativeTask = { id: 'ongoing_research', kind: 'research', ownerId: workers[3].id, revision: 0, dependsOn: [],
      objective: 'Investigate the exact missing construction and retain the unfinished argument.' };
    for (const item of state.cooperation!.tasks) if (item.task.kind === 'goal') item.task.status = 'paused';
    state.cooperation!.tasks.push({ task, status: 'pending', attempts: 0 }); refresh();
    let assignmentId: string | undefined;
    for (let turn = 0; turn < 5; turn++) {
      const action = (await track(cooperative.next(workers[3], budget)))!;
      if (action.kind !== 'task' || action.task.id !== task.id) throw new Error('fixture_expected_research_draft');
      assignmentId ??= action.assignment.assignmentId;
      expect(action.assignment.assignmentId).toBe(assignmentId);
      fs.writeFileSync(path.join(workers[3].worktree, 'RESEARCH.md'), 'The same unfinished quantitative argument.\n');
      await cooperative.deliver(workers[3], action, commitSolverSources(problem, workers[3].worktree), true,
        turn < 3 ? 'scheduling-checkpoint' : 'checkpoint');
      expect(node(task.id).status).toBe(turn === 4 ? 'blocked' : 'pending');
      if (turn < 3) expect(state.cooperation!.researchCheckpoints?.[task.id]).toBeUndefined();
    }
    expect(state.cooperation!.researchDrafts?.[task.id]?.workerId).toBe(workers[3].id);
    expect(state.cooperation!.researchCheckpoints?.[task.id]).toMatchObject({ count: 2, paused: true });
  });

  it.each(['active', 'admission-reserved'] as const)('does not duplicate an %s Lead refill', async phase => {
    const action = (await nextLead())!;
    if (phase === 'active') cooperative.activate(workers[0], action, async () => {}, async () => {});
    else cooperative.reserveTurn(workers[0]);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  it('leaves existing M3/M5 typed work for the idle Prover to claim', async () => {
    state.cooperation!.tasks.push(newLemma()); refresh();
    await waitsForInput();
    expect(state.cooperation!.lastCapacityRefill).toBeUndefined();
  });

  it('estimates existing typed capacity without consuming configurable scheduler callbacks or changing claims', () => {
    state.cooperation!.tasks.push(newLemma()); refresh();
    const modules = (cooperative as any).input.modules;
    const ready = vi.spyOn(modules.M3, 'ready').mockImplementation(() => { throw new Error('fixture_extra_scheduler_call'); });
    const assign = vi.spyOn(modules.M5, 'assign').mockImplementation(() => { throw new Error('fixture_extra_assignment_call'); });
    const previous = structuredClone({ tasks: state.cooperation!.tasks, groups: state.cooperation!.groups });
    expect((cooperative as any).capacityRefill()).toBeUndefined();
    expect(ready).not.toHaveBeenCalled(); expect(assign).not.toHaveBeenCalled();
    expect({ tasks: state.cooperation!.tasks, groups: state.cooperation!.groups }).toEqual(previous);
  });

  it.each(['goal', 'outside-plan'] as const)('ignores a custom allocator returning %s work while estimating missing typed capacity', kind => {
    const candidate = kind === 'goal' ? node('goal_0') : newLemma();
    const assign = vi.spyOn((cooperative as any).input.modules.M5, 'assign').mockReturnValue(candidate);
    const previous = structuredClone({ tasks: state.cooperation!.tasks, groups: state.cooperation!.groups });
    expect((cooperative as any).capacityRefill()).toMatchObject({ workerIds: ['idle-prover'] });
    expect(assign).not.toHaveBeenCalled();
    expect({ tasks: state.cooperation!.tasks, groups: state.cooperation!.groups }).toEqual(previous);
  });

  it('counts one shared ready lemma once across several idle Provers without mutating its assignment', async () => {
    moveBusyTaskToEngineer();
    const shared = newLemma(); delete shared.task.ownerId;
    state.cooperation!.tasks.push(shared); refresh();
    expect((await nextLead())?.kind).toBe('lead');
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested', workerIds: ['busy-prover'] });
    expect(shared.status).toBe('pending'); expect(shared.assignment).toBeUndefined();
    expect(state.cooperation!.groups![0].busy).toBe(1);
    expect(busyInterrupt).not.toHaveBeenCalled();
  });

  it('respects the last group slot when existing shared work already covers it', async () => {
    moveBusyTaskToEngineer();
    const shared = newLemma(); delete shared.task.ownerId;
    state.cooperation!.tasks.push(shared);
    state.cooperation!.groups![0].group.maxConcurrent = 2; refresh();
    await waitsForInput();
    expect(state.cooperation!.lastCapacityRefill).toBeUndefined();
    expect(shared.status).toBe('pending'); expect(shared.assignment).toBeUndefined();
    expect(state.cooperation!.groups![0].busy).toBe(1);
  });

  it.each(['preflight', 'cooldown', 'statement-review', 'group-cap'] as const)('respects %s occupancy and intentional route capacity', async control => {
    if (control === 'preflight') {
      const task = newLemma(); state.cooperation!.tasks.push(task);
      (cooperative as any).preparingTaskTypes.set(task, { workerId: workers[1].id, controller: new AbortController(),
        current: () => true, settled: Promise.resolve() });
    } else if (control === 'cooldown') {
      state.workers = [{ id: workers[1].id, recovery: { phase: 'cooling-down' } }] as SolverRunState['workers'];
    } else if (control === 'statement-review') {
      state.cooperation!.statementReviews = [{ taskId: 'busy_helper', workerId: workers[1].id,
        status: 'reviewing' }] as NonNullable<SolverRunState['cooperation']>['statementReviews'];
    } else state.cooperation!.groups![0].group.maxConcurrent = 1;
    expect((cooperative as any).capacityRefill()).toBeUndefined();
    expect(state.cooperation!.lastCapacityRefill).toBeUndefined();
  });

  it('keeps an assessed no-op plan waiting through scheduling changes, ordinary notes and empty progress checkpoints', async () => {
    const action = (await nextLead())!;
    await assess(action);
    const receipt = structuredClone(state.cooperation!.lastCapacityRefill);
    const waiting = await waitsForInput();
    node('busy_helper').status = 'pending'; node('busy_helper').attempts++;
    state.cooperation!.groups![0].turns++;
    fs.appendFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'Ordinary Lead journal without new evidence.\n');
    publish('progress', 'Still investigating the same assignment.');
    for (let index = 0; index < 6; index++) await Promise.resolve();
    expect(waiting.settled()).toBe(false);
    expect(state.cooperation!.lastCapacityRefill).toEqual(receipt);
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  it('wakes on a valid new complete finding and ignores its duplicate delivery identity', async () => {
    await assess((await nextLead())!);
    const first = state.cooperation!.lastCapacityRefill!.inputDigest;
    const waiting = await waitsForInput();
    publish('research', 'A complete new argument supplies the exact missing library interface.');
    const action = await waiting.waiting;
    expect(action?.kind).toBe('lead');
    expect(state.cooperation!.lastCapacityRefill!.inputDigest).not.toBe(first);
    await assess(action!);
    const same = await waitsForInput();
    publish('research', 'A complete new argument supplies the exact missing library interface.');
    for (let index = 0; index < 6; index++) await Promise.resolve();
    expect(same.settled()).toBe(false);
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(2);
  });

  it('does not swallow a peer finding published while the Lead is preparing its plan', async () => {
    const action = (await nextLead())!, first = state.cooperation!.lastCapacityRefill!.inputDigest;
    publish('research', 'A new independently saved construction arrived during the decision.');
    await assess(action);
    expect(state.cooperation!.lastCapacityRefill!.inputDigest).toBe(first);
    expect((await nextLead())?.kind).toBe('lead');
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(2);
  });

  it('separates the mathematical responsibility from inbox and graph presentation freshness', () => {
    const responsibility = (cooperative as any).leadResponsibilityDigest();
    publish('research', 'A new advisory library clue about the same exact obligation.');
    state.cooperation!.planVersion = 'another-presentation';
    const task = node('busy_helper');
    task.task = { ...task.task, ownerId: workers[3].id, revision: task.task.revision + 1, objective: 'Rephrased coordination.' };
    expect((cooperative as any).leadResponsibilityDigest()).toBe(responsibility);
    task.task = { ...task.task, type: 'False' };
    expect((cooperative as any).leadResponsibilityDigest()).not.toBe(responsibility);
  });

  it('marks the post-plan contract once so the Lead cannot trigger itself by extending the graph', async () => {
    const action = (await nextLead())!;
    const added = newLemma(); added.task.ownerId = workers[2].id;
    const originalBasis = requestFor(action).inputDigest;
    state.cooperation!.tasks.push(added);
    // This task still belongs to the occupied Prover, so the spare Prover remains without useful work.
    await assess(action);
    expect(state.cooperation!.lastCapacityRefill!.inputDigest).toBe(originalBasis);
    expect(state.cooperation!.lastCapacityRefill!.coveredInputDigest).not.toBe(originalBasis);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  it('retains an assessed mathematical input across saved-state restore without re-requesting the same capacity decision', async () => {
    await assess((await nextLead())!);
    const file = path.join(directory, 'saved-state.json');
    writeSolverRunState(file, state);
    const receipt = structuredClone(state.cooperation!.lastCapacityRefill);
    instances[0].controller.abort(); await cooperative.stop();
    state = readSolverRunState(file); cooperative = create();
    await cooperative.restore();
    await waitsForInput();
    expect(state.cooperation!.lastCapacityRefill).toEqual(receipt);
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
  });

  const stalledResearch = () => {
    workers[1] = { ...workers[1], role: 'researcher' };
    const task: CooperativeTask = { id: 'stalled_research', kind: 'research', objective: 'Find an independent decomposition.',
      dependsOn: ['busy_helper'], groupId: 'main', revision: 0, ownerId: workers[1].id };
    state.cooperation!.tasks.push({ task, status: 'running', attempts: 4, assignment: {
      taskId: task.id, taskDigest: taskVersion(task), workerId: workers[1].id, seedCommit: problem.baseCommit } });
    state.workers = workers.map(worker => ({ ...worker, phase: 'running', turns: 4,
      ...(worker.id === workers[1].id ? { sessionTaskId: task.id, sessionTaskVersion: taskVersion(task),
        advisoryCheckpoint: { scope: mathDigest('same-responsibility'), noProgressStreak: 3 } } : {}) }));
    refresh();
  };
  const assessStagnation = async (action: CooperativeAction) => {
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(plan()));
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(events.filter(item => item.event === 'plan_rejected')).toEqual([]);
    expect(state.cooperation!.lastStagnationRecovery?.status).toBe('assessed');
  };

  it('resumes one pending stagnation request and admits its explicit no-work receipt', async () => {
    stalledResearch();
    const first = planning(await nextLead()), initial = structuredClone(first.stagnationRecovery!);
    cooperative.deactivate(workers[0]);
    const retry = planning(await nextLead());
    expect(retry.stagnationRecovery!.requestId).toBe(initial.requestId);
    expect(retry.stagnationRecovery!.requestedAt).toBe(initial.requestedAt);
    expect(events.filter(item => item.event === 'stagnation_recovery_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'stagnation_recovery_resumed')).toHaveLength(1);
    expect(cooperative.started(workers[0], retry)).toBe(true);
    cooperative.activate(workers[0], retry, async () => {}, async () => {});
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(retry)!), JSON.stringify({
      kind: 'assessment', dispatchNonce: retry.planNonce, baseVersion: retry.planVersion,
      assessments: [{ kind: 'stagnation', requestId: initial.requestId, inputDigest: initial.inputDigest,
        outcome: 'no-independent-work', reason: 'The exact remaining classification step has not been decomposed.' }],
    }) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.lastStagnationRecovery).toMatchObject({ requestId: initial.requestId,
      inputDigest: initial.inputDigest, status: 'assessed', outcome: 'no-independent-work' });
    expect(state.cooperation!.lastCapacityRefill).toBeUndefined();
  });

  it('wakes Lead for advisory stagnation even with no idle prover, preserving the typed frontier', async () => {
    stalledResearch();
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    const before = structuredClone(state.cooperation!.tasks);
    const action = planning(await nextLead());
    expect(action.capacityRefill).toBeUndefined();
    expect(action.stagnationRecovery).toMatchObject({ taskIds: ['busy_helper'], workerIds: [workers[1].id],
      reason: 'advisory-no-durable-progress' });
    expect(Object.isFrozen(action.stagnationRecovery)).toBe(true);
    expect(Object.isFrozen(action.stagnationRecovery!.taskIds)).toBe(true);
    expect(state.cooperation!.tasks).toEqual(before);
    expect(busyInterrupt).not.toHaveBeenCalled();
    expect(events.filter(item => item.event === 'stagnation_recovery_requested')).toHaveLength(1);
  });

  it('assesses the same graph once, retains the visible unresolved request and reactivates on new external evidence', async () => {
    stalledResearch();
    const first = planning(await nextLead()), request = structuredClone(first.stagnationRecovery);
    await assessStagnation(first);
    expect((cooperative as any).stagnationRecovery()).toBeUndefined();
    expect(cooperative.contextState(first, workers[0]).lastStagnationRecovery).toMatchObject({ ...request, status: 'assessed' });
    expect(cooperative.contextState(undefined, workers[1]).lastStagnationRecovery).toBeUndefined();
    const journal = (worker: typeof workers[number]) => JSON.parse(fs.readFileSync(path.join(worker.worktree, 'COOPERATION.json'), 'utf8'));
    expect(journal(workers[0]).lastStagnationRecovery).toMatchObject({ ...request, status: 'assessed' });
    expect(journal(workers[1])).not.toHaveProperty('lastStagnationRecovery');
    state.workers![1].advisoryCheckpoint!.noProgressStreak = 99;
    refresh(); await waitsForInput();
    expect(events.filter(item => item.event === 'stagnation_recovery_requested')).toHaveLength(1);
    publish('research', 'A new exact closed helper can split the unresolved consumer.');
    const retry = planning(await nextLead());
    expect(retry.stagnationRecovery!.inputDigest).not.toBe(request!.inputDigest);
    expect(first.stagnationRecovery).toEqual(request);
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'lemma' && node.status === 'integrated')).toHaveLength(0);
  });

  it('retains the assessed stagnation tombstone across saved state restore', async () => {
    stalledResearch();
    await assessStagnation(planning(await nextLead()));
    const receipt = structuredClone(state.cooperation!.lastStagnationRecovery);
    const file = path.join(directory, 'stagnation-state.json'); writeSolverRunState(file, state);
    instances[0].controller.abort(); await cooperative.stop();
    state = readSolverRunState(file); cooperative = create(); await cooperative.restore();
    expect(state.cooperation!.lastStagnationRecovery).toEqual(receipt);
    expect((cooperative as any).stagnationRecovery()).toBeUndefined();
    expect(events.filter(item => item.event === 'stagnation_recovery_requested')).toHaveLength(1);
  });

  it.each(['live', 'final'] as const)('accepts an explicit %s no-independent-work decision without rewriting the graph', async mode => {
    const action = planning(await nextLead()), response = noIndependentWork(action);
    const before = structuredClone(state.cooperation!.tasks), basis = requestFor(action).inputDigest;
    if (mode === 'live') {
      expect(cooperative.started(workers[0], action)).toBe(true);
      cooperative.activate(workers[0], action, async () => {}, async () => {});
      const file = path.join(workers[0].worktree, leadPlanDeliveryFile(action)!);
      fs.appendFileSync(file, JSON.stringify(response) + '\n');
      await cooperative.pulse();
      fs.appendFileSync(file, JSON.stringify(response) + '\n');
      await cooperative.pulse();
      cooperative.deactivate(workers[0]);
    } else {
      fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(response));
      await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    }
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ inputDigest: basis, status: 'assessed',
      outcome: 'no-independent-work', decisionReason: response.assessments[0].reason });
    expect(state.cooperation!.tasks).toEqual(before);
    expect(events.filter(item => item.event === 'capacity_refill_assessed')).toHaveLength(1);
    expect(events.some(item => item.event === 'plan_updated' || item.event === 'plan_publication_rejected')).toBe(false);
    await waitsForInput();
  });

  it.each(['requestId', 'inputDigest', 'dispatchNonce', 'baseVersion'] as const)('rejects a live assessment with stale %s', async field => {
    const action = planning(await nextLead()), response = noIndependentWork(action);
    if (field === 'requestId' || field === 'inputDigest') response.assessments[0][field] = mathDigest('stale');
    else response[field] = 'stale';
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify(response) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(events.some(item => item.event === 'plan_publication_rejected')).toBe(true);
    expect(events.some(item => item.event === 'capacity_refill_assessed')).toBe(false);
  });

  it('restores a final assessment as an acknowledged decision rather than an invalid graph', async () => {
    const action = planning(await nextLead()), response = noIndependentWork(action);
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(response));
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    const receipt = structuredClone(state.cooperation!.lastCapacityRefill);
    const file = path.join(directory, 'assessment-state.json'); writeSolverRunState(file, state);
    instances[0].controller.abort(); await cooperative.stop();
    state = readSolverRunState(file); cooperative = create(); await cooperative.restore();
    expect(state.cooperation!.lastCapacityRefill).toEqual(receipt);
    expect(events.some(item => item.event === 'plan_rejected')).toBe(false);
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('does not cover new evidence that arrived before an old short acknowledgement', async () => {
    const action = planning(await nextLead()), response = noIndependentWork(action);
    publish('research', 'New evidence about the unchanged exact missing construction.');
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(response));
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(state.cooperation!.lastCapacityRefill!.coveredInputDigest).toBeUndefined();
    const next = planning(await nextLead());
    expect(next.capacityRefill!.requestId).not.toBe(action.capacityRefill!.requestId);
  });

  it('does not let a short assessment swallow a newly arrived handoff', async () => {
    const action = planning(await nextLead()), response = noIndependentWork(action);
    const finding = 'A fully typed smaller bridge requires an explicit Lead decision.';
    (cooperative as any).record(workers[2], node('busy_helper').task, 'research', 'advisory', finding,
      { finding, findingDigest: mathDigest(finding), lemmaRequests: [newLemma().task] });
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify(response) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(state.cooperation!.researchDecisions).toBeUndefined();
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_publication_rejected',
      details: expect.objectContaining({ reason: 'math_plan_assessment_inbox_unresolved' }) }));
  });

  it('restores a requested but unassessed refill and retries it until a plan is accepted', async () => {
    const firstAction = (await nextLead())!, firstRequest = requestFor(firstAction), snapshot = structuredClone(firstRequest);
    const receipt = structuredClone(state.cooperation!.lastCapacityRefill);
    const file = path.join(directory, 'saved-unassessed-state.json');
    writeSolverRunState(file, state);
    instances[0].controller.abort(); await cooperative.stop();
    state = readSolverRunState(file); cooperative = create();
    await cooperative.restore();
    expect(state.cooperation!.lastCapacityRefill).toEqual(receipt);
    expect((cooperative as any).capacityRefill()).toMatchObject({ inputDigest: receipt!.inputDigest });
    const retry = (await nextLead())!;
    expect(retry.kind).toBe('lead');
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested', inputDigest: receipt!.inputDigest });
    expect(requestFor(retry)).toEqual(archivedRequest());
    expect(requestFor(retry)).not.toBe(firstRequest);
    expect(requestFor(firstAction)).toEqual(snapshot);
    expect(contextFor(retry).workContract).toHaveProperty('capacityRefill', archivedRequest());
    cooperative.activate(workers[0], retry, async () => {}, async () => {});
    expect((cooperative as any).capacityRefill()).toBeUndefined();
    await assess(retry);
    expect(requestFor(firstAction)).toEqual(snapshot);
    await waitsForInput();
    expect(events.filter(item => item.event === 'capacity_refill_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_refill_resumed')).toHaveLength(1);
  });
});
