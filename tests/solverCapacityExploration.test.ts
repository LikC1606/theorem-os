import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { readCooperationPlan } from '../src/solver/cooperationShared';
import * as contextCompiler from '../src/solver/contextCompiler';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { captureObligationSnapshot } from '../src/solver/obligationProgress';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion,
  type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('host exploration for spare cooperative capacity', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const focuses = ['boundary', 'construction', 'decomposition', 'interface'];
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let pending: Promise<unknown>[], events: { event: string; details?: Record<string, unknown> }[];
  let interrupts: Map<string, ReturnType<typeof vi.fn>>, model: ReturnType<typeof vi.fn>;
  let modelAllowed: boolean;
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const overlays = () => state.cooperation!.tasks.filter(item => item.capacityExploration);
  const provers = () => workers.filter(worker => worker.role === 'prover');
  const track = <T,>(promise: Promise<T>) => { pending.push(promise); void promise.catch(() => {}); return promise; };
  const refresh = () => (cooperative as any).changed();
  const create = (overrides: Partial<Parameters<typeof cooperativeResearch>[0]> = {}) => {
    const controller = new AbortController();
    const instance = cooperativeResearch({ state, workers, retrievalRoot: directory, continuousResearch: true,
      signal: controller.signal, modelDispatchAllowed: () => modelAllowed,
      emit: (event, details) => events.push({ event, details }),
      modules: { ...directSolverModules, M1: { ...directSolverModules.M1, open: model },
        M2: { ...directSolverModules.M2,
          check: async () => { throw new Error('fixture_unexpected_verifier'); },
          checkTask: async () => { throw new Error('fixture_unexpected_verifier'); } } }, ...overrides });
    instances.push({ cooperative: instance, controller });
    return instance;
  };
  const activate = (worker: ResearchWorker, action: CooperativeAction) => {
    expect(cooperative.started(worker, action)).toBe(true);
    const interrupt = vi.fn(async () => {});
    interrupts.set(worker.id, interrupt);
    cooperative.activate(worker, action, interrupt, async () => {});
    return action;
  };
  const taskAction = (action: CooperativeAction | undefined) => {
    if (action?.kind !== 'task') throw new Error('fixture_expected_task');
    return action;
  };
  const claim = async (worker: ResearchWorker) => {
    const action = taskAction(await track(cooperative.next(worker, budget)));
    activate(worker, action);
    return action;
  };
  const startGeneralists = async () => {
    for (const worker of workers.filter(peer => peer.role === 'researcher')) {
      const action = await claim(worker);
      expect(node(action.task.id).capacityExploration).toBeUndefined();
    }
  };
  const startLead = async () => {
    const action = await track(cooperative.next(workers[0], budget));
    if (action?.kind !== 'lead') throw new Error('fixture_expected_lead');
    activate(workers[0], action);
    return action;
  };
  const plan = () => ({ tasks: state.cooperation!.tasks.filter(item => !item.capacityExploration).map(item => item.task),
    groups: state.cooperation!.groups!.map(item => item.group) });
  const snapshot = () => captureObligationSnapshot(state.cooperation!.tasks,
    { groups: state.cooperation!.groups, environmentDigest: state.environmentDigest });
  const waitForCapacity = async (worker: ResearchWorker, dispatchBudget = budget) => {
    let settled = false;
    const waiting = track(cooperative.next(worker, dispatchBudget));
    void waiting.then(() => { settled = true; }, () => {});
    // Drain dispatch continuations before a later input change wakes this waiter.
    // Repeated microtask wakes can otherwise make the fixture lose its final notification.
    await new Promise<void>(resolve => setImmediate(resolve));
    expect(settled).toBe(false);
    return { waiting };
  };
  const complete = async (worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>) => {
    fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({
      taskId: action.task.id, conclusion: 'inconclusive',
      summary: `The ${node(action.task.id).capacityExploration?.focus ?? 'planned'} investigation leaves the original statement open.`,
    }) + '\n```\n');
    cooperative.deactivate(worker);
    await cooperative.deliver(worker, action, commitSolverSources(problem, worker.worktree));
    expect(node(action.task.id).status).toBe('completed');
  };
  const restart = async () => {
    const file = path.join(directory, 'capacity-state.json');
    writeSolverRunState(file, state);
    instances.at(-1)!.controller.abort();
    await cooperative.stop();
    state = readSolverRunState(file); cooperative = create();
    await cooperative.restore();
  };

  beforeEach(() => {
    const example = localExample('solver-capacity-exploration-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace),
      peerWorker(example, 'researcher-1'), peerWorker(example, 'researcher-2'),
      ...[1, 2, 3, 4].map(index => peerWorker(example, `prover-${index}`, { role: 'prover' })),
      peerWorker(example, 'engineer', { role: 'engineer' })];
    const initial = parseCooperationPlan(problem, { tasks: [
      ...[1, 2].map(index => ({ id: `planned_research_${index}`, kind: 'research', ownerId: `researcher-${index}`,
        objective: `Investigate the distinct planned mathematical question ${index}.` })),
      { id: 'busy_helper', kind: 'lemma', ownerId: 'engineer', objective: 'Prove the active original-goal frontier.',
        proofPath: 'Submission.lean', theoremName: 'Tutorial.busy_helper', type: 'True' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal', ownerId: 'engineer',
        objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
        dependsOn: ['busy_helper'] })),
    ], groups: [{ id: 'main', objective: 'Prove the original targets.', engineerId: 'engineer', maxConcurrent: 7 }] });
    state = solverState(problem, example.workspace, { runId: 'capacity-exploration-fixture', phase: 'running',
      workers: workers.map(worker => ({ ...worker, phase: 'running', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: initial.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: initial.groups.map(group => ({ group, turns: 0 })) } });
    pending = []; events = []; instances = []; interrupts = new Map(); modelAllowed = true;
    model = vi.fn(() => { throw new Error('fixture_real_models_forbidden'); });
    cooperative = create();
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.planEdited = true; (cooperative as any).syncPlanNotes();
    const busy = node('busy_helper');
    busy.status = 'running';
    busy.assignment = { taskId: busy.task.id, taskDigest: taskVersion(busy.task), workerId: 'engineer',
      seedCommit: problem.baseCommit, assignmentId: 'long-running-original-frontier' };
    activate(workers.at(-1)!, { kind: 'task', task: busy.task, assignment: busy.assignment });
  });
  afterEach(async () => {
    for (const instance of instances) instance.controller.abort();
    await Promise.allSettled(pending);
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    expect(model).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('keeps all eight roles occupied by assigning four distinct methods without superseding a running Lead', async () => {
    await startGeneralists();
    const lead = await startLead(), version = state.cooperation!.planVersion;
    const mathematicalInput = snapshot(), notes = fs.readFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'utf8');
    const actions = await Promise.all(provers().map(claim));
    expect(actions.every(action => action.task.kind === 'research')).toBe(true);
    expect(new Set(actions.map(action => action.task.id)).size).toBe(4);
    expect(overlays().map(item => item.capacityExploration!.focus).sort()).toEqual(focuses);
    expect(new Set(overlays().map(item => item.capacityExploration!.inputDigest)).size).toBe(1);
    expect(new Set(overlays().map(item => item.capacityExploration!.targetTaskId))).toEqual(new Set(['busy_helper']));
    for (const [index, action] of actions.entries()) {
      expect(action.assignment.workerId).toBe(provers()[index].id);
      expect(action.task.ownerId).toBe(provers()[index].id);
      expect(node(action.task.id).assignment).toBe(action.assignment);
      expect(cooperative.current(action)).toBe(true);
    }
    expect((cooperative as any).active.size).toBe(8);
    expect(state.cooperation!.groups![0].busy).toBe(7);
    expect(state.cooperation!.capacityExplorationInputs).toHaveLength(4);
    expect(events.filter(item => item.event === 'capacity_exploration_requested')).toHaveLength(4);
    expect(state.cooperation!.planVersion).toBe(version);
    expect((cooperative as any).planVersion()).toBe(version);
    expect(snapshot()).toEqual(mathematicalInput);
    expect(fs.readFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'utf8')).toBe(notes);
    expect(readCooperationPlan(problem, workers[0].worktree).tasks.map(task => task.id)).not.toEqual(
      expect.arrayContaining(actions.map(action => action.task.id)));
    expect(cooperative.current(lead)).toBe(true);
    for (const interrupt of interrupts.values()) expect(interrupt).not.toHaveBeenCalled();
  });

  it.each(['live', 'final'] as const)('retains host TaskRecords and assignments when a %s Lead graph predates exploration', async publication => {
    await startGeneralists();
    const lead = await startLead(), proposal = plan(), version = state.cooperation!.planVersion;
    const action = await claim(provers()[0]), original = node(action.task.id), assignment = original.assignment;
    expect(proposal.tasks.some(task => task.id === action.task.id)).toBe(false);
    expect(cooperative.current(lead)).toBe(true);
    if (publication === 'live') {
      fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(lead)!), JSON.stringify({
        kind: 'plan', dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
        summary: 'Continue the useful original graph while the host explores independent approaches.', ...proposal,
      }) + '\n');
      await cooperative.pulse();
      expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
      expect(cooperative.current(lead)).toBe(true);
    } else {
      fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(proposal) + '\n```\n');
      cooperative.deactivate(workers[0]);
      await cooperative.deliver(workers[0], lead, commitSolverSources(problem, workers[0].worktree));
      expect(events.some(item => item.event === 'plan_updated')).toBe(true);
    }
    expect(node(action.task.id)).toBe(original);
    expect(node(action.task.id).assignment).toBe(assignment);
    expect(node(action.task.id).status).toBe('running');
    expect(cooperative.current(action)).toBe(true);
    expect(state.cooperation!.planVersion).toBe(version);
    expect(interrupts.get(provers()[0].id)).not.toHaveBeenCalled();
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('preserves an exploration marker and assignment through a group revision with unchanged mathematical inputs', async () => {
    await startGeneralists();
    const lead = await startLead(), proposal = plan(), version = state.cooperation!.planVersion;
    const worker = provers()[0], action = await claim(worker), original = node(action.task.id);
    const marker = original.capacityExploration, assignment = original.assignment;
    proposal.groups = proposal.groups.map(group => ({ ...group, revision: group.revision + 1,
      objective: 'Reorganize the same exact proof obligations under the revised group.' }));
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(lead)!), JSON.stringify({
      kind: 'plan', dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
      summary: 'Revise group coordination while retaining the exact consumer and its inputs.', ...proposal,
    }) + '\n');
    await cooperative.pulse();
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(state.cooperation!.planVersion).not.toBe(version);
    expect(node(action.task.id)).toBe(original);
    expect(original.capacityExploration).toBe(marker);
    expect(original.assignment).toBe(assignment);
    expect(original.status).toBe('running');
    expect(cooperative.current(action)).toBe(true);
    expect(interrupts.get(worker.id)).not.toHaveBeenCalled();
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('retires an exploration when a new proof-route input changes its target without changing the target declaration', async () => {
    // Make the original declarations the active frontier so the route change concerns this exact consumer.
    for (const item of state.cooperation!.tasks) if (item.task.kind === 'goal') item.task = { ...item.task, dependsOn: [] };
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.planEdited = true; (cooperative as any).syncPlanNotes(); refresh();
    await startGeneralists();
    const lead = await startLead(), worker = provers()[0], action = await claim(worker), original = node(action.task.id);
    expect(original.capacityExploration!.targetTaskId).toBe('goal_0');
    const targetDigest = taskVersion(node('goal_0').task), ledger = structuredClone(state.cooperation!.capacityExplorationInputs);
    const proposal = { ...plan(), proofRoutes: [{ id: 'new_consumer_route', targetTaskId: 'goal_0',
      prerequisiteTaskIds: [], closingTaskId: 'busy_helper' }] };
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(lead)!), JSON.stringify({
      kind: 'plan', dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
      summary: 'Declare the exact closing input for the original consumer.', ...proposal,
    }) + '\n');
    await cooperative.pulse();
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(state.cooperation!.proofRoutes).toEqual(proposal.proofRoutes);
    expect(taskVersion(node('goal_0').task)).toBe(targetDigest);
    expect(state.cooperation!.tasks.some(item => item.task.id === action.task.id)).toBe(false);
    expect(cooperative.current(action)).toBe(false);
    expect(interrupts.get(worker.id)).toHaveBeenCalledOnce();
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('rejects a base plan depending on a host exploration ID before changing the archive', async () => {
    const action = await claim(provers()[0]), proposal = plan();
    proposal.tasks.push(action.task);
    proposal.tasks = proposal.tasks.map(task => task.id === 'goal_0'
      ? { ...task, dependsOn: [...task.dependsOn, action.task.id] } : task);
    // The host ID is present, so parsing succeeds and the host boundary must reject its use as a premise.
    const parsed = parseCooperationPlan(problem, proposal), before = JSON.stringify(state.cooperation);
    await expect((cooperative as any).acceptPlan(parsed)).rejects.toThrow('math_plan_host_exploration_dependency');
    expect(JSON.stringify(state.cooperation)).toBe(before);
    expect(cooperative.current(action)).toBe(true);
  });

  it('keeps exploration context and its advisory work contract mandatory with zero optional allowance', async () => {
    const worker = provers()[0], action = await claim(worker), marker = node(action.task.id).capacityExploration!;
    const compile = vi.spyOn(contextCompiler, 'compileTaskContext');
    const context = directSolverModules.M4.build(problem,
      { ...state, cooperation: cooperative.contextState(action, worker) },
      { root: directory, worktree: worker.worktree, retrievalRoot: directory, environment: {},
        taskText: 'Investigate the assigned original-goal frontier.', assignment: action, maxOptionalContextBytes: 0 });
    const section = compile.mock.calls.at(-1)![0].mandatory?.find(item => item.id === 'capacity-exploration');
    expect(section).toMatchObject({ kind: 'assignment' });
    expect(section!.text).toContain(JSON.stringify(marker.targetTaskId));
    expect(section!.text).toContain(JSON.stringify(marker.focus));
    expect(section!.text).toContain('advisory only');
    expect(context.message).toContain(section!.text);
    expect(context.workContract).toMatchObject({ stage: 'capacity-exploration', acceptance: 'advisory-only',
      sourcePolicy: 'read-only', capacityExploration: { targetTaskId: marker.targetTaskId, focus: marker.focus } });
    expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'capacity-exploration', kind: 'assignment', required: true }));
    expect(context.manifest!.omitted).not.toContainEqual(expect.objectContaining({ id: 'capacity-exploration' }));
  });

  it('accepts a dispatched handoff rejection while a new target revision retires its host exploration', async () => {
    await startGeneralists();
    const worker = provers()[0], action = await claim(worker);
    const helper: CooperativeTask = { id: 'proposed_typed_bridge', kind: 'lemma',
      objective: 'Prove the exact proposed consumer interface.', theoremName: 'Tutorial.proposed_typed_bridge',
      proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const finding = JSON.stringify({ taskId: action.task.id, conclusion: 'supporting',
      summary: 'The spare-capacity investigation proposes an exact typed bridge.', lemmaRequests: [helper] });
    (cooperative as any).record(worker, action.task, 'research', 'advisory',
      'An exact typed bridge needs a Lead decision.', { finding, findingDigest: mathDigest(finding), lemmaRequests: [helper] });
    const handoff = pendingResearchHandoffs(state.cooperation!)[0];
    expect(handoff).toBeDefined();
    const lead = await startLead();
    expect(lead.handoffIds).toContain(handoff.id);
    const proposal = plan();
    proposal.tasks = proposal.tasks.map(task => task.id === 'busy_helper' ? { ...task, revision: task.revision + 1 } : task);
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(lead)!), JSON.stringify({
      kind: 'plan', dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
      summary: 'Revise the exact consumer and reject the obsolete candidate interface.', ...proposal,
      handoffDecisions: [{ id: handoff.id, status: 'rejected', reason: 'This proposed bridge does not close the revised consumer.' }],
    }) + '\n');
    await cooperative.pulse();
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(state.cooperation!.tasks.some(item => item.task.id === action.task.id)).toBe(false);
    expect(cooperative.current(action)).toBe(false);
    expect(state.cooperation!.researchDecisions).toContainEqual(expect.objectContaining({ id: handoff.id, status: 'rejected' }));
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('leaves ordinary research forbidden to a Prover even when a custom M5 returns it', async () => {
    vi.spyOn(directSolverModules.M5, 'assign').mockImplementation(ready => ready.find(item => item.task.kind === 'research'));
    await expect(track(cooperative.next(provers()[0], budget))).rejects.toThrow('math_task_assignment_invalid');
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    expect(node('planned_research_1').status).toBe('pending');
  });

  it('honors a custom M5 deferring already ready work without an automatic retry loop', async () => {
    const assign = vi.spyOn(directSolverModules.M5, 'assign').mockImplementation(() => {
      if (assign.mock.calls.length > 8) throw new Error('fixture_scheduler_busy_loop');
      return undefined;
    });
    const { waiting } = await waitForCapacity(workers[1]);
    expect(assign).toHaveBeenCalledOnce();
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    expect(node('planned_research_1').status).toBe('pending');
    assign.mockRestore();
    refresh();
    expect(taskAction(await waiting).task.id).toBe('planned_research_1');
  });

  it('enforces an exploration owner at admission and prevents another Prover from claiming its saved assignment', async () => {
    const owner = provers()[0], other = provers()[1], action = await claim(owner), original = node(action.task.id);
    const attempts = original.attempts;
    expect(() => cooperative.started(other, action)).toThrow('math_task_assignment_invalid');
    expect(original.attempts).toBe(attempts);
    cooperative.deactivate(owner); cooperative.interrupted(owner, action);
    vi.spyOn(directSolverModules.M5, 'assign').mockReturnValue(original);
    await expect(track(cooperative.next(other, budget))).rejects.toThrow('math_task_assignment_invalid');
    expect(original.assignment).toBe(action.assignment);
    expect(original.task.ownerId).toBe(owner.id);
  });

  it('uses planned research before creating exploration for a Researcher', async () => {
    const worker = workers[1], planned = await claim(worker);
    expect(planned.task.id).toBe('planned_research_1');
    expect(overlays()).toHaveLength(0);
    await complete(worker, planned);
    const exploration = await claim(worker);
    expect(node(exploration.task.id).capacityExploration).toBeDefined();
    expect(exploration.task.ownerId).toBe(worker.id);
  });

  it('persists completed input/method tombstones and does not repeat them after process restore', async () => {
    const mathematicalInput = snapshot();
    const actions = await Promise.all(provers().map(claim));
    for (const [index, action] of actions.entries()) await complete(provers()[index], action);
    const ledger = structuredClone(state.cooperation!.capacityExplorationInputs), ids = overlays().map(item => item.task.id);
    expect(snapshot()).toEqual(mathematicalInput);
    await waitForCapacity(provers()[0]);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    await restart();
    await waitForCapacity(provers()[0]);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(overlays().map(item => item.task.id)).toEqual(ids);
    expect(overlays().every(item => item.status === 'completed')).toBe(true);
    expect(events.filter(item => item.event === 'capacity_exploration_requested')).toHaveLength(4);
  });

  it('turns exhausted discovery into one explicit typed-decomposition assessment instead of more research', async () => {
    await startGeneralists();
    const actions = await Promise.all(provers().map(claim));
    await complete(provers()[0], actions[0]);
    expect((cooperative as any).stagnationRecovery()).toBeUndefined();
    for (const [index, action] of actions.entries()) if (index) await complete(provers()[index], action);
    const ledger = structuredClone(state.cooperation!.capacityExplorationInputs);
    const busyAssignment = node('busy_helper').assignment;
    const lead = await startLead();
    expect(lead.stagnationRecovery).toMatchObject({ taskIds: ['busy_helper'], reason: 'frontier-not-decomposed' });
    const receipt = structuredClone(lead.stagnationRecovery);
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify({ kind: 'assessment',
      dispatchNonce: lead.planNonce, baseVersion: lead.planVersion,
      assessments: ([['capacity', lead.capacityRefill], ['stagnation', lead.stagnationRecovery]] as const)
        .flatMap(([kind, request]) => request ? [{ kind, requestId: request.requestId, inputDigest: request.inputDigest,
          outcome: 'no-independent-work',
          reason: 'The four completed investigations have not identified a closed helper for the remaining busy_helper proof.' }] : []),
    }));
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], lead, commitSolverSources(problem, workers[0].worktree));
    expect(state.cooperation!.lastStagnationRecovery).toMatchObject({ ...receipt, status: 'assessed', outcome: 'no-independent-work' });
    expect((cooperative as any).stagnationRecovery()).toBeUndefined();
    await waitForCapacity(provers()[0]);
    expect(overlays()).toHaveLength(4);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(node('busy_helper').status).toBe('running');
    expect(node('busy_helper').assignment).toBe(busyAssignment);
    expect(interrupts.get('engineer')).not.toHaveBeenCalled();
    expect(events.filter(item => item.event === 'stagnation_recovery_requested')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_exploration_requested')).toHaveLength(4);
    expect(state.cooperation!.blockers ?? []).toEqual([]);
  });

  it('resumes a running exploration with its original assignment rather than spending another method tombstone', async () => {
    const worker = provers()[0], first = await claim(worker), assignment = structuredClone(first.assignment);
    const metadata = structuredClone(node(first.task.id).capacityExploration), ledger = structuredClone(state.cooperation!.capacityExplorationInputs);
    await restart();
    const restored = node(first.task.id);
    expect(restored.status).toBe('pending');
    expect(restored.assignment).toEqual(assignment);
    const resumed = await claim(worker);
    expect(resumed.task.id).toBe(first.task.id);
    expect(resumed.assignment).toBe(restored.assignment);
    expect(resumed.assignment).toEqual(assignment);
    expect(restored.capacityExploration).toEqual(metadata);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(events.filter(item => item.event === 'capacity_exploration_requested')).toHaveLength(1);
  });

  it.each([
    { name: 'finite turns', maxTurns: 20, remainingMs: Infinity, continuous: true, workerCount: 8 },
    { name: 'finite time', maxTurns: Infinity, remainingMs: 10_000, continuous: true, workerCount: 8 },
    { name: 'bounded campaign', maxTurns: Infinity, remainingMs: Infinity, continuous: false, workerCount: 8 },
    { name: 'four workers', maxTurns: Infinity, remainingMs: Infinity, continuous: true, workerCount: 4 },
  ])('does not create optional work for $name', async scenario => {
    const selected = scenario.workerCount === 4 ? [workers[0], workers[1], provers()[0], workers.at(-1)!] : workers;
    cooperative = create({ workers: selected, continuousResearch: scenario.continuous });
    await waitForCapacity(provers()[0], scenario);
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
  });

  it('waits for a group slot and only records a method when the slot becomes available', async () => {
    const route = state.cooperation!.groups![0];
    route.group = { ...route.group, maxConcurrent: 1 }; refresh();
    const { waiting } = await waitForCapacity(provers()[0]);
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    route.group = { ...route.group, maxConcurrent: 7 }; refresh();
    const action = taskAction(await waiting);
    expect(node(action.task.id).capacityExploration).toBeDefined();
    expect(state.cooperation!.capacityExplorationInputs).toHaveLength(1);
  });

  it('does not consume exploration capacity while model dispatch is cooling down', async () => {
    modelAllowed = false;
    expect(await track(cooperative.next(provers()[0], budget))).toBeUndefined();
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    modelAllowed = true; cooperative.modelBudgetChanged();
    expect(node((await claim(provers()[0])).task.id).capacityExploration).toBeDefined();
  });

  it('waits through worker recovery and creates exploration only after that worker is eligible again', async () => {
    const worker = provers()[0], saved = state.workers!.find(record => record.id === worker.id)!;
    saved.recovery = { phase: 'cooling-down', reason: 'fixture provider cooldown', cycles: 1,
      startedAt: Date.now(), nextRetryAt: Date.now() + 10_000, waitedMs: 0 };
    const { waiting } = await waitForCapacity(worker);
    expect(overlays()).toHaveLength(0);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    saved.recovery = undefined; refresh();
    expect(node(taskAction(await waiting).task.id).capacityExploration).toBeDefined();
  });

  it.each(['paused', 'stopped'] as const)('retains a %s host exploration as controlled work without reviving or redispatching its method', async status => {
    const actions = await Promise.all(provers().map(claim));
    const worker = provers()[0], action = actions[0], original = node(action.task.id);
    const marker = original.capacityExploration, assignment = original.assignment;
    const ledger = structuredClone(state.cooperation!.capacityExplorationInputs), before = snapshot();
    const proposal = plan();
    proposal.tasks.push({ ...action.task, status });
    await (cooperative as any).acceptPlan(parseCooperationPlan(problem, proposal));
    const matching = state.cooperation!.tasks.filter(item => item.task.id === action.task.id);
    expect(matching).toHaveLength(1);
    expect(matching[0]).toBe(original);
    expect(original.task.status).toBe(status);
    expect(original.capacityExploration).toBe(marker);
    expect(original.assignment).toBe(assignment);
    expect(cooperative.current(action)).toBe(false);
    expect(cooperative.started(worker, action)).toBe(false);
    expect(interrupts.get(worker.id)).toHaveBeenCalledOnce();
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(snapshot()).toEqual(before);
    expect(state.cooperation!.error).toBeUndefined();
    for (const other of actions.slice(1)) expect(cooperative.current(other)).toBe(true);
    cooperative.deactivate(worker);
    await waitForCapacity(worker);
    expect(overlays()).toHaveLength(4);
    expect(node(action.task.id).task.status).toBe(status);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(ledger);
    expect(events.filter(item => item.event === 'capacity_exploration_requested')).toHaveLength(4);
  });

  it('yields a running exploration for an owned typed task even when its current group slot is full', async () => {
    const worker = provers()[0], action = await claim(worker), route = state.cooperation!.groups![0];
    route.group = { ...route.group, maxConcurrent: route.busy }; refresh();
    expect(cooperative.shouldYieldCapacityExploration(worker, action)).toBe(false);
    const typed: TaskRecord = { task: { id: 'ready_typed_step', kind: 'lemma', ownerId: worker.id,
      objective: 'Prove the exact newly available interface.', proofPath: 'Submission.lean',
      theoremName: 'Tutorial.ready_typed_step', type: 'True', dependsOn: [], revision: 0 }, status: 'pending', attempts: 0 };
    state.cooperation!.tasks.push(typed); refresh();
    expect(cooperative.shouldYieldCapacityExploration(worker, action)).toBe(true);
    typed.task = { ...typed.task, ownerId: provers()[1].id }; refresh();
    expect(cooperative.shouldYieldCapacityExploration(worker, action)).toBe(false);
  });
});
