import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import * as contextCompiler from '../src/solver/contextCompiler';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs, researchHandoffs } from '../src/solver/researchHandoffs';
import { validateLemmaRequests } from '../src/solver/taskProposals';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { integratedProof } from './helpers/taskProof';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

type PlanningAction = Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>;
const budget = { maxTurns: Infinity, remainingMs: Infinity };

describe('live explicit handoff publication', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch, proposal: CooperativeTask, interrupt: ReturnType<typeof vi.fn>;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let pending: Promise<unknown>[], events: { event: string; details?: Record<string, unknown> }[];
  let saveCheckpoint: ((current: SolverRunState) => void) | undefined;
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const inbox = () => pendingResearchHandoffs(state.cooperation!);
  const graph = () => ({ tasks: state.cooperation!.tasks.map(item => item.task),
    groups: state.cooperation!.groups!.map(item => item.group), proofRoutes: state.cooperation!.proofRoutes ?? [] });
  const snapshot = () => structuredClone({ ...graph(), records: state.cooperation!.tasks,
    decisions: state.cooperation!.researchDecisions, publication: state.cooperation!.planPublication });
  const create = () => {
    const controller = new AbortController(), current = state;
    const result = cooperativeResearch({ state: current, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => saveCheckpoint?.(current), emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative: result, controller }); return result;
  };
  const start = async () => {
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !action.planNonce) throw new Error('fixture_expected_handoff_publication_dispatch');
    expect(action.handoffIds?.length).toBeGreaterThan(0);
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, interrupt, async () => {});
    return action;
  };
  const file = (action: PlanningAction) => path.join(workers[0].worktree, leadPlanDeliveryFile(action)!);
  const event = (action: PlanningAction, handoffDecisions: unknown[] = [{ id: action.handoffIds![0], status: 'adopted' }],
    extra: Record<string, unknown> = {}) => ({ kind: 'handoff', dispatchNonce: action.planNonce,
    baseVersion: action.planVersion, handoffDecisions, ...extra });
  const publish = async (action: PlanningAction, value: unknown = event(action)) => {
    fs.appendFileSync(file(action), JSON.stringify(value) + '\n'); await cooperative.pulse();
  };
  const helper = (id: string): CooperativeTask => ({ ...proposal, id, theoremName: `Tutorial.${id}`, dependsOn: [] });
  const addProposal = (task: CooperativeTask) => state.cooperation!.deliveries!.push({
    ...structuredClone(state.cooperation!.deliveries![0]), id: `proposal-${task.id}`, createdAt: 2,
    lemmaRequests: [task],
  });
  const addExistingTasks = (...tasks: CooperativeTask[]) => {
    const plan = parseCooperationPlan(problem, { ...graph(), tasks: [...graph().tasks, ...tasks] });
    const records = new Map(state.cooperation!.tasks.map(item => [item.task.id, item]));
    state.cooperation!.tasks = plan.tasks.map(task => records.get(task.id) ?? { task, attempts: 0, status: 'pending' });
    state.cooperation!.planVersion = undefined; cooperative = create();
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(() => { throw new Error('fixture_unexpected_proof_check'); });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-handoff-publication-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'engineer', { role: 'engineer' }),
      peerWorker(example, 'prover', { role: 'prover' }), peerWorker(example, 'researcher')];
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find an exact bridge for the original goals.',
      dependsOn: [], revision: 0 };
    const premise: CooperativeTask = { id: 'premise', kind: 'lemma', objective: 'Prove a precise prerequisite.',
      theoremName: 'Tutorial.premise', proofPath: 'Submission.lean', type: 'True', status: 'paused', dependsOn: [], revision: 0 };
    proposal = { id: 'bridge', kind: 'lemma', objective: 'Prove the exact proposed bridge.',
      theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const plan = parseCooperationPlan(problem, { tasks: [question, premise, ...problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`, ...target,
    }))] });
    state = solverState(problem, example.workspace, { runId: 'handoff-publication-fixture', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'checking', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, attempts: 0, status: task.id === question.id ? 'completed' : 'pending' })),
        groups: plan.groups.map(group => ({ group, turns: 0 })),
        deliveries: [{ id: 'bridge-proposal', producer: workers[3].id, taskId: question.id, taskDigest: taskVersion(question),
          kind: 'research', status: 'advisory', summary: 'This exact bridge needs a Lead decision.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] }] } });
    instances = []; pending = []; events = []; saveCheckpoint = undefined; interrupt = vi.fn(async () => {});
    cooperative = create();
  });
  afterEach(async () => {
    saveCheckpoint = undefined;
    instances.forEach(instance => instance.controller.abort());
    await Promise.allSettled(pending);
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('dispatches the exact adopted typed obligation and preserves the publishing Lead and unrelated running assignment', async () => {
    const running = await cooperative.next(workers[1], budget);
    if (running?.kind !== 'task' || running.task.kind !== 'goal') throw new Error('fixture_expected_unrelated_goal');
    expect(cooperative.started(workers[1], running)).toBe(true);
    const peerInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[1], running, peerInterrupt, async () => {});
    const record = node(running.task.id), assignment = structuredClone(record.assignment);
    const action = await start(), original = structuredClone(action), originalGraph = structuredClone(graph());
    const waiting = cooperative.next(workers[2], budget); pending.push(waiting); void waiting.catch(() => {});
    await publish(action, event(action, [{ id: action.handoffIds![0], status: 'adopted', ownerId: workers[2].id }]));
    const adopted = await waiting;
    expect(adopted).toMatchObject({ kind: 'task', task: { ...proposal, ownerId: workers[2].id } });
    expect(node(proposal.id).task).toEqual({ ...proposal, ownerId: workers[2].id });
    expect(node(running.task.id)).toBe(record);
    expect(record.assignment).toEqual(assignment);
    expect(cooperative.current(running)).toBe(true); expect(cooperative.current(action)).toBe(true);
    expect(action).toEqual(original);
    expect(interrupt).not.toHaveBeenCalled(); expect(peerInterrupt).not.toHaveBeenCalled();
    expect(graph().tasks.filter(task => task.id !== proposal.id)).toEqual(originalGraph.tasks);
    expect(graph().groups).toEqual(originalGraph.groups); expect(graph().proofRoutes).toEqual(originalGraph.proofRoutes);
    expect(state.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce, baseVersion: action.planVersion });
    expect(researchHandoffs(state.cooperation!)[0].status).toBe('adopted');
    expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
    expect(state.check).toBeUndefined();
  });

  it('adopts all explicitly selected sibling obligations with their original dependency interfaces', async () => {
    const next = { ...helper('second_bridge'), dependsOn: [proposal.id] };
    state.cooperation!.deliveries![0].lemmaRequests = [proposal, next];
    const action = await start();
    expect(action.handoffIds).toHaveLength(2);
    await publish(action, event(action, action.handoffIds!.map(id => ({ id, status: 'adopted' }))));
    expect(node(proposal.id)).toMatchObject({ task: proposal, status: 'pending', attempts: 0 });
    expect(node(next.id)).toMatchObject({ task: next, status: 'pending', attempts: 0 });
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(state.cooperation!.researchDecisions).toHaveLength(2);
    expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
  });

  it('retains an existing alternative proof route and all its original task contracts during adoption', async () => {
    const prerequisite = { ...helper('route_input'), status: 'paused' as const };
    const closing = { ...helper('route_closer'), dependsOn: [prerequisite.id], status: 'paused' as const };
    const plan = parseCooperationPlan(problem, { ...graph(), tasks: [...graph().tasks, prerequisite, closing],
      proofRoutes: [{ id: 'existing_route', targetTaskId: 'goal_1', prerequisiteTaskIds: [prerequisite.id], closingTaskId: closing.id }] });
    const records = new Map(state.cooperation!.tasks.map(item => [item.task.id, item]));
    state.cooperation!.tasks = plan.tasks.map(task => records.get(task.id) ?? { task, attempts: 0, status: 'pending' });
    state.cooperation!.proofRoutes = plan.proofRoutes; state.cooperation!.planVersion = undefined;
    cooperative = create();
    const action = await start(), before = structuredClone(graph());
    expect(before.proofRoutes).toHaveLength(1);
    await publish(action);
    expect(graph().proofRoutes).toEqual(before.proofRoutes);
    expect(graph().groups).toEqual(before.groups);
    expect(graph().tasks.filter(task => task.id !== proposal.id)).toEqual(before.tasks);
    expect(node('goal_1').alternativeRoutes).toEqual(before.proofRoutes);
    expect(node('bridge')).toMatchObject({ task: proposal, status: 'pending' });
  });

  it('keeps the exact short publication protocol and shown inbox mandatory with zero optional context allowance', async () => {
    addProposal(helper('second_bridge'));
    const action = await start(), compile = vi.spyOn(contextCompiler, 'compileTaskContext');
    const context = directSolverModules.M4.build(problem,
      { ...state, cooperation: cooperative.contextState(action, workers[0]) },
      { root: directory, worktree: workers[0].worktree, retrievalRoot: directory, environment: {},
        taskText: 'Decide the shown exact mathematical handoffs.', assignment: action, maxOptionalContextBytes: 0 });
    const section = compile.mock.calls.at(-1)![0].mandatory?.find(item => item.id === 'handoff-publication');
    expect(section).toMatchObject({ kind: 'assignment' });
    expect(section!.text).toContain(leadPlanDeliveryFile(action));
    expect(section!.text).toContain(JSON.stringify({ kind: 'handoff', dispatchNonce: action.planNonce,
      baseVersion: action.planVersion, handoffDecisions: [{ id: action.handoffIds![0], status: 'adopted' }] }));
    expect(section!.text).toContain(JSON.stringify(action.handoffIds));
    expect(section!.text).toContain('pending proof work');
    expect(context.message).toContain(section!.text); expect(context.instructions).toContain(section!.text);
    expect(context.message).toContain(proposal.type);
    expect(context.manifest).toMatchObject({ maxOptionalBytes: 0, optionalBytes: 0 });
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'handoff-publication', required: true }));
    expect(context.manifest!.omitted).not.toContainEqual(expect.objectContaining({ id: 'handoff-publication' }));
  });

  it.each(['rejected', 'deferred'] as const)('records a %s decision without rewriting the graph or accepting any proof', async status => {
    const action = await start(), before = structuredClone(graph());
    const reason = 'This interface needs the exact prerequisite before it can close the goal.';
    await publish(action, event(action, [{ id: action.handoffIds![0], status, reason,
      ...(status === 'deferred' ? { waitsOn: ['premise'] } : {}) }]));
    expect(graph()).toEqual(before);
    expect(state.cooperation!.researchDecisions).toMatchObject([{ id: action.handoffIds![0], status, reason,
      ...(status === 'deferred' ? { waitsOn: [{ taskId: 'premise', taskDigest: taskVersion(node('premise').task) }] } : {}) }]);
    expect(researchHandoffs(state.cooperation!)[0].status).toBe(status);
    expect(inbox()).toEqual([]); expect(cooperative.current(action)).toBe(true);
    expect(state.check).toBeUndefined();
  });

  it('atomically mixes exact adoption, rejection and a version-bound deferral in one displayed batch', async () => {
    const rejected = helper('rejected_bridge'), deferred = helper('deferred_bridge');
    state.cooperation!.deliveries![0].lemmaRequests = [proposal, rejected, deferred];
    const action = await start(), shown = new Map(inbox().map(item => [item.proposal.id, item.id]));
    const before = structuredClone(graph());
    await publish(action, event(action, [{ id: shown.get(proposal.id), status: 'adopted', ownerId: workers[2].id },
      { id: shown.get(rejected.id), status: 'rejected', reason: 'Its bound cannot close the original goal.' },
      { id: shown.get(deferred.id), status: 'deferred', reason: 'The prerequisite is still unproved.', waitsOn: ['premise'] }]));
    expect(node(proposal.id)).toMatchObject({ task: { ...proposal, ownerId: workers[2].id }, status: 'pending' });
    expect(node(rejected.id)).toBeUndefined(); expect(node(deferred.id)).toBeUndefined();
    expect(graph().tasks.filter(task => task.id !== proposal.id)).toEqual(before.tasks);
    expect(graph().groups).toEqual(before.groups); expect(graph().proofRoutes).toEqual(before.proofRoutes);
    expect(state.cooperation!.researchDecisions).toMatchObject([
      { id: shown.get(proposal.id), status: 'adopted', taskId: proposal.id },
      { id: shown.get(rejected.id), status: 'rejected' },
      { id: shown.get(deferred.id), status: 'deferred', waitsOn: [{ taskId: 'premise', taskDigest: taskVersion(node('premise').task) }] },
    ]);
    expect(inbox()).toEqual([]);
    expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
  });

  it.each(['unknown-writer', 'solver'] as const)('rejects unavailable proof owner %s without publishing or partially adopting', async ownerId => {
    const action = await start(), before = snapshot();
    await publish(action, event(action, [{ id: action.handoffIds![0], status: 'adopted', ownerId }]));
    expect(snapshot()).toEqual(before);
    expect(inbox()).toHaveLength(1); expect(node(proposal.id)).toBeUndefined();
    expect(events.filter(item => item.event === 'plan_publication_rejected')).toHaveLength(1);
  });

  it.each(['typed-conflict', 'ownership-override'] as const)
  ('rejects an existing target %s without changing its contract or owner', async mode => {
    const existing = { ...proposal, ownerId: workers[1].id, ...(mode === 'typed-conflict' ? { type: 'False' } : {}) };
    addExistingTasks(existing);
    const action = await start(), before = snapshot(), original = node(proposal.id);
    await publish(action, event(action, [{ id: action.handoffIds![0], status: 'adopted',
      ...(mode === 'ownership-override' ? { ownerId: workers[2].id } : {}) }]));
    expect(snapshot()).toEqual(before);
    expect(node(proposal.id)).toBe(original); expect(node(proposal.id).task).toEqual(existing);
    expect(inbox()).toHaveLength(1);
  });

  it.each([{ objective: 'Prove the bridge for the chosen route.' }, { sharing: 'problem' as const },
    { revision: 1 }, { dependsOn: ['premise'] }])
  ('adopts a valid late proposal when an earlier plan already scheduled the same proof target: %j', async change => {
    // The researcher publishes before the independent plan adds this target.
    [proposal] = validateLemmaRequests(problem, graph().tasks, graph().groups, node('question').task, [proposal]);
    state.cooperation!.deliveries![0].lemmaRequests = [proposal];
    const existing = { ...proposal, ...change, ownerId: workers[2].id };
    addExistingTasks(existing);
    const action = await start(), before = structuredClone(graph()), original = node(proposal.id);
    await publish(action, event(action, [{ id: action.handoffIds![0], status: 'adopted', ownerId: existing.ownerId }]));

    expect(researchHandoffs(state.cooperation!)[0]).toMatchObject({ status: 'adopted', decision: {
      taskId: existing.id, taskDigest: taskVersion(existing),
    } });
    expect(graph()).toEqual(before);
    expect(node(proposal.id)).toBe(original);
    expect(node(proposal.id)).toMatchObject({ task: existing, status: 'pending' });
    expect(events.filter(item => item.event === 'plan_publication_rejected')).toEqual([]);
  });

  it.each(['dispatchNonce', 'baseVersion'] as const)('rejects a wrong %s before changing the graph or recording a decision', async key => {
    const action = await start(), before = snapshot();
    await publish(action, event(action, undefined, { [key]: 'not-the-current-dispatch' }));
    expect(snapshot()).toEqual(before);
    expect(events.filter(item => item.event === 'plan_publication_rejected')).toHaveLength(1);
    await publish(action);
    expect(node(proposal.id)).toMatchObject({ status: 'pending' });
  });

  it('rejects an additional proposal that arrived after the immutable inbox was shown', async () => {
    const action = await start(); addProposal(helper('late_bridge'));
    const late = inbox().find(item => item.proposal.id === 'late_bridge')!, before = snapshot();
    expect(action.handoffIds).not.toContain(late.id);
    await publish(action, event(action, [...action.handoffIds!.map(id => ({ id, status: 'adopted' })),
      { id: late.id, status: 'adopted' }]));
    expect(snapshot()).toEqual(before);
    expect(inbox()).toHaveLength(2);
  });

  it('rejects the old dispatch after a deferred proposal reactivates under a fresh prerequisite receipt', async () => {
    const action = await start(), handoff = inbox()[0];
    state.cooperation!.researchDecisions = [{ id: handoff.id, deliveryId: handoff.deliveryId, status: 'deferred',
      reason: 'Wait for the precise prerequisite.', contextDigest: handoff.contextDigest,
      waitsOn: [{ taskId: 'premise', taskDigest: taskVersion(node('premise').task) }] }];
    // An independent mock kernel receipt changes the activation; the event itself performs no proof check.
    integratedProof(node('premise'), { sourceCommit: state.cooperation!.canonicalCommit, environmentDigest: state.environmentDigest });
    expect(inbox()[0]).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites' });
    expect(inbox()[0].activationDigest).not.toBe(action.handoffActivations![handoff.id]);
    const before = snapshot();
    await publish(action);
    expect(snapshot()).toEqual(before);
    expect(node(proposal.id)).toBeUndefined();
  });

  it.each(['tasks', 'groups', 'proofRoutes', 'altered-type'] as const)
  ('rejects %s supplied alongside a decision without extending or modifying the graph', async field => {
    const action = await start(), before = snapshot();
    const extra = field === 'altered-type' ? { handoffDecisions: [{ id: action.handoffIds![0], status: 'adopted',
      proposal: { ...proposal, type: 'False' } }] } : field === 'tasks'
      ? { tasks: [...graph().tasks, { ...proposal, type: 'False' }, helper('unshown_extension')] }
      : field === 'groups' ? { groups: graph().groups } : { proofRoutes: [] };
    await publish(action, event(action, undefined, extra));
    expect(snapshot()).toEqual(before);
    expect(inbox()).toHaveLength(1);
  });

  it('rejects every decision in a batch when one displayed pending handoff has no explicit decision', async () => {
    addProposal(helper('second_bridge'));
    const action = await start(), before = snapshot();
    expect(action.handoffIds).toHaveLength(2);
    await publish(action);
    expect(snapshot()).toEqual(before);
    expect(inbox()).toHaveLength(2);
    await publish(action, event(action, action.handoffIds!.map(id => ({ id, status: 'adopted' }))));
    expect(node('bridge')).toMatchObject({ status: 'pending' });
    expect(node('second_bridge')).toMatchObject({ status: 'pending' });
  });

  it('waits for a complete line and accepts only one immutable event shared with plan publication', async () => {
    const action = await start(), value = JSON.stringify(event(action));
    fs.appendFileSync(file(action), value); await cooperative.pulse();
    expect(state.cooperation!.planPublication).toBeUndefined(); expect(node('bridge')).toBeUndefined();
    fs.appendFileSync(file(action), '\n'); await cooperative.pulse();
    const accepted = snapshot();
    await publish(action);
    await publish(action, event(action, [{ id: action.handoffIds![0], status: 'rejected', reason: 'A later conflicting decision.' }]));
    await publish(action, { kind: 'plan', dispatchNonce: action.planNonce, baseVersion: state.cooperation!.planVersion,
      ...graph(), tasks: [...graph().tasks, helper('second_bridge')] });
    expect(snapshot()).toEqual(accepted);
    expect(node('second_bridge')).toBeUndefined();
    expect(events.filter(item => item.event === 'research_handoff_decided')).toHaveLength(1);
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
  });

  it('lets a human edit supersede the dispatch without resurrecting its proposed obligation', async () => {
    const action = await start();
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'human-chooses-next-step',
      baseVersion: state.cooperation!.planVersion, ...graph(), tasks: [...graph().tasks, helper('human_bridge')] }) + '\n');
    await publish(action);
    expect(state.cooperation!.edits![0].status).toBe('applied');
    expect(node('human_bridge')).toBeDefined(); expect(node('bridge')).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toBeUndefined();
    expect(cooperative.current(action)).toBe(false); expect(interrupt).toHaveBeenCalledOnce();
  });

  it('keeps an independently pending challenge and its exact source without requiring a simultaneous challenge decision', async () => {
    const source = node('question'), finding = JSON.stringify({ conclusion: 'refuted', needsDecision: true,
      summary: 'The estimate fails on the fixed counterexample.' });
    source.finding = finding;
    state.cooperation!.deliveries!.push({ ...structuredClone(state.cooperation!.deliveries![0]), id: 'counterexample-delivery',
      lemmaRequests: undefined, createdAt: 2, findingDigest: mathDigest(finding), evidenceRefs: ['counterexample:RESEARCH.md'] });
    const challenge = pendingResearchChallenges(state.cooperation!)[0], originalTask = structuredClone(source.task);
    const originalDelivery = structuredClone(state.cooperation!.deliveries![1]), action = await start();
    expect(action.challengeIds).toEqual([challenge.id]);
    await publish(action);
    expect(node('bridge')).toMatchObject({ status: 'pending' });
    expect(node('question').task).toEqual(originalTask);
    expect(state.cooperation!.deliveries![1]).toEqual(originalDelivery);
    expect(pendingResearchChallenges(state.cooperation!)).toEqual([challenge]);
    expect(state.cooperation!.challengeDecisions).toBeUndefined();
  });

  it('keeps the published obligation when inherited plan notes are delivered at the end of the same dispatch', async () => {
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(graph()) + '\n```');
    const action = await start(); await publish(action);
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(node('bridge')).toMatchObject({ task: proposal, status: 'pending', attempts: 0 });
    expect(node('bridge').proof).toBeUndefined(); expect(node('bridge').integratedCheck).toBeUndefined();
    expect(state.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce, finalized: true });
    expect(researchHandoffs(state.cooperation!)[0].status).toBe('adopted');
    expect(state.cooperation!.error).toBeUndefined(); expect(state.check).toBeUndefined();
  });

  it.each(['adopted', 'rejected'] as const)('restores the %s decision and graph together from the very first durable publication checkpoint', async status => {
    const action = await start(), original = instances[0], originalSource = structuredClone(node('question').task);
    const checkpointFile = path.join(directory, 'first-handoff-checkpoint.json');
    let firstCheckpoint: SolverRunState | undefined;
    saveCheckpoint = current => {
      if (!current.cooperation!.researchDecisions?.length) return;
      saveCheckpoint = undefined;
      firstCheckpoint = structuredClone(current);
      writeSolverRunState(checkpointFile, firstCheckpoint);
      throw new Error('fixture_process_lost_at_first_publication_checkpoint');
    };
    await Promise.allSettled([publish(action, event(action, [{ id: action.handoffIds![0], status,
      ...(status === 'rejected' ? { reason: 'The exact interface does not close the original goals.' } : {}) }]))]);
    expect(firstCheckpoint).toBeDefined();
    expect(firstCheckpoint!.cooperation!.researchDecisions).toMatchObject([{ id: action.handoffIds![0], status }]);
    expect(firstCheckpoint!.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce });
    expect(firstCheckpoint!.cooperation!.planPublication?.finalized).not.toBe(true);
    expect(firstCheckpoint!.cooperation!.tasks.some(item => item.task.id === proposal.id)).toBe(status === 'adopted');
    original.controller.abort(); await original.cooperative.stop();
    state = readSolverRunState(checkpointFile);
    const restored = create(); await restored.restore();
    expect(state.cooperation!.researchDecisions).toEqual(firstCheckpoint!.cooperation!.researchDecisions);
    expect(state.cooperation!.planPublication).toEqual(firstCheckpoint!.cooperation!.planPublication);
    expect(researchHandoffs(state.cooperation!)[0].status).toBe(status);
    expect(node('question').task).toEqual(originalSource);
    expect(node('bridge')?.status).toBe(status === 'adopted' ? 'pending' : undefined);
    expect(restored.current(action)).toBe(false);
    expect(state.cooperation!.tasks.every(item => !item.proof && !item.integratedCheck)).toBe(true);
    expect(state.cooperation!.error).toBeUndefined(); expect(state.check).toBeUndefined();
  });
});
