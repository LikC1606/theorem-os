import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { advisoryCheckpointScope } from '../src/solver/research';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

type Lead = Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>;
const lead = (fields: Partial<Lead> = {}): Lead => ({ kind: 'lead', seedCommit: 'seed-a', planVersion: 'graph-a',
  planNonce: 'nonce-a', planningInputDigest: 'operational-input-a',
  handoffIds: ['h2', 'h1'], handoffActivations: { h1: 'ha', h2: 'hb' },
  challengeIds: ['c2', 'c1'], challengeActivations: { c1: 'ca', c2: 'cb' },
  capacityRefill: { inputDigest: 'capacity-a', workerIds: ['worker-a'], requestedAt: 1 }, ...fields });

describe('semantic advisory checkpoint inputs', () => {
  it('preserves the same scope across nonce, seed, status, allocation and inbox ordering changes', () => {
    const original = lead();
    const replay = lead({ planNonce: 'nonce-b', seedCommit: 'seed-b', planningInputDigest: 'operational-input-b',
      handoffIds: ['h1', 'h2', 'h1'], handoffActivations: { h2: 'hb', unshown: 'new', h1: 'ha' },
      challengeIds: ['c1', 'c2'], challengeActivations: { c2: 'cb', c1: 'ca', unshown: 'new' },
      capacityRefill: { inputDigest: 'capacity-a', workerIds: ['worker-b', 'worker-c'], requestedAt: 999 } });
    expect(advisoryCheckpointScope(replay)).toBe(advisoryCheckpointScope(original));
  });

  it.each([
    ['handoff activation', { handoffActivations: { h1: 'new', h2: 'hb' } }],
    ['handoff identity', { handoffIds: ['h1', 'h3'], handoffActivations: { h1: 'ha', h3: 'hb' } }],
    ['challenge activation', { challengeActivations: { c1: 'new', c2: 'cb' } }],
    ['challenge identity', { challengeIds: ['c1', 'c3'], challengeActivations: { c1: 'ca', c3: 'cb' } }],
    ['capacity input', { capacityRefill: { inputDigest: 'capacity-b', workerIds: ['worker-a'], requestedAt: 1 } }],
    ['new base graph', { planVersion: 'graph-b' }],
    ['frontier recovery', { recovery: { id: 'recovery-a', taskIds: ['task'], goalIds: ['goal'] } }],
  ] as const)('gives new %s a fresh scope instead of inheriting unrelated backoff', (_label, change) => {
    expect(advisoryCheckpointScope(lead(change as Partial<Lead>))).not.toBe(advisoryCheckpointScope(lead()));
  });

  it('keeps recovery inputs stable when reordered but resets changed recovery contracts', () => {
    const original = lead({ recovery: { id: 'recovery-a', taskIds: ['a', 'b'], goalIds: ['x', 'y'] } });
    const same = lead({ planNonce: 'another-nonce', recovery: { id: 'recovery-a', taskIds: ['b', 'a', 'a'], goalIds: ['y', 'x'] } });
    expect(advisoryCheckpointScope(same)).toBe(advisoryCheckpointScope(original));
    for (const recovery of [
      { id: 'recovery-b', taskIds: ['a', 'b'], goalIds: ['x', 'y'] },
      { id: 'recovery-a', taskIds: ['a', 'c'], goalIds: ['x', 'y'] },
      { id: 'recovery-a', taskIds: ['a', 'b'], goalIds: ['x', 'z'] },
    ]) expect(advisoryCheckpointScope(lead({ recovery }))).not.toBe(advisoryCheckpointScope(original));
  });

  it('distinguishes initial planning without using the initial dispatch nonce', () => {
    const original = lead({ initialPlanNonce: 'initial-a' });
    expect(advisoryCheckpointScope(lead({ initialPlanNonce: 'initial-b' }))).toBe(advisoryCheckpointScope(original));
    expect(advisoryCheckpointScope(lead())).not.toBe(advisoryCheckpointScope(original));
  });

  it('keeps non-Lead research scoped to its exact task contract and excludes proof work', () => {
    const task: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find the missing construction.', dependsOn: [], revision: 0 };
    const assignment = { taskId: task.id, taskDigest: 'task-a', workerId: 'worker-a', seedCommit: 'seed-a', assignmentId: 'first' };
    const action: CooperativeAction = { kind: 'task', task, assignment };
    const original = advisoryCheckpointScope(action);
    expect(advisoryCheckpointScope({ ...action, assignment: { ...assignment, assignmentId: 'second', workerId: 'worker-b', seedCommit: 'seed-b' } })).toBe(original);
    expect(advisoryCheckpointScope({ ...action, assignment: { ...assignment, taskDigest: 'task-b' } })).not.toBe(original);
    expect(advisoryCheckpointScope({ ...action, task: { ...task, kind: 'lemma' } })).toBeUndefined();
    expect(advisoryCheckpointScope(undefined)).toBeUndefined();
  });
});

describe('Lead scheduling checkpoint control responses', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, workers: ResearchWorker[], state: SolverRunState;
  let cooperative: CooperativeResearch, controller: AbortController;
  let events: { event: string; details?: Record<string, unknown> }[];
  let proposal: CooperativeTask;
  const graph = () => ({ tasks: state.cooperation!.tasks.map(node => node.task),
    groups: state.cooperation!.groups!.map(route => route.group) });
  const notes = () => path.join(workers[0].worktree, 'RESEARCH.md');
  const write = (response: unknown) => fs.writeFileSync(notes(), '```math-plan\n' + JSON.stringify(response) + '\n```\n');
  const start = async (baseline?: string | null) => {
    if (baseline === null) fs.rmSync(notes(), { force: true });
    else if (baseline === undefined) write(graph());
    else fs.writeFileSync(notes(), baseline);
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !action.planNonce) throw new Error('fixture_expected_revision_dispatch');
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    return action;
  };
  const checkpoint = (action: Lead) => {
    const commit = commitSolverSources(problem, workers[0].worktree);
    cooperative.deactivate(workers[0]);
    return cooperative.deliver(workers[0], action, commit, true, 'scheduling-checkpoint');
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(() => { throw new Error('fixture_unexpected_proof_acceptance'); });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('lead-checkpoint-semantics-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'researcher')];
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find a bridge.', dependsOn: [], revision: 0 };
    proposal = { id: 'bridge', kind: 'lemma', objective: 'Prove the missing exact bridge.', theoremName: 'Tutorial.bridge',
      proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const parsed = parseCooperationPlan(problem, { tasks: [question, ...problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`, ...target,
    }))] });
    state = solverState(problem, example.workspace, { runId: 'lead-checkpoint-semantics', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'checking', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: parsed.tasks.map(task => ({ task, status: task.id === question.id ? 'completed' : 'pending', attempts: 0 })),
        groups: parsed.groups.map(group => ({ group, turns: 0 })),
        deliveries: [{ id: 'proposal-delivery', producer: workers[1].id, taskId: question.id, taskDigest: taskVersion(question),
          kind: 'research', status: 'advisory', summary: 'A typed bridge needs a Lead decision.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] }] } });
    events = []; controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }) });
  });
  afterEach(async () => {
    controller.abort(); await cooperative.stop();
    expect(host.verify).not.toHaveBeenCalled(); expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each([false, true])('preserves an unchanged control draft without rejecting or resolving its inbox (prose-only: %s)', async prose => {
    const action = await start(), before = structuredClone(state.cooperation!.tasks), base = state.cooperation!.planVersion;
    const pending = pendingResearchHandoffs(state.cooperation!).map(item => item.id);
    if (prose) fs.appendFileSync(notes(), '\nA still unfinished mathematical investigation.\n');
    await expect(checkpoint(action)).resolves.toEqual({ checkWhole: false });
    expect(events).toContainEqual(expect.objectContaining({ event: 'lead_checkpoint_saved',
      details: expect.objectContaining({ reason: 'unchanged-control-response' }) }));
    expect(events.some(item => item.event === 'plan_rejected' || item.event === 'plan_updated')).toBe(false);
    expect(state.cooperation!.tasks).toEqual(before);
    expect(state.cooperation!.planVersion).toBe(base);
    expect(state.cooperation!.researchDecisions).toBeUndefined();
    expect(pendingResearchHandoffs(state.cooperation!).map(item => item.id)).toEqual(pending);
    expect(fs.readFileSync(notes(), 'utf8')).toContain(prose ? 'unfinished mathematical' : 'math-plan');
  });

  it('accepts a new explicit handoff rejection even when the task graph is unchanged', async () => {
    const action = await start(), handoff = pendingResearchHandoffs(state.cooperation!)[0];
    write({ ...graph(), handoffDecisions: [{ id: handoff.id, status: 'rejected', reason: 'The proposed claim cannot supply the needed consumer.' }] });
    await checkpoint(action);
    expect(state.cooperation!.researchDecisions).toContainEqual(expect.objectContaining({ id: handoff.id, status: 'rejected' }));
    expect(events.some(item => item.event === 'lead_checkpoint_saved' || item.event === 'plan_rejected')).toBe(false);
  });

  it.each(['ordinary Markdown with no control response', null])('preserves an unchanged non-JSON draft: %s', async baseline => {
    const action = await start(baseline);
    await checkpoint(action);
    expect(events.some(item => item.event === 'lead_checkpoint_saved')).toBe(true);
    expect(events.some(item => item.event === 'plan_rejected')).toBe(false);
    expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
  });

  it('keeps initial dispatch response validation even if an existing graph is present', async () => {
    const action = await start();
    action.initialPlanNonce = 'initial-dispatch-with-bootstrap-graph';
    await checkpoint(action);
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_rejected',
      details: expect.objectContaining({ error: expect.stringContaining('math_handoff_unresolved:') }) }));
    expect(events.some(item => item.event === 'lead_checkpoint_saved')).toBe(false);
  });

  it.each(['final', 'request-failure', 'checkpoint'] as const)('still validates an inherited graph delivered as %s', async kind => {
    const action = await start(), commit = commitSolverSources(problem, workers[0].worktree);
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commit, kind !== 'final', kind === 'final' ? 'checkpoint' : kind);
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_rejected',
      details: expect.objectContaining({ error: expect.stringContaining('math_handoff_unresolved:') }) }));
    expect(events.some(item => item.event === 'lead_checkpoint_saved')).toBe(false);
    expect(state.cooperation!.researchDecisions).toBeUndefined();
  });

  it('accepts a changed complete checkpoint plan as a new unproved obligation', async () => {
    const action = await start();
    write({ ...graph(), tasks: [...graph().tasks, proposal] });
    await checkpoint(action);
    expect(state.cooperation!.tasks.find(node => node.task.id === proposal.id)).toMatchObject({ status: 'pending', task: proposal });
    expect(state.cooperation!.tasks.find(node => node.task.id === proposal.id)?.integratedCheck).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toContainEqual(expect.objectContaining({ status: 'adopted', taskId: proposal.id }));
    expect(events.some(item => item.event === 'lead_checkpoint_saved' || item.event === 'plan_rejected')).toBe(false);
  });

  it('keeps an already published graph when a checkpoint retains the inherited old notes', async () => {
    const action = await start(), inherited = fs.readFileSync(notes(), 'utf8');
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify({
      kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      ...graph(), tasks: [...graph().tasks, proposal],
    }) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.planPublication).toBeDefined();
    fs.writeFileSync(notes(), inherited);
    await checkpoint(action);
    expect(state.cooperation!.tasks.some(node => node.task.id === proposal.id)).toBe(true);
    expect(state.cooperation!.researchDecisions).toContainEqual(expect.objectContaining({ status: 'adopted', taskId: proposal.id }));
    expect(events.some(item => item.event === 'lead_checkpoint_saved' || item.event === 'plan_rejected')).toBe(false);
  });

  it('merges saved Lean sources despite an unchanged control block and still requests whole-proof checking', async () => {
    const action = await start(), file = path.join(workers[0].worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', 'lemma checkpoint_draft : True := by trivial\ntheorem add_zero'));
    await expect(checkpoint(action)).resolves.toEqual({ checkWhole: true });
    const canonical = state.cooperation!.canonicalCommit!;
    expect(committedSource(workers[0].worktree, canonical, `${problem.projectRelative}/Submission.lean`)).toContain('lemma checkpoint_draft : True');
    expect(events.some(item => item.event === 'lead_checkpoint_saved')).toBe(true);
    expect(events.some(item => item.event === 'plan_rejected')).toBe(false);
    expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });
});
