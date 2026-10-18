import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch, parseCooperationPlan } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { pendingResearchHandoffs, researchHandoffs } from '../src/solver/researchHandoffs';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'deferred-handoff-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

type PlanningAction = Extract<CooperativeAction, { kind: 'lead' | 'assemble' | 'solve' }>;
const budget = { maxTurns: Infinity, remainingMs: Infinity };

describe('deferred research proposal activation', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let lead: ResearchWorker, peer: ResearchWorker, cooperative: CooperativeResearch, primaryLed: boolean;
  let proposal: CooperativeTask;
  let events: { event: string; details?: Record<string, unknown> }[];
  const instances: CooperativeResearch[] = [];
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const handoff = () => researchHandoffs(state.cooperation!)[0];
  const tasks = () => state.cooperation!.tasks.map(item => item.task);
  const notes = (value: unknown) => fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), JSON.stringify(value));
  const create = () => {
    const instance = new CooperativeResearch({ state, workers: [lead, peer],
      access: new Map([lead, peer].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      modules: primaryLed ? { ...directSolverModules, M5: { ...directSolverModules.M5, primaryLed: true } } : directSolverModules,
      signal: new AbortController().signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      exclusiveCheck: async check => check() });
    instances.push(instance); return instance;
  };
  const planResponse = (handoffDecisions: unknown[], proposed = tasks(), requests?: CooperativeTask[]) => notes(primaryLed
    ? { requests: requests ?? proposed.filter(task => task.kind === 'lemma'), handoffDecisions }
    : { tasks: proposed, groups: state.cooperation!.groups!.map(record => record.group), handoffDecisions });
  const dispatch = async () => {
    const action = await cooperative.next(lead, budget);
    if (!action || action.kind !== (primaryLed ? 'solve' : 'lead')) throw new Error('fixture_expected_handoff_dispatch');
    expect(action.handoffIds).toEqual([handoff().id]);
    expect(action.handoffActivations).toEqual({ [handoff().id]: handoff().activationDigest });
    return action as PlanningAction;
  };
  const defer = async () => {
    const action = await dispatch();
    planResponse([{ id: handoff().id, status: 'deferred', reason: 'Wait for the precise checked premise.', waitsOn: ['premise'] }]);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff()).toMatchObject({ status: 'deferred', decision: { waitsOn: [{
      taskId: 'premise', taskDigest: taskVersion(node('premise').task),
    }] } });
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    return action;
  };
  const proveNext = async (id = 'premise') => {
    const action = await cooperative.next(peer, budget);
    if (action?.kind !== 'task') throw new Error('fixture_expected_proof_task');
    expect(action.task.id).toBe(id);
    expect(cooperative.started(peer, action)).toBe(true);
    const file = path.join(peer.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      `lemma ${id} : True := by trivial\ntheorem add_zero`));
    await cooperative.deliver(peer, action, commitSolverSources(problem, peer.worktree));
    expect(node(id)).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
  };
  const reject = async (action: PlanningAction) => {
    planResponse([{ id: handoff().id, status: 'rejected', reason: 'The estimate does not close the original goal.' }]);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
  };
  const saveAndRead = () => {
    const file = path.join(directory, 'saved-state.json');
    fs.writeFileSync(file, JSON.stringify(state));
    return readSolverRunState(file);
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-deferred-handoffs-')));
    const workspace = path.join(directory, 'lead'), receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const peerRoot = path.join(directory, 'peer');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', peerRoot, problem.baseCommit]);
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    peer = { ...lead, id: 'researcher', role: 'researcher', worktree: peerRoot };
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find the missing quantitative bridge.',
      dependsOn: [], revision: 0 };
    const premise: CooperativeTask = { id: 'premise', kind: 'lemma', objective: 'Prove the precise required estimate.',
      theoremName: 'Tutorial.premise', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    proposal = { id: 'bridge', kind: 'lemma', objective: 'Use the checked estimate to close the proof gap.',
      theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: ['premise'], revision: 0 };
    const plan = parseCooperationPlan(problem, { tasks: [question, premise, ...problem.targets.map((target, index) => ({
      id: `original_goal_${index + 1}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
      theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused',
    }))] });
    state = { schema: 'deepscientist.math.solver.v1', runId: 'deferred-handoff-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: plan.groups.map(group => ({ group, turns: 0 })),
        tasks: plan.tasks.map(task => ({ task, status: task.id === question.id ? 'completed' : 'pending', attempts: 0 })),
        deliveries: [{ id: 'proposal-delivery', producer: peer.id, taskId: question.id, taskDigest: taskVersion(question),
          kind: 'research', status: 'advisory', summary: 'An exact bridge waits on the estimate.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] }] } };
    primaryLed = false; events = []; cooperative = create();
  });
  afterEach(async () => {
    for (const instance of instances.splice(0)) await instance.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('reactivates the exact deferred bridge after an independent proof and adopts an unchecked obligation', async () => {
    const original = await defer();
    await proveNext();

    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites', decision: { status: 'deferred' } });
    expect(handoff().activationDigest).not.toBe(original.handoffActivations![handoff().id]);
    const action = await dispatch(), checks = host.verify.mock.calls.length;
    planResponse([], [...tasks(), proposal]);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));

    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff().status).toBe('adopted');
    expect(node('bridge')).toMatchObject({ status: 'pending', attempts: 0 });
    expect(node('bridge').proof).toBeUndefined();
    expect(host.verify).toHaveBeenCalledTimes(checks);
    await cooperative.pulse(); await cooperative.pulse();
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(events.filter(item => item.event === 'research_handoff_decided')).toHaveLength(2);
  });

  it('ignores unrelated checked progress and rejects a stale dispatch after the awaited proof passes', async () => {
    const unrelated = { ...node('premise').task, id: 'unrelated', theoremName: 'Tutorial.unrelated',
      objective: 'Check a separate fact.' };
    state.cooperation!.tasks.splice(1, 0, { task: unrelated, status: 'pending', attempts: 0 });
    const original = await defer();
    await proveNext('unrelated');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    await proveNext();

    await reject({ ...original, planVersion: state.cooperation!.planVersion });

    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites', decision: { status: 'deferred' } });
    expect(state.cooperation!.error).toBeUndefined();
    expect(events.some(item => item.event === 'lead_decision_superseded')).toBe(true);
    const current = await dispatch(); await reject(current);
    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff().status).toBe('rejected');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
  });

  it('rechecks restored JSON receipts before waking once, then preserves the completed decision across another restore', async () => {
    await defer(); await proveNext();
    state = saveAndRead();
    expect(handoff().status).toBe('deferred');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    const checks = host.verify.mock.calls.length;
    cooperative = create(); await cooperative.restore();

    expect(host.verify.mock.calls.length).toBeGreaterThan(checks);
    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites' });
    await reject(await dispatch());
    expect(handoff().status).toBe('rejected');
    state = saveAndRead(); cooperative = create(); await cooperative.restore();
    expect(handoff().status).toBe('rejected');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(events.filter(item => item.event === 'research_handoff_decided')).toHaveLength(2);
  });

  it('does not allow the same already accepted prerequisite to start another deferral cycle', async () => {
    await defer(); await proveNext();
    const previous = structuredClone(state.cooperation!.researchDecisions);
    const action = await dispatch();
    planResponse([{ id: handoff().id, status: 'deferred', reason: 'Wait for the same premise again.', waitsOn: ['premise'] }]);

    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));

    expect(state.cooperation!.error).toContain('math_handoff_waits_on_satisfied');
    expect(state.cooperation!.researchDecisions).toEqual(previous);
    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites' });
    await reject(await dispatch());
    expect(handoff().status).toBe('rejected');
  });

  it('keeps a deferred source and its exact waiting contract until an explicit cancellation', async () => {
    await defer();
    const before = structuredClone(tasks());
    const action: PlanningAction = { kind: 'lead', seedCommit: state.cooperation!.canonicalCommit!,
      planVersion: state.cooperation!.planVersion, handoffIds: [], handoffActivations: {} };
    planResponse([], tasks().filter(task => task.id !== 'question'));

    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));

    expect(state.cooperation!.error).toContain('math_handoff_backlog_source_required:question');
    expect(tasks()).toEqual(before);
    expect(handoff().status).toBe('deferred');
    planResponse([{ id: handoff().id, status: 'rejected', reason: 'The route is deliberately abandoned.' }],
      tasks().filter(task => task.id !== 'question'));
    await cooperative.deliver(lead, { ...action, planVersion: state.cooperation!.planVersion },
      commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBeUndefined();
    expect(tasks().some(task => task.id === 'question')).toBe(false);
    expect(state.cooperation!.researchDecisions).toMatchObject([{ status: 'rejected' }]);
  });

  it('preserves waiting research through Primary help edits and parses an identical adopted request in a new activation', async () => {
    primaryLed = true; cooperative = create();
    await defer();
    expect(node('question').status).toBe('completed');
    expect(node('premise').status).toBe('pending');
    const oldActivation = handoff().activationDigest;
    planResponse([], tasks(), [proposal]);
    const sameNotes = fs.readFileSync(path.join(lead.worktree, 'RESEARCH.md'), 'utf8');
    const ordinary: PlanningAction = { kind: 'solve', seedCommit: state.cooperation!.canonicalCommit!,
      handoffIds: [], handoffActivations: {} };
    await cooperative.deliver(lead, ordinary, commitSolverSources(problem, lead.worktree));
    await cooperative.pulse();
    expect(node('question').status).toBe('completed');
    expect(node('premise').status).toBe('pending');
    expect(node('bridge').status).toBe('pending');
    expect(handoff().status).toBe('deferred');
    await proveNext();

    const action = await dispatch();
    const acceptedHelp = events.filter(item => item.event === 'help_requested').length;
    expect(handoff().activationDigest).toBe(oldActivation);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), sameNotes);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toMatchObject([{ status: 'adopted', taskId: 'bridge' }]);
    expect(events.filter(item => item.event === 'help_requested')).toHaveLength(acceptedHelp + 1);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(node('bridge').status).toBe('pending');
    expect(node('premise').status).toBe('integrated');
  });

  it.each(['none', 'source', 'proposal', 'delivery'] as const)
  ('updates Primary waits without retaining an obsolete premise unless referenced by %s', async reference => {
    proposal = { ...proposal, dependsOn: reference === 'proposal' ? ['premise'] : [] };
    const delivery = state.cooperation!.deliveries![0];
    delivery.lemmaRequests = [proposal];
    if (reference === 'source') {
      node('question').task = { ...node('question').task, dependsOn: ['premise'] };
      delivery.taskDigest = taskVersion(node('question').task);
    }
    if (reference === 'delivery') delivery.dependencies = [{
      taskId: 'premise', taskDigest: taskVersion(node('premise').task),
    }];
    primaryLed = true; cooperative = create();
    await defer();
    const replacement = { ...node('premise').task, id: 'replacement', theoremName: 'Tutorial.replacement',
      objective: 'Prove the replacement estimate.' };
    const action = await cooperative.next(lead, budget);
    if (action?.kind !== 'solve') throw new Error('fixture_expected_primary_dispatch');
    expect(action.handoffIds).toEqual([]);
    cooperative.activate(lead, action, async () => {}, async () => {});
    planResponse([{ id: handoff().id, status: 'deferred', reason: 'Use the replacement estimate.', waitsOn: ['replacement'] }],
      tasks(), [replacement]);

    await cooperative.pulse();
    cooperative.deactivate(lead);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));

    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff()).toMatchObject({ status: 'deferred', decision: { waitsOn: [{
      taskId: replacement.id, taskDigest: taskVersion(replacement),
    }] } });
    expect(node('question').status).toBe('completed');
    expect(node('replacement').status).toBe('pending');
    expect(tasks().some(task => task.id === 'premise')).toBe(reference !== 'none');
    if (reference === 'none') {
      const proof = await cooperative.next(peer, budget);
      expect(proof).toMatchObject({ kind: 'task', task: { id: replacement.id } });
    } else expect(node('premise').status).toBe('pending');
    expect(host.verify).not.toHaveBeenCalled();
  });
});
