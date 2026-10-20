import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { readSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { pendingResearchHandoffs, researchHandoffs } from '../src/solver/researchHandoffs';
import { pendingResearchChallenges, researchChallenges } from '../src/solver/researchChallenges';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import { buildTheoremKnowledge } from '../src/solver/theoremKnowledge';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const verified = (request: MathematicsVerifierBatchRequest) => verifiedBatch(request, { sessionId: 'deferred-handoff-fixture' });

type PlanningAction = Extract<CooperativeAction, { kind: 'lead' | 'assemble' | 'solve' }>;
const budget = { maxTurns: Infinity, remainingMs: Infinity };

describe('deferred research proposal activation', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let lead: ResearchWorker, peer: ResearchWorker, cooperative: CooperativeResearch, primaryLed: boolean;
  let proposal: CooperativeTask;
  let knowledgeSnapshot: KnowledgeContextSnapshot | undefined;
  let events: { event: string; details?: Record<string, unknown> }[];
  const instances: CooperativeResearch[] = [];
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const handoff = () => researchHandoffs(state.cooperation!)[0];
  const tasks = () => state.cooperation!.tasks.map(item => item.task);
  const notes = (value: unknown) => fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), JSON.stringify(value));
  const create = () => {
    const instance = cooperativeResearch({ state, workers: [lead, peer], retrievalRoot: directory,
      access: new Map([lead, peer].map(worker => [worker.id, { environment: {}, retrievalRoot: directory,
        ...(worker.id === peer.id && knowledgeSnapshot ? { knowledgeSnapshot } : {}) }])),
      modules: primaryLed ? { ...directSolverModules, M5: { ...directSolverModules.M5, primaryLed: true } } : directSolverModules,
      emit: (event, details) => events.push({ event, details }) });
    instances.push(instance); return instance;
  };
  const deliverLead = (action: CooperativeAction) => cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
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
    await deliverLead(action);
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
    await deliverLead(action);
  };
  const saveAndRead = () => {
    const file = path.join(directory, 'saved-state.json');
    fs.writeFileSync(file, JSON.stringify(state));
    return readSolverRunState(file);
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-deferred-handoffs-', 'lead');
    ({ directory, problem } = example);
    lead = leadWorker(problem, example.workspace); peer = peerWorker(example, 'researcher', { name: 'peer' });
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
    state = solverState(problem, example.workspace, { runId: 'deferred-handoff-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: plan.groups.map(group => ({ group, turns: 0 })),
        tasks: plan.tasks.map(task => ({ task, status: task.id === question.id ? 'completed' : 'pending', attempts: 0 })),
        deliveries: [{ id: 'proposal-delivery', producer: peer.id, taskId: question.id, taskDigest: taskVersion(question),
          kind: 'research', status: 'advisory', summary: 'An exact bridge waits on the estimate.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] }] } });
    primaryLed = false; knowledgeSnapshot = undefined; events = []; cooperative = create();
  });
  afterEach(async () => {
    for (const instance of instances.splice(0)) await instance.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['proof', 'statement-only', 'wrong-file', 'wrong-catalog', 'unknown-entry'] as const)
  ('records only checked proof references from pinned knowledge during actual helper delivery (%s)', async mode => {
    const base = buildTheoremKnowledge([{ name: 'Saved.bridge', file: 'Submission.lean', type: 'True',
      typeKind: 'closed-task-type', kind: 'lemma', description: 'A previously checked bridge.', premises: [],
      dependencies: { statement: [], proof: [], tasks: [], coverage: 'unavailable' },
      files: { 'Submission.lean': 'namespace Saved\nlemma bridge : True := by trivial\nend Saved\n' },
      provenance: { kind: 'solver-check', problemId: 'saved-problem', source: '/archive/state.json',
        sourceDigest: mathDigest('saved-proof-source'), receiptIds: ['saved-proof-receipt'] } }]);
    knowledgeSnapshot = { digest: mathDigest('fixed-knowledge-catalog'), base };
    cooperative = create();
    const action = await cooperative.next(peer, budget);
    if (action?.kind !== 'task' || action.task.id !== 'premise') throw new Error('fixture_expected_premise');
    expect(cooperative.started(peer, action)).toBe(true);
    const declaration = { name: 'Tutorial.saved_bridge', file: 'Submission.lean' };
    const claim = { id: mode === 'unknown-entry' ? 'f'.repeat(64) : base.entries[0]!.id,
      catalogDigest: mode === 'wrong-catalog' ? mathDigest('other-catalog') : knowledgeSnapshot.digest,
      declaration: { ...declaration, file: mode === 'wrong-file' ? 'Other.lean' : declaration.file } };
    const file = path.join(peer.worktree, problem.projectRelative, 'Submission.lean');
    const target = mode === 'statement-only'
      ? 'lemma premise : (fun (_ : True) => True) saved_bridge := by trivial'
      : 'lemma premise : True := by exact saved_bridge';
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero',
      `lemma saved_bridge : True := by trivial\n${target}\ntheorem add_zero`));
    fs.writeFileSync(path.join(peer.worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'Adapt the saved bridge as saved_bridge.',
      knowledgeUses: [claim] }));
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const result = verified(request);
      return { ...result, results: result.results.map(item => ({ ...item, declarationReferences: {
        statement: item.theoremName === 'Tutorial.premise' && mode === 'statement-only' ? [declaration] : [],
        proof: item.theoremName === 'Tutorial.premise' && mode !== 'statement-only' ? [declaration] : [],
      } })) };
    });
    const commit = commitSolverSources(problem, peer.worktree);
    const delivered = await cooperative.deliver(peer, action, commit);
    expect(delivered.check?.passed).toBe(true);
    expect(node('premise')).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    const proof = node('premise').proof!;
    expect(proof.commit).toBe(commit);
    expect(proof.verification.status).toBe('kernel_verified');
    expect(proof.verification.results.every(item => item.targetCommit === proof.verification.targetCommit)).toBe(true);
    expect(host.verify.mock.calls.some(([request]) => request.targetCommit === proof.verification.targetCommit)).toBe(true);
    // The integration consumes the checked identical projection without another Lean invocation.
    expect(host.verify).toHaveBeenCalledOnce();
    const record = state.cooperation!.deliveries!.find(item => item.taskId === 'premise' && item.kind === 'proof' && item.status === 'verified')!;
    expect(record.commit).toBe(commit);
    expect(record.evidence?.verification.results.every(item => item.receiptId)).toBe(true);
    if (mode === 'wrong-catalog' || mode === 'unknown-entry') {
      expect(record.knowledgeUses).toEqual([]);
      expect(events).toContainEqual({ event: 'knowledge_use_rejected', details: { taskId: 'premise', commit, rejected: 1 } });
    } else {
      const checked = mode === 'proof';
      expect(record.knowledgeUses).toEqual([{ ...claim, consumer: { taskId: 'premise', taskDigest: taskVersion(action.task) },
        status: checked ? 'checked-reference' : 'reported-attempt', attribution: 'model-reported-origin',
        ...(checked ? { checkedCommit: commit, checkedSourceDigest: node('premise').proof!.sourceDigest } : {}) }]);
      expect(events).toContainEqual({ event: 'knowledge_use_observed', details: {
        ...record.knowledgeUses![0], taskId: 'premise', commit } });
    }
    const restored = saveAndRead().cooperation!.deliveries!.find(item => item.id === record.id)!;
    expect(restored.knowledgeUses).toEqual(record.knowledgeUses);
    expect(state.cooperation!.error).toBeUndefined();
  });

  it.each([false, true])('requires and persists challenge decisions in a primary-led=%s dispatch', async primary => {
    const question = node('question');
    question.finding = JSON.stringify({ conclusion: 'refuted', needsDecision: true, summary: 'A fixed counterexample.' });
    state.cooperation!.deliveries = [{ ...state.cooperation!.deliveries![0], lemmaRequests: undefined,
      findingDigest: mathDigest(question.finding), summary: 'A fixed counterexample.', evidenceRefs: ['fixed-source'] }];
    primaryLed = primary; cooperative = create();
    const action = await cooperative.next(lead, budget);
    if (!action || action.kind !== (primary ? 'solve' : 'lead')) throw new Error('fixture_challenge_dispatch_required');
    const challenge = pendingResearchChallenges(state.cooperation!)[0];
    expect(action.challengeIds).toEqual([challenge.id]);
    expect(action.challengeActivations).toEqual({ [challenge.id]: challenge.activationDigest });
    notes(primary ? { requests: [] } : { tasks: tasks() });
    await deliverLead(action);
    expect(state.cooperation!.error).toContain('math_challenge_unresolved');
    expect(pendingResearchChallenges(state.cooperation!)).toHaveLength(1);
    const challengeDecisions = [{ id: challenge.id, status: 'disputed', reason: 'Its input violates the positivity premise.',
      evidenceRefs: ['counterargument-commit:RESEARCH.md'] }];
    notes(primary ? { requests: [], challengeDecisions } : { tasks: tasks(), challengeDecisions });
    await deliverLead(action);
    expect(state.cooperation!.error).toBeUndefined();
    expect(researchChallenges(state.cooperation!)[0]).toMatchObject({ status: 'disputed' });
    expect(saveAndRead().cooperation!.challengeDecisions).toEqual(state.cooperation!.challengeDecisions);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('reactivates the exact deferred bridge after an independent proof and adopts an unchecked obligation', async () => {
    const original = await defer();
    await proveNext();

    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites', decision: { status: 'deferred' } });
    expect(handoff().activationDigest).not.toBe(original.handoffActivations![handoff().id]);
    const action = await dispatch(), checks = host.verify.mock.calls.length;
    planResponse([], [...tasks(), proposal]);
    await deliverLead(action);

    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff().status).toBe('adopted');
    expect(node('bridge')).toMatchObject({ status: 'pending', attempts: 0 });
    expect(node('bridge').proof).toBeUndefined();
    expect(host.verify).toHaveBeenCalledTimes(checks);
    await cooperative.pulse(); await cooperative.pulse();
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(events.filter(item => item.event === 'research_handoff_decided')).toHaveLength(2);
  });

  it('defers and reactivates repeated deliveries once while retaining a durable decision for every source', async () => {
    const original = state.cooperation!.deliveries![0];
    state.cooperation!.deliveries!.push({ ...structuredClone(original), id: 'repeated-proposal-delivery', createdAt: 2 });
    expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
    expect(handoff().sources).toHaveLength(2);
    await defer();
    expect(state.cooperation!.researchDecisions).toHaveLength(2);
    await proveNext();
    expect(pendingResearchHandoffs(state.cooperation!)).toHaveLength(1);
    const action = await dispatch(), checks = host.verify.mock.calls.length;
    planResponse([], [...tasks(), proposal]);
    await deliverLead(action);
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toMatchObject([
      { deliveryId: original.id, status: 'adopted', taskId: proposal.id },
      { deliveryId: 'repeated-proposal-delivery', status: 'adopted', taskId: proposal.id },
    ]);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(node(proposal.id)).toMatchObject({ status: 'pending', attempts: 0 });
    expect(host.verify).toHaveBeenCalledTimes(checks);
  });

  it('resolves a Primary solve response under its original alias after a duplicate becomes the primary handoff', async () => {
    primaryLed = true; cooperative = create();
    const action = await dispatch(), originalId = action.handoffIds![0], original = state.cooperation!.deliveries![0];
    state.cooperation!.deliveries!.unshift({ ...structuredClone(original), id: 'earlier-proposal-delivery', createdAt: 0 });
    expect(handoff().id).not.toBe(originalId);
    expect(cooperative.current(action)).toBe(true);
    notes({ handoffDecisions: [{ id: originalId, status: 'rejected', reason: 'The exact interface does not close the gap.' }] });
    const before = structuredClone(tasks());
    await deliverLead(action);
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toMatchObject([
      { deliveryId: 'earlier-proposal-delivery', status: 'rejected' }, { deliveryId: original.id, status: 'rejected' },
    ]);
    expect(handoff().status).toBe('rejected');
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(tasks()).toEqual(before);
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('retains Primary waits expressed through an old alias and rejects that dispatch after the prerequisites reactivate it', async () => {
    primaryLed = true; cooperative = create();
    const original = await dispatch(), originalId = original.handoffIds![0], delivery = state.cooperation!.deliveries![0];
    state.cooperation!.deliveries!.unshift({ ...structuredClone(delivery), id: 'earlier-proposal-delivery', createdAt: 0 });
    planResponse([{ id: originalId, status: 'deferred', reason: 'Wait for the checked premise.', waitsOn: ['premise'] }]);
    await deliverLead(original);
    expect(state.cooperation!.error).toBeUndefined();
    expect(handoff().status).toBe('deferred');
    expect(node('question').status).toBe('completed');
    await proveNext();
    const previous = structuredClone(state.cooperation!.researchDecisions), checks = host.verify.mock.calls.length;
    expect(cooperative.current(original)).toBe(false);
    planResponse([{ id: originalId, status: 'rejected', reason: 'An outdated response.' }]);
    await deliverLead(original);
    expect(state.cooperation!.researchDecisions).toEqual(previous);
    expect(handoff()).toMatchObject({ status: 'pending', reopened: 'checked-prerequisites' });
    expect(events.some(item => item.event === 'research_handoff_superseded')).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(checks);
    await reject(await dispatch());
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.cooperation!.researchDecisions).toMatchObject([{ status: 'rejected' }, { status: 'rejected' }]);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
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

    await deliverLead(action);

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

    await deliverLead(action);

    expect(state.cooperation!.error).toContain('math_handoff_backlog_source_required:question');
    expect(tasks()).toEqual(before);
    expect(handoff().status).toBe('deferred');
    planResponse([{ id: handoff().id, status: 'rejected', reason: 'The route is deliberately abandoned.' }],
      tasks().filter(task => task.id !== 'question'));
    await deliverLead({ ...action, planVersion: state.cooperation!.planVersion });
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
    await deliverLead(ordinary);
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
    await deliverLead(action);
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
    await deliverLead(action);

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
