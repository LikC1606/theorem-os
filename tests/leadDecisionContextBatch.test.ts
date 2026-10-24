import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import type { SolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges, resolveResearchChallenges, selectResearchChallengeBatch } from '../src/solver/researchChallenges';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('bounded Lead inbox with complete finding references', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController;
  let events: { event: string; details?: Record<string, unknown> }[];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const nextLead = async () => {
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead') throw new Error('fixture_expected_lead');
    return action;
  };
  const contextFor = (action: CooperativeAction) => directSolverModules.M4.build(problem,
    { ...state, cooperation: cooperative.contextState(action, workers[0]),
      workers: workers.map(worker => ({ ...worker, phase: 'running', turns: 0 })) },
    { root: directory, worktree: workers[0].worktree, retrievalRoot: directory, environment: {},
      taskText: 'Prove the fixed original targets.', assignment: action, maxOptionalContextBytes: 0 });
  const challengesIn = (message: string) => JSON.parse(message.split(
    'Research challenges requiring a route decision (advisory, not proof acceptance):\n')[1]!.split('\n\n')[0]!);
  const publish = async (action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, response: unknown) => {
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify(response) + '\n');
    await cooperative.pulse();
  };

  beforeEach(() => {
    const example = localExample('lead-decision-batch-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'idle-prover', { role: 'prover' }),
      peerWorker(example, 'busy-prover', { role: 'prover' }), peerWorker(example, 'engineer', { role: 'engineer' })];
    const initial = parseCooperationPlan(problem, { tasks: [
      { id: 'busy_helper', kind: 'lemma', ownerId: workers[2].id, objective: 'Prove the unresolved uniform estimate.',
        proofPath: 'Submission.lean', theoremName: 'Tutorial.busy_helper', type: 'True' },
      { id: 'question', kind: 'research', objective: 'Check the estimate and identify smaller implementable steps.',
        dependsOn: ['busy_helper'] },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
        dependsOn: ['busy_helper'] })),
    ], groups: [{ id: 'main', objective: 'Prove the original targets.', engineerId: workers[3].id, maxConcurrent: 3 }] });
    const question = initial.tasks.find(task => task.id === 'question')!, helper = initial.tasks.find(task => task.id === 'busy_helper')!;
    const findings = [9 * 1024, 6 * 1024, 4 * 1024].map((size, index) => JSON.stringify({
      conclusion: 'inconclusive', needsDecision: true, summary: `Finding ${index} needs a concrete response.`,
      argument: `COMPLETE_ARGUMENT_${index}_` + '界'.repeat(Math.ceil(size / 3)),
    }));
    state = solverState(problem, example.workspace, { runId: 'lead-decision-batch-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: initial.tasks.map(task => ({ task, status: task.id === 'question' ? 'completed' : 'pending', attempts: 0 })),
        groups: initial.groups.map(group => ({ group, turns: 0 })),
        deliveries: findings.map((finding, index) => ({ id: `challenge-${index}`, producer: 'researcher',
          kind: 'research', status: 'advisory', taskId: question.id, taskDigest: taskVersion(question),
          finding, findingDigest: mathDigest(finding), summary: `Finding ${index} needs a concrete response.`,
          statement: '', premises: [], dependencies: [{ taskId: helper.id, taskDigest: taskVersion(helper) }],
          remainingObligations: [], evidenceRefs: [`fixed-notes-${index}`], commit: problem.baseCommit, createdAt: index + 1 })) } });
    events = []; controller = new AbortController();
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }),
      modules: { ...directSolverModules, M1: { ...directSolverModules.M1,
        open: () => { throw new Error('fixture_real_models_forbidden'); } } } });
    const busy = state.cooperation!.tasks.find(node => node.task.id === helper.id)!;
    busy.status = 'running';
    busy.assignment = { taskId: helper.id, taskDigest: taskVersion(helper), workerId: workers[2].id,
      seedCommit: problem.baseCommit, assignmentId: 'busy-estimate' };
    cooperative.activate(workers[2], { kind: 'task', task: helper, assignment: busy.assignment }, async () => {}, async () => {});
  });
  afterEach(async () => {
    controller.abort();
    await cooperative.stop();
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it('dispatches two medium findings and compiles the same compact identities with recoverable complete bodies', async () => {
    const pending = pendingResearchChallenges(state.cooperation!);
    // The previous 16 KiB inline threshold admitted only the oldest finding in this 12 KiB batch.
    expect(selectResearchChallengeBatch(state.cooperation!, { maxItems: 2, maxBytes: 12 * 1024 })).toEqual([pending[0]]);
    const action = await nextLead(), context = contextFor(action), shown = challengesIn(context.message);
    expect(action.coordination).toBe(true);
    expect(action.challengeIds).toEqual(pending.slice(0, 2).map(item => item.id));
    expect(action.challengeActivations).toEqual(Object.fromEntries(pending.slice(0, 2).map(item => [item.id, item.activationDigest])));
    expect(shown).toHaveLength(2);
    expect(Buffer.byteLength(JSON.stringify(shown))).toBeLessThan(12 * 1024);
    const archive = JSON.parse(fs.readFileSync(path.join(workers[0].worktree, 'COOPERATION.json'), 'utf8'));
    for (const [index, item] of shown.entries()) {
      const original = pending[index]!;
      expect(item).not.toHaveProperty('finding');
      expect(item).toMatchObject({ id: original.id, activationDigest: original.activationDigest,
        contextDigest: original.contextDigest, findingDigest: original.findingDigest,
        sourceTaskDigest: original.sourceTaskDigest, findingBytes: Buffer.byteLength(original.finding),
        findingSource: { file: 'COOPERATION.json', collection: 'researchChallenges', id: original.id,
          findingDigest: original.findingDigest } });
      const saved = archive[item.findingSource.collection].find((record: any) => record.id === item.findingSource.id);
      expect(saved.finding).toBe(original.finding);
      expect(mathDigest(saved.finding)).toBe(item.findingSource.findingDigest);
      expect(context.message).not.toContain(`COMPLETE_ARGUMENT_${index}_`);
    }
    expect(pendingResearchChallenges(state.cooperation!)).toEqual(pending);
    expect(context.message).toContain('"queuedForLater":1');
    expect(context.instructions).toContain('queuedForLater need not be zero');
    expect(context.instructions).toContain('Only a no-independent-work assessment must wait');
    expect(context.instructions).toContain('retrieve and verify the complete referenced finding');
  });

  it('preserves the ordinary planning threshold and complete inline finding bodies', async () => {
    const action = await nextLead();
    const context = contextFor({ ...action, coordination: undefined });
    const shown = challengesIn(context.message), pending = pendingResearchChallenges(state.cooperation!);
    expect(shown).toHaveLength(2);
    expect(shown.map((item: any) => item.finding)).toEqual(pending.slice(0, 2).map(item => item.finding));
    expect(shown.every((item: any) => item.findingSource === undefined)).toBe(true);
  });

  it('rejects decisions for unshown findings and no-work assessments while the inbox remains unresolved', async () => {
    const pending = pendingResearchChallenges(state.cooperation!), action = await nextLead();
    expect(action.capacityRefill).toBeDefined();
    expect(() => resolveResearchChallenges(state.cooperation!, action.challengeIds!, action.challengeActivations!,
      state.cooperation!.tasks.map(node => node.task), pending.map(item => ({ id: item.id, status: 'deferred',
        reason: 'A closed uniform construction is missing.', reopenOn: 'A checked uniform construction is available.' }))))
      .toThrow('math_challenge_decision_invalid');
    await publish(action, { kind: 'assessment', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      assessments: [{ kind: 'capacity', requestId: action.capacityRefill!.requestId,
        inputDigest: action.capacityRefill!.inputDigest, outcome: 'no-independent-work',
        reason: 'The uniform construction is not yet available.' }] });
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_publication_rejected',
      details: expect.objectContaining({ reason: 'math_plan_assessment_inbox_unresolved' }) }));
    expect(state.cooperation!.lastCapacityRefill!.status).toBe('requested');
    expect(pendingResearchChallenges(state.cooperation!)).toEqual(pending);
    expect(state.cooperation!.challengeDecisions).toBeUndefined();
  });

  it('accepts executable new work with shown decisions while retaining the unshown historical finding', async () => {
    const pending = pendingResearchChallenges(state.cooperation!), action = await nextLead();
    const helper: CooperativeTask = { id: 'ready_helper', kind: 'lemma', ownerId: workers[1].id,
      objective: 'Close the independent reflexive base case by exact True.intro; the uniform estimate consumes it.',
      proofPath: 'Submission.lean', theoremName: 'Tutorial.ready_helper', type: 'True', dependsOn: [], revision: 0 };
    await publish(action, { kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      tasks: [...state.cooperation!.tasks.map(node => node.task), helper],
      groups: state.cooperation!.groups!.map(group => group.group),
      challengeDecisions: action.challengeIds!.map(id => ({ id, status: 'deferred',
        reason: 'The general construction remains missing; the independent base case can proceed.',
        reopenOn: 'A uniform construction is supplied.' })) });
    expect(events.some(item => item.event === 'plan_publication_rejected')).toBe(false);
    expect(events.some(item => item.event === 'plan_published')).toBe(true);
    expect(state.cooperation!.tasks).toContainEqual(expect.objectContaining({ status: 'pending', task: helper }));
    expect(state.cooperation!.challengeDecisions).toHaveLength(2);
    expect(pendingResearchChallenges(state.cooperation!)).toEqual([pending[2]]);
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });
});
