import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges, researchChallenges } from '../src/solver/researchChallenges';
import { pendingResearchHandoffs } from '../src/solver/researchHandoffs';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

describe('replacement plan checkpoint atomicity', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let saveCheckpoint: ((current: SolverRunState) => void) | undefined;
  let events: { event: string; details?: Record<string, unknown> }[];
  const create = () => {
    const controller = new AbortController(), current = state;
    const cooperative = cooperativeResearch({ state: current, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => saveCheckpoint?.(current), emit: (event, details) => events.push({ event, details }) });
    const instance = { cooperative, controller }; instances.push(instance); return instance;
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(() => { throw new Error('fixture_unexpected_proof_check'); });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-plan-atomicity-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'researcher')];
    const question: CooperativeTask = { id: 'question', kind: 'research', objective: 'Find a bridge for the original goals.',
      dependsOn: [], revision: 0 };
    const critique: CooperativeTask = { id: 'critique', kind: 'research', objective: 'Check the proposed estimate.',
      dependsOn: [], revision: 0 };
    const proposal: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the proposed bridge.',
      theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const finding = JSON.stringify({ conclusion: 'refuted', needsDecision: true, summary: 'The estimate has a counterexample.' });
    const plan = parseCooperationPlan(problem, { tasks: [question, critique, ...problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`, ...target,
    }))] });
    state = solverState(problem, example.workspace, { runId: 'plan-atomicity-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, attempts: 0,
          status: task.kind === 'research' ? 'completed' : 'pending', ...(task.id === critique.id ? { finding } : {}) })),
        groups: plan.groups.map(group => ({ group, turns: 0 })),
        deliveries: [{ id: 'bridge-proposal', producer: workers[1].id, taskId: question.id, taskDigest: taskVersion(question),
          kind: 'research', status: 'advisory', summary: 'A proposed bridge needs a Lead decision.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1, lemmaRequests: [proposal] },
        { id: 'estimate-critique', producer: workers[1].id, taskId: critique.id, taskDigest: taskVersion(critique),
          kind: 'research', status: 'advisory', summary: 'A fixed counterexample needs a Lead decision.', statement: '', premises: [],
          dependencies: [], remainingObligations: [], evidenceRefs: ['counterexample:RESEARCH.md'], createdAt: 2,
          findingDigest: mathDigest(finding) }] } });
    instances = []; events = []; saveCheckpoint = undefined;
  });
  afterEach(async () => {
    saveCheckpoint = undefined;
    instances.forEach(instance => instance.controller.abort());
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['live', 'final'] as const)('saves the removed source\'s rejection and retained challenge decision with the first %s graph checkpoint', async via => {
    const original = create(), cooperative = original.cooperative;
    const handoff = pendingResearchHandoffs(state.cooperation!)[0];
    const challenge = pendingResearchChallenges(state.cooperation!)[0];
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !action.planNonce) throw new Error('fixture_expected_replacement_dispatch');
    expect(action.handoffIds).toEqual([handoff.id]);
    expect(action.challengeIds).toEqual([challenge.id]);
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    const response = { tasks: state.cooperation!.tasks.filter(node => node.task.id !== 'question').map(node => node.task),
      groups: state.cooperation!.groups!.map(route => route.group),
      handoffDecisions: [{ id: handoff.id, status: 'rejected', reason: 'This bridge does not close the original goals.' }],
      challengeDecisions: [{ id: challenge.id, status: 'disputed', reason: 'The counterexample violates a premise.',
        evidenceRefs: ['counterargument:RESEARCH.md'] }] };
    let commit: string | undefined;
    if (via === 'live') {
      fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify({
        kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion, ...response,
      }) + '\n');
    } else {
      fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(response));
      commit = commitSolverSources(problem, workers[0].worktree);
      cooperative.deactivate(workers[0]);
    }
    const checkpointFile = path.join(directory, 'first-replacement-checkpoint.json');
    const crash = new Error('fixture_process_lost_after_graph_checkpoint');
    let firstCheckpoint: SolverRunState | undefined;
    saveCheckpoint = current => {
      if (current.cooperation!.tasks.some(node => node.task.id === 'question')) return;
      // Keep exactly the first durable graph snapshot; subsequent error handling cannot repair it.
      saveCheckpoint = undefined;
      firstCheckpoint = structuredClone(current);
      writeSolverRunState(checkpointFile, firstCheckpoint);
      throw crash;
    };
    // Final-delivery error handling may consume the injected failure; restore only the saved snapshot.
    await Promise.allSettled([via === 'live' ? cooperative.pulse() : cooperative.deliver(workers[0], action, commit!)]);

    expect(firstCheckpoint).toBeDefined();
    expect(firstCheckpoint!.cooperation!.tasks.map(node => node.task.id)).not.toContain('question');
    expect(firstCheckpoint!.cooperation!.researchDecisions).toMatchObject([{
      id: handoff.id, deliveryId: 'bridge-proposal', status: 'rejected', contextDigest: handoff.contextDigest,
    }]);
    expect(firstCheckpoint!.cooperation!.challengeDecisions).toMatchObject([{
      id: challenge.id, deliveryId: 'estimate-critique', status: 'disputed', contextDigest: challenge.contextDigest,
    }]);
    if (via === 'live') {
      expect(firstCheckpoint!.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce });
      expect(firstCheckpoint!.cooperation!.planPublication?.finalized).not.toBe(true);
    }
    expect(firstCheckpoint!.cooperation!.error).toBeUndefined();

    original.controller.abort(); await cooperative.stop();
    state = readSolverRunState(checkpointFile);
    const restored = create().cooperative; await restored.restore();
    expect(state.cooperation!.researchDecisions).toEqual(firstCheckpoint!.cooperation!.researchDecisions);
    expect(state.cooperation!.challengeDecisions).toEqual(firstCheckpoint!.cooperation!.challengeDecisions);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(pendingResearchChallenges(state.cooperation!)).toEqual([]);
    expect(researchChallenges(state.cooperation!)[0]).toMatchObject({ id: challenge.id, status: 'disputed' });
    expect(state.cooperation!.tasks.map(node => node.task.id)).not.toContain('question');
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'goal')).toHaveLength(problem.targets.length);
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.check).toBeUndefined();
    expect(events.filter(item => item.event === 'research_handoff_decided')).toHaveLength(1);
    expect(events.filter(item => item.event === 'research_challenge_decided')).toHaveLength(1);
  });
});
