import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { pendingResearchChallenges, researchChallenges, resolveResearchChallenges } from '../src/solver/researchChallenges';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('deferred research challenge plan retention', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState;
  let lead: ResearchWorker, peer: ResearchWorker;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const tasks = () => state.cooperation!.tasks.map(node => node.task);
  const notes = (value: unknown) => fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), JSON.stringify(value));
  const plan = (proposed = tasks()) => ({ tasks: proposed, groups: state.cooperation!.groups!.map(record => record.group) });
  const create = (primaryLed = false) => {
    const controller = new AbortController();
    const cooperative = cooperativeResearch({ state, workers: [lead, peer], retrievalRoot: directory, signal: controller.signal,
      modules: primaryLed ? { ...directSolverModules, M5: { ...directSolverModules.M5, primaryLed: true } } : directSolverModules });
    instances.push({ cooperative, controller });
    return cooperative;
  };

  beforeEach(() => {
    const example = localExample('solver-research-challenges-', 'lead'), workspace = example.workspace;
    ({ directory, problem } = example);
    lead = leadWorker(problem, workspace);
    peer = peerWorker(example, 'researcher', { name: 'peer' });
    const source: CooperativeTask = { id: 'question', kind: 'research', objective: 'Test the proposed inference.',
      dependsOn: [], revision: 0 };
    const helpers: CooperativeTask[] = ['waiting', 'delivery_input'].map(id => ({ id, kind: 'lemma',
      objective: `Prove ${id}.`, theoremName: `Tutorial.${id}`, proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 }));
    const parsed = parseCooperationPlan(problem, { tasks: [source, ...helpers, ...problem.targets.map((target, index) => ({
      id: `original_goal_${index + 1}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
      theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused',
    }))] });
    const finding = JSON.stringify({ conclusion: 'refuted', summary: 'The inference omits a positivity assumption.' });
    state = solverState(problem, workspace, { runId: 'research-challenge-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: parsed.groups.map(group => ({ group, turns: 0 })),
        tasks: parsed.tasks.map(task => ({ task, attempts: 0, status: task.id === source.id ? 'completed' : 'pending',
          ...(task.id === source.id ? { finding } : {}) })),
        deliveries: [{ id: 'challenge-delivery', producer: peer.id, kind: 'research', status: 'advisory',
          taskId: source.id, taskDigest: taskVersion(parsed.tasks.find(task => task.id === source.id)!),
          findingDigest: mathDigest(finding), summary: 'The inference omits a positivity assumption.',
          statement: '', premises: [], evidenceRefs: ['fixed-notes'], remainingObligations: [], createdAt: 1,
          dependencies: [{ taskId: 'delivery_input', taskDigest: taskVersion(parsed.tasks.find(task => task.id === 'delivery_input')!) }] }] } });
    const challenge = pendingResearchChallenges(state.cooperation!)[0]!;
    state.cooperation!.challengeDecisions = resolveResearchChallenges(state.cooperation!, [challenge.id],
      { [challenge.id]: challenge.activationDigest }, tasks(), [{ id: challenge.id, status: 'deferred',
        reason: 'Wait for the missing checked estimate.', waitsOn: ['waiting'] }]);
    expect(researchChallenges(state.cooperation!)[0]!.status).toBe('deferred');
    instances = [];
  });
  afterEach(async () => {
    for (const instance of instances) instance.controller.abort();
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    fs.rmSync(directory, { recursive: true, force: true });
  });

  it('rejects a later ordinary Lead plan that drops a still-waiting challenge source', async () => {
    state.cooperation!.error = 'A separate route needs replanning.';
    const cooperative = create(), action = await cooperative.next(lead, budget);
    if (action?.kind !== 'lead') throw new Error('fixture_expected_lead');
    expect(action.challengeIds).toEqual([]);
    notes(plan(tasks().filter(task => task.id !== 'question')));
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBe('math_challenge_backlog_source_required:question');
    expect(tasks().some(task => task.id === 'question')).toBe(true);
    expect(researchChallenges(state.cooperation!)[0]!.status).toBe('deferred');
  });

  it('dispatches the remaining challenge batch after a successful decision records the current planning digest', async () => {
    state.cooperation!.challengeDecisions = [];
    for (const node of state.cooperation!.tasks) if (node.task.kind !== 'research') node.task = { ...node.task, status: 'paused' };
    const source = state.cooperation!.deliveries![0]!;
    state.cooperation!.deliveries = Array.from({ length: 9 }, (_, index) => ({ ...source, id: `challenge_${index}` }));
    const cooperative = create(), first = await cooperative.next(lead, budget);
    if (first?.kind !== 'lead') throw new Error('fixture_expected_lead');
    expect(first.challengeIds).toHaveLength(8);
    notes({ ...plan(), challengeDecisions: first.challengeIds!.map(id => ({ id, status: 'disputed',
      reason: 'The witness omits the positive-input premise.', evidenceRefs: ['fixed-counterargument'] })) });
    await cooperative.deliver(lead, first, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBeUndefined();
    expect(pendingResearchChallenges(state.cooperation!)).toHaveLength(1);
    expect(state.cooperation!.lastLeadInputDigest).toBeTruthy();
    const next = await cooperative.next(lead, budget);
    if (next?.kind !== 'lead') throw new Error('fixture_expected_remaining_challenge_batch');
    expect(next.challengeIds).toEqual(pendingResearchChallenges(state.cooperation!).map(item => item.id));
    expect(next.challengeIds!.every(id => !first.challengeIds!.includes(id))).toBe(true);
  });

  it('keeps a restored deferred challenge when a newer notes draft deletes its waiting proof task', async () => {
    notes(plan(tasks().filter(task => task.id !== 'waiting')));
    state = JSON.parse(JSON.stringify(state));
    const cooperative = create();
    await cooperative.restore();
    expect(state.cooperation!.error).toBe('math_challenge_backlog_source_required:question');
    expect(tasks().some(task => task.id === 'waiting')).toBe(true);
    expect(researchChallenges(state.cooperation!)[0]!.status).toBe('deferred');
  });

  it('retains delivery inputs outside source dependsOn when the primary solver replaces helper requests', async () => {
    const cooperative = create(true), action = await cooperative.next(lead, budget);
    if (action?.kind !== 'solve') throw new Error('fixture_expected_primary_solver');
    expect(action.challengeIds).toEqual([]);
    notes({ requests: [] });
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.error).toBeUndefined();
    expect(tasks().map(task => task.id)).toEqual(expect.arrayContaining(['question', 'waiting', 'delivery_input']));
    expect(researchChallenges(state.cooperation!)[0]!.status).toBe('deferred');
  });
});
