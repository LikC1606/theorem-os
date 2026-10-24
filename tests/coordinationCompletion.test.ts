import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { leadPlanDeliveryFile, parseCooperationPlan, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

type Lead = Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>;

describe('accepted bounded coordination completion', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let events: { event: string; details?: Record<string, unknown> }[];
  let beforeSave: (() => void) | undefined;
  const savedState = () => path.join(directory, 'state.json');
  const graph = () => ({ tasks: state.cooperation!.tasks.map(node => node.task),
    groups: state.cooperation!.groups!.map(route => route.group) });
  const create = () => {
    const controller = new AbortController();
    const result = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      save: () => { beforeSave?.(); writeSolverRunState(savedState(), state); },
      emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative: result, controller });
    return result;
  };
  const start = async () => {
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !action.planNonce || !action.coordination)
      throw new Error('fixture_expected_bounded_coordination');
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, async () => {}, async () => {});
    expect(cooperative.coordinationResult(action)).toBeUndefined();
    return action;
  };
  const publish = async (action: Lead, value: unknown) => {
    fs.appendFileSync(path.join(workers[0].worktree, leadPlanDeliveryFile(action)!), JSON.stringify(value) + '\n');
    await cooperative.pulse();
  };
  const plan = (action: Lead, extra: Record<string, unknown> = {}) => ({ kind: 'plan',
    dispatchNonce: action.planNonce, baseVersion: action.planVersion, ...graph(), ...extra });
  const assessment = (action: Lead) => ({ kind: 'assessment', dispatchNonce: action.planNonce,
    baseVersion: action.planVersion,
    assessments: ([['capacity', action.capacityRefill], ['stagnation', action.stagnationRecovery]] as const)
      .flatMap(([kind, request]) => request ? [{ kind, requestId: request.requestId, inputDigest: request.inputDigest,
        outcome: 'no-independent-work', reason: 'No independent typed construction is available for the exact remaining gap.' }] : []),
  });

  beforeEach(() => {
    const example = localExample('coordination-completion-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'engineer', { role: 'engineer' }),
      peerWorker(example, 'researcher')];
    const parsed = parseCooperationPlan(problem, { tasks: [
      { id: 'question', kind: 'research', ownerId: 'researcher', objective: 'Find the missing construction.' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal',
        objective: `Prove ${target.theoremName}.`, ...target, dependsOn: ['question'] })),
    ] });
    state = solverState(problem, example.workspace, { runId: 'coordination-completion-fixture', phase: 'running',
      workers: workers.map(worker => ({ ...worker, phase: 'checking', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: parsed.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: parsed.groups.map(group => ({ group, turns: 0 })) } });
    instances = []; events = []; beforeSave = undefined;
    cooperative = create();
  });
  afterEach(async () => {
    beforeSave = undefined;
    instances.forEach(instance => instance.controller.abort());
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['plan', 'assessment'] as const)('exposes a successful %s only after its accepted receipt is saved', async kind => {
    const action = await start();
    let observedAcceptedSave = false;
    beforeSave = () => {
      const accepted = kind === 'plan' ? state.cooperation!.planPublication?.nonce === action.planNonce :
        state.cooperation!.lastCapacityRefill?.status === 'assessed';
      if (accepted && !observedAcceptedSave) {
        expect(cooperative.coordinationResult(action)).toBeUndefined();
        observedAcceptedSave = true;
      }
    };
    await publish(action, kind === 'plan' ? plan(action) : assessment(action));
    expect(observedAcceptedSave).toBe(true);
    expect(cooperative.coordinationResult(action)).toEqual({ progress: kind === 'assessment' });
    const durable = readSolverRunState(savedState());
    if (kind === 'plan') expect(durable.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce });
    else expect(durable.cooperation!.lastCapacityRefill).toMatchObject({ status: 'assessed', dispatchNonce: action.planNonce });
    expect(state.check).toBeUndefined();
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });

  it('counts a short accepted handoff and keeps ordinary proof work current', async () => {
    const source = state.cooperation!.tasks.find(node => node.task.id === 'question')!;
    source.status = 'completed';
    const running = await cooperative.next(workers[1], budget);
    if (running?.kind !== 'task' || running.task.kind !== 'goal') throw new Error('fixture_expected_proof');
    const interrupted = vi.fn(async () => {});
    cooperative.activate(workers[1], running, interrupted, async () => {});
    const helper: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the exact bridge.',
      theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    state.cooperation!.deliveries = [{ id: 'bridge-proposal', producer: 'researcher', taskId: source.task.id,
      taskDigest: taskVersion(source.task), kind: 'research', status: 'advisory', summary: 'A precise bridge needs a decision.',
      statement: '', premises: [], dependencies: [], remainingObligations: [], evidenceRefs: [], createdAt: 1,
      lemmaRequests: [helper] }];
    const action = await start();
    expect(action.handoffIds).toHaveLength(1);
    await publish(action, { kind: 'handoff', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      handoffDecisions: [{ id: action.handoffIds![0], status: 'adopted' }] });
    expect(cooperative.coordinationResult(action)).toEqual({ progress: true });
    expect(readSolverRunState(savedState()).cooperation!.researchDecisions).toMatchObject([{ status: 'adopted' }]);
    expect(cooperative.coordinationResult(running)).toBeUndefined();
    expect(cooperative.current(running)).toBe(true);
    expect(interrupted).not.toHaveBeenCalled();
  });

  it('records a changed task graph as progress', async () => {
    const action = await start(), before = state.cooperation!.planVersion;
    const helper: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Prove the exact bridge.',
      theoremName: 'Tutorial.bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    await publish(action, plan(action, { tasks: [...graph().tasks, helper] }));
    expect(state.cooperation!.planVersion).not.toBe(before);
    expect(cooperative.coordinationResult(action)).toEqual({ progress: true });
  });

  it('counts a newly accepted challenge decision even when the task graph stays unchanged', async () => {
    const source = state.cooperation!.tasks.find(node => node.task.id === 'question')!;
    const finding = JSON.stringify({ conclusion: 'inconclusive', needsDecision: true,
      summary: 'The exact construction still needs a mathematical input.' });
    state.cooperation!.deliveries = [{ id: 'construction-challenge', producer: 'researcher', taskId: source.task.id,
      taskDigest: taskVersion(source.task), kind: 'research', status: 'advisory', summary: 'Decide the precise construction gap.',
      finding, findingDigest: mathDigest(finding), statement: '', premises: [], dependencies: [],
      remainingObligations: [], evidenceRefs: [], createdAt: 1 }];
    const action = await start(), before = state.cooperation!.planVersion;
    expect(action.challengeIds).toHaveLength(1);
    await publish(action, { kind: 'handoff', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
      challengeDecisions: [{ id: action.challengeIds![0], status: 'deferred',
        reason: 'No construction is currently available.', reopenOn: 'A concrete independent construction becomes available.' }] });
    expect(state.cooperation!.planVersion).toBe(before);
    expect(cooperative.coordinationResult(action)).toEqual({ progress: true });
    expect(readSolverRunState(savedState()).cooperation!.challengeDecisions).toMatchObject([{ status: 'deferred' }]);
  });

  it('does not turn an unchanged graph into progress when a resumed request gets a new nonce', async () => {
    const first = await start();
    await publish(first, plan(first));
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], first, commitSolverSources(problem, workers[0].worktree));
    const next = await start();
    expect(next.planNonce).not.toBe(first.planNonce);
    expect(cooperative.coordinationResult(next)).toBeUndefined();
    await publish(next, plan(next));
    expect(cooperative.coordinationResult(first)).toEqual({ progress: false });
    expect(cooperative.coordinationResult(next)).toEqual({ progress: false });
    expect(state.cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
  });

  it('keeps accepted ordinary planning outside the bounded coordination lifecycle', async () => {
    const action = await start();
    delete action.coordination;
    await publish(action, plan(action));
    expect(events.filter(item => item.event === 'plan_published')).toHaveLength(1);
    expect(cooperative.coordinationResult(action)).toBeUndefined();
    expect(cooperative.current(action)).toBe(true);
  });

  it.each(['plan', 'assessment'] as const)('does not accept a duplicate %s a second time or accept a different decision for the nonce', async kind => {
    const action = await start(), value = kind === 'plan' ? plan(action) : assessment(action);
    await publish(action, value);
    await publish(action, value);
    await publish(action, { ...value, summary: 'A second immutable event is not allowed for the same dispatch.' });
    expect(cooperative.coordinationResult(action)).toEqual({ progress: kind === 'assessment' });
    expect(events.filter(item => item.event === (kind === 'plan' ? 'plan_published' : 'lead_assessment_published'))).toHaveLength(1);
    expect(events.filter(item => item.event === 'plan_publication_rejected')).toHaveLength(1);
    expect(events.filter(item => item.event === 'capacity_refill_assessed')).toHaveLength(kind === 'assessment' ? 1 : 0);
  });

  it('does not count a rejected or superseded publication', async () => {
    const action = await start(), value = plan(action);
    await publish(action, { ...value, dispatchNonce: 'wrong-dispatch' });
    await publish(action, { ...value, baseVersion: 'stale-graph' });
    expect(cooperative.coordinationResult(action)).toBeUndefined();
    const helper: CooperativeTask = { id: 'human_bridge', kind: 'lemma', objective: 'Prove the human-provided bridge.',
      theoremName: 'Tutorial.human_bridge', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'new-graph',
      baseVersion: state.cooperation!.planVersion, ...graph(), tasks: [...graph().tasks, helper] }) + '\n');
    await publish(action, value);
    expect(cooperative.current(action)).toBe(false);
    expect(cooperative.coordinationResult(action)).toBeUndefined();
    expect(events.filter(item => item.event === 'plan_publication_rejected')).toHaveLength(3);
  });

  it('does not report completion when saving the accepted assessment fails', async () => {
    const action = await start();
    beforeSave = () => { if (state.cooperation!.lastCapacityRefill?.status === 'assessed') throw new Error('fixture_save_failed'); };
    await expect(publish(action, assessment(action))).rejects.toThrow('fixture_save_failed');
    expect(cooperative.coordinationResult(action)).toBeUndefined();
    expect(readSolverRunState(savedState()).cooperation!.lastCapacityRefill).toMatchObject({ status: 'requested' });
  });

  it.each(['plan', 'assessment'] as const)('does not transfer a saved %s completion to a cloned or restored action', async kind => {
    const action = await start();
    await publish(action, kind === 'plan' ? plan(action) : assessment(action));
    expect(cooperative.coordinationResult(action)).toEqual({ progress: kind === 'assessment' });
    expect(cooperative.coordinationResult(structuredClone(action))).toBeUndefined();
    state = readSolverRunState(savedState());
    const restored = create(); await restored.restore();
    expect(restored.coordinationResult(action)).toBeUndefined();
    expect(restored.coordinationResult(structuredClone(action))).toBeUndefined();
  });

  it('counts a final assessment after its persisted acceptance without treating planning as bounded coordination', async () => {
    const action = await start();
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify(assessment(action)));
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(cooperative.coordinationResult(action)).toEqual({ progress: true });
    expect(cooperative.coordinationResult({ kind: 'lead', seedCommit: problem.baseCommit })).toBeUndefined();
  });
});
