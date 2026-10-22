import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { leadPlanDeliveryFile, parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { integratedProof } from './helpers/taskProof';

describe('live replacement plan publication', () => {
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let cooperative: CooperativeResearch, interrupt: ReturnType<typeof vi.fn>;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let events: { event: string; details?: Record<string, unknown> }[], pending: Promise<unknown>[];
  const graph = () => ({ tasks: state.cooperation!.tasks.map(node => node.task),
    groups: state.cooperation!.groups!.map(route => route.group) });
  const create = () => {
    const controller = new AbortController();
    const result = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative: result, controller });
    return result;
  };
  const start = async () => {
    const action = await cooperative.next(workers[0], budget);
    if (action?.kind !== 'lead' || !action.planNonce) throw new Error('fixture_expected_revision_dispatch');
    expect(cooperative.started(workers[0], action)).toBe(true);
    cooperative.activate(workers[0], action, interrupt, async () => {});
    return action;
  };
  const file = (action: CooperativeAction) => path.join(workers[0].worktree, leadPlanDeliveryFile(action)!);
  const line = (action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, plan = graph()) => JSON.stringify({
    kind: 'plan', dispatchNonce: action.planNonce, baseVersion: action.planVersion,
    summary: 'A complete next mathematical step is ready for an idle writer.', ...plan,
  });
  const publish = async (action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, value = line(action)) => {
    fs.appendFileSync(file(action), value + '\n'); await cooperative.pulse();
  };
  const helper = (id: string) => ({ id, kind: 'lemma' as const, objective: `Prove the independent step ${id}.`,
    theoremName: `Tutorial.${id}`, proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 });
  const withHelper = (id: string) => ({ ...graph(), tasks: [...graph().tasks, helper(id)] });

  beforeEach(() => {
    const example = localExample('solver-plan-publication-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'engineer', { role: 'engineer' }),
      peerWorker(example, 'prover', { role: 'prover' })];
    const plan = parseCooperationPlan(problem, { tasks: problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}.`, ...target,
    })) });
    state = solverState(problem, example.workspace, { runId: 'replacement-publication-fixture', phase: 'running',
      workers: workers.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree,
        phase: 'checking', turns: 0 })),
      cooperation: { tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })), error: 'fixture_request_new_plan' } });
    events = []; instances = []; pending = []; interrupt = vi.fn(async () => {});
    cooperative = create();
  });
  afterEach(async () => {
    instances.forEach(instance => instance.controller.abort());
    await Promise.allSettled(pending);
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('starts newly published work without invalidating the publishing Lead or unrelated running writers', async () => {
    const running = await cooperative.next(workers[1], budget);
    if (running?.kind !== 'task') throw new Error('fixture_expected_goal');
    const peerInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[1], running, peerInterrupt, async () => {});
    const action = await start(), original = structuredClone(action);
    const waiting = cooperative.next(workers[2], budget); pending.push(waiting); void waiting.catch(() => {});
    await publish(action, line(action, withHelper('first_bridge')));
    const next = await waiting;
    expect(next).toMatchObject({ kind: 'task', task: { id: 'first_bridge' } });
    expect(cooperative.current(action)).toBe(true);
    expect(cooperative.current(running)).toBe(true);
    expect(action).toEqual(original);
    expect(interrupt).not.toHaveBeenCalled(); expect(peerInterrupt).not.toHaveBeenCalled();
    expect(state.cooperation!.planPublication).toMatchObject({ nonce: action.planNonce, baseVersion: original.planVersion });
    expect(state.cooperation!.initialPlanPublication).toBeUndefined();
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });

  it('accepts only one complete immutable event in a revision dispatch', async () => {
    const action = await start(), value = line(action, withHelper('first_bridge'));
    fs.appendFileSync(file(action), value);
    await cooperative.pulse();
    expect(state.cooperation!.planPublication).toBeUndefined();
    fs.appendFileSync(file(action), '\n'); await cooperative.pulse();
    const accepted = structuredClone(state.cooperation!.planPublication);
    await publish(action, value);
    await publish(action, line(action, withHelper('second_bridge')));
    expect(state.cooperation!.planPublication).toEqual(accepted);
    expect(state.cooperation!.tasks.some(node => node.task.id === 'second_bridge')).toBe(false);
    expect(events.filter(event => event.event === 'plan_published')).toHaveLength(1);
  });

  it('requires both the dispatch nonce and current base version before accepting a replacement', async () => {
    const action = await start(), value = JSON.parse(line(action, withHelper('bridge')));
    await publish(action, JSON.stringify({ ...value, dispatchNonce: 'different-dispatch' }));
    await publish(action, JSON.stringify({ ...value, baseVersion: 'stale-version' }));
    expect(state.cooperation!.planPublication).toBeUndefined();
    expect(events.filter(event => event.event === 'plan_publication_rejected')).toHaveLength(2);
    await publish(action, JSON.stringify(value));
    expect(state.cooperation!.tasks.some(node => node.task.id === 'bridge')).toBe(true);
  });

  it('lets a concurrent human edit supersede the Lead without later resurrecting its plan', async () => {
    const action = await start(), proposal = line(action, withHelper('stale_bridge'));
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'new-human-plan',
      baseVersion: state.cooperation!.planVersion, ...withHelper('human_bridge') }) + '\n');
    await publish(action, proposal);
    expect(state.cooperation!.edits![0].status).toBe('applied');
    expect(cooperative.current(action)).toBe(false);
    expect(interrupt).toHaveBeenCalledOnce();
    expect(state.workers![0].scheduling?.status).toBe('stopping');
    expect(state.cooperation!.tasks.some(node => node.task.id === 'human_bridge')).toBe(true);
    expect(state.cooperation!.tasks.some(node => node.task.id === 'stale_bridge')).toBe(false);
  });

  it.each([false, true])('keeps a live graph when inherited plan notes remain in a notes-only final (append prose: %s)', async append => {
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(graph()) + '\n```');
    const action = await start();
    await publish(action, line(action, withHelper('published_bridge')));
    if (append) fs.appendFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '\nA new mathematical observation with the exact remaining gap.\n');
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(state.cooperation!.tasks.some(node => node.task.id === 'published_bridge')).toBe(true);
    expect(state.cooperation!.planPublication?.finalized).toBe(true);
    expect(events.filter(event => event.event === 'plan_updated')).toHaveLength(1);
    expect(state.workers![0].scheduling?.status).toBe('idle');
    expect(state.workers![0].phase).toBe('checking');
  });

  it('restores the published revision while leaving a newer unpublished graph unaccepted', async () => {
    const action = await start(); await publish(action, line(action, withHelper('published_bridge')));
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(withHelper('unpublished_bridge')) + '\n```');
    const stateFile = path.join(directory, 'state.json'); writeSolverRunState(stateFile, state);
    state = readSolverRunState(stateFile);
    const restored = create(); await restored.restore();
    expect(state.cooperation!.planPublication?.nonce).toBe(action.planNonce);
    expect(state.cooperation!.tasks.some(node => node.task.id === 'published_bridge')).toBe(true);
    expect(state.cooperation!.tasks.some(node => node.task.id === 'unpublished_bridge')).toBe(false);
    expect(restored.current(action)).toBe(false);
  });

  it('accepts an explicit final plan written immediately after its event, before the host polls', async () => {
    const action = await start(), published = withHelper('published_bridge');
    const final = { ...published, tasks: [...published.tasks, helper('final_bridge')] };
    fs.appendFileSync(file(action), line(action, published) + '\n');
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(final) + '\n```');
    await cooperative.pulse();
    expect(state.cooperation!.tasks.some(node => node.task.id === 'final_bridge')).toBe(false);
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
    expect(state.cooperation!.tasks.some(node => node.task.id === 'final_bridge')).toBe(true);
    expect(state.cooperation!.planPublication?.finalized).toBe(true);
  });

  it('refills and claims three successive proof waves while a long original-goal writer keeps its assignment', async () => {
    delete state.cooperation!.error; cooperative = create();
    const goal = await cooperative.next(workers[1], budget);
    if (goal?.kind !== 'task') throw new Error('fixture_expected_long_goal');
    const goalInterrupt = vi.fn(async () => {});
    cooperative.activate(workers[1], goal, goalInterrupt, async () => {});
    for (let wave = 1; wave <= 3; wave++) {
      const action = await start(), id = `wave_${wave}`;
      await publish(action, line(action, withHelper(id)));
      const task = await cooperative.next(workers[2], budget);
      if (task?.kind !== 'task' || task.task.id !== id) throw new Error('fixture_expected_next_wave');
      cooperative.activate(workers[2], task, async () => {}, async () => {});
      fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), 'The complete published graph is executable.\n');
      cooperative.deactivate(workers[0]);
      await cooperative.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
      // This scheduler fixture supplies an explicit mock kernel receipt; real integration is tested separately.
      integratedProof(state.cooperation!.tasks.find(node => node.task.id === id)!, {
        sourceCommit: state.cooperation!.canonicalCommit, environmentDigest: state.environmentDigest,
      });
      cooperative.deactivate(workers[2]);
      expect(cooperative.current(goal)).toBe(true);
      expect(goalInterrupt).not.toHaveBeenCalled();
    }
    const finalAssessment = await start();
    fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(graph()) + '\n```');
    cooperative.deactivate(workers[0]);
    await cooperative.deliver(workers[0], finalAssessment, commitSolverSources(problem, workers[0].worktree));
    let dispatched = false;
    const waiting = cooperative.next(workers[0], budget); pending.push(waiting);
    void waiting.then(() => { dispatched = true; }, () => {});
    for (let poll = 0; poll < 6; poll++) { await cooperative.pulse(); await Promise.resolve(); }
    expect(dispatched).toBe(false);
    expect(events.filter(event => event.event === 'capacity_refill_requested')).toHaveLength(4);
    expect(events.filter(event => event.event === 'plan_published')).toHaveLength(3);
    expect(state.cooperation!.tasks.filter(node => node.task.id.startsWith('wave_') && node.status === 'integrated')).toHaveLength(3);
    expect(state.cooperation!.lastCapacityRefill?.status).toBe('assessed');
    expect(state.check).toBeUndefined();
  });
});
