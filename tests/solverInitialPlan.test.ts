import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, git, type SolverProblem } from '../src/solver/problem';
import { ResearchUsage } from '../src/solver/researchUsage';
import { initialPlanDeliveryFile, type CooperativeAction } from '../src/solver/tasks';
import { buildTokenBudget, initializeUsageAccounting } from '../src/solver/usageBudget';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('explicit initial Lead plan publication', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, lead: ResearchWorker, peer: ResearchWorker;
  let events: { event: string; details?: Record<string, unknown> }[];
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[];
  let interrupt: ReturnType<typeof vi.fn>;
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const plan = (suffix = '') => ({ tasks: problem.targets.map((target, index) => ({
    id: `goal_${index + 1}${suffix}`, kind: 'goal', objective: `Prove ${target.theoremName}.`,
    theoremName: target.theoremName, proofPath: target.proofPath,
  })) });
  const create = () => {
    const controller = new AbortController();
    const cooperative = cooperativeResearch({ state, workers: [lead, peer], retrievalRoot: directory,
      signal: controller.signal, emit: (event, details) => events.push({ event, details }) });
    instances.push({ cooperative, controller });
    return cooperative;
  };
  const startLead = async (cooperative: CooperativeResearch) => {
    const action = await cooperative.next(lead, budget);
    if (action?.kind !== 'lead') throw new Error('fixture_expected_lead');
    expect(initialPlanDeliveryFile(action)).toMatch(/^DELIVERIES-[a-f0-9]{64}\.jsonl$/u);
    expect(cooperative.started(lead, action)).toBe(true);
    cooperative.activate(lead, action, interrupt, async () => {});
    return action;
  };
  const file = (action: CooperativeAction) => path.join(lead.worktree, initialPlanDeliveryFile(action)!);
  const event = (action: CooperativeAction, value = plan()) => JSON.stringify({
    kind: 'plan', baseVersion: action.kind === 'lead' ? action.planVersion : undefined,
    summary: 'The direct original-goal tasks are ready for independent workers.', ...value,
  });
  const publish = async (cooperative: CooperativeResearch, action: CooperativeAction, line = event(action)) => {
    fs.appendFileSync(file(action), line + '\n');
    await cooperative.pulse();
  };

  beforeEach(() => {
    const example = localExample('solver-initial-plan-', 'lead');
    ({ directory, problem } = example);
    lead = leadWorker(problem, example.workspace);
    peer = peerWorker(example, 'engineer', { role: 'engineer' });
    state = solverState(problem, example.workspace, { runId: 'initial-plan-fixture', phase: 'prepared',
      evaluatorDigest: 'evaluation', model: 'fixture', effort: 'fixture' });
    instances = []; events = []; interrupt = vi.fn(async () => {});
  });
  afterEach(async () => {
    for (const instance of instances) instance.controller.abort();
    await Promise.allSettled(instances.map(instance => instance.cooperative.stop()));
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('starts a waiting peer while the same Lead remains active at its frozen dispatch identity', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    const originalAction = structuredClone(action), head = git(lead.worktree, ['rev-parse', 'HEAD']);
    const relative = path.join(problem.projectRelative, 'Submission.lean');
    const originalSource = fs.readFileSync(path.join(lead.worktree, relative), 'utf8');
    const unpublishedSource = originalSource.replace('n + 0 = n := by sorry', 'n + 0 = n := by exact Nat.add_zero n');
    expect(unpublishedSource).not.toBe(originalSource);
    fs.writeFileSync(path.join(lead.worktree, relative), unpublishedSource);
    const waiting = cooperative.next(peer, budget);
    void waiting.catch(() => {});
    await publish(cooperative, action);
    const assigned = await waiting;
    expect(assigned).toMatchObject({ kind: 'task', task: { id: 'goal_1' } });
    expect(cooperative.current(action)).toBe(true);
    expect(action).toEqual(originalAction);
    expect(cooperative.initialPlanSnapshot(action)?.tasks.map(task => task.id)).toEqual(['goal_1', 'goal_2']);
    expect(state.cooperation!.initialPlanPublication).toMatchObject({ nonce: action.initialPlanNonce,
      baseVersion: originalAction.planVersion, planVersion: state.cooperation!.planVersion });
    expect(interrupt).not.toHaveBeenCalled();
    expect(git(lead.worktree, ['rev-parse', 'HEAD'])).toBe(head);
    expect(fs.readFileSync(path.join(lead.worktree, relative), 'utf8')).toBe(unpublishedSource);
    expect(fs.readFileSync(path.join(peer.worktree, relative), 'utf8')).toBe(originalSource);
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });

  it('leaves ordinary notes and a partial JSONL event unpublished', async () => {
    const cooperative = create(), action = await startLead(cooperative), line = event(action);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(plan('_draft')) + '\n```');
    await cooperative.pulse();
    expect(state.cooperation!.tasks).toEqual([]);
    fs.appendFileSync(file(action), line.slice(0, line.length / 2));
    await cooperative.pulse();
    expect(state.cooperation!.tasks).toEqual([]);
    expect(state.cooperation!.initialPlanPublication).toBeUndefined();
    fs.appendFileSync(file(action), line.slice(Math.floor(line.length / 2)));
    await cooperative.pulse();
    expect(state.cooperation!.tasks).toEqual([]);
    fs.appendFileSync(file(action), '\n');
    await cooperative.pulse();
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
  });

  it('ignores an older dispatch log and rejects malformed or stale events before accepting a valid one', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    fs.appendFileSync(file({ ...action, initialPlanNonce: 'old-dispatch' }), event(action) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.tasks).toEqual([]);
    await publish(cooperative, action, '{bad JSON');
    await publish(cooperative, action, JSON.stringify({ kind: 'plan', baseVersion: 'stale', ...plan() }));
    await publish(cooperative, action, event(action, { tasks: [] }));
    expect(state.cooperation!.tasks).toEqual([]);
    expect(events.filter(item => item.event === 'initial_plan_rejected')).toHaveLength(3);
    await publish(cooperative, action);
    expect(state.cooperation!.tasks).toHaveLength(problem.targets.length);
  });

  it('accepts one frozen event and keeps duplicate or later events from rewriting it', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    const receipt = structuredClone(state.cooperation!.initialPlanPublication);
    await publish(cooperative, action);
    await publish(cooperative, action, event(action, plan('_second')));
    expect(state.cooperation!.initialPlanPublication).toEqual(receipt);
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(events.filter(item => item.event === 'initial_plan_published')).toHaveLength(1);
    expect(events.filter(item => item.event === 'plan_updated')).toHaveLength(1);
  });

  it('keeps later human edits above the original Lead self-publication', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id: 'new-direction',
      baseVersion: state.cooperation!.planVersion, ...plan('_human') }) + '\n');
    await cooperative.pulse();
    expect(state.cooperation!.edits?.[0].status).toBe('applied');
    expect(cooperative.current(action)).toBe(false);
    expect(cooperative.initialPlanSnapshot(action)).toBeUndefined();
  });

  it('restores the accepted graph without importing a newer unpublished valid notes draft', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(plan('_unpublished')) + '\n```');
    const stateFile = path.join(directory, 'state.json');
    writeSolverRunState(stateFile, state); state = readSolverRunState(stateFile);
    expect(state.cooperation!.initialPlanPublication?.nonce).toBe(action.initialPlanNonce);
    const restored = create();
    await restored.restore();
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(cooperative.current({ ...action })).toBe(false);
  });

  it.each([false, true])('keeps a published plan after a notes-only final delivery (request failure: %s)', async recovering => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), 'The peers can work while the next mathematical route is investigated.\n');
    cooperative.deactivate(lead);
    const delivered = await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree), recovering, 'request-failure');
    expect(delivered).toEqual({ checkWhole: false, ...(recovering ? { savedPlan: true } : {}) });
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(state.cooperation!.initialPlanPublication?.finalized).toBe(recovering ? undefined : true);
    expect(events.filter(item => item.event === 'plan_rejected')).toEqual([]);
    expect(events.filter(item => item.event === 'plan_updated')).toHaveLength(1);
  });

  it('validates a later explicit replacement plan through ordinary final delivery', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(plan('_final')) + '\n```');
    cooperative.deactivate(lead);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1_final', 'goal_2_final']);
    expect(state.cooperation!.initialPlanPublication?.finalized).toBe(true);
    expect(events.filter(item => item.event === 'plan_updated')).toHaveLength(2);
  });

  it('reports an invalid final plan without losing an earlier published plan', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), '```math-plan\n{"tasks":[]}\n```');
    cooperative.deactivate(lead);
    const delivered = await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree), true, 'request-failure');
    expect(delivered).toEqual({ checkWhole: false, savedPlan: true });
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(state.cooperation!.error).toBe('math_plan_invalid');
    expect(state.cooperation!.initialPlanPublication?.finalized).toBeUndefined();
    expect(events.filter(item => item.event === 'plan_rejected')).toHaveLength(1);
  });

  it('still checks changed Lead proof sources through the ordinary integration path', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    await publish(cooperative, action);
    const sourceFile = path.join(lead.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(sourceFile, fs.readFileSync(sourceFile, 'utf8').replace('n + 0 = n := by sorry',
      'n + 0 = n := by exact Nat.add_zero n'));
    fs.writeFileSync(path.join(lead.worktree, 'RESEARCH.md'), 'The saved proof requires host integration.\n');
    const merge = vi.spyOn(cooperative as any, 'mergeLeadSources').mockRejectedValue(new Error('fixture_integration_rejected'));
    cooperative.deactivate(lead);
    await cooperative.deliver(lead, action, commitSolverSources(problem, lead.worktree));
    expect(merge).toHaveBeenCalledOnce();
    expect(state.cooperation!.error).toBe('fixture_integration_rejected');
    expect(state.cooperation!.canonicalCommit).not.toBe(git(lead.worktree, ['rev-parse', 'HEAD']));
    expect(state.cooperation!.tasks.every(node => !node.proof && !node.integratedCheck)).toBe(true);
  });

  it('retains the finite shared budget and pending usage while leaving initial planning after publication', async () => {
    const cooperative = create(), action = await startLead(cooperative);
    initializeUsageAccounting(state);
    state.tokenBudget = buildTokenBudget(1000, [state], 'provider-observed-upstream-request-limit');
    const controller = instances[0].controller;
    const usage = new ResearchUsage({ state, research: state, maxTotalTokens: 1000,
      signal: controller.signal, remainingMs: () => Infinity,
      changed: () => { state.tokenBudget = buildTokenBudget(1000, [state], 'provider-observed-upstream-request-limit'); },
      emit: (name, details) => events.push({ event: name, details }) });
    const callbacks = usage.bindSession('fixture-session', () => undefined);
    usage.sessionOpened({ threadId: 'fixture-thread', usageSource: 'upstream-requests', run: async () => 'completed',
      close: async () => {}, interrupt: async () => {} });
    usage.begin(action);
    const first = callbacks.requestGate!(), second = callbacks.requestGate!();
    if (!first.allowed || !second.allowed) throw new Error('fixture_request_not_admitted');
    first.settle({ usage: { totalTokens: 20, inputTokens: 15, outputTokens: 5 }, complete: true });
    await publish(cooperative, action);
    expect(state.requestUsageAccounting!.pendingRequests).toBe(1);
    expect(state.usageAccounting).toMatchObject({ pending: true, reportedTurns: 0 });
    const third = callbacks.requestGate!();
    expect(third.allowed).toBe(true);
    if (!third.allowed) throw new Error('fixture_publication_did_not_leave_initial_planning');
    second.settle({ usage: { totalTokens: 500, inputTokens: 450, outputTokens: 50 }, complete: true });
    third.settle({ usage: { totalTokens: 500, inputTokens: 450, outputTokens: 50 }, complete: true });
    expect(callbacks.requestGate!()).toEqual({ allowed: false, reason: 'math_total_token_limit' });
    usage.finish(true);
    expect(state.requestUsageAccounting).toMatchObject({ reportedRequests: 3, pendingRequests: 0, incomplete: false });
    expect(events.some(item => item.event === 'planning_budget_stopped')).toBe(false);
  });
});
