import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathAgentOptions } from '../src/runtime/codexSession';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { git, type SolverProblem } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('saved Lead plans after request failure', () => {
  let directory: string, problem: SolverProblem, workers: ResearchWorker[], state: SolverRunState;
  let modules: SolverModules, retry: ReturnType<typeof vi.fn>, close: ReturnType<typeof vi.fn>;
  let events: { event: string; details?: Record<string, unknown> }[];
  let execute: (action: CooperativeAction, options: MathAgentOptions) => Promise<string>;
  let actions: CooperativeAction[];
  let sessionError: string;
  let requestAccounting: boolean;

  const plan = () => ({ tasks: problem.targets.map((target, index) => ({
    id: `goal_${index + 1}`, kind: 'goal', objective: `Prove ${target.theoremName}`,
    proofPath: target.proofPath, theoremName: target.theoremName,
  })) });
  const writePlan = (options: MathAgentOptions, value: unknown = plan()) => fs.writeFileSync(
    path.join(options.workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify(value) + '\n```');
  const existingPlan = () => {
    const parsed = parseCooperationPlan(problem, plan());
    state.cooperation = { tasks: parsed.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
      groups: parsed.groups.map(group => ({ group, turns: 0 })), error: 'A Lead decision is requested.' };
  };
  const run = (maxTotalTokens = 0) => runResearchWorkers({ state, workers, modules,
    access: workerAccess(workers, directory),
    root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
    executable: 'fixture-no-model', profile: 'fixture', signal: new AbortController().signal,
    deadline: Infinity, maxTurns: 3, maxTurnMs: Infinity, maxTotalTokens,
    save: () => {}, emit: (event, details) => events.push({ event, details }) });

  beforeEach(() => {
    const example = localExample('solver-saved-plan-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'engineer', { role: 'engineer' })];
    state = solverState(problem, example.workspace, { runId: 'saved-plan-fixture', phase: 'prepared',
      evaluatorDigest: 'evaluation', model: 'fixture', effort: 'fixture',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })) });
    events = []; actions = []; sessionError = 'fetch failed'; requestAccounting = false;
    retry = vi.fn().mockReturnValue(undefined);
    close = vi.fn(async () => {});
    execute = async (_action, options) => { writePlan(options); return 'failed'; };
    modules = { ...directSolverModules,
      M1: { ...directSolverModules.M1, open: async options => ({ threadId: 'failed-plan-thread',
        ...(requestAccounting ? { usageSource: 'upstream-requests' as const } : {}),
        get lastError() { return sessionError; }, close, interrupt: vi.fn(async () => {}),
        run: async message => {
          const action = JSON.parse(message) as CooperativeAction;
          actions.push(action);
          return execute(action, options);
        } }) },
      M2: { ...directSolverModules.M2,
        check: async () => { throw new Error('fixture_unexpected_whole_proof_check'); },
        checkTask: async () => { throw new Error('fixture_unexpected_task_proof_check'); } },
      M3: { ...directSolverModules.M3, retry,
        select: (_state, _operations, _estimates, _budget, assignment) => assignment?.kind === 'task'
          ? { operation: 'stop', reason: 'fixture_task_dispatch_observed' }
          : { operation: 'direct', reason: 'fixture_lead_request' } },
      M4: { ...directSolverModules.M4, build: (_problem, _state, access) => ({
        instructions: 'Local fixture session.', message: JSON.stringify(access.assignment),
        scope: 'original-problem-and-allowed-library', sources: { problemReceiptDigest: problem.receiptDigest } }) },
    };
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it.each(['failed', 'transport-closed', 'request-error'])('uses an accepted saved initial plan after %s', async failure => {
    if (failure === 'transport-closed') sessionError = 'math_codex_transport_closed:fixture';
    execute = async (_action, options) => {
      writePlan(options);
      if (failure === 'transport-closed') throw new Error('math_codex_transport_closed:fixture');
      if (failure === 'request-error') throw new Error('fetch failed');
      return 'failed';
    };
    await expect(run()).resolves.toBeUndefined();
    expect(actions.map(action => action.kind)).toEqual(['lead']);
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(events).toContainEqual(expect.objectContaining({ event: 'task_assigned' }));
    expect(events).toContainEqual({ event: 'worker_recovered', details: {
      workerId: 'solver', reason: failure === 'transport-closed' ? 'math_codex_transport_closed' : 'math_model_request_failed',
      savedPlan: true,
    } });
    expect(events).toContainEqual(expect.objectContaining({ event: 'context_restarted', details: expect.objectContaining({ reason: 'request' }) }));
    expect(state.workers![0].previousThreadIds).toContain('failed-plan-thread');
    expect(close).toHaveBeenCalledOnce();
    expect(retry).not.toHaveBeenCalled();
  });

  it.each(['empty', 'invalid', 'unchanged'])('retries a failed Lead with an %s response', async response => {
    if (response === 'unchanged') existingPlan();
    execute = async (_action, options) => {
      if (response === 'empty') fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '');
      else if (response === 'invalid') writePlan(options, { tasks: [] });
      else writePlan(options);
      return 'failed';
    };
    await expect(run()).rejects.toThrow('math_model_request_failed');
    expect(retry).toHaveBeenCalledOnce();
    expect(events.some(item => item.event === 'worker_recovered')).toBe(false);
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
    if (response !== 'unchanged') expect(state.cooperation!.tasks).toEqual([]);
  });

  it('repeats an incomplete initial planning request and accepts its later complete response', async () => {
    retry.mockImplementation((_error, attempts) => attempts === 0
      ? { attempt: 1, delayMs: 0, reason: 'math_model_request_failed' } : undefined);
    execute = async (_action, options) => {
      writePlan(options, actions.length === 1 ? { tasks: [] } : plan());
      return actions.length === 1 ? 'failed' : 'completed';
    };
    await expect(run()).resolves.toBeUndefined();
    expect(actions.map(action => action.kind)).toEqual(['lead', 'lead']);
    expect(retry).toHaveBeenCalledOnce();
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
  });

  it.each(['tokens', 'requests', 'resume', 'saved-plan'] as const)
    ('hands off initial planning after its %s limit without losing complete usage', async mode => {
      requestAccounting = true; sessionError = 'HTTP 403 Forbidden';
      if (mode === 'resume') {
        const lead = state.workers![0];
        lead.turns = state.turns = 1;
        lead.usage = { inputTokens: 250, outputTokens: 50, totalTokens: 300 };
        lead.usageAccounting = { startedTurns: 1, reportedTurns: 1, pending: false, incomplete: false };
        lead.requestUsageAccounting = { startedRequests: 1, reportedRequests: 1, pendingRequests: 0, incomplete: false };
        state = JSON.parse(JSON.stringify(state));
      }
      let requests = 0;
      execute = async (_action, options) => {
        for (const totalTokens of mode === 'resume' ? [] : mode === 'requests' ? [20, 10] : [300]) {
          const admission = options.requestGate!();
          expect(admission.allowed).toBe(true);
          if (admission.allowed) {
            requests++;
            admission.settle({ usage: { totalTokens, inputTokens: totalTokens - 5, outputTokens: 5 }, complete: true });
          }
        }
        if (mode === 'saved-plan') writePlan(options);
        for (let retry = 0; retry < 2; retry++) expect(options.requestGate!()).toEqual({
          allowed: false, reason: 'math_initial_planning_limit' });
        return 'failed';
      };
      await expect(run(1000)).resolves.toBeUndefined();
      expect(actions.map(action => action.kind)).toEqual(['lead']);
      expect(requests).toBe(mode === 'resume' ? 0 : mode === 'requests' ? 2 : 1);
      expect(state.tokenBudget).toMatchObject({ status: 'available', usageComplete: true,
        reportedTotalTokens: mode === 'requests' ? 30 : 300 });
      const lead = state.workers![0];
      expect(lead.requestUsageAccounting).toEqual({ startedRequests: mode === 'requests' ? 2 : 1,
        reportedRequests: mode === 'requests' ? 2 : 1, pendingRequests: 0, incomplete: false });
      expect(lead.lastFailure).toBeUndefined(); expect(lead.error).toBeUndefined();
      expect(state.turnLedger!.turns.at(-1)).toMatchObject({ execution: 'interrupted', outcomeStatus: 'recorded' });
      expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(mode === 'saved-plan'
        ? ['goal_1', 'goal_2'] : ['initial_goal_1', 'initial_goal_2']);
      expect(state.cooperation!.tasks.every(node => node.status === 'pending' && !node.proof)).toBe(true);
      expect(Boolean(state.cooperation!.initialPlanFallback)).toBe(mode !== 'saved-plan');
      expect(events.filter(item => item.event === 'planning_budget_stopped')).toHaveLength(1);
      expect(events.some(item => item.event === 'task_assigned')).toBe(true);
      expect(events.some(item => ['worker_failed', 'turn_failed'].includes(item.event))).toBe(false);
      expect(close).toHaveBeenCalled(); expect(retry).not.toHaveBeenCalled();
    });

  it.each(['exhausted', 'missing'] as const)('prioritizes global %s usage over a planning handoff', async mode => {
    requestAccounting = true; sessionError = 'HTTP 403 Forbidden';
    const reason = mode === 'exhausted' ? 'math_total_token_limit' : 'math_model_usage_unavailable';
    execute = async (_action, options) => {
      const admission = options.requestGate!();
      expect(admission.allowed).toBe(true);
      if (admission.allowed) admission.settle(mode === 'exhausted'
        ? { usage: { totalTokens: 1000, inputTokens: 990, outputTokens: 10 }, complete: true } : { complete: false });
      expect(options.requestGate!()).toEqual({ allowed: false, reason });
      return 'failed';
    };
    await expect(run(1000)).resolves.toBeUndefined();
    expect(state.cooperation!.tasks).toEqual([]);
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
    expect(state.workers![0].lastFailure?.reason).toBe(reason);
    expect(events.some(item => item.event === 'planning_budget_stopped')).toBe(false);
    expect(retry).not.toHaveBeenCalled();
  });

  it('does not create a planning checkpoint while request receipts are pending', async () => {
    requestAccounting = true; sessionError = 'HTTP 403 Forbidden';
    execute = async (_action, options) => {
      const pending = [options.requestGate!(), options.requestGate!()];
      expect(pending.every(admission => admission.allowed)).toBe(true);
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_model_request_stopped' });
      for (const admission of pending) if (admission.allowed)
        admission.settle({ usage: { totalTokens: 20, inputTokens: 15, outputTokens: 5 }, complete: true });
      return 'failed';
    };
    await expect(run(1000)).rejects.toThrow('math_model_request_stopped');
    expect(state.cooperation!.tasks).toEqual([]);
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
    expect(state.turnLedger!.turns.at(-1)?.execution).toBe('failed');
    expect(events.some(item => item.event === 'planning_budget_stopped')).toBe(false);
    expect(state.tokenBudget).toMatchObject({ status: 'available', usageComplete: true, reportedTotalTokens: 40 });
  });

  it('waits for the planning writer to close before publishing its saved plan', async () => {
    requestAccounting = true; sessionError = 'HTTP 403 Forbidden';
    const closing = deferred(), startedClosing = deferred();
    close.mockImplementation(async () => { startedClosing.resolve(); await closing.promise; });
    execute = async (_action, options) => {
      const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
      if (admission.allowed) admission.settle({ usage: { totalTokens: 300, inputTokens: 250, outputTokens: 50 }, complete: true });
      writePlan(options);
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_initial_planning_limit' });
      return 'failed';
    };
    const running = run(1000);
    try {
      await startedClosing.promise;
      expect(events.some(item => ['plan_updated', 'task_assigned'].includes(item.event))).toBe(false);
      expect(state.cooperation!.tasks).toEqual([]);
    } finally { closing.resolve(); }
    await expect(running).resolves.toBeUndefined();
    expect(state.cooperation!.tasks.map(node => node.task.id)).toEqual(['goal_1', 'goal_2']);
    expect(events.some(item => item.event === 'task_assigned')).toBe(true);
  });

  it('does not apply the initial planning limit to unlimited runs or later Lead decisions', async () => {
    requestAccounting = true;
    execute = async (_action, options) => {
      for (let request = 0; request < 3; request++) {
        const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
        if (admission.allowed) admission.settle({ usage: { totalTokens: 10, inputTokens: 5, outputTokens: 5 }, complete: true });
      }
      writePlan(options); return 'completed';
    };
    await expect(run()).resolves.toBeUndefined();
    expect(state.workers![0].requestUsageAccounting?.startedRequests).toBe(3);
    existingPlan();
    await expect(run(1000)).resolves.toBeUndefined();
    expect(state.workers![0].requestUsageAccounting?.startedRequests).toBe(6);
    expect(events.some(item => item.event === 'planning_budget_stopped')).toBe(false);
  });

  it.each(['returned', 'thrown', 'changed-source'] as const)('keeps %s host integrity errors above planning checkpoints', async mode => {
    requestAccounting = true;
    execute = async (_action, options) => {
      const admission = options.requestGate!(); expect(admission.allowed).toBe(true);
      if (admission.allowed) admission.settle({ usage: { totalTokens: 300, inputTokens: 250, outputTokens: 50 }, complete: true });
      expect(options.requestGate!()).toEqual({ allowed: false, reason: 'math_initial_planning_limit' });
      if (mode === 'returned') sessionError = 'math_source_outside_ownership';
      else if (mode === 'thrown') throw new Error('math_candidate_identity_changed');
      else {
        const trusted = Object.keys(problem.trustedFiles)[0];
        fs.appendFileSync(path.join(options.workspace, problem.projectRelative, trusted), '\nchanged frozen input\n');
      }
      return 'failed';
    };
    await expect(run(1000)).rejects.toThrow(mode === 'changed-source' ? 'math_trusted_source_changed'
      : mode === 'returned' ? 'math_source_outside_ownership' : 'math_candidate_identity_changed');
    expect(state.cooperation!.initialPlanFallback).toBeUndefined();
    expect(state.cooperation!.tasks).toEqual([]);
    if (mode !== 'changed-source') expect(state.turnLedger!.turns.at(-1)?.execution).toBe('failed');
  });

  it.each(['research', 'sketch'])('keeps failed %s work on the ordinary retry path', async kind => {
    modules.M3.select = () => ({ operation: 'direct', reason: 'fixture_advisory_request' });
    execute = async (action, options) => {
      if (action.kind === 'lead') {
        const initial = plan();
        writePlan(options, { tasks: [
          { id: 'advice', kind, objective: 'Investigate the original claims' },
          ...initial.tasks.map(task => ({ ...task, dependsOn: ['advice'] })),
        ] });
        return 'completed';
      }
      if (action.kind !== 'task') throw new Error('fixture_unexpected_advisory_assignment');
      fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({
        taskId: action.task.id, summary: 'A saved hypothesis requiring independent proof.',
        conclusion: 'supporting', needsDecision: true, lemmaRequests: [{
          id: 'saved_bridge', kind: 'lemma', objective: 'Prove the saved hypothesis',
          theoremName: 'Tutorial.saved_bridge', type: 'True', proofPath: problem.targets[0].proofPath, dependsOn: [],
        }],
      }) + '\n```');
      return 'failed';
    };
    await expect(run()).rejects.toThrow('math_model_request_failed');
    expect(retry).toHaveBeenCalledOnce();
    expect(actions.map(action => action.kind)).toEqual(['lead', 'task']);
    expect(state.cooperation!.tasks[0].task).toMatchObject({ id: 'advice', kind });
    expect(state.cooperation!.tasks[0].finding).toBeUndefined();
    expect(state.cooperation!.tasks.slice(1).every(node => !node.attempts && !node.proof)).toBe(true);
    const checkpoint = state.cooperation!.researchDrafts?.advice;
    expect(checkpoint).toMatchObject({ taskDigest: state.cooperation!.tasks[0].assignment!.taskDigest,
      workerId: 'engineer' });
    expect(git(workers[1].worktree, ['show', `${checkpoint!.commit}:RESEARCH.md`])).toContain('saved_bridge');
    expect(state.cooperation!.researchCheckpoints?.advice).toBeUndefined();
    expect(state.cooperation!.deliveries?.some(delivery => delivery.kind === 'research')).not.toBe(true);
    expect(events.some(item => item.event === 'worker_recovered')).toBe(false);
  });

  it('keeps failed Primary solve work on the ordinary retry path', async () => {
    modules.M5 = { ...modules.M5, primaryLed: true };
    await expect(run()).rejects.toThrow('math_model_request_failed');
    expect(actions.map(action => action.kind)).toEqual(['solve']);
    expect(retry).toHaveBeenCalledOnce();
    expect(state.cooperation!.tasks).toEqual([]);
    expect(events.some(item => item.event === 'worker_recovered')).toBe(false);
  });

  it('discards a saved plan without retrying its superseded Lead assignment', async () => {
    existingPlan();
    state.cooperation!.planVersion = 'assigned-plan-version';
    execute = async (_action, options) => {
      state.cooperation!.planVersion = 'superseding-plan-version';
      const revised = plan(); revised.tasks[0].objective = 'Superseded proposed objective';
      writePlan(options, revised);
      return 'failed';
    };
    await expect(run()).resolves.toBeUndefined();
    expect(retry).not.toHaveBeenCalled();
    expect(events.some(item => item.event === 'lead_decision_superseded')).toBe(true);
    expect(events.some(item => item.event === 'assignment_superseded')).toBe(true);
    expect(events.some(item => item.event === 'worker_recovered')).toBe(false);
    expect(state.cooperation!.tasks[0].task.objective).toBe(plan().tasks[0].objective);
  });

  it('keeps failed frontier recovery plans subject to explicit completion', async () => {
    existingPlan();
    const next = CooperativeResearch.prototype.next;
    vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(async function(worker, budget) {
      const action = await next.call(this, worker, budget);
      return action?.kind === 'lead' ? { ...action, recovery: { id: 'fixture-recovery', taskIds: ['goal_1'], goalIds: ['goal_1'] } } : action;
    });
    execute = async (_action, options) => {
      const revised = plan(); revised.tasks[0].objective = 'An incomplete recovery proposal';
      writePlan(options, revised);
      return 'failed';
    };
    await expect(run()).rejects.toThrow('math_model_request_failed');
    expect(retry).toHaveBeenCalledOnce();
    expect(events.some(item => item.event === 'worker_recovered')).toBe(false);
    expect(state.cooperation!.tasks[0].task.objective).toBe(plan().tasks[0].objective);
  });
});
