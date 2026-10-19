import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathAgentOptions } from '../src/runtime/codexSession';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { parseCooperationPlan, type CooperativeAction } from '../src/solver/tasks';

vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));

describe('saved Lead plans after request failure', () => {
  let directory: string, problem: SolverProblem, workers: ResearchWorker[], state: SolverRunState;
  let modules: SolverModules, retry: ReturnType<typeof vi.fn>, close: ReturnType<typeof vi.fn>;
  let events: { event: string; details?: Record<string, unknown> }[];
  let execute: (action: CooperativeAction, options: MathAgentOptions) => Promise<string>;
  let actions: CooperativeAction[];
  let sessionError: string;

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
  const run = () => runResearchWorkers({ state, workers, modules,
    access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
    root: directory, buildFile: path.join(directory, 'build.json'), taskText: 'Prove the original targets.',
    executable: 'fixture-no-model', profile: 'fixture', signal: new AbortController().signal,
    deadline: Infinity, maxTurns: 3, maxTurnMs: Infinity, maxTotalTokens: 0,
    save: () => {}, emit: (event, details) => events.push({ event, details }) });

  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-saved-plan-')));
    const workspace = path.join(directory, 'lead');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const peer = path.join(directory, 'engineer');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', peer, problem.baseCommit]);
    workers = [{ id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles },
      { id: 'engineer', role: 'engineer', worktree: peer, ownedFiles: problem.ownedFiles }];
    state = { schema: 'deepscientist.math.solver.v1', runId: 'saved-plan-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluation',
      model: 'fixture', effort: 'fixture', worktree: workspace, phase: 'prepared', turns: 0,
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })) };
    events = []; actions = []; sessionError = 'fetch failed';
    retry = vi.fn().mockReturnValue(undefined);
    close = vi.fn(async () => {});
    execute = async (_action, options) => { writePlan(options); return 'failed'; };
    modules = { ...directSolverModules,
      M1: { ...directSolverModules.M1, open: async options => ({ threadId: 'failed-plan-thread',
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
