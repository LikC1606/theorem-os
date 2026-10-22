import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules, type SolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { runResearchWorkers } from '../src/solver/research';
import { parseCooperationPlan, taskVersion, type CooperativeAction } from '../src/solver/tasks';
import { buildTokenBudget } from '../src/solver/usageBudget';
import { cooperativeResearch, workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

describe('continuous frontier recovery within solving budgets', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, workers: ResearchWorker[];
  let modules: SolverModules, controller: AbortController, cooperation: CooperativeResearch | undefined;
  let events: { event: string; details?: Record<string, unknown> }[];
  let onEvent: (event: string) => void;

  beforeEach(() => {
    const example = localExample('solver-continuous-research-', 'lead');
    ({ directory, problem } = example);
    workers = [leadWorker(problem, example.workspace), peerWorker(example, 'researcher')];
    const plan = parseCooperationPlan(problem, { tasks: problem.targets.map((target, index) => ({
      id: `goal_${index}`, kind: 'goal', objective: `Prove ${target.theoremName}`,
      proofPath: target.proofPath, theoremName: target.theoremName,
    })) });
    state = solverState(problem, example.workspace, { runId: 'continuous-research-fixture', phase: 'prepared',
      workers: workers.map(worker => ({ ...worker, phase: 'prepared', turns: 0 })),
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: plan.tasks.map(task => ({ task, status: 'blocked', attempts: 1 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } });
    modules = { ...directSolverModules,
      M1: { ...directSolverModules.M1, open: vi.fn(async () => { throw new Error('fixture_unexpected_model'); }) },
      M2: { ...directSolverModules.M2,
        check: vi.fn(async () => { throw new Error('fixture_unexpected_proof_check'); }),
        checkTask: vi.fn(async () => { throw new Error('fixture_unexpected_task_check'); }) },
      M3: { ...directSolverModules.M3, select: () => ({ operation: 'stop', reason: 'fixture_observe_recovery' }) },
    };
    controller = new AbortController(); events = []; onEvent = () => {}; cooperation = undefined;
    const next = CooperativeResearch.prototype.next;
    vi.spyOn(CooperativeResearch.prototype, 'next').mockImplementation(function(worker, budget) {
      cooperation = this;
      return next.call(this, worker, budget);
    });
  });

  afterEach(async () => {
    controller.abort();
    await cooperation?.stop();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  const awaitingInput = async (completedInvestigation = false) => {
    const fixture = cooperativeResearch({ state, workers, modules, retrievalRoot: directory });
    try {
      const action = (fixture as any).requestFrontierRecovery((fixture as any).activeGoalFrontier());
      expect(action).toMatchObject({ kind: 'lead' });
      const recovery = state.cooperation!.frontierRecoveries![0];
      recovery.status = 'awaiting-input'; recovery.reason = 'A new mathematical construction is required.';
      if (completedInvestigation) {
        recovery.investigationTaskId = 'saved_investigation'; recovery.investigationAttempts = 1;
        state.cooperation!.tasks.push({ task: { id: 'saved_investigation', kind: 'research', revision: 0,
          dependsOn: [...recovery.taskIds], objective: 'Investigate the missing construction.' },
          status: 'completed', attempts: 1, finding: 'The construction is unavailable in the inspected library.' });
      }
      state.cooperation!.planVersion = (fixture as any).planVersion();
      state.cooperation!.lastLeadInputDigest = (fixture as any).planningInputDigest();
    } finally { await fixture.stop(); }
  };

  const run = (deadline: number, maxTurns = Infinity, maxTotalTokens = 0) => runResearchWorkers({
    state, workers, modules, access: workerAccess(workers, directory),
    root: directory, buildFile: path.join(directory, 'unused-build.json'), taskText: 'Prove the original targets.',
    executable: 'fixture-no-model', profile: 'fixture', signal: controller.signal,
    deadline, maxTurns, maxTurnMs: Infinity, maxTotalTokens, save: () => {},
    emit: (event, details) => { events.push({ event, details }); onEvent(event); },
  });

  it.each([
    { finiteTime: true, unlimitedTurns: true },
    { finiteTime: false, unlimitedTurns: true },
    { finiteTime: true, unlimitedTurns: false },
    { finiteTime: false, unlimitedTurns: false },
  ])('investigates an unresolved frontier with finite time=$finiteTime, unlimited turns=$unlimitedTurns', async ({ finiteTime, unlimitedTurns }) => {
    await awaitingInput();
    onEvent = event => { if (event === 'frontier_investigation_requested') controller.abort(); };
    const result = run(finiteTime ? Date.now() + 30_000 : Infinity, unlimitedTurns ? Infinity : 3);
    if (unlimitedTurns) await expect(result).rejects.toMatchObject({ name: 'AbortError' });
    else await expect(result).resolves.toBeUndefined();
    expect(events.filter(item => item.event === 'frontier_investigation_requested')).toHaveLength(unlimitedTurns ? 1 : 0);
    expect(state.cooperation!.frontierRecoveries![0].investigationAttempts).toBe(unlimitedTurns ? 1 : undefined);
    expect(state.cooperation!.tasks.filter(node => node.task.id.startsWith('frontier_input_'))).toHaveLength(unlimitedTurns ? 1 : 0);
    expect(state.cooperation!.tasks.filter(node => node.task.kind === 'goal').every(node => node.status === 'blocked' && node.attempts === 1)).toBe(true);
    expect(modules.M1.open).not.toHaveBeenCalled(); expect(state.turns).toBe(0);
  });

  it.each(['abort', 'token-budget'] as const)('waits without repeated dispatches until %s ends a finite-time run', async stop => {
    await awaitingInput(true);
    let settled = false;
    const result = run(Date.now() + 30_000, Infinity, 100).then(
      value => { settled = true; return { value }; }, error => { settled = true; return { error }; });
    try {
      await vi.waitFor(() => expect(state.cooperation!.frontierWaiting?.reason).toBe('awaiting-new-mathematical-input'));
      for (let wake = 0; wake < 3; wake++) {
        cooperation!.modelBudgetChanged();
        await new Promise<void>(resolve => setTimeout(resolve, 0));
      }
      expect(settled).toBe(false);
      expect(events.filter(item => item.event === 'frontier_recovery_waiting')).toHaveLength(1);
      expect(events.filter(item => item.event === 'frontier_investigation_requested')).toHaveLength(0);
      expect(state.cooperation!.tasks.filter(node => node.task.kind === 'research')).toHaveLength(1);
      expect(state.turns).toBe(0); expect(modules.M1.open).not.toHaveBeenCalled();
      if (stop === 'abort') {
        controller.abort();
        expect(await result).toMatchObject({ error: { name: 'AbortError' } });
      } else {
        state.workers![0].usage = { totalTokens: 100 };
        state.tokenBudget = buildTokenBudget(100, state.workers!);
        cooperation!.modelBudgetChanged();
        expect(await result).toEqual({ value: undefined });
        expect(state.tokenBudget.status).toBe('exhausted');
      }
    } finally { controller.abort(); await result; }
  });

  it('does not schedule recovery after the finite solving budget is already spent', async () => {
    await awaitingInput();
    await expect(run(Date.now() - 1)).resolves.toBeUndefined();
    expect(events.some(item => item.event === 'frontier_investigation_requested')).toBe(false);
    expect(modules.M1.open).not.toHaveBeenCalled(); expect(state.turns).toBe(0);
  });

  it.each([
    { continuous: true, restored: false },
    { continuous: true, restored: true },
    { continuous: false, restored: false },
    { continuous: false, restored: true },
  ])('handles repeated invalid plans with continuous=$continuous, restored=$restored', async ({ continuous, restored }) => {
    const create = () => cooperativeResearch({ state, workers, modules, retrievalRoot: directory,
      continuousResearch: continuous, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }),
    });
    cooperation = create();
    state.cooperation!.planVersion = (cooperation as any).planVersion();
    (cooperation as any).rejectPlan(new Error('math_plan_changed_original_target'));
    (cooperation as any).rejectPlan(new Error('math_plan_changed_original_target'));
    expect(state.cooperation!.planRejection?.stalled).toBe(true);
    if (restored) {
      await cooperation.stop();
      state = JSON.parse(JSON.stringify(state));
      cooperation = create();
      await cooperation.restore();
    }
    const action = await cooperation.next(workers[0], { maxTurns: Infinity, remainingMs: Infinity });
    if (continuous) {
      expect(action).toMatchObject({ kind: 'lead', recovery: { taskIds: ['goal_0', 'goal_1'] } });
      expect(events.filter(item => item.event === 'frontier_recovery_requested')).toHaveLength(1);
      expect(state.cooperation!.frontierRecoveries).toHaveLength(1);
    } else {
      expect(action).toBeUndefined();
      expect(events.some(item => item.event === 'frontier_recovery_requested')).toBe(false);
    }
    expect(state.cooperation!.planRejection?.stalled).toBe(true);
    expect(modules.M1.open).not.toHaveBeenCalled();
    expect(state.turns).toBe(0);
  });

  it('keeps a stalled plan waiting for new input after its recovery investigation is complete', async () => {
    await awaitingInput(true);
    cooperation = cooperativeResearch({ state, workers, modules, retrievalRoot: directory,
      continuousResearch: true, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }),
    });
    (cooperation as any).rejectPlan(new Error('math_plan_changed_original_target'));
    (cooperation as any).rejectPlan(new Error('math_plan_changed_original_target'));
    let settled = false;
    const pending = cooperation.next(workers[0], { maxTurns: Infinity, remainingMs: Infinity }).then(
      value => { settled = true; return { value }; }, error => { settled = true; return { error }; });
    try {
      await vi.waitFor(() => expect(state.cooperation!.frontierWaiting?.reason).toBe('awaiting-new-mathematical-input'));
      cooperation.modelBudgetChanged();
      await new Promise<void>(resolve => setTimeout(resolve, 0));
      expect(settled).toBe(false);
      expect(events.filter(item => item.event === 'frontier_recovery_waiting')).toHaveLength(1);
      expect(events.some(item => item.event === 'frontier_recovery_requested' || item.event === 'frontier_investigation_requested')).toBe(false);
      expect(modules.M1.open).not.toHaveBeenCalled();
    } finally { controller.abort(); await pending; }
    expect(await pending).toMatchObject({ error: { name: 'AbortError' } });
  });

  it.each(['abort', 'new-input'] as const)('does not redispatch an identical rejected recovery before %s', async stop => {
    const question = { id: 'question', kind: 'research' as const, objective: 'Find a bridge.', dependsOn: [], revision: 0 };
    state.cooperation!.tasks.push({ task: question, status: 'completed', attempts: 1 });
    state.cooperation!.deliveries = [{ id: 'proposal', producer: workers[1].id, taskId: question.id, taskDigest: taskVersion(question),
      kind: 'research', status: 'advisory', summary: 'Propose a new bridge.', dependencies: [], evidenceRefs: [], remainingObligations: [],
      lemmaRequests: [{ id: 'bridge', kind: 'lemma', objective: 'Prove the bridge.', type: 'True',
        proofPath: 'Submission.lean', theoremName: 'Tutorial.bridge', dependsOn: [], revision: 0 }] }];
    cooperation = cooperativeResearch({ state, workers, modules, retrievalRoot: directory,
      continuousResearch: true, signal: controller.signal, emit: (event, details) => events.push({ event, details }),
    });
    state.cooperation!.planVersion = (cooperation as any).planVersion();
    const budget = { maxTurns: Infinity, remainingMs: Infinity };
    let action: CooperativeAction = (cooperation as any).requestFrontierRecovery((cooperation as any).activeGoalFrontier());
    expect(action).toMatchObject({ kind: 'lead', handoffIds: [expect.any(String)], recovery: expect.anything() });
    for (let attempt = 0; attempt < 2; attempt++) {
      fs.writeFileSync(path.join(workers[0].worktree, 'RESEARCH.md'), JSON.stringify({
        tasks: state.cooperation!.tasks.map(node => node.task), groups: state.cooperation!.groups!.map(route => route.group),
        recovery: { status: 'awaiting-input', reason: 'A new construction is required.' },
      }));
      await cooperation.deliver(workers[0], action, commitSolverSources(problem, workers[0].worktree));
      if (!attempt) {
        action = (await cooperation.next(workers[0], budget))!;
        expect(action).toMatchObject({ kind: 'lead', recovery: expect.anything() });
      }
    }
    expect(state.cooperation!.planRejection).toMatchObject({ stalled: true, error: expect.stringContaining('math_handoff_unresolved') });
    expect(state.cooperation!.frontierRecoveries![0].status).toBe('requested');
    let settled = false;
    const pending = cooperation.next(workers[0], budget).then(
      value => { settled = true; return { value }; }, error => { settled = true; return { error }; });
    try {
      await vi.waitFor(() => expect(state.cooperation!.frontierWaiting?.reason).toBe('awaiting-new-mathematical-input'));
      cooperation.modelBudgetChanged();
      await new Promise<void>(resolve => setTimeout(resolve, 0));
      expect(settled).toBe(false);
      expect(events.filter(item => item.event === 'frontier_recovery_requested')).toHaveLength(1);
      if (stop === 'new-input') {
        state.environmentDigest = 'updated-environment';
        cooperation.modelBudgetChanged();
        expect(await pending).toMatchObject({ value: { kind: 'lead', recovery: expect.anything() } });
      } else {
        controller.abort();
        expect(await pending).toMatchObject({ error: { name: 'AbortError' } });
      }
      expect(modules.M1.open).not.toHaveBeenCalled();
    } finally { controller.abort(); await pending; }
  });
});
