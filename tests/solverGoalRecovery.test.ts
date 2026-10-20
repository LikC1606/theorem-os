import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { configuredSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { buildProofContinuation } from '../src/solver/progress';
import { commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { markTaskAcceptance, parseCooperationPlan, taskVersion,
  type CooperativeAction, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ capture: vi.fn(), checkTask: vi.fn(), session: vi.fn() }));
vi.mock('../src/solver/statementReview', async importOriginal => ({
  ...await importOriginal<typeof import('../src/solver/statementReview')>(), captureStatementContexts: host.capture,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.session }));

const budget = { maxTurns: Infinity, remainingMs: Infinity };
type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type LeadAction = Extract<CooperativeAction, { kind: 'lead' }>;

describe('original-goal recovery alongside independent proof work', () => {
  let directory: string, workspace: string, seed: string, problem: SolverProblem, state: SolverRunState;
  let cooperative: CooperativeResearch, lead: ResearchWorker, researcher: ResearchWorker, controller: AbortController;
  let events: { event: string; details?: Record<string, unknown> }[], pending: Promise<unknown>[];
  const record = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const helper = (id: string, dependsOn: string[] = [], type = 'True'): CooperativeTask => ({
    id, kind: 'lemma', objective: `Prove ${id}.`, theoremName: `Tutorial.${id}`, proofPath: 'Submission.lean',
    type, dependsOn, revision: 0,
  });
  const checkpoint = (notes: unknown, worker = lead) => {
    fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), JSON.stringify(notes));
    git(worker.worktree, ['add', '--', 'RESEARCH.md']);
    git(worker.worktree, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
      'commit', '--no-gpg-sign', '--quiet', '--allow-empty', '-m', 'Save recovery fixture notes']);
    return git(worker.worktree, ['rev-parse', 'HEAD']);
  };
  const priorAssessment = () => {
    state.cooperation!.planVersion = (cooperative as any).planVersion();
    state.cooperation!.lastLeadInputDigest = (cooperative as any).planningInputDigest();
    // The fixture resumes after the Lead already assessed this exact archived plan.
    (cooperative as any).needsLead = false;
  };
  const leadOutcome = async (): Promise<CooperativeAction | 'waiting' | undefined> => {
    let settled = false, action: CooperativeAction | undefined;
    const next = cooperative.next(lead, budget);
    pending.push(next);
    void next.then(value => { action = value; settled = true; });
    await vi.waitFor(() => expect(settled || (cooperative as any).waiters.size > 0).toBe(true));
    return settled ? action : 'waiting';
  };
  const recovery = async (): Promise<LeadAction> => {
    const action = await leadOutcome();
    expect(action).toMatchObject({ kind: 'lead', recovery: { taskIds: ['missing_argument'], goalIds: ['original_goal'] } });
    if (!action || action === 'waiting' || action.kind !== 'lead' || !action.recovery) throw new Error('expected_goal_recovery');
    return action;
  };
  const expectWaiting = async () => {
    expect(await leadOutcome()).toBe('waiting');
    expect(state.cooperation!.frontierRecoveries ?? []).toEqual([]);
    expect(events.filter(item => item.event === 'frontier_recovery_requested')).toEqual([]);
  };
  const start = async (id: string): Promise<TaskAction> => {
    const action = await cooperative.next(researcher, budget);
    expect(action).toMatchObject({ kind: 'task', task: { id } });
    if (action?.kind !== 'task') throw new Error('expected_fixture_task');
    expect(cooperative.started(researcher, action)).toBe(true);
    cooperative.activate(researcher, action, async () => {}, async () => {});
    return action;
  };
  const feasibilityPeers = (role: ResearchWorker['role'] = 'researcher', pinned = false) => {
    const peer = (id: string, peerRole: ResearchWorker['role'] = 'researcher'): ResearchWorker => {
      const worktree = path.join(directory, id);
      git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, seed]);
      return { ...researcher, id, role: peerRole, worktree };
    };
    const checker = peer('early-checker', role), replacement = peer('replacement-checker');
    const core = record('missing_argument');
    core.assignment = { taskId: core.task.id, taskDigest: taskVersion(core.task), workerId: researcher.id, seedCommit: seed };
    record('more_auxiliary').task = { ...record('more_auxiliary').task, status: 'paused' };
    const task: CooperativeTask = { id: 'dynamic_route_check', kind: 'research', reviewScope: 'feasibility',
      objective: 'Independently test the core estimate and its original-goal application.',
      dependsOn: ['original_goal', core.task.id], revision: 0, ...(pinned ? { ownerId: checker.id } : {}) };
    state.cooperation!.tasks.push({ task, status: 'pending', attempts: 0 });
    const workers = [lead, researcher, checker, replacement], modules = configuredSolverModules('direct', 'continuation');
    const create = () => new CooperativeResearch({ state, workers,
      access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: { ...modules, M2: { ...modules.M2, checkTask: host.checkTask } }, exclusiveCheck: async check => check() });
    cooperative = create(); priorAssessment();
    const claim = async (worker = checker): Promise<TaskAction> => {
      const action = await cooperative.next(worker, budget);
      expect(action).toMatchObject({ kind: 'task', task: { id: task.id }, assignment: { workerId: worker.id } });
      if (action?.kind !== 'task') throw new Error('expected_dynamic_feasibility_review');
      return action;
    };
    return { checker, replacement, task, create, claim };
  };
  const alternativeFrontier = () => {
    const saved = record('saved_auxiliary'), goal = record('original_goal');
    goal.task = { ...goal.task, dependsOn: [] };
    const parked: TaskRecord = { task: helper('parked_closing', [saved.task.id]), status: 'integrated', attempts: 1 };
    parked.integratedCheck = { ...saved.integratedCheck!, taskDigest: taskVersion(parked.task),
      references: { ...saved.integratedCheck!.references!,
        root: { file: 'Submission.lean', name: parked.task.theoremName! },
        tasks: [{ taskId: saved.task.id, taskDigest: taskVersion(saved.task) }],
        proof: [{ file: 'Submission.lean', name: saved.task.theoremName! }],
      } };
    markTaskAcceptance(parked.integratedCheck);
    const closing: TaskRecord = { task: helper('active_closing', ['missing_argument']), status: 'pending', attempts: 0 };
    state.cooperation!.tasks.push(parked, closing);
    state.cooperation!.proofRoutes = [
      { id: 'parked_route', targetTaskId: goal.task.id, prerequisiteTaskIds: [saved.task.id], closingTaskId: parked.task.id },
      { id: 'active_route', targetTaskId: goal.task.id, prerequisiteTaskIds: ['missing_argument'], closingTaskId: closing.task.id },
    ];
    (cooperative as any).syncProofRoutes();
    goal.assignment = { taskId: goal.task.id, taskDigest: taskVersion(goal.task), workerId: researcher.id,
      seedCommit: seed, routeId: 'parked_route' };
    const blocker = [{ mechanism: 'checked route does not supply the original inference', scope: 'original-goal application' }];
    (cooperative as any).reportBlockers(goal.task, blocker);
    (cooperative as any).reportBlockers(goal.task, blocker);
    goal.assignment = undefined;
    (cooperative as any).changed(); priorAssessment();
    expect(goal.parkedRoutes?.parked_route).toHaveLength(1);
    return { goal, saved, parked, closing };
  };

  beforeEach(() => {
    host.capture.mockReset().mockImplementation(async (_problem: unknown, tasks: readonly CooperativeTask[]) =>
      new Map(tasks.map(task => [task.id, { type: task.type ?? 'True', constants: [], omitted: [] }])));
    host.checkTask.mockReset().mockImplementation(() => { throw new Error('unexpected_fixture_proof_check'); });
    host.session.mockReset().mockImplementation(() => { throw new Error('fixture_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-goal-recovery-')));
    workspace = path.join(directory, 'lead');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const file = path.join(workspace, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', 'lemma saved_auxiliary : True := by trivial\n\ntheorem add_zero'));
    seed = commitSolverSources(problem, workspace);
    const worktree = path.join(directory, 'researcher');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, seed]);
    lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles };
    researcher = { ...lead, id: 'researcher', role: 'researcher', worktree };
    const tasks: CooperativeTask[] = [helper('saved_auxiliary'), helper('more_auxiliary', ['saved_auxiliary'], 'Nat.succ 0 = 1'),
      helper('missing_argument'), ...problem.targets.map((target, index) => ({
        id: index === 0 ? 'original_goal' : `other_goal_${index}`, kind: 'goal' as const,
        objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
        dependsOn: index === 0 ? ['missing_argument'] : [], revision: 0,
        ...(index === 0 ? {} : { status: 'paused' as const }),
      }))];
    const plan = parseCooperationPlan(problem, { tasks });
    state = { schema: 'deepscientist.math.solver.v1', runId: 'goal-recovery-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: seed, tasks: plan.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: plan.groups.map(group => ({ group, turns: 0 })) } };
    const saved = record('saved_auxiliary');
    saved.status = 'integrated';
    saved.integratedCheck = { passed: true, taskDigest: taskVersion(saved.task), commit: seed, seedCommit: seed,
      sourceDigest: 'fixture-source', changes: [], conditions: [], imports: [],
      verification: { status: 'kernel_verified', targetCommit: seed, results: [
        { status: 'kernel_verified', targetCommit: seed, receiptId: 'saved-fixture-receipt' },
      ] }, references: { root: { file: 'Submission.lean', name: 'Tutorial.saved_auxiliary' }, sourceCommit: seed,
        environmentDigest: 'environment', contextDigest: 'fixture-context', inputs: [], statement: [], proof: [], tasks: [] },
    } as unknown as TaskProof;
    markTaskAcceptance(saved.integratedCheck);
    const core = record('missing_argument'); core.status = 'blocked'; core.attempts = 2;
    core.feedback = 'The independent check found that the substantive original argument is missing.';
    events = []; pending = []; controller = new AbortController();
    const modules = configuredSolverModules('direct', 'continuation');
    cooperative = new CooperativeResearch({ state, workers: [lead, researcher],
      access: new Map([lead, researcher].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: { ...modules, M2: { ...modules.M2, checkTask: host.checkTask } }, exclusiveCheck: async check => check() });
    priorAssessment();
  });

  afterEach(async () => {
    await cooperative.stop(); await Promise.all(pending);
    expect(host.session).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('recovers the blocked original argument even while an unrelated proof consumer is ready', async () => {
    const saved = record('saved_auxiliary').integratedCheck;
    const action = await recovery();
    expect(state.cooperation!.frontierRecoveries).toEqual([expect.objectContaining({ id: action.recovery!.id, status: 'requested' })]);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(record('more_auxiliary').status).toBe('pending');
    expect(record('saved_auxiliary').integratedCheck).toBe(saved);
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it('requests recovery without interrupting independent proof work already running', async () => {
    const work = await start('more_auxiliary');
    const action = await recovery();
    expect(action.recovery!.taskIds).toEqual(['missing_argument']);
    expect(record('more_auxiliary')).toMatchObject({ status: 'running', assignment: work.assignment, attempts: 1 });
    expect(cooperative.current(work)).toBe(true);
    expect(events.filter(item => item.event === 'frontier_recovery_requested')).toHaveLength(1);
  });

  it('keeps Lead recovery available when independent work fills the only route slot', async () => {
    const route = state.cooperation!.groups![0];
    route.group = { ...route.group, maxConcurrent: 1 }; priorAssessment();
    const work = await start('more_auxiliary');
    expect(route.busy).toBe(1);
    const action = await recovery();
    expect(action.recovery!.taskIds).toEqual(['missing_argument']);
    expect(route.busy).toBe(1);
    expect(record('more_auxiliary')).toMatchObject({ status: 'running', assignment: work.assignment, attempts: 1 });
    expect(cooperative.current(work)).toBe(true);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
  });

  it('recovers the failed active OR premise when a parked alternative already has all checked inputs', async () => {
    const { goal, saved, parked } = alternativeFrontier();
    const routes = structuredClone(state.cooperation!.proofRoutes), savedProof = saved.integratedCheck, parkedProof = parked.integratedCheck;
    const report = buildProofContinuation(state.cooperation!.tasks, { proofRoutes: routes });
    expect(report.goals.find(item => item.taskId === goal.task.id)?.frontier).toEqual([goal.task.id]);
    expect(report.goals.find(item => item.taskId === goal.task.id)?.alternatives).toEqual([
      { routeId: 'parked_route', frontier: [], missingDependencies: [], parkedBy: goal.parkedRoutes!.parked_route },
      { routeId: 'active_route', frontier: ['missing_argument'], missingDependencies: [], parkedBy: [] },
    ]);

    const action = await recovery();

    expect(action.recovery!.taskIds).toEqual(['missing_argument']);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(state.cooperation!.proofRoutes).toEqual(routes);
    expect(goal.alternativeRoutes).toEqual(routes);
    expect(goal.parkedRoutes!.parked_route).toHaveLength(1);
    expect(saved.integratedCheck).toBe(savedProof);
    expect(parked.integratedCheck).toBe(parkedProof);
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it('retains every active OR frontier and all original-goal owners of shared failed premises', async () => {
    const { goal } = alternativeFrontier();
    const other = state.cooperation!.tasks.find(node => node.task.kind === 'goal' && node !== goal)!;
    other.task = { ...other.task, status: 'active', dependsOn: [] };
    const alternative: TaskRecord = { task: helper('alternative_missing'), status: 'blocked', attempts: 2,
      feedback: 'A distinct construction is still missing.' };
    const closing: TaskRecord = { task: helper('alternative_closing', [alternative.task.id]), status: 'pending', attempts: 0 };
    state.cooperation!.tasks.push(alternative, closing);
    state.cooperation!.proofRoutes!.push(
      { id: 'alternative_route', targetTaskId: goal.task.id, prerequisiteTaskIds: [alternative.task.id], closingTaskId: closing.task.id },
      { id: 'other_active_route', targetTaskId: other.task.id, prerequisiteTaskIds: ['missing_argument'], closingTaskId: 'active_closing' },
      { id: 'other_alternative_route', targetTaskId: other.task.id, prerequisiteTaskIds: [alternative.task.id], closingTaskId: closing.task.id },
    );
    (cooperative as any).syncProofRoutes(); (cooperative as any).changed(); priorAssessment();
    const routes = structuredClone(state.cooperation!.proofRoutes);
    const frontier = (cooperative as any).activeGoalFrontier();
    expect(frontier).toHaveLength(2);
    for (const taskId of ['missing_argument', alternative.task.id]) {
      const entry = frontier.find((item: { taskId: string }) => item.taskId === taskId);
      expect(entry?.goalIds).toEqual(expect.arrayContaining([goal.task.id, other.task.id]));
      expect(entry?.goalIds).toHaveLength(2);
    }

    const action = await leadOutcome();

    expect(action).toMatchObject({ kind: 'lead', recovery: {
      taskIds: expect.arrayContaining(['missing_argument', alternative.task.id]),
      goalIds: expect.arrayContaining([goal.task.id, other.task.id]),
    } });
    if (!action || action === 'waiting' || action.kind !== 'lead' || !action.recovery) throw new Error('expected_shared_goal_recovery');
    expect(action.recovery.taskIds).toHaveLength(2);
    expect(action.recovery.goalIds).toHaveLength(2);
    expect(state.cooperation!.frontierRecoveries).toEqual([expect.objectContaining({
      taskIds: action.recovery.taskIds, goalIds: action.recovery.goalIds, status: 'requested',
    })]);
    expect(state.cooperation!.proofRoutes).toEqual(routes);
    expect(goal.alternativeRoutes?.map(route => route.id)).toEqual(['parked_route', 'active_route', 'alternative_route']);
    expect(other.alternativeRoutes?.map(route => route.id)).toEqual(['other_active_route', 'other_alternative_route']);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(alternative).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it.each(['paused', 'stopped'] as const)('preserves a %s failed OR premise when selecting recovery', async control => {
    alternativeFrontier();
    const core = record('missing_argument'); core.task = { ...core.task, status: control }; priorAssessment();

    await expectWaiting();

    expect(core).toMatchObject({ status: 'blocked', attempts: 2, task: { status: control } });
    expect(record('original_goal').parkedRoutes!.parked_route).toHaveLength(1);
  });

  it.each(['paused', 'stopped'] as const)('excludes a %s original goal from OR recovery ownership', async control => {
    const { goal } = alternativeFrontier();
    const other = state.cooperation!.tasks.find(node => node.task.kind === 'goal' && node !== goal)!;
    other.task = { ...other.task, status: 'active', dependsOn: [] };
    state.cooperation!.proofRoutes!.push({ id: 'other_active_route', targetTaskId: other.task.id,
      prerequisiteTaskIds: ['missing_argument'], closingTaskId: 'active_closing' });
    goal.task = { ...goal.task, status: control };
    (cooperative as any).syncProofRoutes(); (cooperative as any).changed(); priorAssessment();

    expect(await leadOutcome()).toMatchObject({ kind: 'lead', recovery: {
      taskIds: ['missing_argument'], goalIds: [other.task.id],
    } });

    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(goal.task.status).toBe(control);
  });

  it.each(['paused', 'stopped', 'turns-exhausted'] as const)('preserves a %s prerequisite group in OR recovery', async control => {
    const { closing } = alternativeFrontier(), core = record('missing_argument');
    core.task = { ...core.task, groupId: 'active_inputs', sharing: 'problem' };
    closing.task = { ...closing.task, groupId: 'active_inputs', sharing: 'problem' };
    state.cooperation!.groups!.push({ group: { id: 'active_inputs', objective: 'Active route input controls', revision: 0,
      status: control === 'turns-exhausted' ? 'active' : control,
      ...(control === 'turns-exhausted' ? { maxTurns: 1 } : {}) }, turns: control === 'turns-exhausted' ? 1 : 0 });
    priorAssessment();

    await expectWaiting();

    expect(core).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(record('original_goal').parkedRoutes!.parked_route).toHaveLength(1);
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it.each(['paused', 'turns-exhausted'] as const)('preserves the %s group gate when deciding recovery', async control => {
    const route = state.cooperation!.groups![0];
    if (control === 'paused') route.group = { ...route.group, status: 'paused' };
    else { route.group = { ...route.group, maxTurns: 1 }; route.turns = 1; }
    priorAssessment();
    expect(await leadOutcome()).toBeUndefined();
    expect(state.cooperation!.frontierRecoveries ?? []).toEqual([]);
    expect(events.filter(item => item.event === 'frontier_recovery_requested')).toEqual([]);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
  });

  it('allows a pending original prerequisite to advance before requesting recovery', async () => {
    record('original_goal').task = { ...record('original_goal').task, conditional: false };
    record('missing_argument').status = 'pending'; priorAssessment();
    await expectWaiting();
    const work = await start('missing_argument');
    expect(work.task.id).toBe('missing_argument');
    expect(state.cooperation!.frontierRecoveries ?? []).toEqual([]);
  });

  it('waits for running work on the original path instead of issuing a recovery', async () => {
    record('original_goal').task = { ...record('original_goal').task, conditional: false };
    record('missing_argument').status = 'pending'; priorAssessment();
    await start('missing_argument');
    await expectWaiting();
    expect(record('missing_argument').status).toBe('running');
  });

  it('keeps a targeted investigation eligible before a new Lead recovery', async () => {
    const probe: CooperativeTask = { id: 'targeted_investigation', kind: 'research', objective: 'Find a new construction for the missing original argument.',
      dependsOn: ['missing_argument'], revision: 0 };
    record('more_auxiliary').task = { ...record('more_auxiliary').task, status: 'paused' };
    state.cooperation!.tasks.push({ task: probe, status: 'pending', attempts: 0 }); priorAssessment();
    await expectWaiting();
    await start(probe.id);
    expect(record('missing_argument')).toMatchObject({ status: 'blocked', attempts: 2 });
    expect(record(probe.id).integratedCheck).toBeUndefined();
  });

  it('dispatches a conditional original consumer before recovering its still-open typed premise', async () => {
    const goal = record('original_goal'); goal.task = { ...goal.task, conditional: true }; priorAssessment();
    await expectWaiting();
    const work = await start('original_goal');
    expect(work.task.conditional).toBe(true);
    expect(record('missing_argument').status).toBe('blocked');
    expect(goal.integratedCheck).toBeUndefined();
  });

  it.each(['supporting', 'refuted', 'inconclusive'] as const)
  ('dispatches an independent early review of blocked inputs and retains a %s result as advisory', async conclusion => {
    const reviewRoot = path.join(directory, 'independent-reviewer');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', reviewRoot, seed]);
    const checker: ResearchWorker = { ...researcher, id: 'independent-checker', worktree: reviewRoot };
    const core = record('missing_argument');
    core.assignment = { taskId: core.task.id, taskDigest: taskVersion(core.task),
      workerId: researcher.id, seedCommit: seed };
    const task: CooperativeTask = { id: 'early_route_check', kind: 'research', reviewScope: 'feasibility',
      objective: 'Test whether the proposed core input is sufficient and mathematically feasible.',
      dependsOn: ['original_goal', core.task.id], revision: 0 };
    state.cooperation!.tasks.push({ task, status: 'pending', attempts: 0 });
    const modules = configuredSolverModules('direct', 'continuation');
    cooperative = new CooperativeResearch({ state, workers: [lead, researcher, checker],
      access: new Map([lead, researcher, checker].map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
      modules: { ...modules, M2: { ...modules.M2, checkTask: host.checkTask } }, exclusiveCheck: async check => check() });
    priorAssessment();

    const ordinary = await cooperative.next(researcher, budget);
    expect(ordinary).toMatchObject({ kind: 'task', task: { id: 'more_auxiliary' } });
    const action = await cooperative.next(checker, budget);
    expect(action).toMatchObject({ kind: 'task', task: { id: task.id }, assignment: { workerId: checker.id } });
    if (action?.kind !== 'task') throw new Error('expected_independent_feasibility_review');
    expect(cooperative.started(checker, action)).toBe(true);
    const canonical = state.cooperation!.canonicalCommit;
    const commit = checkpoint({ summary: 'The core input needs a sharper uniform estimate.', conclusion,
      evidenceRefs: ['Exact core contract and original consumer'] }, checker);
    await cooperative.deliver(checker, action, commit);

    expect(record(task.id)).toMatchObject({ status: 'completed', attempts: 1 });
    expect(record(task.id).finding).toContain(conclusion);
    expect(record(task.id).proof).toBeUndefined();
    expect(record(task.id).integratedCheck).toBeUndefined();
    expect(core.status).toBe('blocked');
    expect(record('original_goal').status).toBe('pending');
    expect(record('original_goal').integratedCheck).toBeUndefined();
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it.each(['owner', 'engineer'] as const)('refunds an unstarted review when a directly inspected %s becomes its reviewer', async origin => {
    const { checker, task, claim } = feasibilityPeers(origin === 'engineer' ? 'engineer' : 'researcher');
    const action = await claim(), route = state.cooperation!.groups![0];
    const attempts = record(task.id).attempts, turns = route.turns;
    if (origin === 'owner') record('missing_argument').task = { ...record('missing_argument').task, ownerId: checker.id };
    else route.group = { ...route.group, engineerId: checker.id };

    expect(cooperative.current(action)).toBe(false);
    expect(cooperative.started(checker, action)).toBe(false);
    expect(record(task.id)).toMatchObject({ status: 'pending', attempts });
    expect(record(task.id).assignment).toBeUndefined();
    expect(route.turns).toBe(turns);
    expect(events).toContainEqual({ event: 'feasibility_review_reassigned', details: expect.objectContaining({
      taskId: task.id, workerId: checker.id, reason: 'reviewer-no-longer-independent',
    }) });
  });

  it('interrupts an active review after an owner edit while preserving its explicit review owner and unsaved notes', async () => {
    const { checker, task, claim } = feasibilityPeers('researcher', true), action = await claim();
    expect(cooperative.started(checker, action)).toBe(true);
    const interrupt = vi.fn(async () => {});
    cooperative.activate(checker, action, interrupt, async () => {});
    const notes = 'An unfinished independent mathematical argument.\n';
    fs.writeFileSync(path.join(checker.worktree, 'RESEARCH.md'), notes);
    const head = git(checker.worktree, ['rev-parse', 'HEAD']);
    const plan = parseCooperationPlan(problem, { tasks: state.cooperation!.tasks.map(node =>
      node.task.id === 'missing_argument' ? { ...node.task, ownerId: checker.id } : node.task),
    groups: state.cooperation!.groups!.map(route => route.group) });
    await (cooperative as any).acceptPlan(plan);

    expect(interrupt).toHaveBeenCalledTimes(1);
    expect(cooperative.current(action)).toBe(false);
    expect(record(task.id)).toMatchObject({ status: 'pending', attempts: 1, task: { ownerId: checker.id } });
    expect(record(task.id).assignment).toBeUndefined();
    expect(fs.readFileSync(path.join(checker.worktree, 'RESEARCH.md'), 'utf8')).toBe(notes);
    expect(git(checker.worktree, ['rev-parse', 'HEAD'])).toBe(head);
    expect((cooperative as any).hasAssignableTask(new Set([task.id]))).toBe(false);
  });

  it('recovers an invalid restored reviewer pin and ignores its late delivery after a new independent assignment', async () => {
    const { checker, replacement, task, create, claim } = feasibilityPeers(), old = await claim();
    expect(cooperative.started(checker, old)).toBe(true);
    record('missing_argument').task = { ...record('missing_argument').task, ownerId: checker.id };
    const saved = record('saved_auxiliary'); saved.status = 'pending'; saved.task = { ...saved.task, status: 'paused' };
    state = JSON.parse(JSON.stringify(state));
    cooperative = create();
    await cooperative.restore();

    expect(record(task.id)).toMatchObject({ status: 'pending', attempts: 1 });
    expect(record(task.id).assignment).toBeUndefined();
    const fresh = await claim(replacement);
    expect(fresh.assignment.assignmentId).not.toBe(old.assignment.assignmentId);
    expect(cooperative.started(replacement, fresh)).toBe(true);
    const late = checkpoint({ summary: 'Late work from the now disqualified reviewer.', conclusion: 'supporting' }, checker);
    await cooperative.deliver(checker, old, late);

    expect(record(task.id)).toMatchObject({ status: 'running', attempts: 2, assignment: fresh.assignment });
    expect(record(task.id).finding).toBeUndefined();
    expect(cooperative.current(fresh)).toBe(true);
    expect(state.cooperation!.deliveries).toContainEqual(expect.objectContaining({ taskId: task.id,
      producer: checker.id, status: 'superseded', commit: late }));
    const current = checkpoint({ summary: 'A new independent check identifies the exact remaining estimate.', conclusion: 'inconclusive' }, replacement);
    await cooperative.deliver(replacement, fresh, current);
    expect(record(task.id).status).toBe('completed');
    expect(record(task.id).finding).toContain('A new independent check');
    expect(record(task.id).proof).toBeUndefined();
    expect(record(task.id).integratedCheck).toBeUndefined();
    expect(host.checkTask).not.toHaveBeenCalled();
  });

  it('rechecks reviewer independence after an asynchronous draft restore before returning the assignment', async () => {
    const { checker, replacement, task, claim } = feasibilityPeers(), old = await claim();
    cooperative.interrupted(checker, old);
    vi.spyOn(cooperative as any, 'researchWorkspaceChanged').mockReturnValue(true);
    const restore = vi.spyOn(cooperative as any, 'restoreResearchDraft').mockImplementation(async () => {
      record('missing_argument').task = { ...record('missing_argument').task, ownerId: checker.id };
      await Promise.resolve();
      return true;
    });
    let returned = false;
    const waiting = cooperative.next(checker, budget).then(action => { returned = true; return action; });
    pending.push(waiting);
    await vi.waitFor(() => {
      expect(restore).toHaveBeenCalled();
      expect(record(task.id).status).toBe('pending');
      expect(record(task.id).assignment).toBeUndefined();
      expect((cooperative as any).waiters.size).toBeGreaterThan(0);
    });
    expect(returned).toBe(false);
    expect(cooperative.current(old)).toBe(false);
    const fresh = await claim(replacement);
    expect(fresh.assignment.assignmentId).not.toBe(old.assignment.assignmentId);
    expect(record(task.id).attempts).toBe(0);
  });

  it('does not request the same mathematical recovery again after unrelated new findings', async () => {
    const question: CooperativeTask = { id: 'independent_question', kind: 'research', objective: 'Investigate an independent identity.', dependsOn: [], revision: 0 };
    state.cooperation!.tasks.unshift({ task: question, status: 'pending', attempts: 0 }); priorAssessment();
    const action = await recovery();
    const commit = checkpoint({ tasks: state.cooperation!.tasks.map(item => item.task),
      groups: state.cooperation!.groups!.map(item => item.group),
      recovery: { status: 'awaiting-input', reason: 'A precise cancellation estimate is still needed.' } });
    await cooperative.deliver(lead, action, commit);
    expect(state.cooperation!.frontierRecoveries).toMatchObject([{ id: action.recovery!.id, status: 'awaiting-input' }]);
    const work = await start(question.id);
    const finding = checkpoint({ summary: 'A distinct auxiliary identity is available, with no connection to the missing estimate.' }, researcher);
    await cooperative.deliver(researcher, work, finding); cooperative.deactivate(researcher);
    expect(record(question.id).status).toBe('completed');
    expect(await leadOutcome()).toBe('waiting');
    expect(state.cooperation!.frontierRecoveries).toMatchObject([{ id: action.recovery!.id, status: 'awaiting-input' }]);
    expect(events.filter(item => item.event === 'frontier_recovery_requested')).toHaveLength(1);
    expect(record('more_auxiliary').status).toBe('pending');
    expect(record('original_goal').integratedCheck).toBeUndefined();
  });

  it.each(['consumer', 'proof-route'] as const)('resumes proof work when recovery connects a saved helper through an explicit %s', async connection => {
    const action = await recovery();
    let tasks = state.cooperation!.tasks.map(item => item.task);
    let routes: unknown[] = [];
    if (connection === 'consumer') tasks = tasks.map(task => task.id === 'missing_argument' ? { ...task, dependsOn: ['more_auxiliary'] } : task);
    else {
      tasks = tasks.map(task => task.id === 'original_goal' ? { ...task, dependsOn: [] } : task);
      tasks.push(helper('closing_argument', ['more_auxiliary'], 'forall (n : Nat), n + 0 = n'));
      routes = [{ id: 'alternative_argument', targetTaskId: 'original_goal', prerequisiteTaskIds: ['more_auxiliary'], closingTaskId: 'closing_argument' }];
    }
    const commit = checkpoint({ tasks, groups: state.cooperation!.groups!.map(item => item.group),
      ...(routes.length ? { proofRoutes: routes } : {}), recovery: { status: 'planned', taskIds: ['more_auxiliary'] } });
    await cooperative.deliver(lead, action, commit);
    expect(state.cooperation!.error).toBeUndefined();
    expect(state.cooperation!.frontierRecoveries).toMatchObject([{ status: 'planned', readyTaskIds: ['more_auxiliary'] }]);
    const work = await start('more_auxiliary');
    expect(work.assignment.dependencies).toContainEqual({ taskId: 'saved_auxiliary', taskDigest: taskVersion(record('saved_auxiliary').task) });
    expect(record('original_goal').integratedCheck).toBeUndefined();
    if (connection === 'consumer') expect(record('missing_argument').task.dependsOn).toEqual(['more_auxiliary']);
    else expect(record('original_goal').alternativeRoutes).toMatchObject([{ closingTaskId: 'closing_argument' }]);
  });
});
