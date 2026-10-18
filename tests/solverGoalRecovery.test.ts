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
    record('missing_argument').status = 'pending'; priorAssessment();
    await expectWaiting();
    const work = await start('missing_argument');
    expect(work.task.id).toBe('missing_argument');
    expect(state.cooperation!.frontierRecoveries ?? []).toEqual([]);
  });

  it('waits for running work on the original path instead of issuing a recovery', async () => {
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
