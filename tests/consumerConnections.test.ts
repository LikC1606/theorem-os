import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { CooperativeResearch, parseCooperationPlan } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { readyResearchTasks, taskCanStart } from '../src/solver/modules/search';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { automaticTaskConnection, createTaskConnectionCheck, freshTaskConnection, hasTaskConnectionCheck,
  taskConnectionCheckCurrent } from '../src/solver/taskConnections';
import { taskVersion, type CooperativeAction, type CooperativeTask, type TaskAssignment, type TaskRecord } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));
const identity = { environmentDigest: 'environment', problemReceiptDigest: 'problem' };
const records = (): TaskRecord[] => [{ task: { id: 'input', kind: 'lemma', objective: 'Core input', type: 'True',
  theoremName: 'N.input', proofPath: 'Submission.lean', revision: 0, dependsOn: [] }, status: 'pending', attempts: 0 },
{ task: { id: 'consumer', kind: 'goal', objective: 'Apply the input', theoremName: 'N.target',
  proofPath: 'Submission.lean', revision: 0, dependsOn: ['input'] }, status: 'pending', attempts: 8 }];
const assignmentFor = (tasks: TaskRecord[]): TaskAssignment => ({ taskId: tasks[1].task.id,
  taskDigest: taskVersion(tasks[1].task), workerId: 'engineer', seedCommit: 'fixed-seed',
  dependencies: [{ taskId: tasks[0].task.id, taskDigest: taskVersion(tasks[0].task) }] });

describe('consumer connection dispatch', () => {
  it('offers an ordinary consumer before its typed input without changing the task contract', () => {
    const tasks = records(), digest = taskVersion(tasks[1].task);
    expect(taskCanStart(tasks[1].task, tasks)).toBe(true);
    expect(readyResearchTasks(tasks)[0].task.id).toBe('consumer');
    expect(freshTaskConnection(tasks[1], tasks)).toBe(true);
    const assignment = assignmentFor(tasks);
    assignment.connectionCheck = createTaskConnectionCheck(tasks[1].task, assignment, tasks, identity);
    expect(hasTaskConnectionCheck(tasks[1].task, assignment)).toBe(true);
    tasks[1].assignment = assignment;
    expect(freshTaskConnection(tasks[1], tasks)).toBe(false);
    expect(taskVersion(tasks[1].task)).toBe(digest); expect(tasks[1].task.conditional).toBeUndefined();
  });

  it('binds the dispatch to exact inputs, environment, seed and route topology', () => {
    const tasks = records(), assignment = assignmentFor(tasks);
    assignment.connectionCheck = createTaskConnectionCheck(tasks[1].task, assignment, tasks, identity);
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, identity)).toBe(true);
    tasks[0].status = 'integrated';
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, identity)).toBe(true);
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, { ...identity, environmentDigest: 'other' })).toBe(false);
    expect(hasTaskConnectionCheck(tasks[1].task, { ...assignment, seedCommit: 'other' })).toBe(false);
    tasks[0].task = { ...tasks[0].task, type: 'False' };
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, identity)).toBe(false);
    const fresh = records(), next = assignmentFor(fresh);
    next.connectionCheck = createTaskConnectionCheck(fresh[1].task, next, fresh, identity);
    fresh[1].alternativeRoutes = [{ id: 'route', targetTaskId: 'consumer', closingTaskId: 'input', prerequisiteTaskIds: [] }];
    expect(taskConnectionCheckCurrent(fresh[1].task, next, fresh, identity)).toBe(false);
  });

  it('respects explicit opt out, untyped blockers, private inputs and paused groups', () => {
    const tasks = records(); tasks[1].task = { ...tasks[1].task, conditional: false };
    expect(taskCanStart(tasks[1].task, tasks)).toBe(false);
    tasks[1].task = { ...tasks[1].task, conditional: undefined };
    tasks[0].task = { ...tasks[0].task, groupId: 'private', sharing: 'group' };
    expect(automaticTaskConnection(tasks[1].task, tasks)).toBe(false);
    tasks[0].task = { ...tasks[0].task, groupId: undefined, kind: 'research', type: undefined };
    expect(automaticTaskConnection(tasks[1].task, tasks)).toBe(false);
    expect(readyResearchTasks(records(), [{ group: { id: 'main', objective: 'Paused', status: 'paused', revision: 0 }, turns: 0 }])).toEqual([]);
  });

  it('does not revive blocked or parked inputs through a fresh consumer', () => {
    const tasks = records(); tasks[0].status = 'blocked';
    expect(taskCanStart(tasks[1].task, tasks)).toBe(false);
    tasks[0].status = 'pending'; tasks[0].routeParking = ['missing-core-input'];
    expect(taskCanStart(tasks[1].task, tasks)).toBe(false);
    tasks[0].routeParking = [];
    expect(taskCanStart(tasks[1].task, tasks)).toBe(true);
  });

  it.each(['paused', 'stopped', 'spent'] as const)('does not offer an early check using an unfinished input from a %s group', control => {
    const tasks = records(); tasks[0].task = { ...tasks[0].task, groupId: 'input-group', sharing: 'problem' };
    const groups = [{ group: { id: 'main', objective: 'Consumer', status: 'active' as const, revision: 0 }, turns: 0 },
      { group: { id: 'input-group', objective: 'Input', status: control === 'spent' ? 'active' as const : control,
        revision: 0, maxTurns: control === 'spent' ? 1 : undefined }, turns: 1 }];
    expect(taskCanStart(tasks[1].task, tasks, groups)).toBe(false);
    expect(readyResearchTasks(tasks, groups)).toEqual([]);
    tasks[0].status = 'integrated';
    expect(taskCanStart(tasks[1].task, tasks, groups)).toBe(true);
  });

  it.each(['integrated', 'paused', 'stopped', 'parked', 'route-parked', 'group-paused', 'group-stopped', 'group-spent'] as const)(
    'does not offer a helper connection solely for a %s consumer', control => {
      const tasks = records(); tasks[1].task = { ...tasks[1].task, kind: 'lemma', type: 'True' };
      tasks.push({ task: { id: 'target', kind: 'goal', objective: 'Original consumer', theoremName: 'N.target',
        proofPath: 'Submission.lean', revision: 0, dependsOn: ['consumer'], groupId: 'target-group' }, status: 'pending', attempts: 0 });
      const consumer = tasks[2];
      if (control === 'integrated') consumer.status = 'integrated';
      if (control === 'paused' || control === 'stopped') consumer.task = { ...consumer.task, status: control };
      if (control === 'parked') consumer.routeParking = ['closed-route'];
      if (control === 'route-parked') {
        consumer.task = { ...consumer.task, dependsOn: [] };
        consumer.alternativeRoutes = [{ id: 'closed-route', targetTaskId: 'target', closingTaskId: 'consumer', prerequisiteTaskIds: [] }];
        consumer.parkedRoutes = { 'closed-route': ['missing-input'] };
      }
      const groups = [{ group: { id: 'main', objective: 'Helper', status: 'active' as const, revision: 0 }, turns: 0 },
        { group: { id: 'target-group', objective: 'Consumer', revision: 0,
          status: control === 'group-paused' ? 'paused' as const : control === 'group-stopped' ? 'stopped' as const : 'active' as const,
          maxTurns: control === 'group-spent' ? 1 : undefined }, turns: 1 }];
      expect(automaticTaskConnection(tasks[1].task, tasks, groups)).toBe(false);
      expect(taskCanStart(tasks[1].task, tasks, groups)).toBe(false);
      expect(readyResearchTasks(tasks, groups).map(node => node.task.id)).not.toContain('consumer');
    });

  it('checks an OR closing lemma early while the original target still waits for a checked route', () => {
    const tasks = records();
    tasks.splice(1, 0, { task: { id: 'closing', kind: 'lemma', objective: 'Close this route', type: 'True',
      theoremName: 'N.closing', proofPath: 'Submission.lean', revision: 0, dependsOn: ['input'] }, status: 'pending', attempts: 12 });
    tasks[2].task = { ...tasks[2].task, dependsOn: [] };
    tasks[2].alternativeRoutes = [{ id: 'route', targetTaskId: 'consumer', closingTaskId: 'closing', prerequisiteTaskIds: ['input'] }];
    expect(readyResearchTasks(tasks)[0].task.id).toBe('closing');
    expect(taskCanStart(tasks[2].task, tasks)).toBe(false);
    const assignment: TaskAssignment = { taskId: 'closing', taskDigest: taskVersion(tasks[1].task),
      workerId: 'engineer', seedCommit: 'seed', dependencies: [{ taskId: 'input', taskDigest: taskVersion(tasks[0].task) }] };
    assignment.connectionCheck = createTaskConnectionCheck(tasks[1].task, assignment, tasks, identity);
    tasks[2].alternativeRoutes = [{ ...tasks[2].alternativeRoutes[0], id: 'changed-route' }];
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, identity)).toBe(false);
  });
});

describe('host consumer connection lifecycle', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch;
  let instances: { cooperative: CooperativeResearch; controller: AbortController }[], checkedSources: string[];
  type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const sourcePath = (worker: ResearchWorker) => path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
  const create = () => {
    const controller = new AbortController(), cooperative = new CooperativeResearch({ state, workers,
      access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    instances.push({ cooperative, controller }); return cooperative;
  };
  const assigned = async (worker: ResearchWorker) => {
    const action = await cooperative.next(worker, budget);
    if (action?.kind !== 'task') throw new Error('fixture_missing_task');
    expect(cooperative.started(worker, action)).toBe(true); return action;
  };
  const deliverConsumer = async () => {
    const action = await assigned(workers[2]); expect(action.task.id).toBe('goal_0');
    fs.writeFileSync(sourcePath(workers[2]), fs.readFileSync(sourcePath(workers[2]), 'utf8')
      .replace('n + 0 = n := by sorry', 'n + 0 = n := by\n  have h : True := Tutorial.helper\n  rfl'));
    await cooperative.deliver(workers[2], action, commitSolverSources(problem, workers[2].worktree));
    return action;
  };
  const deliverInput = async (action: TaskAction) => {
    fs.writeFileSync(sourcePath(workers[1]), fs.readFileSync(sourcePath(workers[1]), 'utf8')
      .replace('theorem add_zero', 'lemma helper : True := by trivial\ntheorem add_zero'));
    await cooperative.deliver(workers[1], action, commitSolverSources(problem, workers[1].worktree));
  };

  beforeEach(async () => {
    host.verify.mockReset().mockImplementation(async (request: MathematicsVerifierBatchRequest): Promise<MathematicsVerifierBatchResult> => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8'); checkedSources.push(source);
      const passed = !/\b(?:sorry|admit)\b/u.test(source);
      return { schema: 'deepscientist.mathematics.verification-batch/v1', status: passed ? 'kernel_verified' : 'failed',
        targetCommit: request.targetCommit!, sessionId: 'connection-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
        results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
          receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
          status: passed ? 'kernel_verified' : 'failed', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
    });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'consumer-connection-')));
    workspace = path.join(directory, 'workspace'); const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    workers = [{ id: 'lead', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles },
      ...(['researcher', 'engineer', 'observer'] as const).map(id => {
        const worktree = path.join(directory, id); git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
        return { id, role: id === 'engineer' ? 'engineer' as const : 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
      })];
    const tasks: CooperativeTask[] = [{ id: 'helper', kind: 'lemma', objective: 'Core input', type: 'True',
      theoremName: 'Tutorial.helper', proofPath: 'Submission.lean', dependsOn: [], revision: 0, ownerId: 'researcher' },
    { id: 'independent', kind: 'research', objective: 'Independent useful investigation', dependsOn: [], revision: 0, ownerId: 'observer' },
    ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal' as const, objective: 'Prove the original goal',
      theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: index ? [] : ['helper'], revision: 0,
      ownerId: 'engineer', status: index ? 'paused' as const : 'active' as const }))];
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks }) + '\n```');
    state = { schema: 'deepscientist.math.solver.v1', runId: 'connection-fixture', problem, taskDigest: 'task', buildDigest: 'build',
      environmentDigest: 'environment', evaluatorDigest: 'evaluator', model: 'unused', effort: 'unused', worktree: workspace,
      phase: 'running', turns: 0, failures: [], cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } };
    instances = []; checkedSources = []; cooperative = create(); await cooperative.restore();
  });
  afterEach(async () => {
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    expect(host.createSession).not.toHaveBeenCalled(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('dispatches the consumer before any input proof, keeps independent work executable, and integrates only after the input closes', async () => {
    const digest = taskVersion(node('goal_0').task), parent = await deliverConsumer();
    expect(parent.assignment.connectionCheck).toMatchObject({ consumer: { taskId: 'goal_0', taskDigest: digest },
      problemReceiptDigest: problem.receiptDigest, environmentDigest: 'environment' });
    expect(node('goal_0')).toMatchObject({ status: 'conditional', attempts: 1, proof: { passed: true,
      conditions: [{ taskId: 'helper', taskDigest: taskVersion(node('helper').task) }] } });
    expect(node('goal_0').integratedCheck).toBeUndefined(); expect(state.cooperation!.review).toBeUndefined();
    expect(taskVersion(node('goal_0').task)).toBe(digest); expect(node('goal_0').task.conditional).toBeUndefined();
    expect(checkedSources.some(source => source.includes('theorem add_zero (helper : True)'))).toBe(true);
    const independent = await assigned(workers[3]); expect(independent.task.id).toBe('independent');
    const context = buildResearchContext(problem, state, { root: directory, worktree: workers[2].worktree, taskText: 'Problem',
      environment: {}, retrievalRoot: directory, assignment: parent, maxOptionalContextBytes: 0 });
    expect(context.instructions).toContain('host-dispatched consumer connection check');
    expect(context.workContract?.input).toHaveProperty('connectionCheck.basisDigest', parent.assignment.connectionCheck!.basisDigest);
    await deliverInput(await assigned(workers[1]));
    expect(node('goal_0')).toMatchObject({ status: 'integrated', attempts: 1, integratedCheck: { passed: true } });
    expect(node('goal_0').integratedCheck!.conditions).toBeUndefined();
    const canonical = committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`);
    expect(canonical).toContain('lemma helper : True := by trivial'); expect(canonical).not.toContain('(helper : True)');
  });

  it('rechecks restored conditional receipts without another consumer dispatch or granting unproved inputs acceptance', async () => {
    await deliverConsumer(); const proof = node('goal_0').proof!, previous = host.verify.mock.calls.length;
    const snapshot = path.join(directory, 'state.json'); writeSolverRunState(snapshot, state);
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    state = readSolverRunState(snapshot); cooperative = create(); await cooperative.restore();
    expect(host.verify.mock.calls.length).toBeGreaterThan(previous);
    expect(node('goal_0')).toMatchObject({ status: 'conditional', attempts: 1, proof: { commit: proof.commit } });
    expect(node('goal_0').integratedCheck).toBeUndefined();
    await deliverInput(await assigned(workers[1]));
    expect(node('goal_0')).toMatchObject({ status: 'integrated', attempts: 1 });
  });

  it('offers a fresh connection when the core contract changes and excludes the old late delivery', async () => {
    const old = await deliverConsumer(), oldBasis = old.assignment.connectionCheck!.basisDigest;
    const tasks = state.cooperation!.tasks.map(node => node.task.id === 'helper' ? { ...node.task, type: 'True ∧ True' } : node.task);
    await (cooperative as any).acceptPlan(parseCooperationPlan(problem, { tasks }));
    expect(cooperative.current(old)).toBe(false);
    expect(node('goal_0')).toMatchObject({ status: 'pending', attempts: 1 }); expect(node('goal_0').proof).toBeUndefined();
    const next = await assigned(workers[2]);
    expect(next.task.id).toBe('goal_0'); expect(next.assignment.connectionCheck!.basisDigest).not.toBe(oldBasis);
    expect(next.assignment.connectionCheck!.inputs).toEqual([{ taskId: 'helper', taskDigest: taskVersion(node('helper').task) }]);
    expect(node('goal_0').task.conditional).toBeUndefined();
  });
});
