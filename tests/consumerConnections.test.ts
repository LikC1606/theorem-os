import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { buildResearchContext } from '../src/solver/modules/context';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { readyResearchTasks, taskCanStart } from '../src/solver/modules/search';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { automaticTaskConnection, createTaskConnectionCheck, freshTaskConnection, hasTaskConnectionCheck,
  taskConnectionCheckCurrent } from '../src/solver/taskConnections';
import { freshlyAccepted, taskVersion, type CooperativeAction, type CooperativeTask, type TaskAssignment, type TaskRecord } from '../src/solver/tasks';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { verifiedBatch } from './helpers/verifier';

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

  it('freezes only unfinished inputs and binds their assumption permission to the exact worker dispatch', () => {
    const tasks = records(), assignment: TaskAssignment = { ...assignmentFor(tasks), assignmentId: 'dispatch-1' };
    tasks.push({ ...tasks[0], task: { ...tasks[0].task, id: 'ready', theoremName: 'N.ready' }, status: 'integrated' });
    assignment.dependencies.push({ taskId: 'ready', taskDigest: taskVersion(tasks[2].task) });
    assignment.connectionCheck = createTaskConnectionCheck(tasks[1].task, assignment, tasks, identity);
    expect(assignment.connectionCheck.assumedInputs).toEqual([{ taskId: 'input', taskDigest: taskVersion(tasks[0].task) }]);
    tasks[0].status = 'integrated';
    expect(taskConnectionCheckCurrent(tasks[1].task, assignment, tasks, identity)).toBe(true);
    expect(hasTaskConnectionCheck(tasks[1].task, { ...assignment, workerId: 'another-worker' })).toBe(false);
    expect(hasTaskConnectionCheck(tasks[1].task, { ...assignment, assignmentId: 'dispatch-2' })).toBe(false);
    expect(hasTaskConnectionCheck({ ...tasks[1].task, objective: 'Changed contract' }, assignment)).toBe(false);
  });

  it.each([
    ['absent', 'namespace N\nend N\n'],
    ['in another namespace', 'namespace Other\nlemma N.input : True := by trivial\nend Other\n'],
  ])('includes integrated inputs %s from an upgraded historical assignment seed', (_description, source) => {
    const tasks = records(), assignment = assignmentFor(tasks);
    tasks[0].status = 'integrated';
    tasks.push({ ...tasks[0], task: { ...tasks[0].task, id: 'unfinished', theoremName: 'N.unfinished' }, status: 'pending' });
    assignment.dependencies.push({ taskId: 'unfinished', taskDigest: taskVersion(tasks[2].task) });
    assignment.connectionCheck = createTaskConnectionCheck(tasks[1].task, assignment, tasks, identity,
      () => source);
    expect(assignment.connectionCheck.assumedInputs).toEqual(assignment.dependencies);
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
    const controller = new AbortController(), cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory,
      signal: controller.signal });
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
      const batch = verifiedBatch(request, { sessionId: 'connection-fixture' });
      return !/\b(?:sorry|admit)\b/u.test(source) ? batch
        : { ...batch, status: 'failed', results: batch.results.map(item => ({ ...item, status: 'failed' })) };
    });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('consumer-connection-');
    ({ directory, workspace, problem } = example);
    workers = [leadWorker(problem, workspace, 'lead'), ...['researcher', 'engineer', 'observer']
      .map(id => peerWorker(example, id, { role: id === 'engineer' ? 'engineer' : 'researcher' }))];
    const tasks: CooperativeTask[] = [{ id: 'helper', kind: 'lemma', objective: 'Core input', type: 'True',
      theoremName: 'Tutorial.helper', proofPath: 'Submission.lean', dependsOn: [], revision: 0, ownerId: 'researcher' },
    { id: 'independent', kind: 'research', objective: 'Independent useful investigation', dependsOn: [], revision: 0, ownerId: 'observer' },
    ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal' as const, objective: 'Prove the original goal',
      theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: index ? [] : ['helper'], revision: 0,
      ownerId: 'engineer', status: index ? 'paused' as const : 'active' as const }))];
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks }) + '\n```');
    state = solverState(problem, workspace, { runId: 'connection-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } });
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

  const rejectForwardInputReferences = () => {
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      const reference = source.indexOf('Tutorial.helper'), declaration = source.indexOf('lemma helper : True');
      const result = await verify(request);
      return reference >= 0 && (declaration < 0 || declaration > reference)
        ? { ...result, status: 'failed', results: result.results.map(item => ({ ...item, status: 'failed',
          error: 'Lean exited with status 1.',
          stdoutPreview: 'Submission.lean:5:4: error(lean.unknownIdentifier): Unknown identifier `Tutorial.helper`' })) }
        : result;
    });
  };

  it.each(['snapshot', 'legacy', 'explicit'] as const)('keeps %s dispatch assumptions when the input integrates before the worker delivers its old source', async mode => {
    rejectForwardInputReferences();
    const parentWorker = mode === 'explicit' ? workers[3] : workers[2];
    if (mode === 'explicit') {
      const tasks = state.cooperation!.tasks.map(item => item.task.id === 'goal_0' ? { ...item.task, status: 'paused' as const } : item.task);
      tasks.splice(tasks.findIndex(task => task.id === 'independent'), 1, { id: 'consumer', kind: 'lemma', conditional: true,
        objective: 'An explicitly conditional helper without an active downstream consumer', type: 'True',
        theoremName: 'Tutorial.consumer', proofPath: 'Submission.lean', dependsOn: ['helper'], revision: 0, ownerId: 'observer' });
      await (cooperative as any).acceptPlan(parseCooperationPlan(problem, { tasks }));
    }
    const parent = await assigned(parentWorker);
    expect(parent.task.id).toBe(mode === 'explicit' ? 'consumer' : 'goal_0');
    if (mode === 'explicit') expect(parent.assignment.connectionCheck).toBeUndefined();
    if (mode === 'legacy') {
      const { assumedInputs: _inputs, workerId: _worker, assignmentId: _assignment, basisDigest: _basis, ...legacy } = parent.assignment.connectionCheck!;
      parent.assignment.connectionCheck = { ...legacy, basisDigest: mathDigest(canonicalMathJson(legacy)) };
    }
    const source = fs.readFileSync(sourcePath(parentWorker), 'utf8');
    fs.writeFileSync(sourcePath(parentWorker), mode === 'explicit'
      ? source.replace('theorem add_zero', 'lemma consumer : True := by exact Tutorial.helper\ntheorem add_zero')
      : source.replace('n + 0 = n := by sorry', 'n + 0 = n := by\n  have h : True := Tutorial.helper\n  rfl'));
    const commit = commitSolverSources(problem, parentWorker.worktree);
    expect(committedSource(workspace, commit, `${problem.projectRelative}/Submission.lean`)).not.toContain('lemma helper');
    await deliverInput(await assigned(workers[1]));
    expect(node('helper').status).toBe('integrated');
    await cooperative.deliver(parentWorker, parent, commit);
    const consumer = node(parent.task.id);
    expect(consumer.status).toBe('integrated');
    expect(consumer.proof!.conditions).toEqual([{ taskId: 'helper', taskDigest: taskVersion(node('helper').task) }]);
    expect(consumer.integratedCheck!.conditions ?? []).toEqual([]);
    expect(freshlyAccepted(consumer, taskVersion(consumer.task))).toBe(true);
    expect(checkedSources.some(source => source.includes(`${mode === 'explicit' ? 'lemma consumer' : 'theorem add_zero'} (helper : True)`))).toBe(true);
    expect(checkedSources.at(-1)).toContain('lemma helper : True := by trivial');
    expect(checkedSources.at(-1)).not.toContain('(helper : True)');
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('checks an ordinary dispatch using its already integrated source without assumption binders', async () => {
    rejectForwardInputReferences();
    await deliverInput(await assigned(workers[1]));
    const parent = await deliverConsumer();
    expect(parent.assignment.connectionCheck).toBeUndefined();
    expect(node('goal_0').proof!.conditions).toBeUndefined();
    expect(node('goal_0').integratedCheck!.conditions).toBeUndefined();
    expect(checkedSources.some(source => source.includes('theorem add_zero (helper : True)'))).toBe(false);
  });

  it.each(['goal', 'lemma'] as const)('discharges a conditional %s after a later input declaration and preserves added helper order', async kind => {
    rejectForwardInputReferences();
    const tasks = state.cooperation!.tasks.map(item => item.task);
    const parentWorker = kind === 'lemma' ? workers[3] : workers[2];
    if (kind === 'lemma') {
      const goal = tasks.findIndex(task => task.id === 'goal_0');
      tasks[goal] = { ...tasks[goal], dependsOn: ['consumer'], conditional: false };
      tasks.splice(tasks.findIndex(task => task.id === 'independent'), 1, { id: 'consumer', kind: 'lemma', objective: 'Combine the input', type: 'True',
        theoremName: 'Tutorial.consumer', proofPath: 'Submission.lean', dependsOn: ['helper'], revision: 0, ownerId: 'observer' });
      await (cooperative as any).acceptPlan(parseCooperationPlan(problem, { tasks }));
    }
    const parent = await assigned(parentWorker);
    expect(parent.task.id).toBe(kind === 'goal' ? 'goal_0' : 'consumer');
    let source = fs.readFileSync(sourcePath(parentWorker), 'utf8');
    source = kind === 'goal' ? source.replace('n + 0 = n := by sorry',
      'n + 0 = n := by\n  have h : True := Tutorial.helper\n  rfl') : source.replace('theorem add_zero',
      'lemma support_a : True := by exact Tutorial.helper\nlemma support_b : True := by exact Tutorial.helper\n' +
      'lemma consumer : True := by exact Tutorial.helper\ntheorem add_zero');
    fs.writeFileSync(sourcePath(parentWorker), source);
    await cooperative.deliver(parentWorker, parent, commitSolverSources(problem, parentWorker.worktree));
    expect(node(parent.task.id).status).toBe('conditional');
    const input = await assigned(workers[1]);
    fs.writeFileSync(sourcePath(workers[1]), fs.readFileSync(sourcePath(workers[1]), 'utf8')
      .replace('theorem zero_add', 'lemma helper : True := by trivial\ntheorem zero_add'));
    await cooperative.deliver(workers[1], input, commitSolverSources(problem, workers[1].worktree));
    const consumer = node(parent.task.id);
    expect(consumer.status).toBe('integrated');
    expect(consumer.integratedCheck!.conditions ?? []).toEqual([]);
    expect(freshlyAccepted(consumer, taskVersion(consumer.task))).toBe(true);
    const canonical = committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`);
    const consumerName = kind === 'goal' ? 'theorem add_zero' : 'lemma consumer';
    expect(canonical.indexOf('lemma helper')).toBeLessThan(canonical.indexOf(consumerName));
    if (kind === 'lemma') {
      expect(canonical.indexOf('lemma helper')).toBeLessThan(canonical.indexOf('lemma support_a'));
      expect(canonical.indexOf('lemma support_a')).toBeLessThan(canonical.indexOf('lemma support_b'));
      expect(canonical.indexOf('lemma support_b')).toBeLessThan(canonical.indexOf('lemma consumer'));
    }
    expect(canonical).not.toContain('(helper : True)');
  });

  it('blocks a conditional reorder across a frozen option command without advancing canonical acceptance', async () => {
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    const file = sourcePath(workers[0]);
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem zero_add', 'set_option maxRecDepth 1000\ntheorem zero_add'));
    git(workspace, ['add', '--', `${problem.projectRelative}/Submission.lean`]);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', 'Freeze a context barrier']);
    problem = readSolverProblem(workspace, problem.activeProblemPath);
    for (const worker of workers.slice(1)) git(worker.worktree, ['reset', '--hard', problem.baseCommit]);
    state = solverState(problem, workspace, { runId: 'connection-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit, tasks: [] } });
    instances = []; cooperative = create(); await cooperative.restore();
    rejectForwardInputReferences();
    await deliverConsumer();
    const input = await assigned(workers[1]);
    fs.writeFileSync(sourcePath(workers[1]), fs.readFileSync(sourcePath(workers[1]), 'utf8')
      .replace('theorem zero_add', 'lemma helper : True := by trivial\ntheorem zero_add'));
    await cooperative.deliver(workers[1], input, commitSolverSources(problem, workers[1].worktree));
    expect(node('helper').status).toBe('integrated');
    expect(node('goal_0').status).toBe('blocked');
    expect(node('goal_0').feedback).toContain('math_task_integration_missing_context');
    expect(node('goal_0').feedback).not.toContain('math_verifier_unavailable');
    expect(state.cooperation!.canonicalCommit).toBe(node('helper').integratedCheck!.commit);
    expect(freshlyAccepted(node('goal_0'), taskVersion(node('goal_0').task))).toBe(false);
    const canonical = committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`);
    expect(canonical).toContain('n + 0 = n := by sorry');
    expect(state.cooperation!.error).toBeUndefined();
  });

  it('rechecks restored conditional receipts without another consumer dispatch or granting unproved inputs acceptance', async () => {
    await deliverConsumer(); const proof = node('goal_0').proof!, previous = host.verify.mock.calls.length;
    const snapshot = path.join(directory, 'state.json'); writeSolverRunState(snapshot, state);
    for (const instance of instances) { instance.controller.abort(); await instance.cooperative.stop(); }
    state = readSolverRunState(snapshot); cooperative = create(); await cooperative.restore();
    expect(node('goal_0').assignment!.connectionCheck!.assumedInputs).toEqual(node('goal_0').proof!.conditions);
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
