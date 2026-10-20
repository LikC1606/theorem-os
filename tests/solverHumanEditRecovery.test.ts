import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch, HumanEditRecord } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { git, type SolverProblem } from '../src/solver/problem';
import { parseCooperationPlan, taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { temporaryDirectory } from './helpers/files';
import { solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ capture: vi.fn() }));
vi.mock('../src/solver/statementReview', async importOriginal => ({
  ...await importOriginal<typeof import('../src/solver/statementReview')>(),
  captureStatementContexts: host.capture,
}));

describe('human edit recovery', () => {
  let directory: string, problem: SolverProblem, state: SolverRunState, cooperative: CooperativeResearch;
  let controller: AbortController;
  let exclusive: <T>(check: () => Promise<T>) => Promise<T>;
  let events: { event: string; details?: Record<string, unknown> }[];
  let snapshots: NonNullable<SolverRunState['cooperation']>[];
  let prepare: ReturnType<typeof vi.spyOn>;
  const route = (revision: number): CooperativeTask => ({ id: 'route', kind: 'research',
    objective: `Investigate route revision ${revision}.`, dependsOn: [], revision });
  const plan = (revision: number) => parseCooperationPlan(problem, { tasks: [route(revision)] });
  const version = (revision: number) => mathDigest(canonicalMathJson(plan(revision)));
  const editsFile = () => path.join(directory, 'edits.jsonl');
  const save = () => snapshots.push(JSON.parse(JSON.stringify(state.cooperation)));
  const append = (id: string, revision: number, baseVersion = state.cooperation!.planVersion) => {
    fs.appendFileSync(editsFile(), JSON.stringify({ id, baseVersion, ...plan(revision) }) + '\n');
    return fs.statSync(editsFile()).size;
  };
  const record = (id: string) => state.cooperation!.edits?.find(edit => edit.id === id);
  const create = (peers: ResearchWorker[] = []) => {
    const instance = cooperativeResearch({ state, retrievalRoot: directory,
      workers: [{ id: 'lead', role: 'lead', worktree: path.join(directory, 'lead'), ownedFiles: [] }, ...peers],
      access: new Map([['lead', { environment: {}, retrievalRoot: directory }]]),
      signal: controller.signal, save, emit: (event, details) => events.push({ event, details }), exclusiveCheck: check => exclusive(check) });
    // This fixture tests control records rather than worker-context file projections.
    vi.spyOn(instance as any, 'changed').mockImplementation((edit: unknown) => {
      const current = edit as HumanEditRecord | undefined;
      if (current?.status === 'applied') current.planVersion = state.cooperation!.planVersion;
      save();
    });
    prepare = vi.spyOn(instance as any, 'prepareStatementContexts').mockReturnValue(undefined);
    state.cooperation!.planVersion ??= (instance as any).planVersion();
    return instance;
  };
  const resume = () => {
    state = JSON.parse(JSON.stringify(state));
    controller = new AbortController(); exclusive = async check => check(); cooperative = create();
  };

  beforeEach(() => {
    host.capture.mockReset().mockImplementation(async (_problem: unknown, tasks: readonly CooperativeTask[]) =>
      new Map(tasks.map(task => [task.id, { type: 'True', constants: [], omitted: [] }])));
    directory = temporaryDirectory('solver-human-edit-recovery-');
    fs.mkdirSync(path.join(directory, 'lead'));
    problem = { kind: 'example', workspace: path.join(directory, 'lead'), projectRelative: 'generated/p',
      baseCommit: 'a'.repeat(40), receiptDigest: 'human-edit-fixture', ownedFiles: [], targets: [], trustedFiles: {},
      declarations: {}, sourceStructure: {}, contract: { assumptions: [], formalStatement: 'Fixture research.' } } as unknown as SolverProblem;
    const initial = plan(0);
    state = solverState(problem, path.join(directory, 'lead'), { runId: 'human-edit-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit,
        tasks: initial.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
        groups: initial.groups.map(group => ({ group, turns: 0 })) } });
    events = []; snapshots = []; controller = new AbortController(); exclusive = async check => check();
    cooperative = create();
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('rechecks the base version after waiting for exclusive ownership', async () => {
    const entered = deferred(), release = deferred();
    append('queued-v1', 1);
    exclusive = async check => { entered.resolve(); await release.promise; return check(); };
    const pending = cooperative.pulse();
    try {
      await entered.promise;
      await (cooperative as any).acceptPlan(plan(2));
      expect(state.cooperation!.planVersion).toBe(version(2));
    } finally { release.resolve(); }
    await pending;
    expect(record('queued-v1')).toMatchObject({ status: 'rejected', reason: 'math_edit_version_conflict' });
    expect(state.cooperation!.planVersion).toBe(version(2));
    expect(state.cooperation!.tasks[0].task).toEqual(route(2));
    expect(state.cooperation!.history).toHaveLength(1);
    expect(events.filter(event => event.event === 'edit_applied')).toEqual([]);
  });

  it.each(['abort', 'storage'] as const)('preserves an edit interrupted by %s before entering the lock', async failure => {
    append('retry-after-lock-failure', 1);
    const error = Object.assign(new Error('Transient control storage failure'), { code: 'EIO' });
    exclusive = async () => {
      if (failure === 'abort') { controller.abort(); controller.signal.throwIfAborted(); }
      throw error;
    };
    await expect(cooperative.pulse()).rejects.toMatchObject({ name: failure === 'abort' ? 'AbortError' : 'Error' });
    expect(record('retry-after-lock-failure')).toMatchObject({ status: 'received' });
    expect(state.cooperation!.cursors?.edits ?? 0).toBe(0);
    expect(state.cooperation!.planVersion).toBe(version(0));
    expect(state.cooperation!.tasks[0].task).toEqual(route(0));
    expect(events.some(event => event.event === 'edit_rejected')).toBe(false);
    resume();
    await cooperative.pulse();
    expect(record('retry-after-lock-failure')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(state.cooperation!.cursors?.edits).toBe(fs.statSync(editsFile()).size);
    expect(state.cooperation!.history).toHaveLength(1);
    expect(events.filter(event => event.event === 'edit_received')).toHaveLength(1);
  });

  it('accepts an unrelated research edit without preparing statement contexts', async () => {
    append('research-only', 1);
    await cooperative.pulse();
    expect(prepare).not.toHaveBeenCalled();
    expect(record('research-only')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(state.cooperation!.planVersion).toBe((cooperative as any).planVersion());
    expect(state.cooperation!.tasks[0].task).toEqual(route(1));
    expect(state.cooperation!.history).toHaveLength(1);
    expect(state.cooperation!.cursors?.edits).toBe(fs.statSync(editsFile()).size);
    expect(events.some(event => event.event === 'edit_rejected')).toBe(false);
  });

  it('persists a successful prefix without replaying it when the following edit must retry', async () => {
    const prefixEnd = append('prefix', 1);
    append('following-retry', 2, version(1));
    const accepted = vi.spyOn(cooperative as any, 'acceptPlan');
    const error = Object.assign(new Error('Temporary lock EIO'), { code: 'EIO' });
    let turns = 0;
    exclusive = async check => { if (++turns === 2) throw error; return check(); };
    await expect(cooperative.pulse()).rejects.toBe(error);
    expect(record('prefix')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(record('following-retry')).toMatchObject({ status: 'received' });
    expect(state.cooperation!.cursors?.edits).toBe(prefixEnd);
    expect(snapshots.at(-1)?.cursors?.edits).toBe(prefixEnd);
    exclusive = async check => check();
    await cooperative.pulse();
    expect(accepted.mock.calls.map(([, edit]) => (edit as HumanEditRecord).id)).toEqual(['prefix', 'following-retry']);
    expect(record('following-retry')).toMatchObject({ status: 'applied', planVersion: version(2) });
    expect(state.cooperation!.tasks[0].task).toEqual(route(2));
    expect(state.cooperation!.history).toHaveLength(2);
    expect(events.filter(event => event.event === 'edit_applied' && event.details?.id === 'prefix')).toHaveLength(1);
  });

  it('resumes review synchronization after an applied edit without applying its graph again', async () => {
    append('sync-retry', 1);
    const error = Object.assign(new Error('Statement review synchronization EIO'), { code: 'EIO' });
    vi.spyOn(cooperative as any, 'syncStatementReviews').mockImplementationOnce(() => { throw error; });
    await expect(cooperative.pulse()).rejects.toBe(error);
    expect(record('sync-retry')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(state.cooperation!.planVersion).toBe(version(1));
    expect(state.cooperation!.tasks[0].task).toEqual(route(1));
    expect(state.cooperation!.history).toHaveLength(1);
    expect(state.cooperation!.cursors?.edits ?? 0).toBe(0);
    expect(snapshots.at(-1)?.edits?.find(edit => edit.id === 'sync-retry')).toMatchObject({ status: 'applied' });
    resume();
    const sync = vi.spyOn(cooperative as any, 'syncStatementReviews');
    const accept = vi.spyOn(cooperative as any, 'acceptPlan');
    await cooperative.pulse(); await cooperative.pulse();
    expect(sync).toHaveBeenCalledOnce();
    expect(accept).not.toHaveBeenCalled();
    expect(record('sync-retry')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(state.cooperation!.history).toHaveLength(1);
    expect(state.cooperation!.cursors?.edits).toBe(fs.statSync(editsFile()).size);
    expect(events.filter(event => event.event === 'edit_applied' && event.details?.id === 'sync-retry')).toHaveLength(1);
    expect(events.some(event => event.event === 'edit_rejected')).toBe(false);
  });

  it.each(['new-route', 'owner-transfer'] as const)('uses the committed dependency graph for statement context caching after %s', async change => {
    const workspace = path.join(directory, 'lead'), project = path.join(workspace, 'generated/p');
    fs.mkdirSync(project, { recursive: true });
    fs.writeFileSync(path.join(project, 'Submission.lean'), 'theorem g : True := by sorry\n');
    git(workspace, ['init', '--quiet']); git(workspace, ['add', '.']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '-m', 'Fixture']);
    const commit = git(workspace, ['rev-parse', 'HEAD']);
    problem = { ...problem, baseCommit: commit, ownedFiles: ['Submission.lean'],
      targets: [{ proofPath: 'Submission.lean', theoremName: 'g', declarationHash: 'fixture' }],
      declarations: { 'Submission.lean': [{ name: 'g', header: 'g : True' }] } };
    const helper = (id: string, dependsOn: string[] = []) => ({ id, kind: 'lemma', objective: `Prove ${id}.`,
      proofPath: 'Submission.lean', theoremName: id, type: 'True', dependsOn });
    const tasks = [
      { id: 'g', kind: 'goal', objective: 'Prove g.', proofPath: 'Submission.lean', theoremName: 'g',
        ...(change === 'owner-transfer' ? { ownerId: 'old' } : {}) },
      helper('p'), helper('c', ['p']), helper('q'), helper('d', ['q']),
      { ...helper('h', ['g']), statementReview: true, informalStatement: 'True.' },
    ];
    const routes = [
      { id: 'route-b', targetTaskId: 'g', prerequisiteTaskIds: ['q'], closingTaskId: 'd' },
      { id: 'route-a', targetTaskId: 'g', prerequisiteTaskIds: ['p'], closingTaskId: 'c' },
    ];
    const initial = parseCooperationPlan(problem, { tasks,
      ...(change === 'owner-transfer' ? { proofRoutes: routes } : {}) });
    state = { ...state, problem, cooperation: { canonicalCommit: commit,
      tasks: initial.tasks.map(task => ({ task, status: 'pending', attempts: 0 })),
      groups: initial.groups.map(group => ({ group, turns: 0 })), proofRoutes: initial.proofRoutes } };
    const peers: ResearchWorker[] = ['old', 'new'].map(id => {
      const worktree = path.join(directory, id); fs.mkdirSync(worktree);
      return { id, role: 'researcher', worktree, ownedFiles: ['Submission.lean'] };
    });
    cooperative = create(peers); prepare.mockRestore();
    const interrupted = vi.fn(async () => {});
    let oldAction: Parameters<CooperativeResearch['current']>[0] | undefined;
    if (change === 'owner-transfer') {
      const node = state.cooperation!.tasks.find(item => item.task.id === 'g')!;
      node.status = 'running';
      node.assignment = { taskId: 'g', taskDigest: taskVersion(node.task), workerId: 'old', seedCommit: commit, routeId: 'route-a' };
      oldAction = { kind: 'task', task: node.task, assignment: node.assignment };
      cooperative.activate(peers[0], oldAction, interrupted, async () => {});
    }
    const proposed = parseCooperationPlan(problem, {
      tasks: tasks.map(task => task.id === 'g' && change === 'owner-transfer' ? { ...task, ownerId: 'new' } : task),
      proofRoutes: change === 'new-route' ? [routes[1]] : routes,
    });
    fs.appendFileSync(editsFile(), JSON.stringify({ id: 'cache-update', baseVersion: state.cooperation!.planVersion, ...proposed }) + '\n');
    await cooperative.pulse();
    await (cooperative as any).schedulePlanSynchronization();
    expect(record('cache-update')).toMatchObject({ status: 'applied' });
    expect(host.capture).toHaveBeenCalledOnce();
    const review = state.cooperation!.statementReviews!.find(item => item.taskId === 'h')!;
    const saved = JSON.parse(fs.readFileSync(path.join(review.workspace, 'STATEMENT.json'), 'utf8'));
    expect(saved.dependencies.map((dependency: { taskId: string }) => dependency.taskId)).toEqual(
      change === 'new-route' ? ['g', 'p', 'c'] : ['g', 'q', 'd']);
    expect(saved.elaboration).toEqual({ type: 'True', constants: [], omitted: [] });
    if (oldAction) {
      expect(interrupted).toHaveBeenCalledOnce();
      expect(cooperative.current(oldAction)).toBe(false);
      expect(state.cooperation!.tasks.find(item => item.task.id === 'g')).toMatchObject({ status: 'pending', assignment: undefined });
    }
  });

  it('still rejects deterministic invalid edits once and accepts the following valid control', async () => {
    fs.appendFileSync(editsFile(), '{broken\n');
    fs.appendFileSync(editsFile(), JSON.stringify({ id: 'invalid-cycle', baseVersion: state.cooperation!.planVersion,
      tasks: [{ ...route(1), dependsOn: ['route'] }] }) + '\n');
    append('valid-after-invalid', 1);
    await cooperative.pulse(); await cooperative.pulse();
    expect(record('invalid-cycle')).toMatchObject({ status: 'rejected', reason: 'math_plan_dependency_cycle' });
    expect(record('valid-after-invalid')).toMatchObject({ status: 'applied', planVersion: version(1) });
    expect(events.filter(event => event.event === 'edit_rejected')).toHaveLength(2);
    expect(state.cooperation!.cursors?.edits).toBe(fs.statSync(editsFile()).size);
  });
});
