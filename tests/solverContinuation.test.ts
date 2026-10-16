import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { continuationResearchTasks, readyResearchTasks } from '../src/solver/modules/search';
import { assignSharedResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import { taskVersion, type CooperativeAction, type TaskRecord, type RouteRecord } from '../src/solver/tasks';
import { CooperativeResearch, type CooperationState } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { git, type SolverProblem } from '../src/solver/problem';
import type { SolverRunState } from '../src/solver/archive';

const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: id, type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
const integrated = (record: TaskRecord): TaskRecord => {
  record.status = 'integrated';
  record.integratedCheck = { passed: true, taskDigest: taskVersion(record.task), conditions: [] } as TaskRecord['integratedCheck'];
  return record;
};
const main: RouteRecord = { group: { id: 'main', objective: 'Original problem', status: 'active', revision: 0 }, turns: 0 };

describe('proof continuation scheduling', () => {
  it('advances a consumer of checked helpers before untouched core gaps and disconnected work', () => {
    const tasks = [node('explore', 'research'), node('core'), integrated(node('checked')),
      node('bridge', 'lemma', ['checked']), node('middle', 'lemma', ['core']), node('goal', 'goal', ['bridge', 'middle'])];
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['bridge', 'core', 'explore']);
    expect(readyResearchTasks(tasks).map(record => record.task.id)).toEqual(['explore', 'core', 'bridge']);
    tasks.find(record => record.task.id === 'checked')!.integratedCheck!.taskDigest = 'obsolete';
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['core', 'bridge', 'explore']);
  });

  it('prefers a ready original target and never counts conditional premises as proved', () => {
    const checked = integrated(node('checked')), open = node('open');
    const consumer = node('consumer', 'lemma', ['checked']), goal = node('ready-goal', 'goal', ['checked']);
    const conditional = node('conditional-goal', 'goal', ['open']); conditional.task = { ...conditional.task, conditional: true };
    const tasks = [open, checked, consumer, node('later-goal', 'goal', ['consumer']), conditional, goal];
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual([
      'ready-goal', 'consumer', 'conditional-goal', 'open',
    ]);
    expect(open.status).toBe('pending');
    expect(conditional.integratedCheck).toBeUndefined();
  });

  it('offers a spare proof slot to a different route and keeps owner and group pins', () => {
    const running = [node('working-a'), node('working-b')]; running.forEach(record => record.status = 'running');
    const tried = node('tried', 'research'); tried.attempts = 5;
    const fresh = node('fresh', 'research'); fresh.task = { ...fresh.task, ownerId: 'researcher' };
    const core = node('core'), goal = node('goal', 'goal', [...running.map(record => record.task.id), 'core']);
    const tasks = [tried, core, ...running, fresh, goal];
    const ready = continuationResearchTasks(tasks, [main]);
    expect(ready.map(record => record.task.id)).toEqual(['fresh', 'core', 'tried']);
    const engineer: ResearchWorker = { id: 'engineer', role: 'engineer', worktree: '/engineer', ownedFiles: [] };
    const researcher: ResearchWorker = { ...engineer, id: 'researcher', role: 'researcher' };
    expect(assignSharedResearchTask(ready, engineer, [engineer, researcher], [main])).toBe(core);
    expect(assignSharedResearchTask(ready, researcher, [engineer, researcher], [main])).toBe(fresh);
    fresh.status = 'running';
    expect(continuationResearchTasks(tasks, [main])).toEqual([]);
    expect(continuationResearchTasks(tasks).map(record => record.task.id)).toEqual(['core', 'tried']);
    core.task = { ...core.task, ownerId: 'researcher' };
    core.assignment = { taskId: 'core', taskDigest: taskVersion(core.task), workerId: 'researcher', seedCommit: 'seed' };
    expect(assignSharedResearchTask(continuationResearchTasks(tasks), engineer, [engineer, researcher], [main])).toBe(tried);
  });

  it('preserves dependency, pause, spent route and concurrency gates', () => {
    const tasks = [node('core'), node('blocked', 'goal', ['core']), node('paused'), node('full'), node('spent')];
    tasks[2].task = { ...tasks[2].task, status: 'paused' };
    tasks[3].task = { ...tasks[3].task, groupId: 'full' }; tasks[4].task = { ...tasks[4].task, groupId: 'spent' };
    const groups: RouteRecord[] = [main,
      { group: { ...main.group, id: 'full', maxConcurrent: 1 }, turns: 0, busy: 1 },
      { group: { ...main.group, id: 'spent', maxTurns: 1 }, turns: 1 }];
    expect(continuationResearchTasks(tasks, groups).map(record => record.task.id)).toEqual(['core']);
  });
});

describe('unchanged research delivery recovery and budget wakeup', () => {
  let directory: string, seed: string, cooperative: CooperativeResearch, state: SolverRunState, record: TaskRecord;
  let lead: ResearchWorker, researcher: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>;
  let allowed: boolean;
  const signal = () => new AbortController().signal;
  const checkpoint = (notes: string) => {
    fs.writeFileSync(path.join(directory, 'RESEARCH.md'), notes);
    git(directory, ['add', '--', 'RESEARCH.md']);
    git(directory, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '--allow-empty', '-m', 'Research checkpoint']);
    return git(directory, ['rev-parse', 'HEAD']);
  };
  beforeEach(() => {
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'continuation-test-')));
    fs.mkdirSync(path.join(directory, 'generated/p'), { recursive: true });
    fs.writeFileSync(path.join(directory, 'generated/p/Submission.lean'), 'theorem goal : True := by sorry\n');
    git(directory, ['init', '--quiet']); git(directory, ['add', '--', 'generated']);
    seed = checkpoint('Inherited research notes.');
    record = node('question', 'research'); record.status = 'running';
    record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: 'researcher', seedCommit: seed };
    lead = { id: 'solver', role: 'lead', worktree: directory, ownedFiles: ['Submission.lean'] };
    researcher = { ...lead, id: 'researcher', role: 'researcher' };
    const cooperation: CooperationState = { canonicalCommit: seed, tasks: [record, node('goal', 'goal', ['question'])],
      groups: [{ ...main, group: { ...main.group } }] };
    state = { runId: 'continuation-fixture', turns: 0, environmentDigest: 'fixture', cooperation,
      problem: { projectRelative: 'generated/p', ownedFiles: ['Submission.lean'], declarations: {}, targets: [],
        trustedFiles: {}, baseCommit: seed, sourceStructure: {}, sourceImports: {},
        contract: { assumptions: [], formalStatement: 'Prove the original goal.' } } as unknown as SolverProblem } as SolverRunState;
    allowed = true;
    cooperative = new CooperativeResearch({ state, workers: [lead, researcher], access: new Map(), signal: signal(),
      modelDispatchAllowed: () => allowed, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    action = { kind: 'task', task: record.task, assignment: record.assignment };
  });
  afterEach(async () => { await cooperative.stop(); vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('retries the first unchanged completion and asks Lead to revise after the second', async () => {
    record.attempts = 40; // Long-lived work and checkpoint counts must not consume the repair opportunity.
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('blocked');
    expect(state.cooperation!.deliveries).toEqual([expect.objectContaining({ kind: 'failure', status: 'failed', taskId: 'question' })]);
    vi.spyOn(cooperative as any, 'seed').mockReturnValue(seed);
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toMatchObject({ kind: 'lead' });
  });

  it('does not count recovered checkpoints as unchanged completed findings and resets after new findings', async () => {
    await cooperative.deliver(researcher, action, seed);
    record.status = 'running';
    await cooperative.deliver(researcher, action, seed, true);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    record.status = 'running';
    await cooperative.deliver(researcher, action, checkpoint('A new concrete route and unresolved mathematical gap.'));
    expect(record.status).toBe('completed');
    expect(record.feedback).toBeUndefined();
    expect(state.cooperation!.unchangedResearch!.question).toBeUndefined();
  });

  it('binds unchanged repetitions to the task version and inherited notes content', async () => {
    await cooperative.deliver(researcher, action, seed);
    seed = checkpoint('A different inherited checkpoint.');
    record.assignment!.seedCommit = seed; record.status = 'running';
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
    await (cooperative as any).acceptPlan({ tasks: [
      { ...record.task, revision: 1 }, state.cooperation!.tasks[1].task,
    ], groups: [{ ...main.group }] });
    expect(state.cooperation!.unchangedResearch!.question).toBeUndefined();
    record = state.cooperation!.tasks[0];
    record.assignment = { taskId: record.task.id, taskDigest: taskVersion(record.task), workerId: researcher.id, seedCommit: seed };
    record.status = 'running'; action = { kind: 'task', task: record.task, assignment: record.assignment };
    await cooperative.deliver(researcher, action, seed);
    expect(record.status).toBe('pending');
    expect(state.cooperation!.unchangedResearch!.question.count).toBe(1);
  });

  it('wakes idle peers on model budget changes and does not schedule pending reviews', async () => {
    record.status = 'blocked';
    let settled = false;
    const pending = cooperative.next(researcher, { maxTurns: Infinity, remainingMs: Infinity }).then(value => { settled = true; return value; });
    await new Promise(resolve => setImmediate(resolve));
    expect(settled).toBe(false);
    state.cooperation!.review = { status: 'pending', commit: seed, sourceDigest: 'source' };
    allowed = false; cooperative.modelBudgetChanged();
    await expect(pending).resolves.toBeUndefined();
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toBeUndefined();
    expect(state.cooperation!.review.status).toBe('pending');
    state.cooperation!.review = undefined;
    state.cooperation!.statementReviews = [{ taskId: 'question', status: 'pending' }] as CooperationState['statementReviews'];
    await expect(cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity })).resolves.toBeUndefined();
    expect(state.cooperation!.statementReviews[0].status).toBe('pending');
  });

  it('waits for active work to settle after budget exhaustion while allowing host assembly', async () => {
    cooperative.activate(researcher, action, async () => {}, async () => {});
    allowed = false;
    let settled = false;
    const pending = cooperative.next(lead, { maxTurns: Infinity, remainingMs: Infinity }).then(value => { settled = true; return value; });
    await new Promise(resolve => setImmediate(resolve));
    expect(settled).toBe(false);
    record.status = 'completed'; state.cooperation!.tasks[1].status = 'integrated';
    vi.spyOn(cooperative as any, 'seed').mockReturnValue(seed);
    cooperative.deactivate(researcher);
    await expect(pending).resolves.toMatchObject({ kind: 'assemble' });
  });
});
