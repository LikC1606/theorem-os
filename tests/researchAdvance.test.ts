import { describe, expect, it } from 'vitest';
import { originalGoalTaskFocus, readyResearchTasks, researchCanAdvance, taskDependenciesReady } from '../src/solver/modules/search';
import { assignSharedResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import { type RouteRecord, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, kind: TaskRecord['task']['kind'], dependsOn: string[] = [],
  status: TaskRecord['status'] = 'pending'): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: id, type: 'True', proofPath: 'Submission.lean' } : {}) },
  status, attempts: 0,
});
const group = (): RouteRecord => ({ group: { id: 'main', objective: 'Prove the original goal', status: 'active', revision: 0 }, turns: 0 });

describe('future research advancement', () => {
  it('distinguishes independent auxiliary work from advancement of an unfinished original argument', () => {
    const core = node('core', 'lemma', [], 'blocked');
    const auxiliary = node('auxiliary', 'lemma');
    const tasks = [core, auxiliary, node('goal', 'goal', ['core'])];
    const support = originalGoalTaskFocus(tasks).support;
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(false);
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, new Set())).toBe(false);
    expect(auxiliary.status).toBe('pending');
  });

  it('scopes full-proof root candidates without dropping dependencies outside that set', () => {
    const premise = node('premise', 'lemma', [], 'blocked');
    const goal = node('goal', 'goal', ['premise']);
    goal.task = { ...goal.task, conditional: false };
    const tasks = [premise, goal, node('auxiliary', 'lemma')], candidates = new Set(['goal']);
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, candidates)).toBe(false);
    premise.status = 'pending';
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, candidates)).toBe(true);
    premise.task = { ...premise.task, ownerId: 'offline' };
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, candidates)).toBe(false);
  });

  it.each(['research', 'sketch'] as const)('counts targeted %s and its proof inputs as original-goal support', kind => {
    const core = node('core', 'lemma', [], 'blocked');
    const investigation = node('investigation', kind, ['core']);
    const tasks = [core, investigation, node('goal', 'goal', ['core'])];
    const support = originalGoalTaskFocus(tasks).support;
    expect(support.has(investigation.task.id)).toBe(true);
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(true);
    investigation.task = { ...investigation.task, ownerId: 'offline' };
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(false);
  });

  it.each(['research', 'sketch'] as const)('looks through completed %s records before claiming original-goal advancement', kind => {
    const core = node('core', 'lemma', [], 'blocked');
    const finding = node('finding', kind, ['core'], 'completed');
    const outer = node('outer', 'research', ['finding'], 'completed');
    const goal = node('goal', 'goal', ['outer']);
    goal.task = { ...goal.task, conditional: false };
    const tasks = [core, finding, outer, goal, node('auxiliary', 'lemma')];
    const support = originalGoalTaskFocus(tasks).support;
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(false);
    core.status = 'pending';
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(true);
    core.task = { ...core.task, ownerId: 'offline' };
    expect(researchCanAdvance(tasks, undefined, new Set(), undefined, support)).toBe(false);
  });

  it('fails closed on missing or cyclic inputs of completed advisory records', () => {
    const finding = node('finding', 'research', ['absent'], 'completed');
    const goal = node('goal', 'goal', ['finding']);
    expect(researchCanAdvance([finding, goal], undefined, new Set())).toBe(false);
    finding.task = { ...finding.task, dependsOn: ['goal'] };
    expect(researchCanAdvance([finding, goal], undefined, new Set())).toBe(false);
  });

  it.each(['research', 'sketch'] as const)('can investigate a blocked typed premise with a pending %s task', kind => {
    const premise = node('premise', 'lemma', [], 'blocked');
    const investigation = node('investigation', kind, ['premise']);
    const tasks = [premise, investigation];
    expect(readyResearchTasks(tasks)).toEqual([investigation]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
    expect(premise.status).toBe('blocked');
  });

  it('can investigate a typed premise whose proof owner is unavailable', () => {
    const premise = node('premise', 'lemma');
    premise.task = { ...premise.task, ownerId: 'offline' };
    const investigation = node('investigation', 'research', ['premise']);
    const tasks = [premise, investigation];
    expect(readyResearchTasks(tasks)).toContain(investigation);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
  });

  it.each(['parked', 'paused-task', 'stopped-task', 'paused-group', 'spent-group', 'busy-group'] as const)
  ('does not advance an explicitly %s investigation', control => {
    const premise = node('premise', 'lemma', [], 'blocked');
    const investigation = node('investigation', 'research', ['premise']);
    const route = group();
    if (control === 'parked') investigation.routeParking = ['local-obstruction'];
    else if (control === 'paused-task') investigation.task = { ...investigation.task, status: 'paused' };
    else if (control === 'stopped-task') investigation.task = { ...investigation.task, status: 'stopped' };
    else if (control === 'paused-group') route.group = { ...route.group, status: 'paused' };
    else if (control === 'spent-group') { route.group = { ...route.group, maxTurns: 1 }; route.turns = 1; }
    else { route.group = { ...route.group, maxConcurrent: 1 }; route.busy = 1; }
    const tasks = [premise, investigation];
    expect(readyResearchTasks(tasks, [route])).toEqual([]);
    expect(researchCanAdvance(tasks, [route], new Set())).toBe(false);
  });

  it.each(['owner', 'assignment'] as const)('requires the investigation %s to be available', ownership => {
    const premise = node('premise', 'lemma', [], 'blocked');
    const investigation = node('investigation', 'research', ['premise']);
    if (ownership === 'owner') investigation.task = { ...investigation.task, ownerId: 'researcher' };
    else investigation.assignment = { taskId: investigation.task.id, taskDigest: 'task', workerId: 'researcher', seedCommit: 'seed' };
    const tasks = [premise, investigation];
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(false);
    expect(researchCanAdvance(tasks, undefined, new Set(['researcher']))).toBe(true);
  });

  it('does not promise progress on a goal whose pinned engineer has stopped', () => {
    const goal = node('goal', 'goal'), route = group();
    route.group = { ...route.group, engineerId: 'engineer' };
    const researcher: ResearchWorker = { id: 'researcher', role: 'researcher', worktree: '/unused', ownedFiles: [] };
    const ready = readyResearchTasks([goal], [route]);
    expect(ready).toEqual([goal]);
    expect(assignSharedResearchTask(ready, researcher, [researcher], [route])).toBeUndefined();
    expect(researchCanAdvance([goal], [route], new Set([researcher.id]))).toBe(false);
    expect(researchCanAdvance([goal], [route], new Set([researcher.id, 'engineer']))).toBe(true);
    expect(goal.task.ownerId).toBeUndefined();
    expect(route.group.engineerId).toBe('engineer');
  });

  it.each(['owner', 'assignment'] as const)('rejects conflicting live %s and engineer pins', ownership => {
    const goal = node('goal', 'goal'), route = group();
    route.group = { ...route.group, engineerId: 'engineer' };
    if (ownership === 'owner') goal.task = { ...goal.task, ownerId: 'researcher' };
    else goal.assignment = { taskId: goal.task.id, taskDigest: 'task', workerId: 'researcher', seedCommit: 'seed' };
    expect(researchCanAdvance([goal], [route], new Set(['researcher', 'engineer']))).toBe(false);
  });

  it('does not apply an original-goal engineer pin to independent investigations', () => {
    const route = group(), investigation = node('investigation', 'research');
    route.group = { ...route.group, engineerId: 'offline' };
    expect(researchCanAdvance([investigation], [route], new Set(['researcher']))).toBe(true);
  });

  it('uses the assignment policy to distinguish live role slots from proof workers', () => {
    const goal = node('goal', 'goal');
    const lead: ResearchWorker = { id: 'lead', role: 'lead', worktree: '/unused', ownedFiles: [] };
    const researcher: ResearchWorker = { ...lead, id: 'researcher', role: 'researcher' };
    const canAdvance = (workers: readonly ResearchWorker[]) => researchCanAdvance([goal], undefined,
      new Set(workers.map(worker => worker.id)), candidate => workers.some(worker =>
        assignSharedResearchTask([candidate], worker, workers) === candidate));
    expect(canAdvance([lead])).toBe(false);
    expect(canAdvance([lead, researcher])).toBe(true);
  });

  it('can consume a saved conditional proof without assigning its former producer again', () => {
    const premise = node('premise', 'lemma', [], 'integrated');
    const bridge = node('bridge', 'lemma', ['premise'], 'conditional');
    bridge.task = { ...bridge.task, conditional: true, ownerId: 'offline' };
    const consumer = node('consumer', 'goal', ['bridge']);
    expect(researchCanAdvance([premise, bridge, consumer], undefined, new Set(['researcher']), candidate =>
      candidate === consumer)).toBe(true);
  });

  it.each(['lemma', 'goal'] as const)('does not start a typed %s past an unproved blocked premise', kind => {
    const tasks = [node('premise', 'lemma', [], 'blocked'), node('consumer', kind, ['premise'])];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(false);
  });

  it('preserves a saved conditional proof as future progress without its former owner', () => {
    const premise = node('premise', 'lemma', [], 'integrated');
    const bridge = node('bridge', 'lemma', ['premise'], 'conditional');
    bridge.task = { ...bridge.task, conditional: true, ownerId: 'offline' };
    const consumer = node('consumer', 'goal', ['bridge']);
    consumer.task = { ...consumer.task, conditional: false };
    const tasks = [premise, bridge, consumer];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
    expect(taskDependenciesReady(consumer.task, tasks)).toBe(false);
    expect(bridge.status).toBe('conditional');
    expect(consumer.status).toBe('pending');
  });

  it('keeps a conditional proof blocked on an unavailable premise', () => {
    const bridge = node('bridge', 'lemma', ['premise'], 'conditional');
    bridge.task = { ...bridge.task, conditional: true };
    const tasks = [node('premise', 'lemma', [], 'blocked'), bridge, node('consumer', 'goal', ['bridge'])];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(false);
  });

  it('does not treat advisory final review as an investigation before the original goal is checked', () => {
    const review = node('review', 'research', ['original']);
    review.task = { ...review.task, reviewScope: 'final-candidate' };
    const tasks = [node('original', 'goal', [], 'blocked'), review];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(false);
  });
});
