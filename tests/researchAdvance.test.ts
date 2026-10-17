import { describe, expect, it } from 'vitest';
import { readyResearchTasks, researchCanAdvance } from '../src/solver/modules/search';
import { type RouteRecord, type TaskRecord } from '../src/solver/tasks';

const node = (id: string, kind: TaskRecord['task']['kind'], dependsOn: string[] = [],
  status: TaskRecord['status'] = 'pending'): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { theoremName: id, type: 'True', proofPath: 'Submission.lean' } : {}) },
  status, attempts: 0,
});
const group = (): RouteRecord => ({ group: { id: 'main', objective: 'Prove the original goal', status: 'active', revision: 0 }, turns: 0 });

describe('future research advancement', () => {
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

  it.each(['lemma', 'goal'] as const)('does not start a typed %s past an unproved blocked premise', kind => {
    const tasks = [node('premise', 'lemma', [], 'blocked'), node('consumer', kind, ['premise'])];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(false);
  });

  it('preserves a saved conditional proof as future progress without its former owner', () => {
    const premise = node('premise', 'lemma', [], 'integrated');
    const bridge = node('bridge', 'lemma', ['premise'], 'conditional');
    bridge.task = { ...bridge.task, conditional: true, ownerId: 'offline' };
    const tasks = [premise, bridge, node('consumer', 'goal', ['bridge'])];
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
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
