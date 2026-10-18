import { describe, expect, it } from 'vitest';
import { assignSharedResearchTask, type ResearchWorker } from '../src/solver/modules/organization';
import { continuationResearchTasks, originalGoalTaskFocus, readyResearchTasks } from '../src/solver/modules/search';
import { markTaskAcceptance, taskVersion, type RouteRecord, type TaskRecord } from '../src/solver/tasks';
import { buildProofContinuation } from '../src/solver/progress';

const node = (id: string, kind: TaskRecord['task']['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord => ({
  task: { id, kind, objective: `Prove ${id}`, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: id, type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
const integrate = (record: TaskRecord) => {
  record.status = 'integrated';
  record.integratedCheck = { passed: true, taskDigest: taskVersion(record.task), conditions: [],
    verification: { status: 'kernel_verified', targetCommit: 'checked-source', results: [
      { status: 'kernel_verified', targetCommit: 'checked-source', receiptId: 'fixture-receipt' },
    ] } } as TaskRecord['integratedCheck'];
  markTaskAcceptance(record.integratedCheck!);
  return record;
};
const ids = (tasks: readonly TaskRecord[]) => tasks.map(record => record.task.id);
const main: RouteRecord = { group: { id: 'main', objective: 'Original proof', status: 'active', revision: 0 }, turns: 0 };

describe('original-goal frontier priority', () => {
  it('checks a conditional connection once before returning priority to its open premise', () => {
    const unrelated = node('peripheral'); unrelated.task = { ...unrelated.task, objective: 'Useful for goal and core' };
    const core = node('core'), conditional = node('wrapper', 'goal', ['core']);
    conditional.task = { ...conditional.task, conditional: true };
    const tasks = [unrelated, conditional, core];

    expect(ids(readyResearchTasks(tasks))).toEqual(['wrapper', 'peripheral', 'core']);
    expect(ids(continuationResearchTasks(tasks))).toEqual(['wrapper', 'core', 'peripheral']);
    conditional.attempts = 1;
    expect(ids(readyResearchTasks(tasks))).toEqual(['peripheral', 'wrapper', 'core']);
    expect(ids(continuationResearchTasks(tasks))).toEqual(['core', 'wrapper', 'peripheral']);
    expect(originalGoalTaskFocus(tasks).support.has('peripheral')).toBe(false);
    expect(core.status).toBe('pending');
    expect(conditional.integratedCheck).toBeUndefined();
  });

  it('recognizes transitive targeted investigations and their separately provable inputs', () => {
    const core = node('core'); core.status = 'blocked'; core.attempts = 2;
    const seed = node('seed'), collar = node('collar', 'lemma', ['seed']);
    const local = node('local_probe', 'research', ['core']);
    const probe = node('ambient_probe', 'research', ['local_probe', 'collar']);
    const unrelated = node('explore', 'research');
    const tasks = [unrelated, probe, collar, local, seed, core, node('goal', 'goal', ['core'])];
    const focus = originalGoalTaskFocus(tasks);

    expect([...focus.frontier]).toEqual(['core']);
    expect([...focus.targetedResearch].sort()).toEqual(['ambient_probe', 'local_probe']);
    expect(focus.support.has('seed')).toBe(true);
    expect(focus.support.has('collar')).toBe(true);
    expect(focus.proofPath.has('collar')).toBe(false);
    expect(continuationResearchTasks(tasks)[0]).toBe(seed);
    integrate(seed);
    expect(continuationResearchTasks(tasks)[0]).toBe(collar);
    expect(core.status).toBe('blocked');
    expect(core.attempts).toBe(2);
    expect(probe.integratedCheck).toBeUndefined();
  });

  it.each(['research', 'sketch'] as const)('looks through completed %s dependencies to the still unproved original premise', kind => {
    const core = node('core');
    const completed = node('completed_finding', kind, ['core']); completed.status = 'completed';
    const outer = node('completed_review', 'research', ['completed_finding']); outer.status = 'completed';
    const goal = node('goal', 'goal', ['completed_review']);
    const goalProbe = node('goal_probe', 'research', ['goal']);
    const coreProbe = node('core_probe', 'research', ['core']);
    const tasks = [goalProbe, coreProbe, goal, completed, outer, core];
    const focus = originalGoalTaskFocus(tasks);

    expect(readyResearchTasks(tasks)).not.toContain(goal);
    expect([...focus.frontier]).toEqual(['core']);
    expect(buildProofContinuation(tasks).goals[0].frontier).toEqual(['core']);
    expect(focus.proofPath.has('core')).toBe(true);
    expect(focus.support.has('core')).toBe(true);
    expect(focus.targetedResearch.has('core_probe')).toBe(true);
    expect(continuationResearchTasks(tasks)[0]).toBe(core);
    expect(completed.integratedCheck).toBeUndefined();
    expect(outer.integratedCheck).toBeUndefined();

    integrate(core);
    expect(readyResearchTasks(tasks)).toContain(goal);
    expect([...originalGoalTaskFocus(tasks).frontier]).toEqual(['goal']);
    expect(buildProofContinuation(tasks).goals[0].frontier).toEqual(['goal']);
    expect(originalGoalTaskFocus(tasks).targetedResearch.has('core_probe')).toBe(false);
    expect(continuationResearchTasks(tasks)[0]).toBe(goal);
    expect(goal.integratedCheck).toBeUndefined();
  });

  it('keeps a checked shared interface encapsulated when completed findings consume it', () => {
    const hidden = integrate(node('private_input'));
    const shared = integrate(node('shared', 'lemma', ['private_input']));
    shared.integratedCheck!.references = { root: { file: 'Submission.lean', name: 'shared' },
      sourceCommit: 'checked-source', environmentDigest: 'environment', contextDigest: 'context', inputs: [],
      statement: [], proof: [{ file: 'Submission.lean', name: 'private_input' }],
      tasks: [{ taskId: hidden.task.id, taskDigest: taskVersion(hidden.task) }] };
    const finding = node('finding', 'research', ['shared']); finding.status = 'completed';
    const review = node('review', 'sketch', ['finding']); review.status = 'completed';
    const goal = node('goal', 'goal', ['review']), tasks = [shared, finding, review, goal];
    const focus = originalGoalTaskFocus(tasks);

    expect([...focus.frontier]).toEqual(['goal']);
    expect(focus.proofPath.has('private_input')).toBe(false);
    expect(buildProofContinuation(tasks).goals[0].frontier).toEqual(['goal']);
    expect(buildProofContinuation(tasks).goals[0].missingDependencies).toEqual([]);
    expect(goal.integratedCheck).toBeUndefined();
  });

  it('tracks all unparked OR branches and excludes the inputs of a parked branch', () => {
    const cores = ['a', 'b', 'c'].map(suffix => {
      const record = node(`core_${suffix}`); record.status = 'blocked'; return record;
    });
    const closers = cores.map(record => node(`close_${record.task.id}`, 'lemma', [record.task.id]));
    const goal = node('goal', 'goal');
    goal.alternativeRoutes = cores.map((record, index) => ({ id: `route_${index}`, targetTaskId: 'goal',
      prerequisiteTaskIds: [record.task.id], closingTaskId: closers[index].task.id }));
    goal.parkedRoutes = { route_2: ['parked-obstruction'] };
    const probes = cores.map(record => node(`probe_${record.task.id}`, 'research', [record.task.id]));
    const tasks = [...probes.toReversed(), ...cores, ...closers, goal];
    const focus = originalGoalTaskFocus(tasks);

    expect([...focus.frontier].sort()).toEqual(['core_a', 'core_b']);
    expect([...focus.preferred.frontier]).toEqual(['core_a']);
    expect(focus.preferred.support.has('core_b')).toBe(false);
    expect(focus.support.has('core_b')).toBe(true);
    expect([...focus.targetedResearch].sort()).toEqual(['probe_core_a', 'probe_core_b']);
    expect(focus.support.has('core_c')).toBe(false);
    expect(focus.support.has('close_core_c')).toBe(false);
    expect(ids(continuationResearchTasks(tasks))).toEqual(['probe_core_a', 'probe_core_b', 'probe_core_c']);
  });

  it('does not spread relevance through a checked shared helper or its other consumers', () => {
    const core = node('core'); core.status = 'blocked';
    const shared = integrate(node('shared', 'lemma', ['core']));
    const unrelated = node('independent_probe', 'research', ['shared']);
    const targeted = node('targeted_probe', 'research', ['core', 'shared']);
    const tasks = [unrelated, targeted, core, shared, node('goal', 'goal', ['core'])];
    const focus = originalGoalTaskFocus(tasks);

    expect([...focus.targetedResearch]).toEqual(['targeted_probe']);
    expect(focus.support.has('shared')).toBe(true);
    expect(focus.support.has('independent_probe')).toBe(false);
    expect(ids(continuationResearchTasks(tasks))).toEqual(['targeted_probe', 'independent_probe']);
    tasks.splice(tasks.indexOf(targeted), 1);
    expect(originalGoalTaskFocus(tasks).support.has('shared')).toBe(false);
  });

  it('reserves independent exploration after two frontier workers, including targeted research workers', () => {
    const core = node('core'); core.status = 'running';
    const helper = node('helper');
    const probe = node('probe', 'research', ['core', 'helper']); probe.status = 'running';
    const old = node('old_exploration', 'research'); old.attempts = 5;
    const fresh = node('fresh_exploration', 'research'); fresh.task = { ...fresh.task, ownerId: 'researcher' };
    const tasks = [helper, old, fresh, core, probe, node('goal', 'goal', ['core'])];
    const ready = continuationResearchTasks(tasks, [main]);
    const engineer: ResearchWorker = { id: 'engineer', role: 'engineer', worktree: '/engineer', ownedFiles: [] };
    const researcher: ResearchWorker = { ...engineer, id: 'researcher', role: 'researcher' };

    expect(ids(ready)).toEqual(['fresh_exploration', 'helper', 'old_exploration']);
    expect(assignSharedResearchTask(ready, engineer, [engineer, researcher], [main])).toBe(helper);
    expect(assignSharedResearchTask(ready, researcher, [engineer, researcher], [main])).toBe(fresh);
    fresh.status = 'running';
    expect(continuationResearchTasks(tasks, [main])).toEqual([]);
    expect(continuationResearchTasks(tasks)[0]).toBe(helper);
  });

  it('preserves route, ownership, parking, dependency and final-review gates while ranking', () => {
    const core = node('core'); core.task = { ...core.task, ownerId: 'researcher' };
    const paused = node('paused'); paused.task = { ...paused.task, status: 'paused' };
    const parked = node('parked'); parked.routeParking = ['blocker'];
    const full = node('full'); full.task = { ...full.task, groupId: 'full' };
    const spent = node('spent'); spent.task = { ...spent.task, groupId: 'spent' };
    const finalReview = node('candidate_review', 'research', ['core']);
    finalReview.task = { ...finalReview.task, reviewScope: 'final-candidate' };
    const probe = node('feasibility', 'research', ['core']);
    const goal = node('goal', 'goal', ['core', 'paused', 'parked', 'full', 'spent']);
    const groups: RouteRecord[] = [main,
      { group: { ...main.group, id: 'full', maxConcurrent: 1 }, turns: 0, busy: 1 },
      { group: { ...main.group, id: 'spent', maxTurns: 1 }, turns: 1 }];
    const tasks = [finalReview, goal, probe, paused, parked, full, spent, core];
    const ready = continuationResearchTasks(tasks, groups);
    const engineer: ResearchWorker = { id: 'engineer', role: 'engineer', worktree: '/engineer', ownedFiles: [] };
    const researcher: ResearchWorker = { ...engineer, id: 'researcher', role: 'researcher' };

    expect(ids(ready)).toEqual(['core', 'feasibility']);
    expect(assignSharedResearchTask(ready, engineer, [engineer, researcher], groups)).toBe(probe);
    expect(assignSharedResearchTask(ready, researcher, [engineer, researcher], groups)).toBe(core);
    expect(tasks.map(record => record.status)).toEqual(tasks.map(() => 'pending'));
  });

  it('uses a newly checked premise to move from constructing the gap to its original consumer', () => {
    const core = node('core'), goal = node('goal', 'goal', ['core']);
    const probe = node('probe', 'research', ['core']);
    const tasks = [probe, goal, core];
    expect(continuationResearchTasks(tasks)[0]).toBe(core);
    expect([...originalGoalTaskFocus(tasks).targetedResearch]).toEqual(['probe']);

    integrate(core);
    expect(continuationResearchTasks(tasks)[0]).toBe(goal);
    expect([...originalGoalTaskFocus(tasks).frontier]).toEqual(['goal']);
    expect(originalGoalTaskFocus(tasks).targetedResearch.has('probe')).toBe(false);
    integrate(goal);
    expect(originalGoalTaskFocus(tasks).support.size).toBe(0);
    expect(ids(continuationResearchTasks(tasks))).toEqual(['probe']);
  });
});
