import { describe, expect, it } from 'vitest';
import type { SolverProblem } from '../src/solver/problem';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { describeProofRoutes, type ProofRoute } from '../src/solver/proofRoutes';
import { recordRouteBlockers, refreshRouteBlockers, type RouteBlocker } from '../src/solver/routeControl';
import { continuationResearchTasks, criticalPathResearchTasks, finalCandidateReviewReady, plannedTaskDependencyIds,
  readyResearchTasks, researchCanAdvance, routeAllowsTask, selectedTaskRoute, taskCanStart, taskDependenciesReady } from '../src/solver/modules/search';
import { markTaskAcceptance, parseCooperationPlan, taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';

const problem = { ownedFiles: ['Submission.lean'], targets: [{ theoremName: 'Submission.goal', proofPath: 'Submission.lean' }],
  declarations: { 'Submission.lean': [{ name: 'Submission.goal' }] } } as unknown as SolverProblem;

function node(id: string, kind: CooperativeTask['kind'] = 'lemma', dependsOn: string[] = []): TaskRecord {
  return { task: { id, kind, objective: id, dependsOn, revision: 0,
    ...(['lemma', 'goal'].includes(kind) ? { proofPath: 'Submission.lean', theoremName: `Submission.${id}` } : {}),
    ...(kind === 'lemma' ? { type: 'True' } : {}) }, status: 'pending', attempts: 0 };
}
function checked(item: TaskRecord, uses: TaskRecord[] = []) {
  item.status = 'integrated';
  const proof = item.integratedCheck = { taskDigest: taskVersion(item.task), passed: true, commit: 'canonical',
    sourceDigest: 'source', seedCommit: 'seed', changes: [], verification: { status: 'kernel_verified', targetCommit: 'projection',
      results: [{ status: 'kernel_verified', targetCommit: 'projection', receiptId: `receipt-${item.task.id}` }] },
    references: { sourceCommit: 'canonical', environmentDigest: 'environment', contextDigest: 'context', inputs: [],
      root: { name: item.task.theoremName!, file: item.task.proofPath! }, statement: [],
      proof: uses.map(input => ({ name: input.task.theoremName!, file: input.task.proofPath! })),
      tasks: uses.map(input => ({ taskId: input.task.id, taskDigest: taskVersion(input.task) })) } } as TaskProof;
  markTaskAcceptance(proof);
  return proof;
}
function fixture() {
  const a = node('a'), closeA = node('close_a', 'lemma', ['a']), b = node('b'), c = node('c');
  const closeB = node('close_b', 'lemma', ['b', 'c']), goal = node('goal', 'goal');
  const routes: ProofRoute[] = [
    { id: 'a_route', targetTaskId: 'goal', prerequisiteTaskIds: ['a'], closingTaskId: 'close_a' },
    { id: 'b_route', targetTaskId: 'goal', prerequisiteTaskIds: ['b', 'c'], closingTaskId: 'close_b' },
  ];
  goal.alternativeRoutes = routes;
  return { a, b, c, closeA, closeB, goal, routes, tasks: [a, closeA, b, c, closeB, goal] };
}

describe('alternative route scheduling', () => {
  it.each(['paused', 'stopped', 'inactive-group', 'exhausted-group', 'checked-consumer', 'parked-task', 'parked-routes'] as const)(
    'does not promote a helper solely for a %s consumer', inactive => {
      const current = node('current'), input = node('checked_input'), helper = node('helper', 'lemma', [input.task.id]);
      const goal = node('goal', 'goal', [current.task.id]), unused = node('unused_goal', 'goal', [helper.task.id]);
      goal.task = { ...goal.task, conditional: false };
      checked(input);
      if (inactive === 'paused' || inactive === 'stopped') unused.task = { ...unused.task, status: inactive };
      if (inactive === 'inactive-group' || inactive === 'exhausted-group') unused.task = { ...unused.task, groupId: 'old' };
      if (inactive === 'checked-consumer') checked(unused);
      if (inactive === 'parked-task') unused.routeParking = ['local-obstruction'];
      if (inactive === 'parked-routes') {
        unused.alternativeRoutes = [{ id: 'old-route', targetTaskId: unused.task.id,
          prerequisiteTaskIds: [], closingTaskId: helper.task.id }];
        unused.parkedRoutes = { 'old-route': ['local-obstruction'] };
      }
      const groups = [
        { group: { id: 'main', objective: 'Current proof', status: 'active' as const, revision: 0 }, turns: 0 },
        { group: { id: 'old', objective: 'Earlier proof', status: inactive === 'inactive-group' ? 'stopped' as const : 'active' as const,
          revision: 0, ...(inactive === 'exhausted-group' ? { maxTurns: 1 } : {}) }, turns: 1 },
      ];
      expect(readyResearchTasks([current, input, helper, goal, unused], groups)).toEqual([current, helper]);
    });

  it('follows checked input evidence on a later branch and recomputes priority after its version changes', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    closeA.task = { ...closeA.task, conditional: false };
    closeB.task = { ...closeB.task, conditional: false };
    checked(b);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    expect(readyResearchTasks(tasks)).toEqual([c, a]);
    expect(continuationResearchTasks(tasks)).toEqual([c, a]);
    expect(taskCanStart(goal.task, tasks)).toBe(false);
    b.task = { ...b.task, type: 'False', revision: 1 };
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('a_route');
    expect(continuationResearchTasks(tasks)).toEqual([a, c]);
    expect(goal.status).toBe('pending');
    expect(goal.integratedCheck).toBeUndefined();
  });

  it('reorders an unready pending branch by evidence while preserving an active assignment', () => {
    const { b, goal, tasks } = fixture();
    goal.assignment = { taskId: goal.task.id, taskDigest: taskVersion(goal.task), workerId: 'engineer',
      seedCommit: 'saved-draft', routeId: 'a_route' };
    checked(b);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    goal.status = 'running';
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('a_route');
    expect(goal.assignment.routeId).toBe('a_route');
  });

  it('preserves old plan contracts while offering a conditional connection without route metadata', () => {
    const input = node('input'), goal = node('goal', 'goal', ['input']);
    const version = taskVersion(goal.task);
    const parsed = parseCooperationPlan(problem, { tasks: [input.task, goal.task] });
    expect(parsed).toEqual({ tasks: [input.task, goal.task], groups: [
      { id: 'main', objective: 'Prove the original problem', status: 'active', revision: 0 },
    ] });
    expect(plannedTaskDependencyIds(goal, [input, goal])).toEqual(['input']);
    expect(selectedTaskRoute(goal, [input, goal])).toBeUndefined();
    expect(readyResearchTasks([input, goal])).toEqual([goal, input]);
    expect(taskDependenciesReady(goal.task, [input, goal])).toBe(false);
    expect(taskVersion(goal.task)).toBe(version);
    expect(goal.task.conditional).toBeUndefined();
    expect(goal.status).toBe('pending');
    expect(finalCandidateReviewReady([input, goal])).toBe(false);
    checked(input);
    expect(readyResearchTasks([input, goal])).toEqual([goal]);
    expect(taskDependenciesReady(goal.task, [input, goal])).toBe(true);
    expect(finalCandidateReviewReady([input, goal])).toBe(false);
  });

  it('passes route contracts through the plan parser without rewriting frozen goal dependencies', () => {
    const { tasks, routes, goal } = fixture();
    const version = taskVersion(goal.task);
    const parsed = parseCooperationPlan(problem, { tasks: tasks.map(item => item.task), proofRoutes: routes });
    expect(parsed.proofRoutes).toEqual(routes);
    expect(parsed.tasks.find(task => task.id === 'goal')!.dependsOn).toEqual([]);
    expect(taskVersion(parsed.tasks.find(task => task.id === 'goal')!)).toBe(version);
  });

  it('dispatches a checked B branch when the A branch is blocked or parked', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    a.status = 'blocked'; closeA.routeParking = ['a-obstruction'];
    checked(b); checked(c); checked(closeB, [b, c]);
    expect(taskCanStart(goal.task, tasks)).toBe(true);
    expect(taskDependenciesReady(goal.task, tasks)).toBe(true);
    expect(readyResearchTasks(tasks)).toContain(goal);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    expect(plannedTaskDependencyIds(goal, tasks)).toEqual(['b', 'c', 'close_b']);
    expect(researchCanAdvance(tasks, undefined, new Set())).toBe(true);
  });

  it('requires every B premise and the closing task rather than mixing partial branches', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(b); checked(closeB, [b]);
    expect(taskCanStart(goal.task, tasks)).toBe(false);
    expect(readyResearchTasks(tasks)).not.toContain(goal);
    checked(c);
    closeB.status = 'pending';
    expect(taskCanStart(goal.task, tasks)).toBe(false);
    checked(closeB, [b, c]);
    expect(readyResearchTasks(tasks)).toContain(goal);
    closeB.status = 'blocked'; checked(closeA, [a]);
    expect(readyResearchTasks(tasks)).toContain(goal);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('a_route');
  });

  it.each(['conditional', 'archived', 'stale'] as const)('does not dispatch goals from %s closing evidence', invalid => {
    const { a, b, c, closeB, goal, tasks } = fixture();
    a.status = 'blocked'; checked(b); checked(c); const proof = checked(closeB, [b, c]);
    if (invalid === 'conditional') proof.conditions = [{ taskId: 'b', taskDigest: taskVersion(b.task) }];
    if (invalid === 'stale') proof.references!.tasks![0].taskDigest = 'old-version';
    const currentTasks = invalid === 'archived' ? JSON.parse(JSON.stringify(tasks)) as TaskRecord[] : tasks;
    const currentGoal = currentTasks.find(item => item.task.id === goal.task.id)!;
    expect(taskCanStart(currentGoal.task, currentTasks)).toBe(false);
    expect(taskDependenciesReady(currentGoal.task, currentTasks)).toBe(false);
    expect(readyResearchTasks(currentTasks)).not.toContain(currentGoal);
  });

  it('keeps original ordinary dependencies as additional AND conditions', () => {
    const { a, b, c, closeB, goal, tasks } = fixture(), extra = node('extra');
    goal.task = { ...goal.task, dependsOn: ['extra'] };
    a.status = 'blocked'; checked(b); checked(c); checked(closeB, [b, c]);
    expect(taskCanStart(goal.task, [...tasks, extra])).toBe(false);
    expect(plannedTaskDependencyIds(goal, [...tasks, extra])).toEqual(['extra', 'b', 'c', 'close_b']);
    checked(extra);
    expect(readyResearchTasks([...tasks, extra])).toContain(goal);
  });

  it('retains the selected branch and its dependencies on an interrupted assignment', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'draft', routeId: 'b_route' };
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    expect(plannedTaskDependencyIds(goal, tasks)).toEqual(['b', 'c', 'close_b']);
  });

  it('chooses the ready B route for a pending draft after the previously assigned A route loses evidence', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'saved-a-draft',
      routeId: 'a_route', dependencies: [{ taskId: 'a', taskDigest: taskVersion(a.task) },
        { taskId: 'close_a', taskDigest: taskVersion(closeA.task) }] };
    a.status = 'blocked';
    expect(taskCanStart(goal.task, tasks)).toBe(true);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    expect(plannedTaskDependencyIds(goal, tasks)).toEqual(['b', 'c', 'close_b']);
  });

  it('keeps an active A assignment fixed even when B becomes the only ready alternative', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'active-a-draft', routeId: 'a_route' };
    a.status = 'blocked'; goal.status = 'running';
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('a_route');
    expect(plannedTaskDependencyIds(goal, tasks)).toEqual(['a', 'close_a']);
    expect(readyResearchTasks(tasks)).not.toContain(goal);
    goal.parkedRoutes = { a_route: ['a-local-obstruction'] };
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('a_route');
  });

  it('keeps route inputs on the original proof path in critical-path and continuation scheduling', () => {
    const { a, b, c, closeB, goal, tasks } = fixture(), unrelated = node('unrelated');
    closeB.task = { ...closeB.task, conditional: false };
    a.status = 'blocked';
    expect(criticalPathResearchTasks([unrelated, ...tasks]).slice(0, 2)).toEqual([b, c]);
    checked(b); checked(c); checked(closeB, [b, c]);
    expect(continuationResearchTasks([unrelated, ...tasks])[0]).toBe(goal);
  });

  it('parks one selected OR branch while allowing a fresh B route to dispatch the same original goal', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'draft', routeId: 'a_route' };
    const blockers: RouteBlocker[] = [], proposal = { mechanism: 'missing-a-inference', scope: 'a-closure',
      reopenOn: [{ kind: 'environment-changed' as const }] };
    recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
    recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
    refreshRouteBlockers(blockers, tasks, 'environment', 'problem');
    expect(goal.parkedRoutes).toEqual({ a_route: [blockers[0].id] });
    expect(goal.routeParking).toEqual([]);
    expect(routeAllowsTask(goal.task, tasks)).toBe(true);
    expect(readyResearchTasks(tasks)).toContain(goal);
    expect(selectedTaskRoute(goal, tasks)?.id).toBe('b_route');
    expect(plannedTaskDependencyIds(goal, tasks)).toEqual(['b', 'c', 'close_b']);
  });

  it('does not dispatch or claim future work when every checked alternative is parked', () => {
    const { a, b, c, closeA, closeB, goal, tasks, routes } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    const blockers: RouteBlocker[] = [];
    for (const route of routes) {
      goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'draft', routeId: route.id };
      const proposal = { mechanism: `missing-${route.id}-inference`, scope: 'closure', reopenOn: [{ kind: 'environment-changed' as const }] };
      recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
      recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
    }
    refreshRouteBlockers(blockers, tasks, 'environment', 'problem');
    expect(routeAllowsTask(goal.task, tasks)).toBe(false);
    expect(taskCanStart(goal.task, tasks)).toBe(false);
    expect(readyResearchTasks(tasks)).toEqual([]);
    expect(selectedTaskRoute(goal, tasks)).toBeUndefined();
    expect(researchCanAdvance(tasks, undefined, new Set(['engineer']))).toBe(false);
  });

  it('releases a restored A assignment after parking without losing its saved proof draft', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture();
    checked(a); checked(closeA, [a]); checked(b); checked(c); checked(closeB, [b, c]);
    goal.assignment = { taskId: 'goal', taskDigest: taskVersion(goal.task), workerId: 'engineer', seedCommit: 'draft', routeId: 'a_route' };
    goal.proof = { ...checked(node('saved_draft')), passed: false,
      changes: [{ file: 'Submission.lean', name: 'saved_support', after: 'lemma saved_support : True := by trivial' }] };
    goal.finding = 'Saved A work remains available when trying B.';
    const blockers: RouteBlocker[] = [], proposal = { mechanism: 'same-a-blocker', scope: 'closure',
      reopenOn: [{ kind: 'environment-changed' as const }] };
    recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
    recordRouteBlockers(blockers, [proposal], goal.task, tasks, 'environment', 'problem');
    const restored: { tasks: TaskRecord[]; blockers: RouteBlocker[] } = JSON.parse(JSON.stringify({ tasks, blockers }));
    const byId = new Map(restored.tasks.map(item => [item.task.id, item]));
    for (const id of ['a', 'b', 'c']) checked(byId.get(id)!);
    checked(byId.get('close_a')!, [byId.get('a')!]); checked(byId.get('close_b')!, [byId.get('b')!, byId.get('c')!]);
    refreshRouteBlockers(restored.blockers, restored.tasks, 'environment', 'problem');
    const restoredGoal = byId.get('goal')!;
    expect(restoredGoal.assignment).toBeUndefined();
    expect(restoredGoal.proof).toEqual(goal.proof);
    expect(restoredGoal.finding).toBe(goal.finding);
    expect(readyResearchTasks(restored.tasks)).toContain(restoredGoal);
    expect(selectedTaskRoute(restoredGoal, restored.tasks)?.id).toBe('b_route');
  });

  it('never promotes checked closing helpers into original proof acceptance', () => {
    const { b, c, closeB, goal, tasks, routes } = fixture();
    checked(b); checked(c); checked(closeB, [b, c]);
    expect(taskCanStart(goal.task, tasks)).toBe(true);
    expect(finalCandidateReviewReady(tasks)).toBe(false);
    expect(describeProofRoutes(routes, tasks).routes[1].connection).toBe('awaiting-original-check');
    checked(goal, [closeB]);
    expect(finalCandidateReviewReady(tasks)).toBe(true);
    expect(describeProofRoutes(routes, tasks).routes[1].connection).toBe('closed-by-original-check');
  });
});
