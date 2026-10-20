import { describe, expect, it } from 'vitest';
import { proofRouteReady, type ProofRoute } from '../src/solver/proofRoutes';
import { createProofRoutePriority } from '../src/solver/routePriority';
import { markTaskAcceptance, taskVersion, type RouteRecord, type TaskRecord } from '../src/solver/tasks';
import { integratedProof } from './helpers/taskProof';

const node = (id: string, dependsOn: string[] = [], kind: 'lemma' | 'goal' = 'lemma'): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0, proofPath: 'Submission.lean',
    theoremName: `Submission.${id}`, ...(kind === 'lemma' ? { type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
function checked(item: TaskRecord, uses: TaskRecord[] = []) { return integratedProof(item, { uses }); }
function conditional(item: TaskRecord, inputs: TaskRecord[]) {
  const proof = checked(item);
  delete item.integratedCheck;
  item.status = 'conditional'; item.proof = proof;
  delete proof.references;
  proof.conditions = inputs.map(input => ({ taskId: input.task.id, taskDigest: taskVersion(input.task) }));
  markTaskAcceptance(proof);
  return proof;
}
function fixture() {
  const a = node('a'), closeA = node('close_a', ['a']), b = node('b'), c = node('c');
  const closeB = node('close_b', ['b', 'c']), goal = node('goal', [], 'goal');
  const routes: ProofRoute[] = [
    { id: 'route_a', targetTaskId: 'goal', prerequisiteTaskIds: ['a'], closingTaskId: 'close_a' },
    { id: 'route_b', targetTaskId: 'goal', prerequisiteTaskIds: ['b', 'c'], closingTaskId: 'close_b' },
  ];
  goal.alternativeRoutes = routes;
  return { a, b, c, closeA, closeB, goal, routes, tasks: [a, closeA, b, c, closeB, goal] };
}

describe('evidence-based alternative route priority', () => {
  it('uses checked progress on a later route to order its remaining ready work', () => {
    const { a, b, c, routes, tasks } = fixture(); checked(b);
    const priority = createProofRoutePriority(tasks), ready = [a, c];
    expect(routes.toSorted(priority.compareRoutes).map(route => route.id)).toEqual(['route_b', 'route_a']);
    expect(ready.toSorted(priority.compareTasks)).toEqual([c, a]);
    expect(new Set(ready.toSorted(priority.compareTasks))).toEqual(new Set(ready));
    expect(priority.routes[1].checkedInputIds).toEqual(['b']);
    expect(priority.routes[1].frontierTaskIds).toEqual(['c']);
  });

  it('uses a freshly checked conditional connection without claiming its premises or original goal', () => {
    const { b, c, closeB, goal, routes, tasks } = fixture(); conditional(closeB, [b, c]);
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[1].closingEvidence).toBe('conditional');
    expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    expect(priority.routes[1].checkedInputIds).toEqual([]);
    expect(proofRouteReady(routes[1], tasks)).toBe(false);
    expect(goal.status).toBe('pending');
    expect(goal.integratedCheck).toBeUndefined();
  });

  it.each(['condition', 'closing', 'references'] as const)('drops conditional priority after a %s version changes', change => {
    const { b, c, closeB, routes, tasks } = fixture(); const proof = conditional(closeB, [b, c]);
    if (change === 'condition') b.task = { ...b.task, revision: 1 };
    if (change === 'closing') closeB.task = { ...closeB.task, revision: 1 };
    if (change === 'references') proof.references = { sourceCommit: 'canonical', environmentDigest: 'environment',
      contextDigest: 'context', inputs: [], root: { name: closeB.task.theoremName!, file: 'Submission.lean' },
      proof: [], statement: [], tasks: [{ taskId: b.task.id, taskDigest: 'old-version' }] };
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[1].closingEvidence).toBe('none');
    expect(priority.compareRoutes(routes[1], routes[0])).toBe(0);
  });

  it('does not give restored conditional receipts current-process priority', () => {
    const { b, c, closeB, tasks } = fixture(); conditional(closeB, [b, c]);
    const restored = JSON.parse(JSON.stringify(tasks)) as TaskRecord[];
    expect(createProofRoutePriority(restored).routes[1].closingEvidence).toBe('none');
  });

  it('uses recorded unconditional evidence only for ordering after restore', () => {
    const { b, c, closeB, routes, tasks } = fixture(); checked(b); checked(c); checked(closeB, [b, c]);
    const restored = JSON.parse(JSON.stringify(tasks)) as TaskRecord[], priority = createProofRoutePriority(restored);
    expect(priority.routes[1].closingEvidence).toBe('checked');
    expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    expect(proofRouteReady(routes[1], restored)).toBe(false);
  });

  it('drops checked priority after exact prerequisite versions change', () => {
    const { b, routes, tasks } = fixture(); checked(b);
    expect(createProofRoutePriority(tasks).compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    b.task = { ...b.task, type: 'False', revision: 1 };
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[1].checkedInputIds).toEqual([]);
    expect(priority.compareRoutes(routes[1], routes[0])).toBe(0);
  });

  it('does not reward a checked prerequisite with stale recorded transitive references', () => {
    const { b, tasks } = fixture(), input = node('input');
    checked(input); checked(b, [input]); input.task = { ...input.task, revision: 1 };
    expect(createProofRoutePriority([...tasks, input]).routes[1].checkedInputIds).toEqual([]);
  });

  it('recomputes positive evidence for the requested environment', () => {
    const { b, tasks } = fixture(); checked(b);
    expect(createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[1].checkedInputIds).toEqual(['b']);
    expect(createProofRoutePriority(tasks, { environmentDigest: 'changed' }).routes[1].checkedInputIds).toEqual([]);
  });

  it('does not assume an explicit environment for a conditional projection without references', () => {
    const { b, c, closeB, tasks } = fixture(); conditional(closeB, [b, c]);
    expect(createProofRoutePriority(tasks, { environmentDigest: 'environment' }).routes[1].closingEvidence).toBe('none');
  });

  it('distinguishes a fully checked closing receipt from conditional evidence', () => {
    const { a, b, c, closeA, closeB, routes, tasks } = fixture();
    checked(a); checked(closeA, [a]); conditional(closeB, [b, c]);
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[0].closingEvidence).toBe('checked');
    expect(priority.compareRoutes(routes[0], routes[1])).toBeLessThan(0);
    expect(proofRouteReady(routes[0], tasks)).toBe(true);
  });

  it('uses structured obstruction state while preserving independent work on that route', () => {
    const { a, b, c, closeB, goal, routes, tasks } = fixture(), independent = node('independent');
    closeB.task = { ...closeB.task, dependsOn: ['b', 'c', independent.task.id] };
    const revised = { ...routes[1], prerequisiteTaskIds: ['b', 'c', independent.task.id] };
    goal.alternativeRoutes = [routes[0], revised]; tasks.push(independent);
    checked(b); c.status = 'blocked';
    let priority = createProofRoutePriority(tasks);
    expect(priority.compareRoutes(routes[0], revised)).toBeLessThan(0);
    expect(priority.routes[1].blockedInputIds).toEqual(['c']);
    expect([independent, a].toSorted(priority.compareTasks)).toEqual([a, independent]);
    expect(independent.status).toBe('pending');
    c.status = 'pending'; priority = createProofRoutePriority(tasks);
    expect(priority.compareRoutes(revised, routes[0])).toBeLessThan(0);
  });

  it('does not follow obsolete planned obstacles through a checked formal interface', () => {
    const { b, tasks } = fixture(), obsolete = node('obsolete'); obsolete.status = 'blocked';
    b.task = { ...b.task, dependsOn: [obsolete.task.id] }; checked(b);
    const priority = createProofRoutePriority([...tasks, obsolete]);
    expect(priority.routes[1].checkedInputIds).toEqual(['b']);
    expect(priority.routes[1].blockedInputIds).toEqual([]);
    expect(priority.routes[1].frontierTaskIds).not.toContain('obsolete');
  });

  it('keeps prose feedback from inventing an obstruction or a mathematical equivalence', () => {
    const { a, routes, tasks } = fixture();
    a.feedback = 'This route is impossible and duplicates route_b.';
    a.finding = 'A useful investigation still has unfinished steps.';
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[0].blockedInputIds).toEqual([]);
    expect(priority.compareRoutes(routes[0], routes[1])).toBe(0);
  });

  it('removes parking preference when an existing blocker is reopened', () => {
    const { b, goal, routes, tasks } = fixture(); checked(b);
    goal.parkedRoutes = { route_b: ['concrete-blocker'] };
    expect(createProofRoutePriority(tasks).compareRoutes(routes[0], routes[1])).toBeLessThan(0);
    goal.parkedRoutes = {};
    expect(createProofRoutePriority(tasks).compareRoutes(routes[1], routes[0])).toBeLessThan(0);
  });

  it('diversifies equally evidenced routes when one is already running', () => {
    const { a, c, routes, tasks } = fixture(); a.status = 'running';
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes[0].runningInputIds).toEqual(['a']);
    expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    expect(priority.compareTasks(c, a)).toBeLessThan(0);
  });

  it('keeps checked progress ahead of diversity at the same obstruction level', () => {
    const { a, b, c, routes, tasks } = fixture(); checked(b); c.status = 'running';
    const priority = createProofRoutePriority(tasks);
    expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    expect(priority.compareTasks(c, a)).toBeLessThan(0);
  });

  it('uses the best eligible consumer route for a helper shared by alternatives', () => {
    const { a, b, c, closeA, closeB, goal, tasks } = fixture(), shared = node('shared');
    a.task = { ...a.task, dependsOn: ['shared'] }; b.task = { ...b.task, dependsOn: ['shared'] };
    shared.status = 'running'; a.status = 'blocked';
    const priority = createProofRoutePriority([...tasks, shared]);
    expect(priority.routes[0].runningInputIds).toEqual(['shared']);
    expect(priority.routes[1].runningInputIds).toEqual(['shared']);
    expect(priority.compareTasks(shared, c)).toBe(0);
    expect(priority.compareTasks(shared, closeA)).toBeLessThan(0);
    expect(goal.alternativeRoutes).toHaveLength(2);
    expect(closeB.task.dependsOn).toEqual(['b', 'c']);
  });

  it('does not count a shared running input as spare capacity on either alternative', () => {
    const { a, b, routes, tasks } = fixture(), shared = node('shared');
    a.task = { ...a.task, dependsOn: ['shared'] }; b.task = { ...b.task, dependsOn: ['shared'] };
    shared.status = 'running';
    const priority = createProofRoutePriority([...tasks, shared]);
    expect(priority.routes.map(route => route.runningInputIds)).toEqual([['shared'], ['shared']]);
    expect(priority.compareRoutes(routes[0], routes[1])).toBe(0);
  });

  it('keeps a shared helper eligible through an unparked consumer route', () => {
    const { a, b, c, goal, tasks } = fixture(), shared = node('shared');
    a.task = { ...a.task, dependsOn: ['shared'] }; b.task = { ...b.task, dependsOn: ['shared'] };
    goal.parkedRoutes = { route_a: ['blocked-a-only'] };
    const priority = createProofRoutePriority([...tasks, shared]);
    expect(priority.compareTasks(shared, c)).toBe(0);
    expect(priority.compareTasks(shared, a)).toBeLessThan(0);
  });

  it('records missing inputs without dropping a route or any remaining work', () => {
    const { b, c, routes, tasks } = fixture();
    const priority = createProofRoutePriority(tasks.filter(item => item !== c));
    expect(priority.routes).toHaveLength(2);
    expect(priority.routes[1].missingInputIds).toEqual(['c']);
    expect(priority.compareRoutes(routes[0], routes[1])).toBeLessThan(0);
    expect(b.status).toBe('pending');
  });

  it('preserves stable ties and does not use premise count as an estimate of difficulty', () => {
    const { routes, tasks } = fixture(); const priority = createProofRoutePriority(tasks);
    expect(priority.compareRoutes(routes[0], routes[1])).toBe(0);
    expect(routes.toSorted(priority.compareRoutes)).toEqual(routes);
    expect([...routes].reverse().toSorted(priority.compareRoutes)).toEqual([...routes].reverse());
    expect(priority.compareRoutes(structuredClone(routes[0]), structuredClone(routes[1]))).toBe(0);
  });

  it('does not change assignments, owners, task versions, work sets, or acceptance', () => {
    const { a, b, goal, routes, tasks } = fixture(); checked(b);
    a.task = { ...a.task, ownerId: 'researcher' }; goal.status = 'running';
    goal.assignment = { taskId: goal.task.id, taskDigest: taskVersion(goal.task), workerId: 'engineer',
      seedCommit: 'saved-draft', routeId: routes[0].id };
    const before = structuredClone(tasks), versions = tasks.map(item => taskVersion(item.task));
    const priority = createProofRoutePriority(tasks), ordered = tasks.toSorted(priority.compareTasks);
    expect(tasks).toEqual(before);
    expect(tasks.map(item => taskVersion(item.task))).toEqual(versions);
    expect(new Set(ordered)).toEqual(new Set(tasks));
    expect(goal.assignment.routeId).toBe('route_a');
    expect(proofRouteReady(routes[1], tasks)).toBe(false);
  });

  it('keeps plans without alternatives in their existing order', () => {
    const tasks = [node('first'), node('second')], priority = createProofRoutePriority(tasks);
    expect(priority.routes).toEqual([]);
    expect(tasks.toSorted(priority.compareTasks)).toEqual(tasks);
  });

  it.each(['paused', 'stopped'] as const)('keeps %s goal routes visible without promoting their tasks', status => {
    const { a, b, c, goal, routes, tasks } = fixture(); checked(b);
    goal.task = { ...goal.task, status };
    const priority = createProofRoutePriority(tasks);
    expect(priority.routes).toHaveLength(2);
    expect(priority.routes[1].checkedInputIds).toEqual(['b']);
    expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
    expect(priority.compareTasks(c, a)).toBe(0);
  });

  it('keeps settled goal evidence visible without giving its unfinished alternative tasks priority', () => {
    const { a, b, closeA, closeB, goal, routes, tasks } = fixture(), other = node('other');
    checked(a); checked(closeA, [a]); checked(goal, [closeA]); checked(closeB);
    const priority = createProofRoutePriority([...tasks, other]);
    expect(priority.routes[1].closingEvidence).toBe('checked');
    expect(priority.compareRoutes(routes[1], routes[0])).toBe(0);
    expect(priority.compareTasks(b, other)).toBe(0);
    expect(b.status).toBe('pending');
  });

  it.each(['paused', 'stopped', 'exhausted', 'missing'] as const)(
    'ignores task priority from a %s target group while retaining its route report', control => {
      const { a, b, c, routes, tasks } = fixture(); checked(b);
      const groups: RouteRecord[] = control === 'missing' ? [] : [{ group: { id: 'main', objective: 'main', revision: 0,
        status: control === 'exhausted' ? 'active' : control, maxTurns: 2 }, turns: control === 'exhausted' ? 2 : 0 }];
      const priority = createProofRoutePriority(tasks, { groups });
      expect(priority.routes).toHaveLength(2);
      expect(priority.compareRoutes(routes[1], routes[0])).toBeLessThan(0);
      expect(priority.compareTasks(c, a)).toBe(0);
    });

  it('keeps an active group eligible before its configured turn limit', () => {
    const { a, b, c, tasks } = fixture(); checked(b);
    const groups: RouteRecord[] = [{ group: { id: 'main', objective: 'main', revision: 0, status: 'active', maxTurns: 2 }, turns: 1 }];
    expect(createProofRoutePriority(tasks, { groups }).compareTasks(c, a)).toBeLessThan(0);
  });

  it('does not let a stopped consumer change the ordering of shared work for an active goal', () => {
    const { a, b, tasks } = fixture(), oldClosing = node('old_closing', ['b']), stopped = node('stopped', [], 'goal');
    stopped.task = { ...stopped.task, status: 'stopped' };
    stopped.alternativeRoutes = [{ id: 'old_route', targetTaskId: 'stopped', prerequisiteTaskIds: ['b'], closingTaskId: 'old_closing' }];
    checked(oldClosing);
    const priority = createProofRoutePriority([...tasks, oldClosing, stopped]);
    expect(priority.routes).toHaveLength(3);
    expect(priority.routes[2].closingEvidence).toBe('checked');
    expect(priority.compareTasks(b, a)).toBe(0);
    expect([a, b].toSorted(priority.compareTasks)).toEqual([a, b]);
  });

  it('does not let a paused consumer group change the ordering of shared work for another active group', () => {
    const { a, b, tasks } = fixture(), oldClosing = node('old_closing', ['b']), paused = node('paused', [], 'goal');
    b.task = { ...b.task, sharing: 'problem' };
    oldClosing.task = { ...oldClosing.task, groupId: 'other' }; paused.task = { ...paused.task, groupId: 'other' };
    paused.alternativeRoutes = [{ id: 'paused_route', targetTaskId: 'paused', prerequisiteTaskIds: ['b'], closingTaskId: 'old_closing' }];
    checked(oldClosing);
    const groups: RouteRecord[] = ['main', 'other'].map(id => ({ group: { id, objective: id, revision: 0,
      status: id === 'main' ? 'active' : 'paused' }, turns: 0 }));
    const priority = createProofRoutePriority([...tasks, oldClosing, paused], { groups });
    expect(priority.routes).toHaveLength(3);
    expect(priority.routes[2].closingEvidence).toBe('checked');
    expect(priority.compareTasks(b, a)).toBe(0);
  });
});
