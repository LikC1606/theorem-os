import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { ProofRoute } from '../src/solver/proofRoutes';
import { createProofRoutePriority, createProofRoutePriorityIndex, selectProofRoutePriorityContext } from '../src/solver/routePriority';
import type { TaskRecord } from '../src/solver/tasks';
import { integratedProof } from './helpers/taskProof';

const node = (id: string, dependsOn: string[] = [], kind: 'lemma' | 'goal' = 'lemma'): TaskRecord => ({
  task: { id, kind, objective: id, dependsOn, revision: 0, proofPath: 'Submission.lean',
    theoremName: `Submission.${id}`, ...(kind === 'lemma' ? { type: 'True' } : {}) },
  status: 'pending', attempts: 0,
});
function checked(item: TaskRecord, inputs: TaskRecord[] = []) { integratedProof(item, { uses: inputs }); }
function fixture(count: number) {
  const goal = node('goal', [], 'goal');
  const cores = Array.from({ length: count }, (_, index) => node(`core_${index}`));
  const closings = cores.map((core, index) => node(`closing_${index}`, [core.task.id]));
  const routes: ProofRoute[] = cores.map((core, index) => ({ id: `route_${index}`, targetTaskId: goal.task.id,
    prerequisiteTaskIds: [core.task.id], closingTaskId: closings[index]!.task.id }));
  goal.alternativeRoutes = routes;
  return { goal, cores, closings, routes, tasks: [...cores, ...closings, goal] };
}

describe('scoped route priority context', () => {
  it.each([10, 100, 500])('bounds the local preview independently of %i alternative routes', count => {
    const { routes, tasks } = fixture(count), original = canonicalMathJson(tasks);
    const index = createProofRoutePriorityIndex(tasks);
    const context = selectProofRoutePriorityContext(index, { assignedRouteId: routes.at(-1)!.id,
      relatedRouteIds: routes.slice(0, -1).map(route => route.id) });

    expect(index.count).toBe(count);
    expect(index.routes).toHaveLength(count);
    expect(context).toMatchObject({ evidence: 'recorded-not-replayed', selection: 'bounded-preview',
      selectedCount: 5, totalCount: count, omittedCount: count - 5 });
    expect(context.routes).toHaveLength(5);
    expect(context.routes[0]!.routeId).toBe(routes.at(-1)!.id);
    expect(Buffer.byteLength(JSON.stringify(context))).toBeLessThan(4000);
    expect(canonicalMathJson(tasks)).toBe(original);
    expect(tasks.every(item => item.status === 'pending')).toBe(true);
  });

  it('retains an assigned parked route ahead of the full preview allowance', () => {
    const { goal, routes, tasks } = fixture(10);
    goal.parkedRoutes = { [routes.at(-1)!.id]: ['local-obstruction'] };
    const index = createProofRoutePriorityIndex(tasks);
    const context = selectProofRoutePriorityContext(index, { assignedRouteId: routes.at(-1)!.id });

    expect(context.routes[0]).toEqual(expect.objectContaining({ routeId: routes.at(-1)!.id, parked: true }));
    expect(context.routes.slice(1).every(route => !route.parked)).toBe(true);
    expect(context).toMatchObject({ selectedCount: 5, omittedCount: 5 });
    expect(goal.status).toBe('pending');
  });

  it('selects related routes by their evidence before filling the allowance with global routes', () => {
    const { cores, closings, routes, tasks } = fixture(10);
    checked(cores[0]!); checked(closings[0]!, [cores[0]!]);
    checked(cores[7]!);
    checked(cores[8]!); checked(closings[8]!, [cores[8]!]);
    const index = createProofRoutePriorityIndex(tasks, { environmentDigest: 'environment' });
    const context = selectProofRoutePriorityContext(index, { assignedRouteId: routes[9]!.id,
      relatedRouteIds: [routes[7]!.id, routes[8]!.id] });

    expect(context.routes.map(route => route.routeId)).toEqual(['route_9', 'route_8', 'route_7', 'route_0', 'route_1']);
    expect(context.routes[1]).toMatchObject({ checkedInputIds: ['core_8', 'closing_8'], frontierTaskIds: [] });
    expect(selectProofRoutePriorityContext(index, { relatedRouteIds: [routes[7]!.id] })
      .routes.map(route => route.routeId)).toEqual(['route_7', 'route_0', 'route_8', 'route_1']);
  });

  it('counts an assigned route only once when it is also related or globally preferred', () => {
    const { routes, tasks } = fixture(10);
    const context = selectProofRoutePriorityContext(createProofRoutePriorityIndex(tasks), {
      assignedRouteId: routes[0]!.id, relatedRouteIds: [routes[0]!.id, routes[0]!.id],
    });

    expect(context.routes.map(route => route.routeId)).toEqual(['route_0', 'route_1', 'route_2', 'route_3', 'route_4']);
    expect(context).toMatchObject({ selectedCount: 5, omittedCount: 5 });
  });

  it('uses explicit routes for scheduling and treats an explicit empty array as authoritative', () => {
    const { routes, tasks } = fixture(2);
    expect(createProofRoutePriority(tasks).routes).toHaveLength(2);
    expect(createProofRoutePriority(tasks, { proofRoutes: [routes[1]!] }).routes.map(route => route.routeId)).toEqual(['route_1']);
    const priority = createProofRoutePriority(tasks, { proofRoutes: [] });
    expect(priority.routes).toEqual([]);
    expect(priority.compareRoutes(routes[0]!, routes[1]!)).toBe(0);
    expect(priority.compareTasks(tasks[0]!, tasks[1]!)).toBe(0);
    expect(createProofRoutePriorityIndex(tasks, { proofRoutes: [] })).toMatchObject({ count: 0, routes: [] });
  });

  it('does not recover an excluded route from embedded node alternatives', () => {
    const { routes, tasks } = fixture(2);
    routes[0]!.id = 'PRIVATE_ROUTE_MARKER';
    const index = createProofRoutePriorityIndex(tasks, { proofRoutes: [routes[1]!] });
    const context = selectProofRoutePriorityContext(index, { assignedRouteId: 'PRIVATE_ROUTE_MARKER',
      relatedRouteIds: ['PRIVATE_ROUTE_MARKER'] });

    expect(index.count).toBe(1);
    expect(JSON.stringify({ index, context })).not.toContain('PRIVATE_ROUTE_MARKER');
  });

  it.each(['target', 'closing', 'prerequisite'] as const)('excludes a route with a hidden %s endpoint', endpoint => {
    const { routes, tasks } = fixture(2);
    routes[0]!.id = 'PRIVATE_ROUTE_MARKER';
    if (endpoint === 'target') routes[0]!.targetTaskId = 'PRIVATE_TASK_MARKER';
    else if (endpoint === 'closing') routes[0]!.closingTaskId = 'PRIVATE_TASK_MARKER';
    else routes[0]!.prerequisiteTaskIds = ['PRIVATE_TASK_MARKER'];
    const index = createProofRoutePriorityIndex(tasks);

    expect(index.routes.map(route => route.routeId)).toEqual(['route_1']);
    expect(JSON.stringify(index)).not.toContain('PRIVATE_');
  });

  it('excludes indirect out-of-scope dependency identities without changing scheduler diagnostics', () => {
    const { cores, tasks } = fixture(2);
    cores[0]!.task = { ...cores[0]!.task, dependsOn: ['PRIVATE_IMPLEMENTATION_MARKER'] };
    expect(createProofRoutePriority(tasks).routes[0]!.missingInputIds).toEqual(['PRIVATE_IMPLEMENTATION_MARKER']);
    const index = createProofRoutePriorityIndex(tasks);

    expect(index.routes.map(route => route.routeId)).toEqual(['route_1']);
    expect(JSON.stringify(index)).not.toContain('PRIVATE_IMPLEMENTATION_MARKER');
  });

  it('provides an exact count and digest for the full scoped array persisted at its reference', () => {
    const { cores, tasks } = fixture(10);
    checked(cores[8]!);
    const index = createProofRoutePriorityIndex(tasks), context = selectProofRoutePriorityContext(index);
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'theorem-route-priority-'));
    try {
      fs.writeFileSync(path.join(directory, context.index.path), JSON.stringify({ routePriority: index }));
      const saved = JSON.parse(fs.readFileSync(path.join(directory, context.index.path), 'utf8'));
      const full = context.index.field.split('.').reduce((value, field) => value[field], saved);

      expect(saved.routePriority.schema).toBe('theorem-os.route-priority.v1');
      expect(full).toEqual(index.routes);
      expect(full).toHaveLength(context.index.count);
      expect(mathDigest(canonicalMathJson(full))).toBe(context.index.digest);
      expect(context.selectedCount).toBe(4);
      expect(context.omittedCount).toBe(6);
      full[0].parked = !full[0].parked;
      expect(mathDigest(canonicalMathJson(full))).not.toBe(context.index.digest);
    } finally { fs.rmSync(directory, { recursive: true, force: true }); }
  });

  it('reports an empty or fully included scope without pretending that it covers omitted alternatives', () => {
    const empty = selectProofRoutePriorityContext(createProofRoutePriorityIndex([], { proofRoutes: [] }));
    expect(empty).toMatchObject({ selection: 'bounded-preview', routes: [], selectedCount: 0, totalCount: 0, omittedCount: 0 });
    const single = selectProofRoutePriorityContext(createProofRoutePriorityIndex(fixture(1).tasks));
    expect(single).toMatchObject({ selection: 'bounded-preview', selectedCount: 1, totalCount: 1, omittedCount: 0 });
  });
});
