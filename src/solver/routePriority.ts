import { describeProofRoutes, type ProofRoute, type RecordedRouteProofStatus } from './proofRoutes';
import { createRecordedTaskSettlement } from './progress';
import { groupOpen, hasTaskAcceptance, taskGroup, type RouteRecord, type TaskRecord } from './tasks';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';

export type ProofRoutePriority = Readonly<{
  routeId: string; targetTaskId: string; parked: boolean; closingStatus: RecordedRouteProofStatus;
  closingEvidence: 'none' | 'conditional' | 'checked'; checkedInputIds: readonly string[];
  blockedInputIds: readonly string[]; missingInputIds: readonly string[]; runningInputIds: readonly string[];
  frontierTaskIds: readonly string[];
}>;
export type ProofRoutePriorityOptions = Readonly<{
  environmentDigest?: string; groups?: readonly RouteRecord[]; proofRoutes?: readonly ProofRoute[];
}>;
export type ProofRoutePriorityIndex = Readonly<{
  schema: 'theorem-os.route-priority.v1'; evidence: 'recorded-not-replayed';
  count: number; digest: string; routes: readonly ProofRoutePriority[];
}>;

type Priority = Pick<ProofRoutePriority, 'parked' | 'closingEvidence' | 'checkedInputIds' |
  'blockedInputIds' | 'missingInputIds' | 'runningInputIds'>;
const neutral: Priority = { parked: false, closingEvidence: 'none', checkedInputIds: [],
  blockedInputIds: [], missingInputIds: [], runningInputIds: [] };
const closingRank = { none: 0, conditional: 1, checked: 2 };
const routeKey = (route: ProofRoute) => JSON.stringify([route.id, route.targetTaskId, route.prerequisiteTaskIds, route.closingTaskId]);
const compare = (a: Priority, b: Priority) => Number(a.parked) - Number(b.parked) ||
  Number(Boolean(a.blockedInputIds.length || a.missingInputIds.length)) -
    Number(Boolean(b.blockedInputIds.length || b.missingInputIds.length)) ||
  closingRank[b.closingEvidence] - closingRank[a.closingEvidence] ||
  Number(Boolean(b.checkedInputIds.length)) - Number(Boolean(a.checkedInputIds.length)) ||
  Number(Boolean(a.runningInputIds.length)) - Number(Boolean(b.runningInputIds.length));

/** Evidence orders existing work; it never enables dispatch or estimates proof difficulty. */
export function createProofRoutePriority(tasks: readonly TaskRecord[], options: ProofRoutePriorityOptions = {}) {
  const routes = options.proofRoutes ?? tasks.flatMap(node => node.alternativeRoutes ?? []);
  if (!routes.length) return { routes: [] as readonly ProofRoutePriority[],
    compareRoutes: (_a: ProofRoute, _b: ProofRoute) => 0, compareTasks: (_a: TaskRecord, _b: TaskRecord) => 0 };
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const descriptions = describeProofRoutes(routes, tasks, options.environmentDigest).routes;
  const { settled } = createRecordedTaskSettlement(tasks, { ...options, includeParkedRoutes: false });
  const byRoute = new Map<string, ProofRoutePriority>();
  const byTask = new Map<string, ProofRoutePriority[]>();
  const priorities = routes.map((route, index): ProofRoutePriority => {
    const description = descriptions[index]!, target = nodes.get(route.targetTaskId), closing = nodes.get(route.closingTaskId);
    const proof = closing?.integratedCheck ?? closing?.proof;
    // Recorded environment and input checks are shared with context; only a fresh
    // host acceptance can turn a conditional receipt into a scheduling signal.
    const conditional = description.closingStatus === 'conditional' && closing?.status === 'conditional' &&
      proof && hasTaskAcceptance(proof);
    const checkedInputIds = description.prerequisiteStatuses.filter(input => input.status === 'checked' &&
      nodes.get(input.taskId)?.status === 'integrated').map(input => input.taskId);
    const closingChecked = description.closingStatus === 'checked' && closing?.status === 'integrated';
    if (closingChecked) checkedInputIds.push(route.closingTaskId);
    const seen = new Set<string>(), blocked = new Set<string>(), missing = new Set<string>();
    const running = new Set<string>(), frontier = new Set<string>();
    const visit = (id: string) => {
      if (seen.has(id)) return;
      seen.add(id);
      const node = nodes.get(id);
      if (!node) { missing.add(id); return; }
      if (settled(node)) return;
      if (node.status === 'blocked' || node.routeParking?.length || (node.task.status ?? 'active') !== 'active') blocked.add(id);
      if (node.status === 'running') running.add(id);
      const open = node.task.dependsOn.filter(input => !settled(nodes.get(input)));
      if (open.length) open.forEach(visit);
      else frontier.add(id);
    };
    [...route.prerequisiteTaskIds, route.closingTaskId].forEach(visit);
    const priority: ProofRoutePriority = { routeId: route.id, targetTaskId: route.targetTaskId,
      parked: Boolean(target?.parkedRoutes?.[route.id]?.length || target?.routeParking?.length),
      closingStatus: description.closingStatus, closingEvidence: closingChecked ? 'checked' : conditional ? 'conditional' : 'none',
      checkedInputIds: [...new Set(checkedInputIds)], blockedInputIds: [...blocked], missingInputIds: [...missing],
      runningInputIds: [...running], frontierTaskIds: [...frontier] };
    byRoute.set(routeKey(route), priority);
    const active = target && (target.task.status ?? 'active') === 'active' && !settled(target) &&
      (!options.groups || options.groups.some(record => record.group.id === taskGroup(target.task) && groupOpen(record)));
    if (active) for (const id of [...seen, route.targetTaskId]) {
      const list = byTask.get(id) ?? []; list.push(priority); byTask.set(id, list);
    }
    return priority;
  });
  const best = new Map([...byTask].map(([id, entries]) => [id, entries.toSorted(compare)[0]!]));
  return { routes: priorities as readonly ProofRoutePriority[],
    compareRoutes: (a: ProofRoute, b: ProofRoute): number => compare(byRoute.get(routeKey(a)) ?? neutral, byRoute.get(routeKey(b)) ?? neutral),
    compareTasks: (a: TaskRecord, b: TaskRecord): number => compare(best.get(a.task.id) ?? neutral, best.get(b.task.id) ?? neutral) };
}

/** Persist the complete scope-safe list; live references grant no proof acceptance. */
export function createProofRoutePriorityIndex(tasks: readonly TaskRecord[], options: ProofRoutePriorityOptions = {}): ProofRoutePriorityIndex {
  const visible = new Set(tasks.map(node => node.task.id));
  const proofRoutes = (options.proofRoutes ?? tasks.flatMap(node => node.alternativeRoutes ?? []))
    .filter(route => [route.targetTaskId, route.closingTaskId, ...route.prerequisiteTaskIds].every(id => visible.has(id)));
  const routes = createProofRoutePriority(tasks, { ...options, proofRoutes }).routes.filter(route =>
    [...route.checkedInputIds, ...route.blockedInputIds, ...route.missingInputIds,
      ...route.runningInputIds, ...route.frontierTaskIds].every(id => visible.has(id)));
  return { schema: 'theorem-os.route-priority.v1', evidence: 'recorded-not-replayed',
    count: routes.length, digest: mathDigest(canonicalMathJson(routes)), routes };
}

/** A local preview retains its assigned route, then at most four related or global routes. */
export function selectProofRoutePriorityContext(index: ProofRoutePriorityIndex,
  options: { assignedRouteId?: string; relatedRouteIds?: readonly string[] } = {}) {
  const assigned = index.routes.find(route => route.routeId === options.assignedRouteId);
  const relatedIds = new Set(options.relatedRouteIds ?? []);
  const remaining = index.routes.filter(route => route !== assigned);
  const preferred = [...remaining.filter(route => relatedIds.has(route.routeId)).toSorted(compare),
    ...remaining.filter(route => !relatedIds.has(route.routeId)).toSorted(compare)].slice(0, 4);
  const routes = [...(assigned ? [assigned] : []), ...preferred];
  return { evidence: index.evidence, selection: 'bounded-preview' as const,
    routes, selectedCount: routes.length, totalCount: index.count, omittedCount: index.count - routes.length,
    index: { path: 'COOPERATION.json' as const, field: 'routePriority.routes' as const,
      count: index.count, digest: index.digest,
      retrieval: 'Read this scoped live array and require its length and SHA-256 of canonicalMathJson(array) to match count and digest. ' +
        'A missing or changed array is unavailable, not a complete route list or proof acceptance.' } };
}
