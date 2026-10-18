import { describeProofRoutes, type ProofRoute, type RecordedRouteProofStatus } from './proofRoutes';
import { createRecordedTaskSettlement } from './progress';
import { hasTaskAcceptance, taskGroup, taskVersion, type RouteRecord, type TaskRecord } from './tasks';

export type ProofRoutePriority = Readonly<{
  routeId: string; targetTaskId: string; parked: boolean; closingStatus: RecordedRouteProofStatus;
  closingEvidence: 'none' | 'conditional' | 'checked'; checkedInputIds: readonly string[];
  blockedInputIds: readonly string[]; missingInputIds: readonly string[]; runningInputIds: readonly string[];
  frontierTaskIds: readonly string[];
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
export function createProofRoutePriority(tasks: readonly TaskRecord[], options: {
  environmentDigest?: string; groups?: readonly RouteRecord[];
} = {}) {
  const routes = tasks.flatMap(node => node.alternativeRoutes ?? []);
  if (!routes.length) return { routes: [] as readonly ProofRoutePriority[],
    compareRoutes: (_a: ProofRoute, _b: ProofRoute) => 0, compareTasks: (_a: TaskRecord, _b: TaskRecord) => 0 };
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const versions = new Map(tasks.map(node => [node.task.id, taskVersion(node.task)]));
  const descriptions = describeProofRoutes(routes, tasks, options.environmentDigest).routes;
  const { settled } = createRecordedTaskSettlement(tasks, { ...options, includeParkedRoutes: false });
  const byRoute = new Map<string, ProofRoutePriority>();
  const byTask = new Map<string, ProofRoutePriority[]>();
  const current = (inputs: readonly { taskId: string; taskDigest: string }[]) =>
    inputs.every(input => versions.get(input.taskId) === input.taskDigest);
  const priorities = routes.map((route, index): ProofRoutePriority => {
    const description = descriptions[index]!, target = nodes.get(route.targetTaskId), closing = nodes.get(route.closingTaskId);
    const proof = closing?.integratedCheck ?? closing?.proof;
    // Conditional projections omit reference environments. Keep their signal local
    // to a fresh check, and require a match for an explicitly requested environment.
    const conditional = description.closingStatus === 'conditional' && closing?.status === 'conditional' &&
      proof && hasTaskAcceptance(proof) && proof.conditions?.length && current(proof.conditions) &&
      (!options.environmentDigest || proof.references?.environmentDigest === options.environmentDigest) &&
      (!proof.references || current(proof.references.tasks ?? []));
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
      (!options.groups || options.groups.some(record => record.group.id === taskGroup(target.task) &&
        record.group.status === 'active' && record.turns < (record.group.maxTurns ?? Infinity)));
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
