import { taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';
import type { ProofRoute } from './proofRoutes';

export type TaskConsumerUse = Readonly<{ kind: 'dependency' } |
  { kind: 'route-prerequisite' | 'route-closing'; routeId: string }>;
export type TaskConsumerInterface = Readonly<{
  task: CooperativeTask; taskDigest: string; status: TaskRecord['status']; uses: readonly TaskConsumerUse[];
}>;
export type TaskConsumerProjection = Readonly<{
  taskId: string; taskDigest: string; interfaces: readonly TaskConsumerInterface[];
}>;
export type TaskConsumerContext = Readonly<{
  proofRoutes?: readonly ProofRoute[];
  /** Host-scoped planning interfaces only; never execution dependencies or proof evidence. */
  consumerInterfaces?: TaskConsumerProjection;
}>;

/** Describe reverse uses without visiting consumers' prerequisites or exposing their proofs. */
export function taskConsumerInterfaces(active: CooperativeTask, tasks: readonly TaskRecord[],
  proofRoutes: readonly ProofRoute[] = []): TaskConsumerInterface[] {
  const routes = [...proofRoutes, ...tasks.flatMap(node => node.alternativeRoutes ?? [])];
  return tasks.flatMap(node => {
    if (node.task.id === active.id || (taskGroup(node.task) !== taskGroup(active) && node.task.sharing === 'group')) return [];
    const uses: TaskConsumerUse[] = node.task.dependsOn.includes(active.id) ? [{ kind: 'dependency' }] : [];
    for (const route of routes) {
      if (route.targetTaskId !== node.task.id) continue;
      const kind = route.closingTaskId === active.id ? 'route-closing' :
        route.prerequisiteTaskIds.includes(active.id) ? 'route-prerequisite' : undefined;
      if (kind && !uses.some(use => use.kind === kind && 'routeId' in use && use.routeId === route.id))
        uses.push({ kind, routeId: route.id });
    }
    return uses.length ? [{ task: node.task, taskDigest: taskVersion(node.task), status: node.status, uses }] : [];
  });
}

export function taskConsumerProjection(active: CooperativeTask, tasks: readonly TaskRecord[], proofRoutes: readonly ProofRoute[] = []): TaskConsumerProjection {
  return { taskId: active.id, taskDigest: taskVersion(active), interfaces: taskConsumerInterfaces(active, tasks, proofRoutes) };
}

export function contextTaskConsumers(active: CooperativeTask, tasks: readonly TaskRecord[], context: TaskConsumerContext = {}) {
  const projection = context.consumerInterfaces;
  if (projection && (projection.taskId !== active.id || projection.taskDigest !== taskVersion(active)))
    throw new Error(`math_context_stale_required:consumer-assignment:${active.id}`);
  return (projection?.interfaces ?? taskConsumerInterfaces(active, tasks, context.proofRoutes))
    .filter(consumer => consumer.task.id !== active.id &&
      (taskGroup(consumer.task) === taskGroup(active) || consumer.task.sharing !== 'group'));
}
