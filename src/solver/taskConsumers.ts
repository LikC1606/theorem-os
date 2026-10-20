import { taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';
import type { ProofRoute } from './proofRoutes';

export type TaskConsumerUse = Readonly<{ kind: 'dependency' } | { kind: 'primary-application'; residualGoal?: string } |
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

export const primaryOwnedGoal = (node: TaskRecord) => node.task.kind === 'goal' && node.primaryOwned === true &&
  node.task.status === 'paused';

/** An application is advisory and expires with either exact contract or its execution control. */
export function primaryApplicationConsumer(helper: TaskRecord, tasks: readonly TaskRecord[]) {
  const link = helper.application;
  if (!link || link.helperDigest !== taskVersion(helper.task) || (helper.task.status ?? 'active') !== 'active') return;
  return tasks.find(node => node.task.id === link.consumerTaskId && primaryOwnedGoal(node) &&
    taskVersion(node.task) === link.consumerDigest &&
    (taskGroup(node.task) === taskGroup(helper.task) || node.task.sharing !== 'group'));
}

/** Resolve only an explicitly selected frozen target (single-target requests have an unambiguous default). */
export function primaryHelpApplications(requests: readonly { id: string; consumer?: {
  theoremName: string; proofPath?: string; residualGoal?: string } }[], tasks: readonly TaskRecord[]) {
  const goals = tasks.filter(node => node.task.kind === 'goal');
  return requests.flatMap(request => {
    const selector = request.consumer;
    if (selector !== undefined && (!selector || typeof selector !== 'object' || typeof selector.theoremName !== 'string' ||
        (selector.proofPath !== undefined && typeof selector.proofPath !== 'string') ||
        (selector.residualGoal !== undefined && (typeof selector.residualGoal !== 'string' ||
          !selector.residualGoal.trim() || Buffer.byteLength(selector.residualGoal) > 4000))))
      throw new Error('math_help_invalid_consumer');
    const matches = selector ? goals.filter(node => node.task.theoremName === selector.theoremName &&
      (selector.proofPath === undefined || node.task.proofPath === selector.proofPath)) : goals;
    const helper = tasks.find(node => node.task.id === request.id);
    // Legacy multi-target requests can still run, but acquire no invented original-goal purpose.
    if (!selector && matches.length !== 1) return [];
    if (matches.length !== 1 || !helper || helper.task.kind === 'goal') throw new Error('math_help_select_original_consumer');
    const consumer = matches[0]!;
    if (taskGroup(consumer.task) !== taskGroup(helper.task) && consumer.task.sharing === 'group')
      throw new Error('math_help_consumer_not_shared');
    return [{ taskId: helper.task.id, application: { helperDigest: taskVersion(helper.task),
      consumerTaskId: consumer.task.id, consumerDigest: taskVersion(consumer.task),
      ...(selector?.residualGoal ? { residualGoal: selector.residualGoal } : {}) } }];
  });
}

/** Describe reverse uses without visiting consumers' prerequisites or exposing their proofs. */
export function taskConsumerInterfaces(active: CooperativeTask, tasks: readonly TaskRecord[],
  proofRoutes: readonly ProofRoute[] = []): TaskConsumerInterface[] {
  const routes = [...proofRoutes, ...tasks.flatMap(node => node.alternativeRoutes ?? [])];
  const helper = tasks.find(node => node.task.id === active.id && taskVersion(node.task) === taskVersion(active));
  const application = helper && primaryApplicationConsumer(helper, tasks);
  return tasks.flatMap(node => {
    if (node.task.id === active.id || (taskGroup(node.task) !== taskGroup(active) && node.task.sharing === 'group')) return [];
    const uses: TaskConsumerUse[] = node.task.dependsOn.includes(active.id) ? [{ kind: 'dependency' }] : [];
    if (application === node) uses.push({ kind: 'primary-application',
      ...(helper!.application!.residualGoal ? { residualGoal: helper!.application!.residualGoal } : {}) });
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
