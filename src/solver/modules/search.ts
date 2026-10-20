import type { SolverRunState } from '../archive';
import type { MathAgentFailureDiagnostic } from '../../runtime/codexSession';
import type { ModelRequestStopReason } from '../../runtime/modelRequest';
import { canonicalMathJson, mathDigest } from '../../math/mathRuntimeIo';
import type { ResearchOperation, ValueEstimate } from './value';
import { proofRouteReady, type ProofRoute } from '../proofRoutes';
import { createRecordedTaskSettlement } from '../progress';
import { createProofRoutePriority } from '../routePriority';
import { automaticTaskConnection, freshTaskConnection } from '../taskConnections';
import { primaryApplicationConsumer, primaryOwnedGoal } from '../taskConsumers';
import { allRoutesParked, checkedUnconditionally, freshlyAccepted, groupOpen, isAdvisoryTask, isFeasibilityReview, isFinalCandidateReview,
  openRoutes, taskGroup, taskReferenceDependencies, taskVersion, type TaskRecord, type RouteRecord, type CooperativeAction } from '../tasks';

export type ResearchBudget = Readonly<{ maxTurns: number; remainingMs: number; aborted: boolean }>;
export type ActionPlan = Readonly<{
  operation: ResearchOperation | 'stop';
  reason: 'continue' | 'budget-exhausted' | 'no-operation' | 'direct-proof-gap' | 'repair-bridge' | 'prove-needed-lemma' | 'dependencies-checked' | 'stalled-obligation';
}>;

/** Select dependency-ready work; worker identities belong to M5. */
export function routeAllowsTask(task: TaskRecord['task'], tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  if ((task.status ?? 'active') !== 'active') return false;
  const node = tasks.find(node => node.task.id === task.id);
  if (node && (node.pendingValidation || node.routeParking?.length || allRoutesParked(node))) return false;
  if (!groups) return true;
  const route = groups.find(record => record.group.id === taskGroup(task));
  return groupOpen(route) &&
    (route.busy ?? tasks.filter(node => node.status === 'running' && taskGroup(node.task) === route.group.id).length) < (route.group.maxConcurrent ?? 3);
}

/** Advisory final review still needs a complete, freshly accepted original candidate. */
export function finalCandidateReviewReady(tasks: readonly TaskRecord[]): boolean {
  const goals = tasks.filter(node => node.task.kind === 'goal');
  return goals.length > 0 && goals.every(node => !node.pendingValidation && freshlyAccepted(node, taskVersion(node.task)));
}

function dispatchRouteReady(route: ProofRoute, tasks: readonly TaskRecord[]) {
  if (!proofRouteReady(route, tasks)) return false;
  const nodes = new Map(tasks.map(node => [node.task.id, node])), visited = new Set<string>();
  const available = (id: string): boolean => {
    if (visited.has(id)) return true;
    visited.add(id);
    const node = nodes.get(id);
    return Boolean(node && !node.pendingValidation &&
      (taskReferenceDependencies(node)?.map(reference => reference.taskId) ?? node.task.dependsOn).every(available));
  };
  return [route.closingTaskId, ...route.prerequisiteTaskIds].every(available);
}

/** Select one OR branch; ordinary dependsOn remains an AND requirement. */
export function selectedTaskRoute(node: TaskRecord, tasks: readonly TaskRecord[],
  priority?: ReturnType<typeof createProofRoutePriority>): ProofRoute | undefined {
  if (!node.alternativeRoutes?.length) return;
  const assigned = node.alternativeRoutes?.find(route => route.id === node.assignment?.routeId);
  // An active proof or delivery keeps its mathematical inputs. A pending draft
  // may resume on another freshly checked branch when its old inputs fail.
  if (assigned && node.status !== 'pending') return assigned;
  const routes = openRoutes(node), ready = routes.filter(route => dispatchRouteReady(route, tasks));
  const compare = (priority ?? createProofRoutePriority(tasks)).compareRoutes;
  const ranked = routes.toSorted((a, b) => compare(a, b) ||
    Number(b.id === node.assignment?.routeId) - Number(a.id === node.assignment?.routeId));
  return ready.find(route => route.id === node.assignment?.routeId) ?? ready[0] ?? ranked[0];
}
export function plannedTaskDependencyIds(node: TaskRecord, tasks: readonly TaskRecord[]): readonly string[] {
  const route = selectedTaskRoute(node, tasks);
  return route ? [...new Set([...node.task.dependsOn, ...route.prerequisiteTaskIds, route.closingTaskId])] : node.task.dependsOn;
}

/** Memoization lasts only for this selection; mutable task state never enters a global cache. */
function taskReadiness(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]) {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const checked = new Map<TaskRecord['task'], boolean>(), available = new Map<string, boolean>();
  const versions = new Map<TaskRecord['task'], string>();
  const version = (task: TaskRecord['task']) => {
    if (!versions.has(task)) versions.set(task, taskVersion(task));
    return versions.get(task)!;
  };
  const dependenciesReady = (task: TaskRecord['task']): boolean => {
    if (checked.has(task)) return checked.get(task)!;
    checked.set(task, false); // Cyclic or malformed restored plans fail closed.
    const node = nodes.get(task.id);
    if (node?.pendingValidation) return false;
    const references = node?.task === task ? taskReferenceDependencies(node) : undefined;
    const dependencies = references ?? task.dependsOn.map(taskId => ({ taskId }));
    const ready = dependencies.every(reference => {
      const dependency = nodes.get(reference.taskId);
      return Boolean(dependency && (!('taskDigest' in reference) || reference.taskDigest === version(dependency.task)) &&
        ['integrated', 'completed'].includes(dependency.status) && dependenciesReady(dependency.task));
    }) && (!node?.alternativeRoutes?.length || Boolean(references) || node.status === 'integrated' ||
      openRoutes(node).some(route => dispatchRouteReady(route, tasks)));
    checked.set(task, ready);
    return ready;
  };
  const dependencyAvailable = (id: string): boolean => {
    if (available.has(id)) return available.get(id)!;
    available.set(id, false);
    const dependency = nodes.get(id);
    const ready = Boolean(dependency && !dependency.pendingValidation && (['integrated', 'completed'].includes(dependency.status) ||
      (dependency.task.kind === 'lemma' && dependency.task.type)) && dependency.task.dependsOn.every(dependencyAvailable));
    available.set(id, ready);
    return ready;
  };
  const canStart = (task: TaskRecord['task']): boolean => {
    const node = nodes.get(task.id);
    if (node?.pendingValidation || node?.alternativeRoutes?.length && !openRoutes(node).some(route => dispatchRouteReady(route, tasks))) return false;
    return isFinalCandidateReview(task) ? finalCandidateReviewReady(tasks) && dependenciesReady(task)
      : ['research', 'sketch'].includes(task.kind) || dependenciesReady(task) ||
        Boolean((task.conditional || automaticTaskConnection(task, tasks, groups)) && task.dependsOn.every(dependencyAvailable));
  };
  return { dependenciesReady, canStart };
}

export function taskDependenciesReady(task: TaskRecord['task'], tasks: readonly TaskRecord[]): boolean {
  return taskReadiness(tasks).dependenciesReady(task);
}

/** Fixed lemma statements can be assumed while constructing a conditional parent. */
export function taskCanStart(task: TaskRecord['task'], tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  return taskReadiness(tasks, groups).canStart(task);
}

export function readyResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const readiness = taskReadiness(tasks, groups);
  const priority = createProofRoutePriority(tasks, { groups });
  const checked = new Set(tasks.filter(checkedUnconditionally).map(node => node.task.id));
  const groupRecords = groups && new Map(groups.map(record => [record.group.id, record]));
  const consumed = new Set(tasks.filter(node => {
    if (isAdvisoryTask(node.task) || node.status === 'integrated' || (node.task.status ?? 'active') !== 'active' ||
      node.routeParking?.length || allRoutesParked(node)) return false;
    return !groupRecords || groupOpen(groupRecords.get(taskGroup(node.task)));
  }).flatMap(node => [...node.task.dependsOn, ...openRoutes(node).flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])]));
  const rank = (node: TaskRecord) => isAdvisoryTask(node.task) || !readiness.dependenciesReady(node.task) ? 0 :
    node.task.kind === 'goal' ? 2 : consumed.has(node.task.id) && node.task.dependsOn.some(id => checked.has(id)) ? 1 : 0;
  const ready = tasks.filter(node => node.status === 'pending' && routeAllowsTask(node.task, tasks, groups) && readiness.canStart(node.task));
  return prioritizeEarlyRouteChecks(ready.toSorted((a, b) => rank(b) - rank(a) || priority.compareTasks(a, b)), tasks, groups);
}

/** Offer one fresh route check before investing in its still-unproved inputs. */
function prioritizeEarlyRouteChecks(ready: TaskRecord[], tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  if (tasks.some(node => node.status === 'running' && (isFeasibilityReview(node.task) ||
      (node.task.conditional || node.assignment?.connectionCheck) && !node.proof))) return ready;
  const review = ready.find(node => !node.attempts && isFeasibilityReview(node.task));
  const bridge = ready.find(node => freshTaskConnection(node, tasks, groups) && !isAdvisoryTask(node.task) &&
    node.task.dependsOn.some(id => tasks.some(input => input.task.id === id &&
      input.task.kind === 'lemma' && input.status !== 'integrated')) &&
    (node.task.kind === 'goal' || tasks.some(consumer => consumer.task.dependsOn.includes(node.task.id) ||
      consumer.alternativeRoutes?.some(route => route.closingTaskId === node.task.id))));
  const check = review ?? bridge;
  if (!check) return ready;
  const readiness = taskReadiness(tasks, groups);
  const consuming = ready.slice(0, ready.indexOf(check)).filter(node => !isAdvisoryTask(node.task) &&
    readiness.dependenciesReady(node.task) && (node.task.kind === 'goal' ||
      node.task.dependsOn.some(id => checkedUnconditionally(tasks.find(candidate => candidate.task.id === id)))));
  return [...consuming, check, ...ready.filter(node => node !== check && !consuming.includes(node))];
}

/** A simple M3 ablation: prefer ready original goals, preserving all readiness gates. */
export function goalsFirstResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  return prioritizeEarlyRouteChecks(readyResearchTasks(tasks, groups).toSorted((a, b) =>
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal')), tasks, groups);
}

/** Unit-cost dependency depth is a scheduling heuristic, not a proof-time estimate. */
export function criticalPathResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const unfinished = new Map(tasks.filter(node => !['integrated', 'completed'].includes(node.status) &&
    (node.task.status ?? 'active') === 'active' && (!groups || groupOpen(groups.find(record => record.group.id === taskGroup(node.task)))))
    .map(node => [node.task.id, node]));
  const consumers = new Map<string, string[]>();
  for (const node of unfinished.values()) for (const id of [...node.task.dependsOn,
    ...(node.alternativeRoutes?.flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? [])]) {
    const list = consumers.get(id) ?? []; list.push(node.task.id); consumers.set(id, list);
  }
  type Priority = { depth: number; goals: Set<string> };
  const priorities = new Map<string, Priority>();
  const priority = (id: string): Priority => {
    const cached = priorities.get(id);
    if (cached) return cached;
    const node = unfinished.get(id);
    const result: Priority = { depth: node?.task.kind === 'goal' ? 1 : 0,
      goals: new Set(node?.task.kind === 'goal' ? [id] : []) };
    priorities.set(id, result);
    if (node) for (const consumer of consumers.get(id) ?? []) {
      const next = priority(consumer);
      if (next.depth) result.depth = Math.max(result.depth, next.depth + 1);
      for (const goal of next.goals) result.goals.add(goal);
    }
    return result;
  };
  const ready = readyResearchTasks(tasks, groups);
  for (const node of ready) priority(node.task.id);
  return prioritizeEarlyRouteChecks(ready.toSorted((a, b) => {
    const left = priority(a.task.id), right = priority(b.task.id);
    return right.depth - left.depth || right.goals.size - left.goals.size;
  }), tasks, groups);
}

type GoalTaskFocus = Readonly<{
  proofPath: ReadonlySet<string>; frontier: ReadonlySet<string>;
  frontierGoals: ReadonlyMap<string, ReadonlySet<string>>;
  targetedResearch: ReadonlySet<string>; support: ReadonlySet<string>;
}>;
export type OriginalGoalTaskFocus = GoalTaskFocus & Readonly<{ preferred: GoalTaskFocus }>;

function collectOriginalGoalTaskFocus(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[],
  priority?: ReturnType<typeof createProofRoutePriority>, environmentDigest?: string, includeParkedTasks = false): GoalTaskFocus {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const active = (node: TaskRecord) => {
    if ((node.task.status ?? 'active') !== 'active' && !primaryOwnedGoal(node) ||
        !includeParkedTasks && (node.routeParking?.length || allRoutesParked(node))) return false;
    return !groups || groupOpen(groups.find(record => record.group.id === taskGroup(node.task)));
  };
  const { settled } = createRecordedTaskSettlement(tasks, { includeParkedRoutes: false, environmentDigest });
  const routes = (node: TaskRecord) => {
    const open = openRoutes(node);
    if (!priority) return open;
    const selected = selectedTaskRoute(node, tasks, priority);
    return selected && open.some(route => route.id === selected.id) ? [selected] : [];
  };
  const inputs = (node: TaskRecord) => [...new Set([...node.task.dependsOn,
    ...routes(node).flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])])];
  const proofPath = new Set<string>(), frontier = new Set<string>();
  const visitPath = (id: string) => {
    if (proofPath.has(id)) return;
    const node = nodes.get(id);
    if (!node || !active(node)) return;
    proofPath.add(id);
    if (isAdvisoryTask(node.task) || !settled(node)) inputs(node).forEach(visitPath);
  };
  const frontierGoals = new Map<string, Set<string>>();
  const visitFrontier = (id: string, goalId: string, visited: Set<string>) => {
    if (visited.has(id)) return;
    visited.add(id);
    const node = nodes.get(id);
    if (!node || !active(node) || settled(node)) return;
    const open = node.task.dependsOn.filter(dependency => !settled(nodes.get(dependency)));
    const alternatives = routes(node);
    if (alternatives.length && !alternatives.some(route =>
      [...route.prerequisiteTaskIds, route.closingTaskId].every(dependency => settled(nodes.get(dependency)))))
      open.push(...alternatives.flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId])
        .filter(dependency => !settled(nodes.get(dependency))));
    if (open.length) open.forEach(dependency => visitFrontier(dependency, goalId, visited));
    else {
      frontier.add(id);
      const goals = frontierGoals.get(id) ?? new Set<string>();
      goals.add(goalId); frontierGoals.set(id, goals);
    }
  };
  for (const node of tasks) if (node.task.kind === 'goal' && active(node) && !settled(node)) {
    visitPath(node.task.id); visitFrontier(node.task.id, node.task.id, new Set());
  }
  const reachesFrontier = (id: string, visited = new Set<string>()): boolean => {
    if (frontier.has(id)) return true;
    if (visited.has(id)) return false;
    visited.add(id);
    const node = nodes.get(id);
    // A shared checked helper does not connect every later investigation to its old planned inputs.
    return Boolean(node && active(node) && !(!isAdvisoryTask(node.task) && settled(node)) &&
      inputs(node).some(dependency => reachesFrontier(dependency, visited)));
  };
  const targetedResearch = new Set(tasks.filter(node => isAdvisoryTask(node.task) && active(node) &&
    inputs(node).some(id => reachesFrontier(id))).map(node => node.task.id));
  const support = new Set(proofPath);
  const visitSupport = (id: string) => {
    if (support.has(id)) return;
    const node = nodes.get(id);
    if (!node || !active(node)) return;
    support.add(id);
    if (isAdvisoryTask(node.task) || !settled(node)) inputs(node).forEach(visitSupport);
  };
  targetedResearch.forEach(visitSupport);
  // Advisory application purpose must not become a proof prerequisite or authorize a paused goal.
  for (const helper of tasks) {
    const consumer = primaryApplicationConsumer(helper, tasks);
    if (!consumer || !proofPath.has(consumer.task.id) || !active(helper)) continue;
    if (isAdvisoryTask(helper.task)) targetedResearch.add(helper.task.id);
    visitSupport(helper.task.id);
  }
  return { proofPath, frontier, frontierGoals, targetedResearch, support };
}

/** Preserve every active frontier, with a separate evidence-ranked focus for allocation. */
export function originalGoalTaskFocus(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[], environmentDigest?: string,
  options: { /** Diagnose the parked obligation without reopening its proof or traversing parked OR branches. */
    includeParkedTasks?: boolean } = {}): OriginalGoalTaskFocus {
  const full = collectOriginalGoalTaskFocus(tasks, groups, undefined, environmentDigest, options.includeParkedTasks);
  return { ...full, preferred: tasks.some(node => node.alternativeRoutes?.length)
    ? collectOriginalGoalTaskFocus(tasks, groups, createProofRoutePriority(tasks, { groups, environmentDigest }),
      environmentDigest, options.includeParkedTasks) : full };
}

export function originalGoalFrontierSnapshot(focus: OriginalGoalTaskFocus) {
  const taskIds = [...focus.frontier], preferredTaskIds = [...focus.preferred.frontier];
  return { evidence: 'recorded-not-replayed' as const, count: taskIds.length,
    digest: mathDigest(canonicalMathJson(taskIds)), taskIds, preferredTaskIds };
}

/** Reconnect checked helpers to unfinished original goals; ranks are facts, not success estimates. */
export function continuationResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const focus = originalGoalTaskFocus(tasks, groups);
  const preferred = focus.preferred, priority = createProofRoutePriority(tasks, { groups });
  const ready = criticalPathResearchTasks(tasks, groups), readiness = taskReadiness(tasks, groups);
  const unconditional = (node: TaskRecord) => ['goal', 'lemma'].includes(node.task.kind) && readiness.dependenciesReady(node.task);
  const continuing = new Set(ready.filter(node => focus.proofPath.has(node.task.id) && unconditional(node) &&
    plannedTaskDependencyIds(node, tasks).some(id => checkedUnconditionally(nodes.get(id)))).map(node => node.task.id));
  const rank = (node: TaskRecord) => node.task.kind === 'goal' && unconditional(node) ? 6 : continuing.has(node.task.id) ? 5 :
    preferred.proofPath.has(node.task.id) && unconditional(node) ? 4 :
    preferred.support.has(node.task.id) && unconditional(node) ? 3 : preferred.targetedResearch.has(node.task.id) ? 2 :
      focus.proofPath.has(node.task.id) || focus.targetedResearch.has(node.task.id) ? 1 : 0;
  const ranked = ready.toSorted((a, b) =>
    rank(b) - rank(a) ||
    Number(continuing.has(b.task.id)) - Number(continuing.has(a.task.id)) ||
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal') || priority.compareTasks(a, b));
  return prioritizeEarlyRouteChecks(ranked, tasks, groups);
}

/** Candidate roots may be scoped; their prerequisites still use the complete task graph. */
export function researchCanAdvance(tasks: readonly TaskRecord[], groups: readonly RouteRecord[] | undefined,
  liveWorkers: ReadonlySet<string>, canAssign?: (node: TaskRecord) => boolean, candidateIds?: ReadonlySet<string>): boolean {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const memo = new Map<string, boolean>();
  const readiness = taskReadiness(tasks, groups);
  const visit = (id: string): boolean => {
    if (memo.has(id)) return memo.get(id)!;
    memo.set(id, false);
    const node = nodes.get(id);
    if (!node || node.status === 'blocked') return false;
    if (isFinalCandidateReview(node.task) && !finalCandidateReviewReady(tasks)) return false;
    if (node.status === 'completed' && isAdvisoryTask(node.task)) {
      const ready = node.task.dependsOn.every(visit);
      memo.set(id, ready); return ready;
    }
    if (['integrated', 'completed', 'delivered', 'running'].includes(node.status)) {
      memo.set(id, true); return true;
    }
    if (node.status !== 'conditional') {
      const engineerId = node.task.kind === 'goal'
        ? groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId : undefined;
      const owners = [node.task.ownerId, node.assignment?.workerId, engineerId].filter((id): id is string => Boolean(id));
      if (owners.some(id => !liveWorkers.has(id) || id !== owners[0]) || !routeAllowsTask(node.task, tasks, groups) ||
          (canAssign && !canAssign(node))) return false;
    }
    // Reuse future-progress traversal before checking whether assumed inputs allow an earlier start.
    const ready = (isAdvisoryTask(node.task) || node.task.dependsOn.every(visit) ||
      node.status !== 'conditional' && readiness.canStart(node.task)) && (!node.alternativeRoutes?.length ||
      openRoutes(node).some(route => [...route.prerequisiteTaskIds, route.closingTaskId].every(visit)));
    memo.set(id, ready);
    return ready;
  };
  return tasks.some(node => (!candidateIds || candidateIds.has(node.task.id)) &&
    ['pending', 'blocked'].includes(node.status) && visit(node.task.id));
}

/** M3 chooses actions; estimates never change mathematical acceptance. */
export function selectResearchAction(state: Readonly<SolverRunState>, options: readonly ResearchOperation[],
  _estimates: readonly ValueEstimate[], budget: ResearchBudget, _assignment?: CooperativeAction): ActionPlan {
  if (budget.aborted || budget.remainingMs <= 0 || state.turns >= budget.maxTurns)
    return { operation: 'stop', reason: 'budget-exhausted' };
  return options.includes('direct') ? { operation: 'direct', reason: 'continue' } :
    { operation: 'stop', reason: 'no-operation' };
}

/** A single conditional connection is checked before investing in its lemma. */
export function selectLemmaAction(state: Readonly<SolverRunState>, options: readonly ResearchOperation[],
  estimates: readonly ValueEstimate[], budget: ResearchBudget, assignment?: CooperativeAction): ActionPlan {
  const baseline = selectResearchAction(state, options, estimates, budget);
  if (baseline.operation === 'stop') return baseline;
  if (assignment) {
    const operation = assignment.kind === 'lead' ? 'decompose' : assignment.kind !== 'task' ? 'direct' :
      assignment.task.kind === 'lemma' ? 'prove-lemma' : assignment.task.kind !== 'goal' ? 'direct' :
      assignment.task.conditional || assignment.assignment.connectionCheck ? 'bridge' : assignment.task.dependsOn.length ? 'integrate-lemma' : 'direct';
    if (!options.includes(operation)) return baseline;
    return { operation, reason: operation === 'decompose' ? 'direct-proof-gap' : operation === 'bridge' ? 'repair-bridge' :
      operation === 'prove-lemma' ? 'prove-needed-lemma' : operation === 'integrate-lemma' ? 'dependencies-checked' : 'continue' };
  }
  if (!state.check || state.check.passed) return baseline;
  const research = state.lemmaResearch;
  const stalled = research?.bridge && !research.bridge.passed ? research.bridge : research?.lemma && !research.lemma.passed ? research.lemma : undefined;
  if (stalled && stalled.unchangedFailures >= 2 && options.includes('decompose'))
    return { operation: 'decompose', reason: 'stalled-obligation' };
  const operation = !research?.plan || research.error ? 'decompose' : !research.bridge?.passed ? 'bridge' :
    !research.lemma?.passed ? 'prove-lemma' : 'integrate-lemma';
  if (!options.includes(operation)) return baseline;
  const reason = operation === 'decompose' ? 'direct-proof-gap' : operation === 'bridge' ? 'repair-bridge' :
    operation === 'prove-lemma' ? 'prove-needed-lemma' : 'dependencies-checked';
  return { operation, reason };
}

function structuredResearchFailure(diagnostic?: MathAgentFailureDiagnostic): string | undefined {
  if (!diagnostic) return undefined;
  const status = diagnostic.httpStatusCode;
  if (diagnostic.code === 'unauthorized' || status === 401 || status === 403) return 'math_model_authentication_failed';
  if (diagnostic.code === 'contextWindowExceeded') return 'math_model_context_window_exceeded';
  if (['usageLimitExceeded', 'rateLimitExceeded'].includes(diagnostic.code) || status === 429) return 'math_model_concurrency_limit';
  if (status === 408) return 'math_model_request_timeout';
  if (status !== undefined && status >= 400 && status < 500) return 'math_model_turn_failed';
  if (['httpConnectionFailed', 'responseStreamConnectionFailed', 'responseStreamDisconnected',
    'responseTooManyFailedAttempts', 'flexUnavailable', 'serverOverloaded', 'internalServerError'].includes(diagnostic.code))
    return 'math_model_request_failed';
  return diagnostic.code === 'other' ? undefined : 'math_model_turn_failed';
}

export function researchFailureReason(error?: string, diagnostic?: MathAgentFailureDiagnostic): string {
  // Host integrity failures retain priority over provider classifications.
  if (/^math_(?!(?:model_|codex_))/u.test(error ?? '')) return error!;
  const structured = structuredResearchFailure(diagnostic);
  if (structured) return structured;
  if (/^math_(?:model_(?:authentication_failed|concurrency_limit|request_failed|request_timeout|request_stopped|usage_unavailable|tool_failed|turn_failed|context_window_exceeded|context_capacity_blocked)|codex_transport_closed)$/u.test(error ?? '')) return error!;
  if (/^math_model_api_key_(?:missing|environment_invalid)(?::|$)/u.test(error ?? '')) return 'math_model_authentication_failed';
  if (/\b(?:invalid|failed|missing|expired)\s+authentication\b|\bauthentication\s+(?:failed|failure|error|required)\b|\bunauthenticated\b|\bunauthorized\b|\b(?:invalid|incorrect|missing|expired|revoked)\s+(?:api[ _-]?key|access[ _-]?token|refresh[ _-]?token)\b|\bHTTP(?:\s+status)?\s*[:=]?\s*(?:401|403)\b|\bstatus(?:\s+code)?\s*[:=]?\s*(?:401|403)\b|\b(?:401\s+unauthorized|403\s+forbidden)\b/iu.test(error ?? '')) return 'math_model_authentication_failed';
  if (/Concurrency limit exceeded|rate.?limit|\b429\b/iu.test(error ?? '')) return 'math_model_concurrency_limit';
  if (/contextWindowExceeded|context (?:window|length).{0,40}(?:exceed|limit)|maximum context length/iu.test(error ?? ''))
    return 'math_model_context_window_exceeded';
  if (/^math_codex_transport_closed(?::|$)/u.test(error ?? '')) return 'math_codex_transport_closed';
  if (/math_codex_rpc_timeout|timed?\s*out|timeout/iu.test(error ?? '')) return 'math_model_request_timeout';
  if (/stream disconnected|error sending request|connection (?:reset|closed)|ECONNRESET|ECONNREFUSED|EAI_AGAIN|fetch failed|service unavailable|temporarily unavailable|\b(?:500|502|503|504)\b/iu.test(error ?? ''))
    return 'math_model_request_failed';
  if (/(?:error parsing|failed to (?:parse|deserialize)) (?:function|tool) (?:call|arguments)|(?:function|tool) (?:call|execution|response)\b[^\n]{0,120}\b(?:interrupted|cancelled|canceled|invalid JSON)\b/iu.test(error ?? ''))
    return 'math_model_tool_failed';
  return 'math_model_turn_failed';
}

/** Host integrity errors precede trusted local stops, which precede provider classifications. */
export function researchFailureDetail(error: unknown, sessionError?: string,
  diagnostic?: MathAgentFailureDiagnostic, localStop?: ModelRequestStopReason): string | undefined {
  const messages: string[] = [];
  const seen = new Set<unknown>();
  for (let current = error; current !== undefined && !seen.has(current) && seen.size < 4;) {
    seen.add(current);
    if (typeof current === 'string') { messages.push(current); break; }
    if (!(current instanceof Error)) break;
    messages.push(current.message);
    current = current.cause;
  }
  if (sessionError) messages.push(sessionError);
  const first = messages[0];
  const hostError = messages.find(message => /^math_(?!(?:model_|codex_))/u.test(message));
  if (hostError) return hostError;
  if (localStop) return localStop;
  const structured = structuredResearchFailure(diagnostic);
  if (structured) return structured;
  const authentication = messages.find(message => researchFailureReason(message) === 'math_model_authentication_failed');
  if (authentication) return authentication;
  return messages.find(message => researchFailureReason(message) !== 'math_model_turn_failed') ?? first;
}

export const recoverableResearchFailure = (error?: string): boolean =>
  ['math_model_concurrency_limit', 'math_model_request_failed', 'math_model_request_timeout',
    'math_model_tool_failed', 'math_codex_transport_closed', 'math_model_context_window_exceeded'].includes(researchFailureReason(error));

/** Advisory reporting only; categories never change Lean acceptance. */
export function researchFailureCategory(error?: string): 'network' | 'environment' | 'source' | 'proof' | 'protocol' | 'authentication' | 'rate_limit' | 'budget' | 'unknown' | undefined {
  if (!error) return undefined;
  if (/math_(?:lean_toolchain|lake_packages|verifier_unavailable|runtime_|path_|trusted_source)|proof environment|dependency cache|sandbox|FUSE|mksquashfs|squashfuse/iu.test(error)) return 'environment';
  if (error === 'math_codex_provider_unreachable') return 'network';
  if (/math_(?:original_|task_source|construction_|local_module_)/u.test(error)) return 'source';
  if (/^math_codex_rpc_failed(?::|$)|^math_(?:(?:research_|review_)?delivery_invalid(?:_json)?|response_invalid|math-result_missing_or_too_large|math-result_requires_one_block)$/u.test(error)) return 'protocol';
  const reason = researchFailureReason(error);
  if (['math_total_token_limit', 'math_model_usage_unavailable', 'math_initial_planning_limit'].includes(reason)) return 'budget';
  if (reason === 'math_model_authentication_failed') return 'authentication';
  if (reason === 'math_model_concurrency_limit') return 'rate_limit';
  if (reason === 'math_model_tool_failed') return 'environment';
  if (['math_model_request_failed', 'math_model_request_timeout', 'math_codex_transport_closed'].includes(reason)) return 'network';
  if (/unsolved goals|type mismatch|tactic.*failed|math_(?:proof_|task_proof_|lemma_)/iu.test(error)) return 'proof';
  return 'unknown';
}

export function planResearchRetry(error: string | undefined, attempts: number, state: Readonly<SolverRunState>,
  budget: ResearchBudget): Readonly<{ attempt: number; delayMs: number; reason: string }> | undefined {
  const reason = researchFailureReason(error);
  if (!recoverableResearchFailure(error) || attempts >= 3 ||
    state.turns >= budget.maxTurns || budget.aborted || budget.remainingMs <= 0) return undefined;
  return { attempt: attempts + 1, delayMs: 10_000 * 2 ** attempts, reason };
}

/** Sustained provider outages cool down unlimited runs without retiring their workers. */
export function planResearchCooldown(error: string | undefined, cycles: number, budget: ResearchBudget):
  Readonly<{ cycle: number; delayMs: number; reason: string }> | undefined {
  const reason = researchFailureReason(error);
  if (budget.maxTurns !== Infinity || budget.remainingMs !== Infinity || budget.aborted ||
      !['math_model_concurrency_limit', 'math_model_request_failed', 'math_model_request_timeout',
        'math_codex_transport_closed'].includes(reason)) return undefined;
  return { cycle: cycles + 1, delayMs: Math.min(300_000, 60_000 * 2 ** Math.min(cycles, 3)), reason };
}
