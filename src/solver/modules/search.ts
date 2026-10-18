import type { SolverRunState } from '../archive';
import type { MathAgentFailureDiagnostic } from '../../runtime/codexSession';
import type { ResearchOperation, ValueEstimate } from './value';
import { proofRouteReady, type ProofRoute } from '../proofRoutes';
import { createRecordedTaskSettlement } from '../progress';
import { createProofRoutePriority } from '../routePriority';
import { hasTaskAcceptance, isAdvisoryTask, isFeasibilityReview, isFinalCandidateReview, taskGroup, taskReferenceDependencies, taskVersion,
  type TaskRecord, type RouteRecord, type CooperativeAction } from '../tasks';

export type ResearchBudget = Readonly<{ maxTurns: number; remainingMs: number; aborted: boolean }>;
export type ActionPlan = Readonly<{
  operation: ResearchOperation | 'stop';
  reason: 'continue' | 'budget-exhausted' | 'no-operation' | 'direct-proof-gap' | 'repair-bridge' | 'prove-needed-lemma' | 'dependencies-checked' | 'stalled-obligation';
}>;

/** Select dependency-ready work; worker identities belong to M5. */
export function routeAllowsTask(task: TaskRecord['task'], tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  if ((task.status ?? 'active') !== 'active') return false;
  if (tasks.find(node => node.task.id === task.id)?.routeParking?.length) return false;
  const node = tasks.find(node => node.task.id === task.id);
  if (node?.alternativeRoutes?.length && node.alternativeRoutes.every(route => node.parkedRoutes?.[route.id]?.length)) return false;
  if (!groups) return true;
  const route = groups.find(record => record.group.id === taskGroup(task));
  return Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity) &&
    (route.busy ?? tasks.filter(node => node.status === 'running' && taskGroup(node.task) === route.group.id).length) < (route.group.maxConcurrent ?? 3));
}

/** Advisory final review still needs a complete, freshly accepted original candidate. */
export function finalCandidateReviewReady(tasks: readonly TaskRecord[]): boolean {
  const goals = tasks.filter(node => node.task.kind === 'goal');
  return goals.length > 0 && goals.every(node => {
    const proof = node.integratedCheck;
    return node.status === 'integrated' && proof?.passed && hasTaskAcceptance(proof) &&
      proof.taskDigest === taskVersion(node.task) && !proof.conditions?.length;
  });
}

/** Select one OR branch; ordinary dependsOn remains an AND requirement. */
export function selectedTaskRoute(node: TaskRecord, tasks: readonly TaskRecord[],
  priority?: ReturnType<typeof createProofRoutePriority>): ProofRoute | undefined {
  if (!node.alternativeRoutes?.length) return;
  const assigned = node.alternativeRoutes?.find(route => route.id === node.assignment?.routeId);
  // An active proof or delivery keeps its mathematical inputs. A pending draft
  // may resume on another freshly checked branch when its old inputs fail.
  if (assigned && node.status !== 'pending') return assigned;
  const routes = node.alternativeRoutes?.filter(route => !node.parkedRoutes?.[route.id]?.length);
  const ready = routes?.filter(route => proofRouteReady(route, tasks));
  const compare = (priority ?? createProofRoutePriority(tasks)).compareRoutes;
  const ranked = routes?.toSorted((a, b) => compare(a, b) ||
    Number(b.id === node.assignment?.routeId) - Number(a.id === node.assignment?.routeId));
  return ready?.find(route => route.id === node.assignment?.routeId) ?? ready?.[0] ?? ranked?.[0];
}
export function plannedTaskDependencyIds(node: TaskRecord, tasks: readonly TaskRecord[]): readonly string[] {
  const route = selectedTaskRoute(node, tasks);
  return route ? [...new Set([...node.task.dependsOn, ...route.prerequisiteTaskIds, route.closingTaskId])] : node.task.dependsOn;
}

/** Memoization lasts only for this selection; mutable task state never enters a global cache. */
function taskReadiness(tasks: readonly TaskRecord[]) {
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
    const references = node?.task === task ? taskReferenceDependencies(node) : undefined;
    const dependencies = references ?? task.dependsOn.map(taskId => ({ taskId }));
    const ready = dependencies.every(reference => {
      const dependency = nodes.get(reference.taskId);
      return Boolean(dependency && (!('taskDigest' in reference) || reference.taskDigest === version(dependency.task)) &&
        ['integrated', 'completed'].includes(dependency.status) && dependenciesReady(dependency.task));
    }) && (!node?.alternativeRoutes?.length || Boolean(references) || node.status === 'integrated' ||
      node.alternativeRoutes.some(route => !node.parkedRoutes?.[route.id]?.length && proofRouteReady(route, tasks)));
    checked.set(task, ready);
    return ready;
  };
  const dependencyAvailable = (id: string): boolean => {
    if (available.has(id)) return available.get(id)!;
    available.set(id, false);
    const dependency = nodes.get(id);
    const ready = Boolean(dependency && (['integrated', 'completed'].includes(dependency.status) ||
      (dependency.task.kind === 'lemma' && dependency.task.type)) && dependency.task.dependsOn.every(dependencyAvailable));
    available.set(id, ready);
    return ready;
  };
  const canStart = (task: TaskRecord['task']): boolean => nodes.get(task.id)?.alternativeRoutes?.length &&
    !nodes.get(task.id)!.alternativeRoutes!.some(route => !nodes.get(task.id)!.parkedRoutes?.[route.id]?.length && proofRouteReady(route, tasks)) ? false : isFinalCandidateReview(task)
    ? finalCandidateReviewReady(tasks) && dependenciesReady(task)
    : ['research', 'sketch'].includes(task.kind) || dependenciesReady(task) ||
      Boolean(task.conditional && task.dependsOn.every(dependencyAvailable));
  return { dependenciesReady, canStart };
}

export function taskDependenciesReady(task: TaskRecord['task'], tasks: readonly TaskRecord[]): boolean {
  return taskReadiness(tasks).dependenciesReady(task);
}

/** Fixed lemma statements can be assumed while constructing a conditional parent. */
export function taskCanStart(task: TaskRecord['task'], tasks: readonly TaskRecord[]): boolean {
  return taskReadiness(tasks).canStart(task);
}

export function readyResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const readiness = taskReadiness(tasks);
  const priority = createProofRoutePriority(tasks, { groups });
  const checked = new Set(tasks.filter(node => node.status === 'integrated' && node.integratedCheck?.passed &&
    node.integratedCheck.taskDigest === taskVersion(node.task) && !node.integratedCheck.conditions?.length).map(node => node.task.id));
  const groupRecords = groups && new Map(groups.map(record => [record.group.id, record]));
  const consumed = new Set(tasks.filter(node => {
    if (isAdvisoryTask(node.task) || node.status === 'integrated' || (node.task.status ?? 'active') !== 'active' ||
      node.routeParking?.length || node.alternativeRoutes?.length &&
      node.alternativeRoutes.every(route => node.parkedRoutes?.[route.id]?.length)) return false;
    const group = groupRecords?.get(taskGroup(node.task));
    return !groupRecords || Boolean(group && group.group.status === 'active' && group.turns < (group.group.maxTurns ?? Infinity));
  }).flatMap(node => [...node.task.dependsOn, ...(node.alternativeRoutes?.filter(route =>
    !node.parkedRoutes?.[route.id]?.length).flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? [])]));
  const rank = (node: TaskRecord) => isAdvisoryTask(node.task) || !readiness.dependenciesReady(node.task) ? 0 :
    node.task.kind === 'goal' ? 2 : consumed.has(node.task.id) && node.task.dependsOn.some(id => checked.has(id)) ? 1 : 0;
  const ready = tasks.filter(node => node.status === 'pending' && routeAllowsTask(node.task, tasks, groups) && readiness.canStart(node.task));
  return prioritizeEarlyRouteChecks(ready.toSorted((a, b) => rank(b) - rank(a) || priority.compareTasks(a, b)), tasks);
}

/** Offer one fresh route check before investing in its still-unproved inputs. */
function prioritizeEarlyRouteChecks(ready: TaskRecord[], tasks: readonly TaskRecord[]): TaskRecord[] {
  if (tasks.some(node => node.status === 'running' && (isFeasibilityReview(node.task) ||
      node.task.conditional && !node.proof))) return ready;
  const review = ready.find(node => !node.attempts && isFeasibilityReview(node.task));
  const bridge = ready.find(node => !node.attempts && node.task.conditional && !isAdvisoryTask(node.task) &&
    node.task.dependsOn.some(id => tasks.some(input => input.task.id === id &&
      input.task.kind === 'lemma' && input.status !== 'integrated')) &&
    (node.task.kind === 'goal' || tasks.some(consumer => consumer.task.dependsOn.includes(node.task.id) ||
      consumer.alternativeRoutes?.some(route => route.closingTaskId === node.task.id))));
  const check = review ?? bridge;
  if (!check) return ready;
  const readiness = taskReadiness(tasks);
  const consuming = ready.slice(0, ready.indexOf(check)).filter(node => !isAdvisoryTask(node.task) &&
    readiness.dependenciesReady(node.task) && (node.task.kind === 'goal' || node.task.dependsOn.some(id => {
      const input = tasks.find(candidate => candidate.task.id === id);
      return input?.status === 'integrated' && input.integratedCheck?.passed &&
        input.integratedCheck.taskDigest === taskVersion(input.task) && !input.integratedCheck.conditions?.length;
    })));
  return [...consuming, check, ...ready.filter(node => node !== check && !consuming.includes(node))];
}

/** A simple M3 ablation: prefer ready original goals, preserving all readiness gates. */
export function goalsFirstResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  return prioritizeEarlyRouteChecks(readyResearchTasks(tasks, groups).toSorted((a, b) =>
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal')), tasks);
}

/** Unit-cost dependency depth is a scheduling heuristic, not a proof-time estimate. */
export function criticalPathResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const unfinished = new Map(tasks.filter(node => {
    if (['integrated', 'completed'].includes(node.status) || (node.task.status ?? 'active') !== 'active') return false;
    const route = groups?.find(record => record.group.id === taskGroup(node.task));
    return !groups || Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity));
  }).map(node => [node.task.id, node]));
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
  }), tasks);
}

type GoalTaskFocus = Readonly<{
  proofPath: ReadonlySet<string>; frontier: ReadonlySet<string>;
  targetedResearch: ReadonlySet<string>; support: ReadonlySet<string>;
}>;
export type OriginalGoalTaskFocus = GoalTaskFocus & Readonly<{ preferred: GoalTaskFocus }>;

function collectOriginalGoalTaskFocus(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[],
  priority?: ReturnType<typeof createProofRoutePriority>): GoalTaskFocus {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const active = (node: TaskRecord) => {
    if ((node.task.status ?? 'active') !== 'active') return false;
    const route = groups?.find(record => record.group.id === taskGroup(node.task));
    return !groups || Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity));
  };
  const { settled } = createRecordedTaskSettlement(tasks, { includeParkedRoutes: false });
  const routes = (node: TaskRecord) => {
    const open = node.alternativeRoutes?.filter(route => !node.parkedRoutes?.[route.id]?.length) ?? [];
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
  const visited = new Set<string>();
  const visitFrontier = (id: string) => {
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
    if (open.length) open.forEach(visitFrontier);
    else frontier.add(id);
  };
  for (const node of tasks) if (node.task.kind === 'goal' && active(node) && !settled(node)) {
    visitPath(node.task.id); visitFrontier(node.task.id);
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
  return { proofPath, frontier, targetedResearch, support };
}

/** Preserve every mathematical frontier, with a separate evidence-ranked focus for allocation. */
export function originalGoalTaskFocus(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): OriginalGoalTaskFocus {
  const full = collectOriginalGoalTaskFocus(tasks, groups);
  return { ...full, preferred: tasks.some(node => node.alternativeRoutes?.length)
    ? collectOriginalGoalTaskFocus(tasks, groups, createProofRoutePriority(tasks, { groups })) : full };
}

/** Reconnect checked helpers to unfinished original goals; ranks are facts, not success estimates. */
export function continuationResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const focus = originalGoalTaskFocus(tasks, groups);
  const preferred = focus.preferred, priority = createProofRoutePriority(tasks, { groups });
  const checked = (node: TaskRecord | undefined) => Boolean(node?.status === 'integrated' && node.integratedCheck?.passed &&
    node.integratedCheck.taskDigest === taskVersion(node.task) && !node.integratedCheck.conditions?.length);
  const ready = criticalPathResearchTasks(tasks, groups), readiness = taskReadiness(tasks);
  const unconditional = (node: TaskRecord) => ['goal', 'lemma'].includes(node.task.kind) && readiness.dependenciesReady(node.task);
  const continuing = new Set(ready.filter(node => focus.proofPath.has(node.task.id) && unconditional(node) &&
    plannedTaskDependencyIds(node, tasks).some(id => checked(nodes.get(id)))).map(node => node.task.id));
  const rank = (node: TaskRecord) => node.task.kind === 'goal' && unconditional(node) ? 6 : continuing.has(node.task.id) ? 5 :
    preferred.proofPath.has(node.task.id) && unconditional(node) ? 4 :
    preferred.support.has(node.task.id) && unconditional(node) ? 3 : preferred.targetedResearch.has(node.task.id) ? 2 :
      focus.proofPath.has(node.task.id) || focus.targetedResearch.has(node.task.id) ? 1 : 0;
  const ranked = ready.toSorted((a, b) =>
    rank(b) - rank(a) ||
    Number(continuing.has(b.task.id)) - Number(continuing.has(a.task.id)) ||
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal') || priority.compareTasks(a, b));
  // Explore with a spare slot after ready original goals and checked-input consumers.
  // Running assignments are reserved synchronously, so repeated selections observe this slot.
  const running = tasks.filter(node => node.status === 'running');
  if (running.filter(node => preferred.support.has(node.task.id)).length >= 2 &&
      !running.some(node => !preferred.support.has(node.task.id))) {
    const exploration = ranked.filter(node => !preferred.support.has(node.task.id))
      .toSorted((a, b) => Number(focus.support.has(b.task.id)) - Number(focus.support.has(a.task.id)) ||
        priority.compareTasks(a, b) || a.attempts - b.attempts)[0];
    if (exploration) {
      const consuming = ranked.filter(node => unconditional(node) &&
        (node.task.kind === 'goal' || continuing.has(node.task.id)));
      return prioritizeEarlyRouteChecks([...consuming, exploration,
        ...ranked.filter(node => node !== exploration && !consuming.includes(node))], tasks);
    }
  }
  return prioritizeEarlyRouteChecks(ranked, tasks);
}

/** Candidate roots may be scoped; their prerequisites still use the complete task graph. */
export function researchCanAdvance(tasks: readonly TaskRecord[], groups: readonly RouteRecord[] | undefined,
  liveWorkers: ReadonlySet<string>, canAssign?: (node: TaskRecord) => boolean, candidateIds?: ReadonlySet<string>): boolean {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const memo = new Map<string, boolean>();
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
    const ready = (isAdvisoryTask(node.task) || node.task.dependsOn.every(visit)) && (!node.alternativeRoutes?.length ||
      node.alternativeRoutes.some(route => !node.parkedRoutes?.[route.id]?.length && [...route.prerequisiteTaskIds, route.closingTaskId].every(visit)));
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
      assignment.task.conditional ? 'bridge' : assignment.task.dependsOn.length ? 'integrate-lemma' : 'direct';
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
  if (/^math_(?:model_(?:authentication_failed|concurrency_limit|request_failed|request_timeout|tool_failed|turn_failed)|codex_transport_closed)$/u.test(error ?? '')) return error!;
  if (/\b(?:invalid|failed|missing|expired)\s+authentication\b|\bauthentication\s+(?:failed|failure|error|required)\b|\bunauthenticated\b|\bunauthorized\b|\b(?:invalid|incorrect|missing|expired|revoked)\s+(?:api[ _-]?key|access[ _-]?token|refresh[ _-]?token)\b|\bHTTP(?:\s+status)?\s*[:=]?\s*(?:401|403)\b|\bstatus(?:\s+code)?\s*[:=]?\s*(?:401|403)\b|\b(?:401\s+unauthorized|403\s+forbidden)\b/iu.test(error ?? '')) return 'math_model_authentication_failed';
  if (/Concurrency limit exceeded|rate.?limit|\b429\b/iu.test(error ?? '')) return 'math_model_concurrency_limit';
  if (/^math_codex_transport_closed(?::|$)/u.test(error ?? '')) return 'math_codex_transport_closed';
  if (/math_codex_rpc_timeout|timed?\s*out|timeout/iu.test(error ?? '')) return 'math_model_request_timeout';
  if (/stream disconnected|error sending request|connection (?:reset|closed)|ECONNRESET|ECONNREFUSED|EAI_AGAIN|fetch failed|service unavailable|temporarily unavailable|\b(?:500|502|503|504)\b/iu.test(error ?? ''))
    return 'math_model_request_failed';
  if (/(?:error parsing|failed to (?:parse|deserialize)) (?:function|tool) (?:call|arguments)|(?:function|tool) (?:call|execution|response)\b[^\n]{0,120}\b(?:interrupted|cancelled|canceled|invalid JSON)\b/iu.test(error ?? ''))
    return 'math_model_tool_failed';
  return 'math_model_turn_failed';
}

/** Unwrap a turn wrapper without letting a transport cause override a host integrity error. */
export function researchFailureDetail(error: unknown, sessionError?: string,
  diagnostic?: MathAgentFailureDiagnostic): string | undefined {
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
  const structured = structuredResearchFailure(diagnostic);
  if (structured) return structured;
  return messages.find(message => researchFailureReason(message) !== 'math_model_turn_failed') ?? first;
}

export const recoverableResearchFailure = (error?: string): boolean =>
  ['math_model_concurrency_limit', 'math_model_request_failed', 'math_model_request_timeout',
    'math_model_tool_failed', 'math_codex_transport_closed'].includes(researchFailureReason(error));

/** Advisory reporting only; categories never change Lean acceptance. */
export function researchFailureCategory(error?: string): 'network' | 'environment' | 'source' | 'proof' | 'authentication' | 'rate_limit' | 'unknown' | undefined {
  if (!error) return undefined;
  if (/math_(?:lean_toolchain|lake_packages|verifier_unavailable|runtime_|path_|trusted_source)|proof environment|dependency cache|sandbox|FUSE|mksquashfs|squashfuse/iu.test(error)) return 'environment';
  if (error === 'math_codex_provider_unreachable') return 'network';
  if (/math_(?:original_|task_source|construction_|local_module_)/u.test(error)) return 'source';
  const reason = researchFailureReason(error);
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
