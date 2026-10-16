import type { SolverRunState } from '../archive';
import type { ResearchOperation, ValueEstimate } from './value';
import { taskGroup, taskReferenceDependencies, taskVersion, type TaskRecord, type RouteRecord, type CooperativeAction } from '../tasks';

export type ResearchBudget = Readonly<{ maxTurns: number; remainingMs: number; aborted: boolean }>;
export type ActionPlan = Readonly<{
  operation: ResearchOperation | 'stop';
  reason: 'continue' | 'budget-exhausted' | 'no-operation' | 'direct-proof-gap' | 'repair-bridge' | 'prove-needed-lemma' | 'dependencies-checked' | 'stalled-obligation';
}>;

/** Select dependency-ready work; worker identities belong to M5. */
export function routeAllowsTask(task: TaskRecord['task'], tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  if ((task.status ?? 'active') !== 'active') return false;
  if (!groups) return true;
  const route = groups.find(record => record.group.id === taskGroup(task));
  return Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity) &&
    (route.busy ?? tasks.filter(node => node.status === 'running' && taskGroup(node.task) === route.group.id).length) < (route.group.maxConcurrent ?? 3));
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
    });
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
  const canStart = (task: TaskRecord['task']): boolean => ['research', 'sketch'].includes(task.kind) || dependenciesReady(task) ||
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
  return tasks.filter(node => node.status === 'pending' && routeAllowsTask(node.task, tasks, groups) &&
    readiness.canStart(node.task));
}

/** A simple M3 ablation: prefer ready original goals, preserving all readiness gates. */
export function goalsFirstResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  return readyResearchTasks(tasks, groups).toSorted((a, b) =>
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal'));
}

/** Unit-cost dependency depth is a scheduling heuristic, not a proof-time estimate. */
export function criticalPathResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const unfinished = new Map(tasks.filter(node => {
    if (['integrated', 'completed'].includes(node.status) || (node.task.status ?? 'active') !== 'active') return false;
    const route = groups?.find(record => record.group.id === taskGroup(node.task));
    return !groups || Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity));
  }).map(node => [node.task.id, node]));
  const consumers = new Map<string, string[]>();
  for (const node of unfinished.values()) for (const id of node.task.dependsOn) {
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
  return ready.toSorted((a, b) => {
    const left = priority(a.task.id), right = priority(b.task.id);
    return right.depth - left.depth || right.goals.size - left.goals.size;
  });
}

/** Reconnect checked helpers to unfinished original goals; ranks are facts, not success estimates. */
export function continuationResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const active = (node: TaskRecord) => {
    if ((node.task.status ?? 'active') !== 'active') return false;
    const route = groups?.find(record => record.group.id === taskGroup(node.task));
    return !groups || Boolean(route && route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity));
  };
  const mainPath = new Set<string>();
  const visit = (id: string) => {
    if (mainPath.has(id)) return;
    const node = nodes.get(id);
    if (!node || !active(node)) return;
    mainPath.add(id);
    for (const dependency of node.task.dependsOn) visit(dependency);
  };
  for (const node of tasks) if (node.task.kind === 'goal' && !['integrated', 'completed'].includes(node.status)) visit(node.task.id);
  const checked = (node: TaskRecord | undefined) => Boolean(node?.status === 'integrated' && node.integratedCheck?.passed &&
    node.integratedCheck.taskDigest === taskVersion(node.task) && !node.integratedCheck.conditions?.length);
  const ready = criticalPathResearchTasks(tasks, groups), readiness = taskReadiness(tasks);
  const continuing = new Set(ready.filter(node => mainPath.has(node.task.id) && ['goal', 'lemma'].includes(node.task.kind) &&
    readiness.dependenciesReady(node.task) && node.task.dependsOn.some(id => checked(nodes.get(id)))).map(node => node.task.id));
  const ranked = ready.toSorted((a, b) =>
    Number(continuing.has(b.task.id)) - Number(continuing.has(a.task.id)) ||
    Number(mainPath.has(b.task.id)) - Number(mainPath.has(a.task.id)) ||
    Number(b.task.kind === 'goal') - Number(a.task.kind === 'goal'));
  // With three proof slots, keep two on the main path and offer the third to another route.
  // Running assignments are reserved synchronously, so repeated selections observe this slot.
  const running = tasks.filter(node => node.status === 'running');
  if (running.filter(node => mainPath.has(node.task.id)).length >= 2 &&
      !running.some(node => !mainPath.has(node.task.id))) {
    const exploration = ranked.filter(node => !mainPath.has(node.task.id)).toSorted((a, b) => a.attempts - b.attempts)[0];
    if (exploration) return [exploration, ...ranked.filter(node => node !== exploration)];
  }
  return ranked;
}

/** Future progress differs from immediate readiness: typed pending premises can still be proved. */
export function researchCanAdvance(tasks: readonly TaskRecord[], groups: readonly RouteRecord[] | undefined,
  liveWorkers: ReadonlySet<string>): boolean {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const memo = new Map<string, boolean>();
  const visit = (id: string): boolean => {
    if (memo.has(id)) return memo.get(id)!;
    memo.set(id, false);
    const node = nodes.get(id);
    if (!node || node.status === 'blocked') return false;
    if (['integrated', 'completed', 'delivered', 'running'].includes(node.status)) {
      memo.set(id, true); return true;
    }
    if (node.status !== 'conditional' && ((node.task.ownerId && !liveWorkers.has(node.task.ownerId)) ||
        (node.assignment && !liveWorkers.has(node.assignment.workerId)) || !routeAllowsTask(node.task, tasks, groups))) return false;
    const ready = node.task.dependsOn.every(visit);
    memo.set(id, ready);
    return ready;
  };
  return tasks.some(node => ['pending', 'blocked'].includes(node.status) && visit(node.task.id));
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

export function researchFailureReason(error?: string): string {
  if (/^math_(?:model_(?:authentication_failed|concurrency_limit|request_failed|request_timeout|turn_failed)|codex_transport_closed)$/u.test(error ?? '')) return error!;
  if (/authentication|unauthorized|forbidden|invalid.*api.?key|\b(?:401|403)\b/iu.test(error ?? '')) return 'math_model_authentication_failed';
  if (/Concurrency limit exceeded|rate.?limit|\b429\b/iu.test(error ?? '')) return 'math_model_concurrency_limit';
  if (/^math_codex_transport_closed(?::|$)/u.test(error ?? '')) return 'math_codex_transport_closed';
  if (/math_codex_rpc_timeout|timed?\s*out|timeout/iu.test(error ?? '')) return 'math_model_request_timeout';
  if (/stream disconnected|error sending request|connection (?:reset|closed)|ECONNRESET|ECONNREFUSED|EAI_AGAIN|fetch failed|service unavailable|temporarily unavailable|\b(?:500|502|503|504)\b/iu.test(error ?? ''))
    return 'math_model_request_failed';
  return 'math_model_turn_failed';
}

/** Advisory reporting only; categories never change Lean acceptance. */
export function researchFailureCategory(error?: string): 'network' | 'environment' | 'source' | 'proof' | 'authentication' | 'rate_limit' | 'unknown' | undefined {
  if (!error) return undefined;
  if (/math_(?:lean_toolchain|lake_packages|verifier_unavailable|runtime_|path_|trusted_source)|proof environment|dependency cache|sandbox|FUSE|mksquashfs|squashfuse/iu.test(error)) return 'environment';
  if (error === 'math_codex_provider_unreachable') return 'network';
  if (/math_(?:original_|task_source|construction_|local_module_)/u.test(error)) return 'source';
  const reason = researchFailureReason(error);
  if (reason === 'math_model_authentication_failed') return 'authentication';
  if (reason === 'math_model_concurrency_limit') return 'rate_limit';
  if (['math_model_request_failed', 'math_model_request_timeout', 'math_codex_transport_closed'].includes(reason)) return 'network';
  if (/unsolved goals|type mismatch|tactic.*failed|math_(?:proof_|task_proof_|lemma_)/iu.test(error)) return 'proof';
  return 'unknown';
}

export function planResearchRetry(error: string | undefined, attempts: number, state: Readonly<SolverRunState>,
  budget: ResearchBudget): Readonly<{ attempt: number; delayMs: number; reason: string }> | undefined {
  const reason = researchFailureReason(error);
  if (['math_model_authentication_failed', 'math_model_turn_failed'].includes(reason) || attempts >= 3 ||
    state.turns >= budget.maxTurns || budget.aborted || budget.remainingMs <= 0) return undefined;
  return { attempt: attempts + 1, delayMs: 10_000 * 2 ** attempts, reason };
}
