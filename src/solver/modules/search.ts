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
  if (/authentication|unauthorized|forbidden|invalid.*api.?key|\b(?:401|403)\b/iu.test(error ?? '')) return 'math_model_authentication_failed';
  if (/Concurrency limit exceeded|rate.?limit|\b429\b/iu.test(error ?? '')) return 'math_model_concurrency_limit';
  if (/^math_codex_transport_closed(?::|$)/u.test(error ?? '')) return 'math_codex_transport_closed';
  if (/math_codex_rpc_timeout|timed?\s*out|timeout/iu.test(error ?? '')) return 'math_model_request_timeout';
  if (/stream disconnected|error sending request|connection (?:reset|closed)|ECONNRESET|ECONNREFUSED|EAI_AGAIN|fetch failed|service unavailable|temporarily unavailable|\b(?:500|502|503|504)\b/iu.test(error ?? ''))
    return 'math_model_request_failed';
  return 'math_model_turn_failed';
}

export function planResearchRetry(error: string | undefined, attempts: number, state: Readonly<SolverRunState>,
  budget: ResearchBudget): Readonly<{ attempt: number; delayMs: number; reason: string }> | undefined {
  const reason = researchFailureReason(error);
  if (['math_model_authentication_failed', 'math_model_turn_failed'].includes(reason) || attempts >= 3 ||
    state.turns >= budget.maxTurns || budget.aborted || budget.remainingMs <= 0) return undefined;
  return { attempt: attempts + 1, delayMs: 10_000 * 2 ** attempts, reason };
}
