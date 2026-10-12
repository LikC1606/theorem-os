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

export function taskDependenciesReady(task: TaskRecord['task'], tasks: readonly TaskRecord[]): boolean {
  const node = tasks.find(node => node.task === task);
  const references = node && taskReferenceDependencies(node);
  const dependencies = references?.map(reference => reference.taskId) ?? task.dependsOn;
  return dependencies.every(id => {
    const dependency = tasks.find(node => node.task.id === id);
    return dependency && (!references || references.find(reference => reference.taskId === id)!.taskDigest === taskVersion(dependency.task)) &&
      ['integrated', 'completed'].includes(dependency.status) && taskDependenciesReady(dependency.task, tasks);
  });
}

/** Fixed lemma statements can be assumed while constructing a conditional parent. */
export function taskCanStart(task: TaskRecord['task'], tasks: readonly TaskRecord[]): boolean {
  if (['research', 'sketch'].includes(task.kind) || taskDependenciesReady(task, tasks)) return true;
  if (!task.conditional) return false;
  const available = (id: string): boolean => {
    const dependency = tasks.find(node => node.task.id === id);
    return Boolean(dependency && (['integrated', 'completed'].includes(dependency.status) ||
      (dependency.task.kind === 'lemma' && dependency.task.type)) && dependency.task.dependsOn.every(available));
  };
  return task.dependsOn.every(available);
}

export function readyResearchTasks(tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): TaskRecord[] {
  return tasks.filter(node => node.status === 'pending' && routeAllowsTask(node.task, tasks, groups) &&
    taskCanStart(node.task, tasks));
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

export function planResearchRetry(error: string | undefined, attempts: number, state: Readonly<SolverRunState>,
  budget: ResearchBudget): Readonly<{ attempt: number; delayMs: number }> | undefined {
  if (!error || !/\bConcurrency limit exceeded\b/iu.test(error) || attempts >= 3 ||
    state.turns >= budget.maxTurns || budget.aborted || budget.remainingMs <= 0) return undefined;
  return { attempt: attempts + 1, delayMs: 10_000 * 2 ** attempts };
}
