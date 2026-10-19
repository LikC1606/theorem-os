import { originalGoalTaskFocus, plannedTaskDependencyIds, taskDependenciesReady, type ActionPlan, type ResearchBudget } from './search';
import { isAdvisoryTask, isFeasibilityReview, taskGroup, taskVersion, type TaskRecord, type RouteRecord } from '../tasks';
import { hasRunningDuplicateQuestion } from '../taskQuestions';
import { createProofRoutePriority } from '../routePriority';

export type ResearchRole = 'lead' | 'researcher' | 'engineer' | 'reviewer';
export type ResearchWorker = Readonly<{ id: string; role: ResearchRole; worktree: string; ownedFiles: readonly string[] }>;
export type TeamPlan = Readonly<{ workers: readonly ResearchWorker[] }>;

export function independentFeasibilityWorker(node: TaskRecord, worker: ResearchWorker,
  tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  if (!isFeasibilityReview(node.task)) return true;
  if (worker.role === 'lead') return false;
  return node.task.dependsOn.every(id => {
    const input = tasks.find(task => task.task.id === id);
    const engineerId = input?.task.kind === 'goal'
      ? groups?.find(group => group.group.id === taskGroup(input.task))?.group.engineerId : undefined;
    return input?.assignment?.workerId !== worker.id && input?.task.ownerId !== worker.id && engineerId !== worker.id;
  });
}

function eligibleResearchTasks(ready: readonly TaskRecord[], worker: ResearchWorker, groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord[] {
  return ready.filter(node =>
    (node.task.kind !== 'goal' || !groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId ||
      groups.find(route => route.group.id === taskGroup(node.task))!.group.engineerId === worker.id) &&
    (!node.task.ownerId || node.task.ownerId === worker.id) && (!node.assignment || node.assignment.workerId === worker.id) &&
    independentFeasibilityWorker(node, worker, tasks, groups) && !hasRunningDuplicateQuestion(node, tasks));
}

/** Assign selected work by responsibility and preserve resumed ownership. */
export function assignResearchTask(ready: readonly TaskRecord[], worker: ResearchWorker, live: readonly ResearchWorker[], groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord | undefined {
  const researchers = live.some(item => item.role === 'researcher');
  const eligible = eligibleResearchTasks(ready, worker, groups, tasks);
  if (worker.role === 'researcher') return eligible.find(node => node.task.kind !== 'goal') ?? eligible.find(node => node.task.kind === 'goal');
  if (worker.role === 'engineer') return (researchers ? eligible.find(node => node.task.kind === 'goal') : undefined) ?? eligible[0];
  return undefined;
}

/** Share ranked work, reserving a final available slot for independent work when the main frontier is occupied. */
export function assignSharedResearchTask(ready: readonly TaskRecord[], worker: ResearchWorker, live: readonly ResearchWorker[], groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord | undefined {
  if (!['researcher', 'engineer'].includes(worker.role)) return;
  const eligible = eligibleResearchTasks(ready, worker, groups, tasks), first = eligible[0];
  if (!first || eligible.length === 1) return first;
  if (first.task.kind === 'goal' || !first.attempts && (isFeasibilityReview(first.task) ||
      first.task.conditional && !isAdvisoryTask(first.task))) return first;
  const proofWorkers = new Set(live.filter(peer => ['researcher', 'engineer'].includes(peer.role)).map(peer => peer.id));
  const running = tasks.filter(node => node.status === 'running' && node.assignment &&
    node.assignment.taskId === node.task.id && node.assignment.taskDigest === taskVersion(node.task) &&
    proofWorkers.has(node.assignment.workerId));
  if (!running.length) return first;
  const occupied = new Set(running.map(node => node.assignment!.workerId));
  const group = groups?.find(route => route.group.id === taskGroup(first.task));
  const groupBusy = group?.busy ?? new Set(running.filter(node => taskGroup(node.task) === taskGroup(first.task))
    .map(node => node.assignment!.workerId)).size;
  const lastSlot = proofWorkers.size - occupied.size === 1;
  const lastGroupSlot = group && (group.group.maxConcurrent ?? 3) - groupBusy === 1;
  if (!lastSlot && !lastGroupSlot) return first;
  const checkedInput = (id: string) => {
    const input = tasks.find(node => node.task.id === id);
    return input?.status === 'integrated' && input.integratedCheck?.passed &&
      input.integratedCheck.taskDigest === taskVersion(input.task) && !input.integratedCheck.conditions?.length;
  };
  if (first.task.type && taskDependenciesReady(first.task, tasks) &&
      plannedTaskDependencyIds(first, tasks).some(checkedInput)) return first;
  const focus = originalGoalTaskFocus(tasks, groups), preferred = focus.preferred.support;
  if (!preferred.has(first.task.id) || running.some(node => !preferred.has(node.task.id))) return first;
  const priority = createProofRoutePriority(tasks, { groups });
  return eligible.filter(node => !preferred.has(node.task.id)).toSorted((a, b) =>
    Number(focus.support.has(b.task.id)) - Number(focus.support.has(a.task.id)) ||
    priority.compareTasks(a, b) || a.attempts - b.attempts)[0] ?? first;
}

export function researchWorkers(worktree: string, ownedFiles: readonly string[], count: number): ResearchWorker[] {
  return Array.from({ length: count }, (_, index) => ({
    id: index === 0 ? 'solver' : index === count - 1 ? 'engineer' : `researcher-${index}`,
    role: index === 0 ? 'lead' : index === count - 1 ? 'engineer' : 'researcher',
    worktree: index === 0 ? worktree : `${worktree}-${index + 1}`, ownedFiles,
  }));
}

/** Reviewers inspect fixed work independently of its producer. */
export function assignResearchReviewer(live: readonly ResearchWorker[], producerId?: string): ResearchWorker | undefined {
  const eligible = live.filter(worker => worker.role !== 'lead' && worker.id !== producerId);
  return eligible.find(worker => worker.role === 'reviewer') ?? eligible.find(worker => worker.role === 'researcher') ?? eligible[0];
}

/** M5 supplies isolated role slots under the same host budget. Idle researchers can review fixed deliveries. */
export function organizeResearch(action: ActionPlan, workers: readonly ResearchWorker[], budget: ResearchBudget): TeamPlan {
  if (action.operation === 'stop' || !workers.length || budget.aborted || budget.remainingMs <= 0)
    throw new Error('math_solver_worker_unavailable');
  return { workers };
}
