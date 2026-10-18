import type { ActionPlan, ResearchBudget } from './search';
import { isFeasibilityReview, taskGroup, type TaskRecord, type RouteRecord } from '../tasks';

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
    independentFeasibilityWorker(node, worker, tasks, groups));
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

/** Proof workers share ranked work; explicit pins and resumed assignments still bind. */
export function assignSharedResearchTask(ready: readonly TaskRecord[], worker: ResearchWorker, _live: readonly ResearchWorker[], groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord | undefined {
  return ['researcher', 'engineer'].includes(worker.role) ? eligibleResearchTasks(ready, worker, groups, tasks)[0] : undefined;
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
