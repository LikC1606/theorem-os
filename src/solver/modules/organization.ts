import type { ActionPlan, ResearchBudget } from './search';
import { taskGroup, type TaskRecord, type RouteRecord } from '../cooperation';

export type ResearchRole = 'lead' | 'researcher' | 'engineer' | 'reviewer';
export type ResearchWorker = Readonly<{ id: string; role: ResearchRole; worktree: string; ownedFiles: readonly string[] }>;
export type TeamPlan = Readonly<{ workers: readonly ResearchWorker[]; communication: 'tasks' }>;

/** Assign selected work by responsibility and preserve resumed ownership. */
export function assignResearchTask(ready: readonly TaskRecord[], worker: ResearchWorker, live: readonly ResearchWorker[], groups?: readonly RouteRecord[]): TaskRecord | undefined {
  const researchers = live.some(item => item.role === 'researcher');
  const engineer = live.some(item => item.role === 'engineer');
  return ready.find(node => (node.task.kind === 'goal' ? worker.role === 'engineer' || !engineer : worker.role === 'researcher' || !researchers) &&
    (node.task.kind !== 'goal' || !groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId ||
      groups.find(route => route.group.id === taskGroup(node.task))!.group.engineerId === worker.id) &&
    (!node.assignment || node.assignment.workerId === worker.id));
}

export function researchWorkers(worktree: string, ownedFiles: readonly string[], count: number): ResearchWorker[] {
  return Array.from({ length: count }, (_, index) => ({
    id: index === 0 ? 'solver' : index === count - 1 ? 'engineer' : `researcher-${index}`,
    role: index === 0 ? 'lead' : index === count - 1 ? 'engineer' : 'researcher',
    worktree: index === 0 ? worktree : `${worktree}-${index + 1}`, ownedFiles,
  }));
}

/** M5 supplies isolated role slots under the same host budget. Idle researchers can review fixed deliveries. */
export function organizeResearch(action: ActionPlan, workers: readonly ResearchWorker[], budget: ResearchBudget): TeamPlan {
  if (action.operation === 'stop' || !workers.length || budget.aborted || budget.remainingMs <= 0)
    throw new Error('math_solver_worker_unavailable');
  return { workers, communication: 'tasks' };
}
