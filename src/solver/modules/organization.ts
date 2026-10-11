import type { ActionPlan, ResearchBudget } from './search';

export type ResearchWorker = Readonly<{ id: string; worktree: string; ownedFiles: readonly string[] }>;
export type TeamPlan = Readonly<{ worker: ResearchWorker; communication: 'isolated' }>;

/** M6: one existing worker owns the proof files and the original run budget. */
export function organizeResearch(action: ActionPlan, workers: readonly ResearchWorker[], budget: ResearchBudget): TeamPlan {
  if (action.operation === 'stop' || !workers.length || budget.aborted || budget.remainingMs <= 0)
    throw new Error('math_solver_worker_unavailable');
  return { worker: workers[0]!, communication: 'isolated' };
}
