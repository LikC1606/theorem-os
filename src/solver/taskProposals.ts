import type { SolverProblem } from './problem';
import { isAdvisoryTask, parseCooperationPlan, taskGroup, type CooperativeTask, type RouteGroup } from './tasks';

/** Research can propose exact proof work; adopting it remains a Lead decision. */
export function validateLemmaRequests(problem: SolverProblem, tasks: readonly CooperativeTask[], groups: readonly RouteGroup[],
  parent: CooperativeTask, value: unknown): readonly CooperativeTask[] {
  if (value === undefined) return [];
  if (!isAdvisoryTask(parent) || !Array.isArray(value) || value.some(proposal =>
    !proposal || proposal.kind !== 'lemma' || tasks.some(task => task.id === proposal.id) ||
    (proposal.groupId !== undefined && proposal.groupId !== taskGroup(parent))))
    throw new Error('math_research_lemma_requests_invalid');
  try {
    const proposed = value.map(proposal => ({ ...proposal, groupId: taskGroup(parent) }));
    const plan = parseCooperationPlan(problem, { tasks: [...tasks, ...proposed], groups });
    const existing = new Set(tasks.map(task => task.id));
    return plan.tasks.filter(task => !existing.has(task.id));
  } catch (error) {
    throw new Error('math_research_lemma_requests_invalid: ' +
      (error instanceof Error ? error.message : 'invalid proof proposal'), { cause: error });
  }
}
