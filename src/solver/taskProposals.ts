import type { SolverProblem } from './problem';
import { parseCooperationPlan, taskGroup, taskVersion, taskProofContractVersion, type CooperativeTask, type RouteGroup } from './tasks';

/** Research can propose exact proof work; adopting it remains a Lead decision. */
export function validateLemmaRequests(problem: SolverProblem, tasks: readonly CooperativeTask[], groups: readonly RouteGroup[],
  parent: CooperativeTask, value: unknown, previousProposals: readonly CooperativeTask[] = []): readonly CooperativeTask[] {
  if (value === undefined) return [];
  if (!Array.isArray(value) || value.some(proposal =>
    !proposal || proposal.kind !== 'lemma' ||
    (proposal.groupId !== undefined && proposal.groupId !== taskGroup(parent))))
    throw new Error('math_research_lemma_requests_invalid');
  try {
    const proposed = value.map(proposal => ({ ...proposal, groupId: taskGroup(parent) }));
    const ids = new Set(proposed.map(proposal => proposal.id));
    const plan = parseCooperationPlan(problem, { tasks: [...tasks.filter(task => !ids.has(task.id)), ...proposed], groups });
    const requests = plan.tasks.filter(task => ids.has(task.id));
    for (const request of requests) {
      const existing = tasks.find(task => task.id === request.id);
      if (existing && (!previousProposals.some(proposal => proposal.id === request.id && taskVersion(proposal) === taskVersion(request)) ||
          taskProofContractVersion(existing) !== taskProofContractVersion(request)))
        throw new Error('existing proposal contract differs or has no publication provenance');
    }
    return requests;
  } catch (error) {
    throw new Error('math_research_lemma_requests_invalid: ' +
      (error instanceof Error ? error.message : 'invalid proof proposal'), { cause: error });
  }
}
