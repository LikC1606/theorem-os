import { canonicalMathJson } from '../math/mathRuntimeIo';
import type { SolverProblem } from './problem';
import { researchHandoffs, resolveResearchHandoffs, sameHandoffTaskContract } from './researchHandoffs';
import { parseCooperationPlan, type CooperativeAction } from './tasks';

/** An explicit decision materializes the immutable proposal, never model-supplied proof or task fields. */
export function composeHandoffPublication(problem: SolverProblem, state: Parameters<typeof researchHandoffs>[0],
  base: Omit<ReturnType<typeof parseCooperationPlan>, 'groups'> & { groups?: ReturnType<typeof parseCooperationPlan>['groups'] },
  action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>,
  response: any) {
  const invalid = () => new Error('math_handoff_publication_invalid');
  const keys = (value: any, allowed: readonly string[]) => value && typeof value === 'object' && !Array.isArray(value) &&
    Object.keys(value).every(key => allowed.includes(key));
  if (action.kind !== 'lead' || action.initialPlanNonce || action.recovery || !action.handoffIds?.length ||
      !keys(response, ['kind', 'dispatchNonce', 'baseVersion', 'summary', 'handoffDecisions']) ||
      response.kind !== 'handoff' || !Array.isArray(response.handoffDecisions)) throw invalid();
  const handoffs = researchHandoffs(state), byAlias = new Map(handoffs.flatMap(item =>
    item.sources.map(source => [source.handoffId, item] as const)));
  const shown = new Set(action.handoffIds), seen = new Set<string>(), seenTargets = new Set<string>();
  const tasks = [...base.tasks], adoptedTaskIds: string[] = [];
  const responses: unknown[] = [];
  for (const decision of response.handoffDecisions) {
    if (!keys(decision, decision?.status === 'adopted' ? ['id', 'status', 'ownerId'] :
      decision?.status === 'deferred' ? ['id', 'status', 'reason', 'waitsOn'] : ['id', 'status', 'reason']) ||
        typeof decision.id !== 'string' || !shown.has(decision.id) || seen.has(decision.id) ||
        !['adopted', 'rejected', 'deferred'].includes(decision.status)) throw invalid();
    const handoff = byAlias.get(decision.id);
    if (!handoff || handoff.status !== 'pending' || seenTargets.has(handoff.id) ||
        action.handoffActivations?.[decision.id] !== handoff.activationDigest)
      throw new Error('math_handoff_dispatch_superseded:' + decision.id);
    seen.add(decision.id); seenTargets.add(handoff.id);
    if (decision.status !== 'adopted') { responses.push(decision); continue; }
    const proposal = handoff.proposal, existing = tasks.find(task => task.id === proposal.id);
    if (existing) {
      if (!sameHandoffTaskContract(existing, proposal) || decision.ownerId !== undefined && decision.ownerId !== existing.ownerId)
        throw new Error('math_handoff_target_conflict:' + proposal.id);
    } else {
      tasks.push({ ...proposal, ...(decision.ownerId === undefined ? {} : { ownerId: decision.ownerId }) });
    }
    adoptedTaskIds.push(proposal.id);
  }
  if (seen.size !== shown.size) throw new Error('math_handoff_unresolved: decide every handoff shown in this dispatch.');
  const plan = parseCooperationPlan(problem, { ...base, tasks });
  // Parsing must leave all existing mathematical contracts and ownership untouched.
  for (const task of base.tasks) if (canonicalMathJson(task) !== canonicalMathJson(plan.tasks.find(item => item.id === task.id)))
    throw new Error('math_handoff_base_changed:' + task.id);
  const handoffDecisions = resolveResearchHandoffs(state, action.handoffIds, plan.tasks, responses, action.handoffActivations);
  return { plan, decisions: { handoffs: handoffDecisions, challenges: [] }, adoptedTaskIds };
}
