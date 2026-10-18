import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import { taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type ResearchHandoffDecision = Readonly<{
  id: string; deliveryId: string; status: 'adopted' | 'rejected' | 'deferred';
  taskId?: string; taskDigest?: string; reason?: string;
}>;
type HandoffState = Readonly<{
  tasks: readonly TaskRecord[]; deliveries?: readonly DeliveryRecord[];
  researchDecisions?: readonly ResearchHandoffDecision[];
}>;
export type ResearchHandoff = Readonly<{
  id: string; deliveryId: string; producer: string; sourceTaskId: string; sourceTaskDigest: string;
  proposal: CooperativeTask; status: 'pending' | ResearchHandoffDecision['status'];
  decision?: ResearchHandoffDecision;
  source?: { commit: string; notesPath: 'RESEARCH.md' };
}>;

/** Adoption creates a proof obligation; it never turns an advisory proposal into a checked lemma. */
function sameProofTarget(proposal: CooperativeTask, task: CooperativeTask) {
  return task.kind === 'lemma' && task.proofPath === proposal.proofPath && task.theoremName === proposal.theoremName &&
    task.type === proposal.type && taskGroup(task) === taskGroup(proposal) &&
    Boolean(task.conditional) === Boolean(proposal.conditional) &&
    canonicalMathJson(task.premises ?? []) === canonicalMathJson(proposal.premises ?? []) &&
    proposal.dependsOn.every(id => task.dependsOn.includes(id));
}

/** Derive the inbox from immutable deliveries, so restarts and prompt selection cannot lose a proposal. */
export function researchHandoffs(state: HandoffState): ResearchHandoff[] {
  const nodes = new Map(state.tasks.map(node => [node.task.id, node]));
  const decisions = new Map(state.researchDecisions?.map(decision => [decision.id, decision]));
  const handoffs: ResearchHandoff[] = [];
  for (const delivery of state.deliveries ?? []) {
    const source = delivery.taskId && nodes.get(delivery.taskId);
    if (delivery.kind !== 'research' || !delivery.lemmaRequests?.length || delivery.status === 'superseded' || !source ||
        delivery.taskDigest !== taskVersion(source.task) || (delivery.dependencies ?? []).some(input =>
          !nodes.has(input.taskId) || taskVersion(nodes.get(input.taskId)!.task) !== input.taskDigest)) continue;
    for (const proposal of delivery.lemmaRequests ?? []) {
      const id = mathDigest(canonicalMathJson({ deliveryId: delivery.id, proposalDigest: taskVersion(proposal) }));
      let decision = decisions.get(id);
      if (decision?.status === 'adopted') {
        const adopted = decision.taskId && nodes.get(decision.taskId);
        if (!adopted || taskVersion(adopted.task) !== decision.taskDigest || !sameProofTarget(proposal, adopted.task)) decision = undefined;
      }
      handoffs.push({ id, deliveryId: delivery.id, producer: delivery.producer,
        sourceTaskId: source.task.id, sourceTaskDigest: delivery.taskDigest!, proposal,
        status: decision?.status ?? 'pending', ...(decision ? { decision } : {}),
        ...(delivery.commit ? { source: { commit: delivery.commit, notesPath: 'RESEARCH.md' as const } } : {}) });
    }
  }
  return handoffs;
}

export const pendingResearchHandoffs = (state: HandoffState) => researchHandoffs(state).filter(item => item.status === 'pending');

/** Bound dispatch without truncating a proposal or requiring an entire dependency chain in one turn. */
export function selectResearchHandoffBatch(state: HandoffState,
  options: { maxItems?: number; maxBytes?: number } = {}): ResearchHandoff[] {
  const maxItems = options.maxItems ?? 8, maxBytes = options.maxBytes ?? 32 * 1024;
  for (const [name, value] of [['maxItems', maxItems], ['maxBytes', maxBytes]] as const)
    if (!Number.isSafeInteger(value) || value <= 0) throw new Error('math_handoff_invalid_batch_limit:' + name);
  const deliveries = new Map<string, ResearchHandoff[]>();
  for (const handoff of pendingResearchHandoffs(state)) {
    const items = deliveries.get(handoff.deliveryId) ?? [];
    items.push(handoff); deliveries.set(handoff.deliveryId, items);
  }
  const ordered: ResearchHandoff[] = [];
  for (const items of deliveries.values()) {
    const byTask = new Map(items.map(item => [item.proposal.id, item]));
    const visited = new Set<string>(), visiting = new Set<string>();
    for (const item of items) {
      if (visited.has(item.id)) continue;
      const stack = [{ item, next: 0 }];
      visiting.add(item.id);
      while (stack.length) {
        const frame = stack.at(-1)!;
        if (frame.next < frame.item.proposal.dependsOn.length) {
          const dependency = byTask.get(frame.item.proposal.dependsOn[frame.next++]);
          if (!dependency || visited.has(dependency.id)) continue;
          if (visiting.has(dependency.id)) throw new Error('math_handoff_dependency_cycle:' + dependency.id);
          visiting.add(dependency.id); stack.push({ item: dependency, next: 0 });
        } else {
          stack.pop(); visiting.delete(frame.item.id); visited.add(frame.item.id); ordered.push(frame.item);
        }
      }
    }
  }
  const selected: ResearchHandoff[] = [];
  let bytes = 2;
  for (const handoff of ordered) {
    const nextBytes = bytes + Buffer.byteLength(JSON.stringify(handoff)) + (selected.length ? 1 : 0);
    if (selected.length && (selected.length >= maxItems || nextBytes > maxBytes)) break;
    selected.push(handoff); bytes = nextBytes;
    // An oversized first interface must reach the hard context check, rather than starve the inbox.
    if (bytes > maxBytes) break;
  }
  return selected;
}

/** Validate all decisions before mutating the graph. Only proposals shown at dispatch require a decision. */
export function resolveResearchHandoffs(state: HandoffState, dispatchedIds: readonly string[],
  tasks: readonly CooperativeTask[], value: unknown): ResearchHandoffDecision[] {
  if (value !== undefined && !Array.isArray(value)) throw new Error('math_handoff_decision_invalid');
  const shown = new Set(dispatchedIds), pending = new Map(pendingResearchHandoffs(state).map(item => [item.id, item]));
  const previous = new Map(state.researchDecisions?.map(decision => [decision.id, decision]));
  const responses = new Map<string, { status: 'rejected' | 'deferred'; reason: string }>();
  const seen = new Set<string>();
  for (const decision of (value ?? []) as any[]) {
    if (!decision || typeof decision.id !== 'string' || seen.has(decision.id) || !['rejected', 'deferred'].includes(decision.status) ||
        typeof decision.reason !== 'string' || !decision.reason.trim()) throw new Error('math_handoff_decision_invalid');
    seen.add(decision.id);
    const recorded = previous.get(decision.id);
    // A primary solver can keep an acknowledged decision while editing its help requests.
    if (!pending.has(decision.id) && recorded?.status === decision.status && recorded.reason === decision.reason.trim()) continue;
    if (!shown.has(decision.id) || !pending.has(decision.id)) throw new Error('math_handoff_decision_invalid');
    responses.set(decision.id, { status: decision.status, reason: decision.reason.trim() });
  }
  const resolved: ResearchHandoffDecision[] = [];
  for (const id of shown) {
    const handoff = pending.get(id);
    if (!handoff) continue; // A concurrent plan edit may have superseded its source.
    const adopted = tasks.find(task => task.id === handoff.proposal.id && sameProofTarget(handoff.proposal, task)) ??
      tasks.find(task => sameProofTarget(handoff.proposal, task));
    const response = responses.get(id);
    if (adopted && response) throw new Error('math_handoff_decision_conflict:' + id);
    if (adopted) {
      if (adopted.id !== handoff.proposal.id && [...pending.values()].some(item => item.id !== id &&
          item.deliveryId === handoff.deliveryId && item.proposal.dependsOn.includes(handoff.proposal.id)))
        throw new Error('math_handoff_dependency_id_required:' + handoff.proposal.id);
      resolved.push({ id, deliveryId: handoff.deliveryId, status: 'adopted', taskId: adopted.id, taskDigest: taskVersion(adopted) });
    } else if (response) resolved.push({ id, deliveryId: handoff.deliveryId, ...response });
    else throw new Error('math_handoff_unresolved:' + id + ': adopt its exact typed target or record a rejected/deferred decision with a reason.');
  }
  return resolved;
}
