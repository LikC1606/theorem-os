import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import { hasTaskAcceptance, isAdvisoryTask, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type ResearchHandoffDecision = Readonly<{
  id: string; deliveryId: string; status: 'adopted' | 'rejected' | 'deferred';
  taskId?: string; taskDigest?: string; reason?: string; contextDigest?: string;
  waitsOn?: readonly { taskId: string; taskDigest: string }[];
}>;
type HandoffState = Readonly<{
  tasks: readonly TaskRecord[]; deliveries?: readonly DeliveryRecord[];
  researchDecisions?: readonly ResearchHandoffDecision[];
}>;
export type ResearchHandoff = Readonly<{
  id: string; deliveryId: string; producer: string; sourceTaskId: string; sourceTaskDigest: string;
  proposal: CooperativeTask; status: 'pending' | ResearchHandoffDecision['status'];
  contextDigest: string;
  sources: readonly Readonly<{ handoffId: string; deliveryId: string; producer: string;
    source?: { commit: string; notesPath: 'RESEARCH.md' } }>[];
  activationDigest: string; reopened?: 'checked-prerequisites';
  decision?: ResearchHandoffDecision;
  source?: { commit: string; notesPath: 'RESEARCH.md' };
}>;

function freshlyChecked(nodes: ReadonlyMap<string, TaskRecord>, reference: { taskId: string; taskDigest: string }): boolean {
  const node = nodes.get(reference.taskId), proof = node?.integratedCheck;
  return Boolean(node && !isAdvisoryTask(node.task) && taskVersion(node.task) === reference.taskDigest &&
    node.status === 'integrated' && proof?.passed && proof.taskDigest === reference.taskDigest &&
    !proof.conditions?.length && hasTaskAcceptance(proof));
}

/** Adoption creates a proof obligation; it never turns an advisory proposal into a checked lemma. */
function sameProofTarget(proposal: CooperativeTask, task: CooperativeTask) {
  return task.kind === 'lemma' && task.proofPath === proposal.proofPath && task.theoremName === proposal.theoremName &&
    task.type === proposal.type && taskGroup(task) === taskGroup(proposal) &&
    Boolean(task.conditional) === Boolean(proposal.conditional) &&
    canonicalMathJson(task.premises ?? []) === canonicalMathJson(proposal.premises ?? []) &&
    proposal.dependsOn.every(id => task.dependsOn.includes(id));
}

const legacyHandoffId = (delivery: DeliveryRecord, proposal: CooperativeTask) =>
  mathDigest(canonicalMathJson({ deliveryId: delivery.id, proposalDigest: taskVersion(proposal) }));
const normalizedDependencies = (delivery: DeliveryRecord) => [...new Map((delivery.dependencies ?? [])
  .map(input => [input.taskId, { taskId: input.taskId, taskDigest: input.taskDigest }]))].map(([, input]) => input)
  .sort((left, right) => left.taskId.localeCompare(right.taskId));
const deliveryContext = (delivery: DeliveryRecord) => ({ delivery, dependencies: normalizedDependencies(delivery),
  proposals: new Map(delivery.lemmaRequests?.map(task => [task.id, task])) });

function handoffContext(context: ReturnType<typeof deliveryContext>, proposal: CooperativeTask,
  tasks: ReadonlyMap<string, CooperativeTask>) {
  const { delivery, dependencies, proposals } = context;
  const inputs = [...new Set(proposal.dependsOn)].sort().map(taskId => {
    const sibling = proposals.get(taskId), current = tasks.get(taskId) ?? sibling;
    return { taskId, taskDigest: current ? taskVersion(current) : null,
      ...(sibling ? { proposalDigest: taskVersion(sibling) } : {}) };
  });
  return { digest: mathDigest(canonicalMathJson({ sourceTaskId: delivery.taskId, sourceTaskDigest: delivery.taskDigest,
    proposalDigest: taskVersion(proposal), dependencies, inputs })),
    unboundInputs: inputs.filter(input => input.taskDigest === null ||
      input.taskDigest !== input.proposalDigest && !dependencies.some(item =>
        item.taskId === input.taskId && item.taskDigest === input.taskDigest)) };
}

/** Derive the inbox from immutable deliveries, so restarts and prompt selection cannot lose a proposal. */
export function researchHandoffs(state: HandoffState): ResearchHandoff[] {
  const nodes = new Map(state.tasks.map(node => [node.task.id, node]));
  const tasks = new Map(state.tasks.map(node => [node.task.id, node.task]));
  const decisions = new Map(state.researchDecisions?.map(decision => [decision.id, decision]));
  const groups = new Map<string, { proposal: CooperativeTask; unboundInputs: ReturnType<typeof handoffContext>['unboundInputs'];
    entries: Map<string, DeliveryRecord> }>();
  for (const delivery of state.deliveries ?? []) {
    const source = delivery.taskId && nodes.get(delivery.taskId);
    if (delivery.kind !== 'research' || !delivery.lemmaRequests?.length || delivery.status === 'superseded' || !source ||
        delivery.taskDigest !== taskVersion(source.task) || (delivery.dependencies ?? []).some(input =>
          !nodes.has(input.taskId) || taskVersion(nodes.get(input.taskId)!.task) !== input.taskDigest)) continue;
    const inputs = deliveryContext(delivery);
    for (const proposal of delivery.lemmaRequests ?? []) {
      const context = handoffContext(inputs, proposal, tasks);
      const group = groups.get(context.digest) ?? { proposal, unboundInputs: context.unboundInputs, entries: new Map() };
      group.entries.set(legacyHandoffId(delivery, proposal), delivery);
      groups.set(context.digest, group);
    }
  }
  return [...groups].map(([contextDigest, group]) => {
    const [id, delivery] = group.entries.entries().next().value!;
    const sources = [...group.entries].map(([handoffId, item]) => ({ handoffId, deliveryId: item.id, producer: item.producer,
      ...(item.commit ? { source: { commit: item.commit, notesPath: 'RESEARCH.md' as const } } : {}) }));
    const recorded = [...group.entries].flatMap(([key, item]) => {
      const decision = decisions.get(key);
      return decision?.deliveryId === item.id ? [decision] : [];
    });
    // Historical decisions require inputs fixed by their delivery or their explicit waiting contracts.
    const applicable = recorded.filter(decision => decision.contextDigest === contextDigest ||
      decision.contextDigest === undefined && group.unboundInputs.every(input =>
        decision.waitsOn?.some(reference => reference.taskId === input.taskId && reference.taskDigest === input.taskDigest)))
      .filter(decision => {
        if (decision.status !== 'adopted') return true;
        const adopted = decision.taskId && nodes.get(decision.taskId);
        return Boolean(adopted && taskVersion(adopted.task) === decision.taskDigest && sameProofTarget(group.proposal, adopted.task));
      });
    const equivalent = (decision: ResearchHandoffDecision) => canonicalMathJson({ status: decision.status, taskId: decision.taskId,
      taskDigest: decision.taskDigest, waitsOn: decision.waitsOn ?? [] });
    const decisionSource = applicable.length && applicable.every(item => equivalent(item) === equivalent(applicable[0])) ?
      applicable.find(decision => decision.id === id) ?? applicable[0] : undefined;
    const decision = decisionSource && { ...decisionSource, id, deliveryId: delivery.id };
    const reopened = decision?.status === 'deferred' && Boolean(decision.waitsOn?.length) &&
      decision.waitsOn!.every(reference => freshlyChecked(nodes, reference));
    const decisionStates = [...new Set(recorded.map(({ id: _id, deliveryId: _deliveryId, ...value }) => canonicalMathJson(value)))].sort();
    return { id, deliveryId: delivery.id, producer: delivery.producer,
      sourceTaskId: delivery.taskId!, sourceTaskDigest: delivery.taskDigest!, proposal: group.proposal,
      contextDigest, sources,
      // Additional identical deliveries are provenance, not a new activation of the same mathematical input.
      activationDigest: mathDigest(canonicalMathJson({ contextDigest, decisions: decisionStates })),
      status: reopened ? 'pending' : decision?.status ?? 'pending', ...(decision ? { decision } : {}),
      ...(reopened ? { reopened: 'checked-prerequisites' as const } : {}),
      ...(delivery.commit ? { source: { commit: delivery.commit, notesPath: 'RESEARCH.md' as const } } : {}) };
  });
}

export const pendingResearchHandoffs = (state: HandoffState) => researchHandoffs(state).filter(item => item.status === 'pending');
export const retainedResearchHandoffs = (state: HandoffState) => researchHandoffs(state).filter(item =>
  item.status === 'pending' || (item.status === 'deferred' && item.decision?.waitsOn?.length));

/** Keep exact mathematical interfaces inline; duplicate provenance is retrievable from the host graph. */
export function researchHandoffContext(handoff: ResearchHandoff) {
  const { sources, ...context } = handoff;
  return { ...context, sourceSet: { count: sources.length, digest: mathDigest(canonicalMathJson(sources)),
    reference: { path: 'COOPERATION.json' as const, handoffId: handoff.id, contextDigest: handoff.contextDigest } } };
}

/** Bound dispatch without truncating a proposal or requiring an entire dependency chain in one turn. */
export function selectResearchHandoffBatch(state: HandoffState,
  options: { maxItems?: number; maxBytes?: number } = {}): ResearchHandoff[] {
  const maxItems = options.maxItems ?? 8, maxBytes = options.maxBytes ?? 32 * 1024;
  for (const [name, value] of [['maxItems', maxItems], ['maxBytes', maxBytes]] as const)
    if (!Number.isSafeInteger(value) || value <= 0) throw new Error('math_handoff_invalid_batch_limit:' + name);
  const pending = pendingResearchHandoffs(state), deliveries = new Map<string, Map<string, ResearchHandoff>>();
  for (const item of pending) for (const source of item.sources) {
    const byTask = deliveries.get(source.deliveryId) ?? new Map<string, ResearchHandoff>();
    byTask.set(item.proposal.id, item); deliveries.set(source.deliveryId, byTask);
  }
  const dependencies = (item: ResearchHandoff) => [...new Set(item.sources.flatMap(source =>
    item.proposal.dependsOn.flatMap(id => deliveries.get(source.deliveryId)?.get(id) ?? [])))];
  const ordered: ResearchHandoff[] = [], visited = new Set<string>(), visiting = new Set<string>();
  for (const item of pending) {
    if (visited.has(item.id)) continue;
    const stack = [{ item, dependencies: dependencies(item), next: 0 }];
    visiting.add(item.id);
    while (stack.length) {
      const frame = stack.at(-1)!;
      if (frame.next < frame.dependencies.length) {
        const dependency = frame.dependencies[frame.next++];
        if (visited.has(dependency.id)) continue;
        if (visiting.has(dependency.id)) throw new Error('math_handoff_dependency_cycle:' + dependency.id);
        visiting.add(dependency.id); stack.push({ item: dependency, dependencies: dependencies(dependency), next: 0 });
      } else {
        stack.pop(); visiting.delete(frame.item.id); visited.add(frame.item.id); ordered.push(frame.item);
      }
    }
  }
  const selected: ResearchHandoff[] = [];
  let bytes = 2;
  for (const handoff of ordered) {
    const nextBytes = bytes + Buffer.byteLength(JSON.stringify(researchHandoffContext(handoff))) + (selected.length ? 1 : 0);
    if (selected.length && (selected.length >= maxItems || nextBytes > maxBytes)) break;
    selected.push(handoff); bytes = nextBytes;
    // An oversized first interface must reach the hard context check, rather than starve the inbox.
    if (bytes > maxBytes) break;
  }
  return selected;
}

/** Validate all decisions before mutating the graph. Only proposals shown at dispatch require a decision. */
export function resolveResearchHandoffs(state: HandoffState, dispatchedIds: readonly string[],
  tasks: readonly CooperativeTask[], value: unknown, activations?: Readonly<Record<string, string>>): ResearchHandoffDecision[] {
  if (value !== undefined && !Array.isArray(value)) throw new Error('math_handoff_decision_invalid');
  const handoffs = researchHandoffs(state), byAlias = new Map(handoffs.flatMap(item =>
    item.sources.map(source => [source.handoffId, item] as const)));
  const shown = new Map<string, string[]>();
  for (const id of new Set(dispatchedIds)) {
    const item = byAlias.get(id);
    if (item) shown.set(item.id, [...(shown.get(item.id) ?? []), id]);
  }
  const pending = new Map(handoffs.filter(item => item.status === 'pending').map(item => [item.id, item]));
  const waiting = new Map(handoffs.filter(item => item.status === 'deferred' && item.decision?.waitsOn?.length).map(item => [item.id, item]));
  const previous = new Map(state.researchDecisions?.map(decision => [decision.id, decision]));
  const proposed = new Map(tasks.map(task => [task.id, task])), nodes = new Map(state.tasks.map(node => [node.task.id, node]));
  const deliveries = new Map(state.deliveries?.map(delivery => [delivery.id, deliveryContext(delivery)]));
  const responses = new Map<string, Pick<ResearchHandoffDecision, 'status' | 'reason' | 'waitsOn'>>();
  const checkActivation = (handoff: ResearchHandoff) => {
    if (activations === undefined && !handoff.reopened) return;
    for (const id of shown.get(handoff.id) ?? []) if (activations?.[id] !== handoff.activationDigest)
      throw new Error('math_handoff_dispatch_superseded:' + id);
  };
  const seen = new Set<string>();
  for (const decision of (value ?? []) as any[]) {
    if (!decision || typeof decision.id !== 'string' || seen.has(decision.id) || !['rejected', 'deferred'].includes(decision.status) ||
        typeof decision.reason !== 'string' || !decision.reason.trim()) throw new Error('math_handoff_decision_invalid');
    seen.add(decision.id);
    const handoff = byAlias.get(decision.id), id = handoff?.id ?? decision.id;
    if (pending.has(id) && shown.has(id)) checkActivation(handoff!);
    let waitsOn: ResearchHandoffDecision['waitsOn'];
    if (decision.waitsOn !== undefined) {
      if (decision.status !== 'deferred' || !Array.isArray(decision.waitsOn) || !decision.waitsOn.length ||
          new Set(decision.waitsOn).size !== decision.waitsOn.length || decision.waitsOn.some((id: unknown) => typeof id !== 'string'))
        throw new Error('math_handoff_waits_on_invalid');
      waitsOn = decision.waitsOn.map((id: string) => {
        const task = proposed.get(id);
        if (!task || isAdvisoryTask(task) || (task.kind === 'lemma' && !task.type?.trim()))
          throw new Error('math_handoff_waits_on_invalid:' + id);
        return { taskId: id, taskDigest: taskVersion(task) };
      }).sort((left: { taskId: string }, right: { taskId: string }) => left.taskId.localeCompare(right.taskId));
    }
    const recorded = handoff?.decision ?? previous.get(decision.id);
    const response = { status: decision.status as 'rejected' | 'deferred', reason: decision.reason.trim(), ...(waitsOn ? { waitsOn } : {}) };
    // A primary solver can keep an acknowledged decision while editing its help requests.
    if (!pending.has(id) && recorded?.status === response.status && recorded.reason === response.reason &&
        canonicalMathJson(recorded.waitsOn ?? []) === canonicalMathJson(waitsOn ?? [])) continue;
    if (!(shown.has(id) && pending.has(id)) && !waiting.has(id))
      throw new Error('math_handoff_decision_invalid');
    if (waitsOn?.every(reference => freshlyChecked(nodes, reference))) throw new Error('math_handoff_waits_on_satisfied:' + decision.id);
    if (responses.has(id) && canonicalMathJson(responses.get(id)) !== canonicalMathJson(response))
      throw new Error('math_handoff_decision_conflict:' + id);
    responses.set(id, response);
  }
  const resolved: ResearchHandoffDecision[] = [];
  for (const id of new Set([...shown.keys(), ...responses.keys()])) {
    const handoff = pending.get(id) ?? (responses.has(id) ? waiting.get(id) : undefined);
    if (!handoff) continue; // A concurrent plan edit may have superseded its source.
    if (pending.has(id)) checkActivation(handoff);
    const adopted = tasks.find(task => task.id === handoff.proposal.id && sameProofTarget(handoff.proposal, task)) ??
      tasks.find(task => sameProofTarget(handoff.proposal, task));
    const response = responses.get(id);
    if (adopted && response) throw new Error('math_handoff_decision_conflict:' + id);
    let result: Pick<ResearchHandoffDecision, 'status' | 'taskId' | 'taskDigest' | 'reason' | 'waitsOn'>;
    if (adopted) {
      if (adopted.id !== handoff.proposal.id && [...pending.values()].some(item => item.id !== id &&
          item.sources.some(source => handoff.sources.some(other => other.deliveryId === source.deliveryId)) &&
          item.proposal.dependsOn.includes(handoff.proposal.id)))
        throw new Error('math_handoff_dependency_id_required:' + handoff.proposal.id);
      result = { status: 'adopted', taskId: adopted.id, taskDigest: taskVersion(adopted) };
    } else if (response) result = response;
    else throw new Error('math_handoff_unresolved:' + id + ': adopt its exact typed target or record a rejected/deferred decision with a reason.');
    // Keep each immutable delivery's old key durable, including when only one alias was dispatched.
    for (const source of handoff.sources) {
      resolved.push({ id: source.handoffId, deliveryId: source.deliveryId, ...result,
        contextDigest: handoffContext(deliveries.get(source.deliveryId)!, handoff.proposal, proposed).digest });
    }
  }
  return resolved;
}
