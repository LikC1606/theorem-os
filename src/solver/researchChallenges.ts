import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import type { ProofRoute } from './proofRoutes';
import { hasTaskAcceptance, isAdvisoryTask, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type ResearchChallengeDecision = Readonly<{
  id: string; deliveryId: string; contextDigest: string;
  status: 'revised' | 'disputed' | 'deferred'; reason: string;
  evidenceRefs?: readonly string[]; reopenOn?: string;
  waitsOn?: readonly { taskId: string; taskDigest: string }[];
}>;
type ChallengeState = Readonly<{
  tasks: readonly TaskRecord[]; deliveries?: readonly DeliveryRecord[]; proofRoutes?: readonly ProofRoute[];
  challengeDecisions?: readonly ResearchChallengeDecision[];
}>;
export type ResearchChallenge = Readonly<{
  id: string; deliveryId: string; sourceTaskId: string; sourceTaskDigest: string; findingDigest: string;
  contextDigest: string; activationDigest: string; conclusion: string; summary: string; evidenceRefs: readonly string[];
  source?: { commit: string; notesPath: 'RESEARCH.md' };
  status: 'pending' | ResearchChallengeDecision['status']; decision?: ResearchChallengeDecision;
}>;

function challengeBasis(state: ChallengeState, source: CooperativeTask, inputs: DeliveryRecord['dependencies']) {
  const nodes = new Map(state.tasks.map(node => [node.task.id, node.task]));
  const routes = state.proofRoutes ?? state.tasks.flatMap(node => node.alternativeRoutes ?? []);
  const required = new Set<string>();
  const visit = (id: string) => {
    if (required.has(id)) return;
    required.add(id);
    nodes.get(id)?.dependsOn.forEach(visit);
    for (const route of routes) if (route.targetTaskId === id)
      [...route.prerequisiteTaskIds, route.closingTaskId].forEach(visit);
  };
  visit(source.id);
  inputs.forEach(input => visit(input.taskId));
  return { tasks: [...required].sort().map(id => ({ id, digest: nodes.has(id) ? taskVersion(nodes.get(id)!) : null,
    status: nodes.get(id)?.status ?? 'active' })),
    routes: routes.filter(route => required.has(route.targetTaskId)).map(route => ({ ...route,
      prerequisiteTaskIds: [...route.prerequisiteTaskIds].sort() })).sort((a, b) => a.id.localeCompare(b.id)) };
}

/** Advisory challenges share immutable deliveries with proposals; no verdict grants or revokes acceptance. */
export function researchChallenges(state: ChallengeState): ResearchChallenge[] {
  const nodes = new Map(state.tasks.map(node => [node.task.id, node]));
  const decisions = new Map(state.challengeDecisions?.map(item => [item.id, item]));
  return (state.deliveries ?? []).flatMap(delivery => {
    const node = delivery.taskId && nodes.get(delivery.taskId);
    if (delivery.kind !== 'research' || delivery.status === 'superseded' || !node?.finding ||
        delivery.taskDigest !== taskVersion(node.task) || delivery.dependencies.some(input =>
          !nodes.has(input.taskId) || taskVersion(nodes.get(input.taskId)!.task) !== input.taskDigest)) return [];
    let finding: any;
    try { finding = JSON.parse(node.finding); } catch { return []; }
    if (!finding || typeof finding !== 'object' || Array.isArray(finding)) return [];
    const findingDigest = mathDigest(node.finding);
    if (delivery.findingDigest !== findingDigest ||
        finding.conclusion !== 'refuted' && finding.needsDecision !== true) return [];
    const id = mathDigest(canonicalMathJson({ deliveryId: delivery.id, findingDigest }));
    const contextDigest = mathDigest(canonicalMathJson({ deliveryId: delivery.id, findingDigest,
      commit: delivery.commit, dependencies: delivery.dependencies, basis: challengeBasis(state, node.task, delivery.dependencies) }));
    const recorded = decisions.get(id);
    const waitingInputs = recorded?.waitsOn?.map(input => ({ ...input,
      currentDigest: nodes.has(input.taskId) ? taskVersion(nodes.get(input.taskId)!.task) : null }));
    const decision = recorded?.deliveryId === delivery.id && recorded.contextDigest === contextDigest &&
      waitingInputs?.every(input => input.currentDigest === input.taskDigest) !== false ? recorded : undefined;
    const reopened = decision?.status === 'deferred' && decision.waitsOn?.length && decision.waitsOn.every(input => {
      const target = nodes.get(input.taskId), proof = target?.integratedCheck;
      return target && taskVersion(target.task) === input.taskDigest && target.status === 'integrated' &&
        proof?.passed && !proof.conditions?.length && proof.taskDigest === input.taskDigest && hasTaskAcceptance(proof);
    });
    return [{ id, deliveryId: delivery.id, sourceTaskId: node.task.id, sourceTaskDigest: taskVersion(node.task), findingDigest,
      contextDigest, activationDigest: mathDigest(canonicalMathJson({ contextDigest, recorded, waitingInputs })),
      conclusion: finding.conclusion ?? 'inconclusive', summary: delivery.summary, evidenceRefs: delivery.evidenceRefs,
      ...(delivery.commit ? { source: { commit: delivery.commit, notesPath: 'RESEARCH.md' as const } } : {}),
      status: reopened ? 'pending' as const : decision?.status ?? 'pending' as const, ...(decision ? { decision } : {}) }];
  });
}

export const pendingResearchChallenges = (state: ChallengeState) => researchChallenges(state).filter(item => item.status === 'pending');
export const retainedResearchChallenges = (state: ChallengeState) => researchChallenges(state).filter(item =>
  item.status === 'pending' || item.status === 'deferred' && Boolean(item.decision?.waitsOn?.length));
export function selectResearchChallengeBatch(state: ChallengeState) {
  const selected: ResearchChallenge[] = [];
  let bytes = 0;
  for (const item of pendingResearchChallenges(state)) {
    const size = Buffer.byteLength(JSON.stringify(item));
    if (selected.length && (selected.length >= 8 || bytes + size > 32 * 1024)) break;
    selected.push(item); bytes += size;
  }
  return selected;
}

/** Validate a fixed dispatch against current evidence before applying a proposed plan. */
export function resolveResearchChallenges(state: ChallengeState, ids: readonly string[], activations: Readonly<Record<string, string>>,
  tasks: readonly CooperativeTask[], value: unknown): ResearchChallengeDecision[] {
  if (value !== undefined && !Array.isArray(value)) throw new Error('math_challenge_decision_invalid');
  const challenges = researchChallenges(state);
  const pending = new Map(challenges.filter(item => item.status === 'pending').map(item => [item.id, item]));
  const deferred = new Map(challenges.filter(item => item.status === 'deferred').map(item => [item.id, item]));
  const shown = new Set(ids), responses = new Map<string, any>();
  for (const response of (value ?? []) as any[]) {
    if (!response || typeof response.id !== 'string' || (!shown.has(response.id) && !deferred.has(response.id)) || responses.has(response.id) ||
        !['revised', 'disputed', 'deferred'].includes(response.status) || typeof response.reason !== 'string' || !response.reason.trim())
      throw new Error('math_challenge_decision_invalid');
    responses.set(response.id, response);
  }
  return [...new Set([...shown, ...responses.keys()])].flatMap(id => {
    const challenge = pending.get(id) ?? (responses.has(id) ? deferred.get(id) : undefined);
    if (!challenge) return []; // Concurrent edits or a prior incremental publication superseded this input.
    if (shown.has(id) && activations[id] !== challenge.activationDigest) throw new Error('math_challenge_dispatch_superseded:' + id);
    const response = responses.get(id);
    if (!response) throw new Error('math_challenge_unresolved:' + id);
    const evidenceRefs = response.evidenceRefs;
    if (evidenceRefs !== undefined && (!Array.isArray(evidenceRefs) || evidenceRefs.some(ref => typeof ref !== 'string' || !ref.trim())))
      throw new Error('math_challenge_evidence_invalid:' + id);
    if (response.status === 'disputed' && !evidenceRefs?.length) throw new Error('math_challenge_evidence_required:' + id);
    const waitsOn = response.waitsOn;
    if (waitsOn !== undefined && (response.status !== 'deferred' || !Array.isArray(waitsOn) || !waitsOn.length ||
        new Set(waitsOn).size !== waitsOn.length || waitsOn.some(item => typeof item !== 'string')))
      throw new Error('math_challenge_waits_on_invalid:' + id);
    const waiting = waitsOn?.map((taskId: string) => {
      const task = tasks.find(task => task.id === taskId);
      if (!task || isAdvisoryTask(task) || task.kind === 'lemma' && !task.type?.trim())
        throw new Error('math_challenge_waits_on_invalid:' + taskId);
      return { taskId, taskDigest: taskVersion(task) };
    });
    if (waiting?.every((input: { taskId: string; taskDigest: string }) => {
      const node = state.tasks.find(node => node.task.id === input.taskId), proof = node?.integratedCheck;
      return node?.status === 'integrated' && taskVersion(node.task) === input.taskDigest && proof?.passed &&
        proof.taskDigest === input.taskDigest && !proof.conditions?.length && hasTaskAcceptance(proof);
    })) throw new Error('math_challenge_waits_on_satisfied:' + id);
    if (response.reopenOn !== undefined && (typeof response.reopenOn !== 'string' || !response.reopenOn.trim()))
      throw new Error('math_challenge_reopen_on_invalid:' + id);
    if (response.status === 'deferred' && !waiting?.length && !response.reopenOn?.trim())
      throw new Error('math_challenge_reopen_on_required:' + id);
    return [{ id, deliveryId: challenge.deliveryId, contextDigest: challenge.contextDigest,
      status: response.status, reason: response.reason.trim(), ...(evidenceRefs ? { evidenceRefs } : {}),
      ...(waiting ? { waitsOn: waiting } : {}), ...(response.reopenOn ? { reopenOn: response.reopenOn.trim() } : {}) }];
  });
}

export function preserveResearchChallengeBacklog(state: ChallengeState, tasks: readonly CooperativeTask[],
  proofRoutes: readonly ProofRoute[] | undefined, decisions: readonly ResearchChallengeDecision[]) {
  const decided = new Set(decisions.map(item => item.id));
  const retained = retainedResearchChallenges(state).filter(item => !decided.has(item.id));
  if (!retained.length) return;
  const previous = new Map(state.tasks.map(node => [node.task.id, node]));
  const proposed = new Map(tasks.map(task => [task.id, task]));
  const next = researchChallenges({ ...state, proofRoutes, tasks: tasks.map(task => ({
    ...(previous.get(task.id) ?? { status: 'pending' as const, attempts: 0 }), task })) });
  for (const item of retained) {
    if (item.status === 'deferred') {
      const source = proposed.get(item.sourceTaskId);
      const inputs = state.deliveries?.find(delivery => delivery.id === item.deliveryId)?.dependencies ?? [];
      if (!source || [...inputs, ...(item.decision?.waitsOn ?? [])].some(input => !proposed.has(input.taskId)))
        throw new Error('math_challenge_backlog_source_required:' + item.sourceTaskId);
      // Explicitly revised source inputs supersede their old evidence. A renamed or
      // removed task alone must not erase a decision still awaiting checked work.
      if (taskVersion(source) !== item.sourceTaskDigest || inputs.some(input =>
        taskVersion(proposed.get(input.taskId)!) !== input.taskDigest)) continue;
      // A changed waiting contract or route topology reopens the retained challenge.
      if (next.some(value => value.id === item.id)) continue;
    } else if (next.some(value => value.id === item.id && value.contextDigest === item.contextDigest)) continue;
    throw new Error('math_challenge_backlog_source_required:' + item.sourceTaskId);
  }
}
