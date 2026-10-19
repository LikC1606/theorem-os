import { hasTaskAcceptance, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';
import type { TaskProof } from './cooperativeProof';

/** Routes are alternatives; the prerequisites within one route are conjunctive. */
export type ProofRoute = {
  id: string; targetTaskId: string; prerequisiteTaskIds: readonly string[]; closingTaskId: string;
};

const validId = (value: unknown): value is string => typeof value === 'string' && /^[a-zA-Z0-9_-]{1,64}$/u.test(value);
const routeKeys = new Set(['id', 'targetTaskId', 'prerequisiteTaskIds', 'closingTaskId']);
const exactLemma = (task: CooperativeTask | undefined): task is CooperativeTask & { type: string } => Boolean(task &&
  task.kind === 'lemma' && typeof task.type === 'string' && task.type.trim() && task.type.trim() !== 'FULL_CLOSED_LEAN_TYPE' &&
  typeof task.theoremName === 'string' && task.theoremName.trim() && typeof task.proofPath === 'string' && task.proofPath.trim());

/** An exact type is an interface, not a syntactic claim that its proof entails the original goal. */
export function parseProofRoutes(value: unknown, tasks: readonly CooperativeTask[]): ProofRoute[] {
  if (value === undefined) return [];
  if (!Array.isArray(value)) throw new Error('math_plan_invalid_proof_routes');
  const nodes = new Map(tasks.map(task => [task.id, task]));
  if (nodes.size !== tasks.length) throw new Error('math_plan_duplicate_task');
  const routes = value.map((item: unknown): ProofRoute => {
    if (!item || typeof item !== 'object' || Array.isArray(item) || Object.keys(item).some(key => !routeKeys.has(key)))
      throw new Error('math_plan_invalid_proof_route');
    const route = item as Record<string, unknown>;
    if (!validId(route.id) || !validId(route.targetTaskId) || !validId(route.closingTaskId) ||
        !Array.isArray(route.prerequisiteTaskIds) || !route.prerequisiteTaskIds.every(validId) ||
        new Set(route.prerequisiteTaskIds).size !== route.prerequisiteTaskIds.length)
      throw new Error('math_plan_invalid_proof_route');
    if (nodes.get(route.targetTaskId)?.kind !== 'goal') throw new Error('math_plan_invalid_proof_route_target');
    if (!exactLemma(nodes.get(route.closingTaskId)) || route.prerequisiteTaskIds.some(id => !exactLemma(nodes.get(id))))
      throw new Error('math_plan_invalid_proof_route_input');
    return { id: route.id, targetTaskId: route.targetTaskId,
      prerequisiteTaskIds: [...route.prerequisiteTaskIds], closingTaskId: route.closingTaskId };
  });
  if (new Set(routes.map(route => route.id)).size !== routes.length ||
      new Set(routes.map(route => route.targetTaskId + '\0' + route.closingTaskId)).size !== routes.length)
    throw new Error('math_plan_duplicate_proof_route');

  // Check ordinary inputs as well as route edges. Cross-route cycles are invalid even
  // when the original goals do not list the alternative closing lemmas in dependsOn.
  const edges = new Map(tasks.map(task => [task.id, [...task.dependsOn]]));
  for (const route of routes) edges.get(route.targetTaskId)!.push(route.closingTaskId);
  const visiting = new Set<string>(), visited = new Set<string>();
  const visit = (id: string) => {
    if (visiting.has(id)) throw new Error('math_plan_proof_route_cycle');
    if (visited.has(id)) return;
    if (!nodes.has(id)) throw new Error('math_plan_missing_dependency');
    visiting.add(id); edges.get(id)!.forEach(visit); visiting.delete(id); visited.add(id);
  };
  tasks.forEach(task => visit(task.id));
  const dependencies = (id: string): Set<string> => {
    const result = new Set<string>();
    const collect = (input: string) => {
      if (result.has(input)) return;
      result.add(input); nodes.get(input)!.dependsOn.forEach(collect);
    };
    nodes.get(id)!.dependsOn.forEach(collect);
    return result;
  };
  for (const route of routes) {
    const inputs = [route.closingTaskId, ...route.prerequisiteTaskIds], target = nodes.get(route.targetTaskId)!;
    const closingDependencies = dependencies(route.closingTaskId);
    if (route.prerequisiteTaskIds.some(id => !closingDependencies.has(id)))
      throw new Error('math_plan_proof_route_missing_prerequisite');
    for (const id of inputs) {
      const input = nodes.get(id)!;
      if (id === target.id || dependencies(id).has(target.id)) throw new Error('math_plan_proof_route_cycle');
      if (taskGroup(input) !== taskGroup(target) && input.sharing === 'group')
        throw new Error('math_plan_proof_route_input_not_shared');
    }
  }
  return routes;
}

export type RecordedRouteProofStatus = 'none' | 'conditional' | 'checked' | 'stale' | 'unverified';

/** Inspect receipts without replaying Lean. No recorded result authorizes acceptance. */
function routeEvidence(tasks: readonly TaskRecord[], environmentDigest?: string) {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const statuses = new Map<string, RecordedRouteProofStatus>();
  const status = (id: string): RecordedRouteProofStatus => {
    const cached = statuses.get(id);
    if (cached) return cached;
    // Fail closed on cyclic or malformed restored reference graphs.
    statuses.set(id, 'unverified');
    const node = nodes.get(id), proof = node?.integratedCheck ?? node?.proof;
    const proofEnvironment = proof?.projection?.environmentDigest ?? proof?.references?.environmentDigest;
    let result: RecordedRouteProofStatus;
    if (!node || !proof) result = 'none';
    else if (proof.taskDigest !== taskVersion(node.task) || (environmentDigest && proofEnvironment &&
        proofEnvironment !== environmentDigest)) result = 'stale';
    else {
      const verification = proof.verification, references = proof.references, projection = proof.projection;
      const receiptsMatch = verification?.status === 'kernel_verified' && Boolean(verification.targetCommit) &&
        Array.isArray(verification.results) && verification.results.length > 0 && verification.results.every(receipt =>
          receipt && receipt.status === 'kernel_verified' && receipt.targetCommit === verification.targetCommit &&
          typeof receipt.receiptId === 'string' && receipt.receiptId.length > 0 &&
          (receipt.proofPath === undefined || receipt.proofPath === node.task.proofPath) &&
          (receipt.theoremName === undefined || receipt.theoremName === node.task.theoremName) &&
          (receipt.statementHash === undefined || receipt.statementHash === proof.taskDigest) &&
          (receipt.leanStatementHash === undefined || receipt.leanStatementHash === proof.taskDigest));
      const referencesMatch = !references || (references.scope !== 'statement' && references.root?.file === node.task.proofPath &&
        typeof references.root?.name === 'string' &&
        (references.root.name === node.task.theoremName || references.root.name.endsWith('.' + node.task.theoremName)) &&
        (references.tasks === undefined || (Array.isArray(references.tasks) && references.tasks.every(input => input &&
          typeof input.taskId === 'string' && typeof input.taskDigest === 'string'))));
      const projectionMatches = !projection || ([projection.environmentDigest, projection.problemReceiptDigest, projection.sourceDigest]
        .every(value => typeof value === 'string' && value.length > 0) &&
        (!references || references.environmentDigest === projection.environmentDigest));
      const conditionsMatch = proof.conditions === undefined || (Array.isArray(proof.conditions) && proof.conditions.every(input => input &&
        typeof input.taskId === 'string' && typeof input.taskDigest === 'string') &&
        new Set(proof.conditions.map(input => input.taskId)).size === proof.conditions.length);
      if (!proof.passed || !receiptsMatch || !referencesMatch || !projectionMatches || !conditionsMatch) result = 'unverified';
      else if (environmentDigest && !proofEnvironment) result = 'unverified';
      else {
        const inputs = references?.tasks ?? [];
        const versions = [...(proof.conditions ?? []), ...inputs];
        if (versions.some(input => !nodes.has(input.taskId) || taskVersion(nodes.get(input.taskId)!.task) !== input.taskDigest)) result = 'stale';
        else if (proof.conditions?.length) result = 'conditional';
        else if ((environmentDigest && !references) || (node.task.dependsOn.length && !references?.tasks)) result = 'unverified';
        else {
          const inputStatuses = inputs.map(input => status(input.taskId));
          result = inputStatuses.includes('stale') ? 'stale' : inputStatuses.every(input => input === 'checked') ? 'checked' : 'unverified';
        }
      }
    }
    statuses.set(id, result);
    return result;
  };
  const settled = (id: string, fresh: boolean, forbiddenId?: string, visiting = new Set<string>()): boolean => {
    const node = nodes.get(id), proof = node?.integratedCheck;
    if (id === forbiddenId || visiting.has(id) || !node || node.status !== 'integrated' || !proof ||
        status(id) !== 'checked' || (fresh && !hasTaskAcceptance(proof))) return false;
    const next = new Set(visiting); next.add(id);
    return (proof.references?.tasks ?? []).every(input => settled(input.taskId, fresh, forbiddenId, next));
  };
  return { nodes, status, settled };
}

/** A ready route enables an original-goal attempt; it never substitutes for that goal's check. */
export function proofRouteReady(route: ProofRoute, tasks: readonly TaskRecord[], environmentDigest?: string, fresh = true): boolean {
  try { parseProofRoutes([route], tasks.map(node => node.task)); } catch { return false; }
  const evidence = routeEvidence(tasks, environmentDigest);
  return [route.closingTaskId, ...route.prerequisiteTaskIds].every(id => evidence.settled(id, fresh, route.targetTaskId));
}

const proofUsesClosing = (proof: TaskProof | undefined, closing: TaskRecord | undefined) => Boolean(proof?.references && closing &&
  Array.isArray(proof.references.tasks) && proof.references.tasks.some(input => input &&
    input.taskId === closing.task.id && input.taskDigest === taskVersion(closing.task)) &&
  Array.isArray(proof.references.proof) && proof.references.proof.some(reference => reference &&
    reference.file === closing.task.proofPath && typeof reference.name === 'string' &&
    (reference.name === closing.task.theoremName || reference.name.endsWith('.' + closing.task.theoremName))));

export function describeProofRoutes(routes: readonly ProofRoute[], tasks: readonly TaskRecord[], environmentDigest?: string) {
  const evidence = routeEvidence(tasks, environmentDigest);
  return { evidence: 'recorded-not-replayed' as const, routes: routes.map(route => {
    const closing = evidence.nodes.get(route.closingTaskId), target = evidence.nodes.get(route.targetTaskId);
    const ready = proofRouteReady(route, tasks, environmentDigest, false);
    const connected = ready && evidence.settled(route.targetTaskId, false) && proofUsesClosing(target?.integratedCheck, closing);
    const inputs = [...new Set([...route.prerequisiteTaskIds, route.closingTaskId, route.targetTaskId])];
    return { evidence: 'recorded-not-replayed' as const, routeId: route.id, targetTaskId: route.targetTaskId,
      prerequisiteTaskIds: [...route.prerequisiteTaskIds], closingTaskId: route.closingTaskId, closingType: closing?.task.type ?? null,
      prerequisiteStatuses: route.prerequisiteTaskIds.map(taskId => ({ taskId, status: evidence.status(taskId) })),
      remainingPrerequisiteTaskIds: route.prerequisiteTaskIds.filter(id => !evidence.settled(id, false, route.targetTaskId)),
      closingStatus: evidence.status(route.closingTaskId), ready, targetStatus: evidence.status(route.targetTaskId),
      connection: connected ? 'closed-by-original-check' as const : 'awaiting-original-check' as const,
      referenceCoverageMissing: inputs.filter(id => {
        const node = evidence.nodes.get(id), references = (node?.integratedCheck ?? node?.proof)?.references;
        return !Array.isArray(references?.tasks) || !Array.isArray(references?.proof);
      }) };
  }) };
}
