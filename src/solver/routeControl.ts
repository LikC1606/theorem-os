import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { freshlyAccepted, hasTaskAcceptance, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type ReopenCondition = { kind: 'contract-changed' } | { kind: 'environment-changed' } |
  { kind: 'dependency-checked'; taskId: string };
export type BlockerProposal = { mechanism: string; scope: string; blockerId?: string; evidenceRefs?: readonly string[];
  reopenOn?: readonly ReopenCondition[] };
/** Field feedback is carried unchanged into the assignment's delivery receipt. */
export class RouteBlockerValidationError extends Error {
  readonly issues: readonly { path: string; message: string }[];
  constructor(path: string, message: string) {
    super('math_route_blocker_invalid: ' + path + ': ' + message);
    this.name = 'RouteBlockerValidationError';
    this.issues = [{ path, message }];
  }
}
export type BlockerBasis = { contractDigest: string; environmentDigest: string;
  dependencies: Record<string, { contractDigest: string; evidenceDigest?: string }> };
export type RouteBlocker = { id: string; taskId: string; groupId: string; taskDigest: string; routeId?: string;
  mechanism: string; scope: string; evidenceStatus: 'advisory'; evidenceRefs: readonly string[];
  reopenOn: readonly ReopenCondition[]; basis: BlockerBasis; fingerprint: string; count: number;
  status: 'open' | 'parked' | 'reopened' | 'superseded'; createdAt: number; updatedAt: number; reopenedReason?: string };

const hash = (value: unknown) => mathDigest(canonicalMathJson(value));
// Operational revision numbers and prose changes are not new mathematical inputs.
const contract = (task: CooperativeTask) => hash({ kind: task.kind, proofPath: task.proofPath,
  theoremName: task.theoremName, type: task.type, premises: task.premises ?? [] });
const normalize = (value: string) => value.trim().replace(/\s+/gu, ' ');

/** Only evidence local to the declared dependency cone can reopen this inference. */
export function routeBlockerBasis(task: CooperativeTask, tasks: readonly TaskRecord[], environmentDigest: string,
  problemReceiptDigest: string, routeId = tasks.find(node => node.task.id === task.id)?.assignment?.routeId): BlockerBasis {
  const nodes = new Map(tasks.map(node => [node.task.id, node])), seen = new Set<string>();
  const dependencies: BlockerBasis['dependencies'] = Object.create(null);
  const visit = (id: string) => {
    if (seen.has(id)) return;
    seen.add(id);
    const node = nodes.get(id);
    if (!node) { dependencies[id] = { contractDigest: 'missing' }; return; }
    const proof = node.integratedCheck;
    const checked = node.status === 'integrated' && proof?.passed && !proof.conditions?.length &&
      proof.taskDigest === taskVersion(node.task) && proof.verification.status === 'kernel_verified' &&
      (!proof.references || proof.references.environmentDigest === environmentDigest);
    // Exclude run commits, receipt IDs and whole-file hashes: an unrelated helper or
    // a replay of the same proof must not reset the recurrence count.
    const evidence = checked ? { contract: contract(node.task),
      declarations: proof.changes?.filter(change => change.file === node.task.proofPath &&
        change.name.split('.').at(-1) === node.task.theoremName?.split('.').at(-1)).map(change => change.after),
      inputs: proof.references?.inputs.filter(input => input.name), imports: proof.imports } : undefined;
    dependencies[id] = { contractDigest: contract(node.task), ...(evidence ? { evidenceDigest: hash(evidence) } : {}) };
    node.task.dependsOn.forEach(visit);
  };
  const route = nodes.get(task.id)?.alternativeRoutes?.find(route => route.id === routeId);
  [...task.dependsOn, ...(route ? [...route.prerequisiteTaskIds, route.closingTaskId] : [])].forEach(visit);
  return { contractDigest: hash({ problemReceiptDigest, contract: contract(task),
    dependencies: Object.entries(dependencies).map(([id, entry]) => [id, entry.contractDigest]).sort() }),
    environmentDigest, dependencies };
}

export function validateBlockerProposals(value: unknown, task: CooperativeTask, tasks: readonly TaskRecord[]): BlockerProposal[] {
  if (value === undefined) return [];
  if (!Array.isArray(value) || value.length > 16)
    throw new RouteBlockerValidationError('blockers', 'Provide an array of at most 16 local obstruction reports.');
  const local = routeBlockerBasis(task, tasks, '', '').dependencies;
  return value.map((item, index) => {
    const field = `blockers[${index}]`;
    if (!item || typeof item.mechanism !== 'string' || !item.mechanism.trim() || item.mechanism.length > 500)
      throw new RouteBlockerValidationError(field + '.mechanism', 'Provide a nonempty mechanism string of at most 500 characters.');
    if (typeof item.scope !== 'string' || !item.scope.trim() || item.scope.length > 2000)
      throw new RouteBlockerValidationError(field + '.scope', 'Provide a nonempty local inference scope of at most 2000 characters.');
    if (item.blockerId !== undefined && (typeof item.blockerId !== 'string' || !/^blocker_[a-f0-9]{24}$/u.test(item.blockerId)))
      throw new RouteBlockerValidationError(field + '.blockerId', 'Use an existing blocker_ ID with 24 lowercase hexadecimal characters, or omit blockerId for a new obstruction.');
    if (item.evidenceRefs !== undefined) {
      if (!Array.isArray(item.evidenceRefs) || item.evidenceRefs.length > 32)
        throw new RouteBlockerValidationError(field + '.evidenceRefs', 'Provide an array of at most 32 evidence reference strings.');
      item.evidenceRefs.forEach((ref: unknown, refIndex: number) => {
        if (typeof ref !== 'string' || ref.length > 2000)
          throw new RouteBlockerValidationError(`${field}.evidenceRefs[${refIndex}]`, 'Provide an evidence reference string of at most 2000 characters.');
      });
    }
    if (item.reopenOn !== undefined) {
      if (!Array.isArray(item.reopenOn) || !item.reopenOn.length || item.reopenOn.length > 64)
        throw new RouteBlockerValidationError(field + '.reopenOn', 'Provide 1 to 64 reopening conditions, or omit reopenOn for host defaults.');
      item.reopenOn.forEach((condition: any, conditionIndex: number) => {
        const path = `${field}.reopenOn[${conditionIndex}]`;
        if (!condition || !['contract-changed', 'environment-changed', 'dependency-checked'].includes(condition.kind))
          throw new RouteBlockerValidationError(path + '.kind', 'Use contract-changed, environment-changed, or dependency-checked.');
        if (condition.kind !== 'dependency-checked') return;
        if (typeof condition.taskId !== 'string')
          throw new RouteBlockerValidationError(path + '.taskId', 'Provide a string taskId from this task\'s declared dependency cone.');
        if (!Object.hasOwn(local, condition.taskId)) {
          const allowed = Object.keys(local).sort();
          throw new RouteBlockerValidationError(path + '.taskId',
            `Task ${JSON.stringify(condition.taskId)} is outside the declared dependency cone of task ${JSON.stringify(task.id)}. ` +
            (allowed.length ? `Allowed dependency taskIds: ${JSON.stringify(allowed)}. ` : 'This task has no declared dependencies for dependency-checked. ') +
            'Remove this condition, use an allowed dependency, or omit reopenOn for host defaults.');
        }
      });
    }
    return { mechanism: normalize(item.mechanism), scope: normalize(item.scope),
      ...(item.blockerId ? { blockerId: item.blockerId } : {}), evidenceRefs: item.evidenceRefs ?? [],
      reopenOn: item.reopenOn ?? [{ kind: 'contract-changed' }, { kind: 'environment-changed' },
        ...Object.keys(local).map(taskId => ({ kind: 'dependency-checked' as const, taskId }))] };
  });
}

/** A report can park a local inference, but can never refute or accept the original theorem. */
export function recordRouteBlockers(records: RouteBlocker[], proposals: readonly BlockerProposal[], task: CooperativeTask,
  tasks: readonly TaskRecord[], environmentDigest: string, problemReceiptDigest: string, at = Date.now()): RouteBlocker[] {
  const currentBasis = routeBlockerBasis(task, tasks, environmentDigest, problemReceiptDigest), changed: RouteBlocker[] = [];
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const routeId = nodes.get(task.id)?.assignment?.routeId;
  // Resolve every explicit reference before updating counts, so malformed batches are atomic.
  const linked = new Map(proposals.filter(proposal => proposal.blockerId).map(proposal => {
    const record = records.find(record => record.id === proposal.blockerId);
    if (!record || record.taskId !== task.id || record.groupId !== taskGroup(task) || record.routeId !== routeId)
      throw new Error('math_route_blocker_invalid: blockerId must name an existing obstruction of this task and route.');
    return [proposal, record] as const;
  }));
  const reported = new Set<string>();
  for (const proposal of proposals) {
    const mechanism = linked.get(proposal)?.mechanism ?? normalize(proposal.mechanism);
    const scope = linked.get(proposal)?.scope ?? normalize(proposal.scope);
    // An ID identifies the obstruction, not the historical inputs of that report.
    let previous: RouteBlocker | undefined;
    for (const record of records) if (record.taskId === task.id && record.groupId === taskGroup(task) && record.routeId === routeId &&
      record.mechanism === mechanism && record.scope === scope && record.basis.contractDigest === currentBasis.contractDigest &&
      record.basis.environmentDigest === currentBasis.environmentDigest && (!previous || record.updatedAt >= previous.updatedAt))
      previous = record;
    const basis: BlockerBasis = { ...currentBasis, dependencies: Object.fromEntries(Object.entries(currentBasis.dependencies).map(([id, entry]) => {
      const dependency = nodes.get(id), proof = dependency?.integratedCheck;
      // Losing or replaying an old receipt supplies no new mathematical evidence.
      const fresh = proof && hasTaskAcceptance(proof) && proof.taskDigest === taskVersion(dependency.task);
      const prior = previous?.basis.environmentDigest === currentBasis.environmentDigest ? previous.basis.dependencies[id] : undefined;
      return [id, { ...entry, evidenceDigest: fresh ? entry.evidenceDigest :
        prior?.contractDigest === entry.contractDigest ? prior.evidenceDigest : undefined }];
    })) };
    const fingerprint = hash({ taskId: task.id, groupId: taskGroup(task), routeId, mechanism, scope, basis });
    if (reported.has(fingerprint)) continue; // Duplicate entries in one response are one attempt.
    reported.add(fingerprint);
    let record = records.find(record => record.fingerprint === fingerprint);
    if (record) {
      record.count++; record.taskId = task.id; record.taskDigest = taskVersion(task); record.updatedAt = at;
      record.status = record.count >= 2 ? 'parked' : 'open'; record.reopenedReason = undefined;
      record.evidenceRefs = [...new Set([...record.evidenceRefs, ...(proposal.evidenceRefs ?? [])])];
      // Changing a reported reopen policy does not erase a previous obstruction.
    } else {
      record = { id: 'blocker_' + fingerprint.slice(0, 24), taskId: task.id, groupId: taskGroup(task), taskDigest: taskVersion(task),
        ...(routeId ? { routeId } : {}),
        mechanism, scope, evidenceStatus: 'advisory',
        evidenceRefs: proposal.evidenceRefs ?? [], reopenOn: proposal.reopenOn ?? [], basis, fingerprint, count: 1,
        status: 'open', createdAt: at, updatedAt: at };
      records.push(record);
    }
    changed.push(record);
  }
  return changed;
}

/** Recompute parking after plan edits, integration and restore; advisory text is never a reopen receipt. */
export function refreshRouteBlockers(records: RouteBlocker[], tasks: readonly TaskRecord[], environmentDigest: string,
  problemReceiptDigest: string, at = Date.now()): RouteBlocker[] {
  const nodes = new Map(tasks.map(node => [node.task.id, node])), reopened: RouteBlocker[] = [];
  for (const node of tasks) { node.routeParking = []; node.parkedRoutes = Object.create(null); }
  for (const record of records) {
    if (['reopened', 'superseded'].includes(record.status)) continue;
    const node = nodes.get(record.taskId);
    if (!node || taskGroup(node.task) !== record.groupId) { record.status = 'superseded'; record.updatedAt = at; continue; }
    if (record.routeId && !node.alternativeRoutes?.some(route => route.id === record.routeId)) {
      record.status = 'superseded'; record.updatedAt = at; continue;
    }
    const basis = routeBlockerBasis(node.task, tasks, environmentDigest, problemReceiptDigest, record.routeId);
    if (basis.contractDigest === record.basis.contractDigest) record.taskDigest = taskVersion(node.task);
    const reason = freshlyAccepted(node, taskVersion(node.task)) ? 'assigned-obligation-checked' : record.reopenOn.find(condition => {
      if (condition.kind === 'contract-changed') return basis.contractDigest !== record.basis.contractDigest;
      if (condition.kind === 'environment-changed') return basis.environmentDigest !== record.basis.environmentDigest;
      const dependency = nodes.get(condition.taskId), receipt = dependency?.integratedCheck;
      return Boolean(receipt && dependency?.status === 'integrated' && hasTaskAcceptance(receipt) &&
        receipt.taskDigest === taskVersion(dependency.task) && !receipt.conditions?.length &&
        basis.dependencies[condition.taskId]?.evidenceDigest &&
        basis.dependencies[condition.taskId].evidenceDigest !== record.basis.dependencies[condition.taskId]?.evidenceDigest);
    })?.kind;
    if (reason) {
      record.status = 'reopened'; record.reopenedReason = reason; record.updatedAt = at; reopened.push(record);
    } else if (record.status === 'parked') {
      if (record.routeId) (node.parkedRoutes[record.routeId] ??= []).push(record.id);
      else node.routeParking.push(record.id);
    }
  }
  for (const node of tasks) if (node.status === 'pending' && node.assignment?.routeId && node.parkedRoutes[node.assignment.routeId]?.length)
    node.assignment = undefined;
  return reopened;
}
