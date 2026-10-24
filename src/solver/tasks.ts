import type { SolverProblem } from './problem';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { isSimpleLeanName } from '../math/leanSyntax';
import type { DeliveryRecord } from './deliveries';
import type { TaskProof } from './cooperativeProof';
import type { StatementAction } from './statementReview';
import type { TaskTypePreflight } from './taskTypePreflight';
import { parseProofRoutes, type ProofRoute } from './proofRoutes';
import type { CapacityExploration } from './capacityExploration';
import type { ResearchBasis, ResearchRecord } from './researchRecords';

export type CooperativeTask = Readonly<{ id: string; kind: 'research' | 'sketch' | 'lemma' | 'goal'; objective: string;
  dependsOn: readonly string[]; revision: number; proofPath?: string; theoremName?: string; type?: string;
  groupId?: string; sharing?: 'group' | 'problem'; status?: 'active' | 'paused' | 'stopped'; ownerId?: string; premises?: readonly string[];
  conditional?: boolean; statementReview?: boolean; informalStatement?: string;
  reviewScope?: 'final-candidate' | 'feasibility' }>;
export type RouteGroup = Readonly<{ id: string; objective: string; status: 'active' | 'paused' | 'stopped'; revision: number;
  engineerId?: string; maxTurns?: number; maxConcurrent?: number }>;
export type RouteRecord = { group: RouteGroup; turns: number; busy?: number };
export const taskGroup = (task: CooperativeTask): string => task.groupId ?? 'main';
export type TaskConnectionCheck = Readonly<{
  schema: 'theorem-os.consumer-connection.v1'; consumer: { taskId: string; taskDigest: string };
  inputs: readonly { taskId: string; taskDigest: string }[]; seedCommit: string; dependenciesDigest: string;
  /** Fixed dispatch inputs that still needed local binders in the worker's seed. */
  assumedInputs?: readonly { taskId: string; taskDigest: string }[]; workerId?: string; assignmentId?: string;
  routeId?: string; routesDigest: string; problemReceiptDigest: string; environmentDigest: string; basisDigest: string;
}>;
export type TaskAssignment = { taskId: string; taskDigest: string; workerId: string; seedCommit: string; assignmentId?: string; groupId?: string; canonicalCommit?: string;
  dependencies?: DeliveryRecord['dependencies']; routeId?: string; connectionCheck?: TaskConnectionCheck;
  /** Historical seed diagnostic for this assignment; never a model failure or accepted proof. */
  canonicalProbe?: Readonly<{ evidence: 'advisory-canonical-check'; proofAcceptance: 'not-accepted';
    sourceCommit: string; environmentDigest: string; verificationStatus: TaskProof['verification']['status'];
    receiptIds: readonly string[]; feedback: string }>;
  /** Actual prompt inputs, frozen when a research turn starts. */
  researchBasis?: ResearchBasis };
export type TaskRecord = { task: CooperativeTask; status: 'pending' | 'running' | 'blocked' | 'conditional' | 'delivered' | 'integrated' | 'completed';
  /** Host-owned advisory work; never supplied by a model plan. */
  capacityExploration?: CapacityExploration;
  attempts: number; assignment?: TaskAssignment; proof?: TaskProof; integratedCheck?: TaskProof; feedback?: string; finding?: string;
  researchCompletion?: ResearchRecord;
  /** One source-contract correction belongs to this assignment, not equivalent mathematical tasks. */
  sourceRepair?: { taskDigest: string; workerId: string; assignmentId?: string; seedCommit: string;
    pending: boolean; startedAttempt?: number };
  pendingValidation?: { id: string; taskDigest: string; canonicalCommit: string; environmentDigest: string; problemReceiptDigest: string; proof?: boolean };
  typePreflight?: TaskTypePreflight;
  routeParking?: string[]; parkedRoutes?: Record<string, string[]>; alternativeRoutes?: readonly ProofRoute[] };
export type CapacityOwnershipCandidate = Readonly<{ taskId: string; taskDigest: string; ownerId: string;
  eligibleWorkerIds: readonly string[] }>;
export type CooperativeAction = { kind: 'lead' | 'assemble'; seedCommit: string; planVersion?: string; planningInputDigest?: string;
  initialPlanNonce?: string;
  planNonce?: string;
  /** A bounded inbox/capacity decision; the complete graph remains host-owned. */
  coordination?: true;
  /** Stable mathematical responsibility, independent of inbox freshness or graph presentation. */
  responsibilityDigest?: string;
  /** Advisory capacity at dispatch; never infer this request from a later archive receipt. */
  capacityRefill?: Readonly<{ requestId?: string; inputDigest: string; workerIds: readonly string[]; requestedAt: number;
    ownershipCandidates?: readonly CapacityOwnershipCandidate[] }>;
  /** Host scheduling recovery only; never a mathematical blocker or proof verdict. */
  stagnationRecovery?: Readonly<{ requestId?: string; inputDigest: string; taskIds: readonly string[]; workerIds: readonly string[]; requestedAt: number;
    reason: 'advisory-no-durable-progress' | 'frontier-not-decomposed' }>;
  handoffIds?: readonly string[];
  handoffActivations?: Readonly<Record<string, string>>;
  challengeIds?: readonly string[];
  challengeActivations?: Readonly<Record<string, string>>;
  recovery?: { id: string; taskIds: string[]; goalIds: string[] } } |
  { kind: 'review'; seedCommit: string; sourceDigest: string; assignmentId?: string } | { kind: 'task'; assignment: TaskAssignment; task: CooperativeTask } | StatementAction;

export const taskVersion = (task: CooperativeTask) => {
  const { status: _status, ownerId: _owner, statementReview: _review, informalStatement: _intent, ...mathematics } = task;
  return mathDigest(canonicalMathJson(mathematics));
};
/** Planning revisions still supersede assignments; checked sources can be revalidated separately. */
export const taskProofContractVersion = (task: CooperativeTask) => {
  if (isAdvisoryTask(task)) return taskVersion(task);
  const { objective: _objective, revision: _revision, ...contract } = task;
  return taskVersion(contract as CooperativeTask);
};
// Object identity is process-local: archived references never authorize narrower dependency checks.
const checkedReferences = new WeakSet<TaskProof>();
export function taskReferenceDependencies(node: TaskRecord): DeliveryRecord['dependencies'] | undefined {
  const proof = node.integratedCheck, references = proof?.references;
  return !node.pendingValidation && node.status === 'integrated' && proof?.passed && !proof.conditions?.length &&
    proof.taskDigest === taskVersion(node.task) && checkedReferences.has(proof) && references?.tasks &&
    references.inputs.every(input => input.name) ? references.tasks : undefined;
}
export const markTaskReferences = (proof: TaskProof) => checkedReferences.add(proof);
export const hasTaskReferences = (proof: TaskProof) => checkedReferences.has(proof);
// Restored JSON cannot authorize final-candidate dispatch before the host rechecks it.
const freshTaskAcceptances = new WeakMap<TaskProof, string>();
const acceptanceIdentity = (proof: TaskProof) => canonicalMathJson({ commit: proof.commit, sourceDigest: proof.sourceDigest,
  taskDigest: proof.taskDigest, conditions: proof.conditions, projection: proof.projection, verification: proof.verification && {
    status: proof.verification.status, targetCommit: proof.verification.targetCommit,
    receipts: proof.verification.results.map(result => [result.receiptId, result.status, result.targetCommit]) } });
export const markTaskAcceptance = (proof: TaskProof) => {
  if (proof.passed && proof.verification?.status === 'kernel_verified') freshTaskAcceptances.set(proof, acceptanceIdentity(proof));
};
export const hasTaskAcceptance = (proof: TaskProof) => freshTaskAcceptances.get(proof) === acceptanceIdentity(proof);
/** A passed, unconditional integration of exactly `taskDigest` that this host process accepted. */
export const freshlyAccepted = (node: TaskRecord | undefined, taskDigest: string): boolean => node?.status === 'integrated' &&
  !!node.integratedCheck?.passed && node.integratedCheck.taskDigest === taskDigest && !node.integratedCheck.conditions?.length &&
  hasTaskAcceptance(node.integratedCheck);
/** Integrated with a passing, unconditional check of the current task version; no acceptance receipt is required. */
export const checkedUnconditionally = (node: TaskRecord | undefined): boolean => node?.status === 'integrated' &&
  !!node.integratedCheck?.passed && node.integratedCheck.taskDigest === taskVersion(node.task) && !node.integratedCheck.conditions?.length;
export const openRoutes = (node: TaskRecord) => node.alternativeRoutes?.filter(route => !node.parkedRoutes?.[route.id]?.length) ?? [];
/** Every OR branch is parked; false for a task without branches. */
export const allRoutesParked = (node: TaskRecord): boolean =>
  Boolean(node.alternativeRoutes?.length && node.alternativeRoutes.every(route => node.parkedRoutes?.[route.id]?.length));
/** The route group is active and below its turn cap. */
export const groupOpen = (record: RouteRecord | undefined): record is RouteRecord =>
  Boolean(record && record.group.status === 'active' && record.turns < (record.group.maxTurns ?? Infinity));

/** Compute invalidation before changing assignments or emitting any notifications. */
export function invalidatedTaskIds(previous: readonly TaskRecord[], tasks: readonly CooperativeTask[],
  changedGroups: ReadonlySet<string>, dependencies: ReadonlyMap<string, readonly string[]>, changedTasks: ReadonlySet<string> = new Set(),
  version: (task: CooperativeTask) => string = taskVersion): Set<string> {
  const proposed = new Map(tasks.map(task => [task.id, version(task)]));
  const invalidated = new Set(previous.filter(node => changedTasks.has(node.task.id) || changedGroups.has(taskGroup(node.task)) ||
    proposed.get(node.task.id) !== version(node.task)).map(node => node.task.id));
  const consumers = new Map<string, string[]>();
  for (const task of tasks) for (const id of dependencies.get(task.id) ?? task.dependsOn) {
    const list = consumers.get(id) ?? []; list.push(task.id); consumers.set(id, list);
  }
  const queue = [...invalidated];
  for (let i = 0; i < queue.length; i++) for (const id of consumers.get(queue[i]) ?? []) {
    if (!invalidated.has(id)) { invalidated.add(id); queue.push(id); }
  }
  return invalidated;
}

export const assignmentDeliveryFile = (assignment: TaskAssignment) => `DELIVERIES-${mathDigest(canonicalMathJson({
  taskId: assignment.taskId, taskDigest: assignment.taskDigest, seedCommit: assignment.seedCommit,
  ...(assignment.assignmentId === undefined ? {} : { assignmentId: assignment.assignmentId }) }))}.jsonl`;

/** An explicit initial-plan event is scoped to one host-created Lead dispatch. */
export const initialPlanDeliveryFile = (action: CooperativeAction) => action.kind === 'lead' && action.initialPlanNonce
  ? `DELIVERIES-${mathDigest(canonicalMathJson({ kind: 'initial-plan', nonce: action.initialPlanNonce,
    seedCommit: action.seedCommit, planVersion: action.planVersion, planningInputDigest: action.planningInputDigest }))}.jsonl`
  : undefined;

/** Later plans also publish once per frozen dispatch, with an explicit compare-and-swap base. */
export const leadPlanDeliveryFile = (action: CooperativeAction) => initialPlanDeliveryFile(action) ??
  (action.kind === 'lead' && action.planNonce
    ? `DELIVERIES-${mathDigest(canonicalMathJson({ kind: 'plan', nonce: action.planNonce,
      seedCommit: action.seedCommit, planVersion: action.planVersion, planningInputDigest: action.planningInputDigest }))}.jsonl`
    : undefined);

export const isAdvisoryTask = (task: CooperativeTask) => task.kind === 'research' || task.kind === 'sketch';
export const isFinalCandidateReview = (task: CooperativeTask) => isAdvisoryTask(task) &&
  (task.reviewScope === 'final-candidate' || task.id === 'independent_candidate_review');
export const isFeasibilityReview = (task: CooperativeTask) => isAdvisoryTask(task) &&
  task.reviewScope === 'feasibility' && !isFinalCandidateReview(task);
/** Pin a deferred decision's `waitsOn` ids to their current typed, non-advisory task versions. `invalid` rejects a malformed
 * list; `invalidTask` prefixes the id that names no such task. */
export function parseWaitsOn(value: unknown, deferred: boolean, task: (id: string) => CooperativeTask | undefined, invalid: string,
  invalidTask: string): { taskId: string; taskDigest: string }[] | undefined {
  if (value === undefined) return undefined;
  if (!deferred || !Array.isArray(value) || !value.length || new Set(value).size !== value.length ||
      value.some(id => typeof id !== 'string')) throw new Error(invalid);
  return value.map((taskId: string) => {
    const proposed = task(taskId);
    if (!proposed || isAdvisoryTask(proposed) || proposed.kind === 'lemma' && !proposed.type?.trim())
      throw new Error(invalidTask + taskId);
    return { taskId, taskDigest: taskVersion(proposed) };
  });
}

const validId = (value: unknown) => typeof value === 'string' && /^[a-zA-Z0-9_-]{1,64}$/u.test(value);
const optionalFields = (value: any, keys: readonly string[]) =>
  Object.fromEntries(keys.filter(key => value[key] !== undefined).map(key => [key, value[key]]));

export function parseCooperationPlan(problem: SolverProblem, value: any): { tasks: CooperativeTask[]; groups: RouteGroup[]; proofRoutes?: ProofRoute[] } {
  if (!value || !Array.isArray(value.tasks) || value.tasks.length < 1)
    throw new Error('math_plan_invalid');
  // Leads routinely serialize an empty explicit list; it carries the same meaning as omitting it.
  const rawGroups = !Array.isArray(value.groups) || !value.groups.length
    ? [{ id: 'main', objective: 'Prove the original problem' }] : value.groups;
  const groups: RouteGroup[] = rawGroups.map((group: any) => {
    if (!group || !validId(group.id) ||
        typeof group.objective !== 'string' || !group.objective.trim() ||
        !['active', 'paused', 'stopped'].includes(group.status ?? 'active') ||
        !Number.isSafeInteger(group.revision ?? 0) || (group.revision ?? 0) < 0 ||
        (group.engineerId !== undefined && (!validId(group.engineerId))) ||
        (group.maxTurns !== undefined && (!Number.isSafeInteger(group.maxTurns) || group.maxTurns < 0)) ||
        (group.maxConcurrent !== undefined && (!Number.isSafeInteger(group.maxConcurrent) || group.maxConcurrent < 1)))
      throw new Error('math_plan_invalid_group');
    return { id: group.id, objective: group.objective, status: group.status ?? 'active', revision: group.revision ?? 0,
      ...optionalFields(group, ['engineerId', 'maxTurns', 'maxConcurrent']) };
  });
  if (new Set(groups.map(group => group.id)).size !== groups.length) throw new Error('math_plan_duplicate_group');
  const tasks: CooperativeTask[] = value.tasks.map((value: any) => {
    // A research request with an exact proof target is proof work, regardless of its label.
    if (value && ['research', 'sketch'].includes(value.kind) && value.theoremName &&
        typeof value.type === 'string' && value.type.trim())
      value = { ...value, kind: 'lemma' };
    const task = value && { ...value, dependsOn: value.dependsOn ?? [], proofPath: value.proofPath ??
      (value.kind === 'goal' ? problem.targets.find(target => target.theoremName === value.theoremName)?.proofPath :
        problem.ownedFiles.filter(file => file.endsWith('.lean')).length === 1 ? problem.ownedFiles.find(file => file.endsWith('.lean')) : undefined) };
    if (!task || !validId(task.id) ||
        !['research', 'sketch', 'lemma', 'goal'].includes(task.kind) || typeof task.objective !== 'string' ||
        !task.objective.trim() || !Array.isArray(task.dependsOn) ||
        task.dependsOn.some((id: unknown) => typeof id !== 'string') ||
        !Number.isSafeInteger(task.revision ?? 0) || (task.revision ?? 0) < 0)
      throw new Error('math_plan_invalid_task');
    if ((task.status !== undefined && !['active', 'paused', 'stopped'].includes(task.status)) ||
        (task.conditional !== undefined && (typeof task.conditional !== 'boolean' || isAdvisoryTask(task))) ||
        (task.statementReview !== undefined && (typeof task.statementReview !== 'boolean' || isAdvisoryTask(task))) ||
        (task.reviewScope !== undefined && (!isAdvisoryTask(task) ||
          !['final-candidate', 'feasibility'].includes(task.reviewScope))) ||
        (task.informalStatement !== undefined && (typeof task.informalStatement !== 'string' || !task.informalStatement.trim())) ||
        (task.statementReview === true && !task.informalStatement) ||
        (task.ownerId !== undefined && (!validId(task.ownerId))) ||
        (task.premises !== undefined && (!Array.isArray(task.premises) ||
          task.premises.some((premise: unknown) => typeof premise !== 'string')))) throw new Error('math_plan_invalid_task');
    if (!groups.some(group => group.id === (task.groupId ?? 'main')) ||
        (task.sharing !== undefined && !['group', 'problem'].includes(task.sharing))) throw new Error('math_plan_invalid_task_group');
    if (!isAdvisoryTask(task) && (!problem.ownedFiles.includes(task.proofPath) ||
        !isSimpleLeanName(task.theoremName)))
      throw new Error('math_plan_invalid_proof_target: ' + JSON.stringify({ taskId: task.id,
        proofPath: task.proofPath, theoremName: task.theoremName }) + '. Use an owned proofPath and an ordinary qualified Lean name.');
    if (task.kind === 'goal' && !problem.targets.some(target => target.proofPath === task.proofPath && target.theoremName === task.theoremName))
      throw new Error('math_plan_changed_original_target');
    if (task.kind === 'lemma' && typeof task.type === 'string' && task.type.trim() === 'FULL_CLOSED_LEAN_TYPE')
      throw new Error('math_plan_placeholder_helper_type: supply the actual closed Lean type, or use an untyped research/sketch task for advisory findings.');
    if (task.kind === 'lemma' && (typeof task.type !== 'string' || !task.type.trim() ||
        Object.values(problem.declarations).some(items => items.some(item => item.name.split('.').at(-1) === task.theoremName.split('.').at(-1)))))
      throw new Error('math_plan_invalid_helper_type');
    return { id: task.id, kind: task.kind, objective: task.objective, dependsOn: [...new Set<string>(task.dependsOn)],
      revision: task.revision ?? 0, ...(isAdvisoryTask(task) ? {} : { proofPath: task.proofPath, theoremName: task.theoremName }),
      ...(task.kind === 'lemma' ? { type: task.type } : {}),
      ...optionalFields(task, ['conditional', 'statementReview', 'informalStatement', 'reviewScope', 'status', 'ownerId', 'premises', 'groupId']),
      ...(task.sharing === undefined ? groups.length > 1 ? { sharing: 'group' } : {} : { sharing: task.sharing }) };
  });
  if (new Set(tasks.map(task => task.id)).size !== tasks.length ||
      new Set(tasks.filter(task => !isAdvisoryTask(task)).map(task => task.theoremName!.split('.').at(-1))).size !== tasks.filter(task => !isAdvisoryTask(task)).length)
    throw new Error('math_plan_duplicate_task');
  if (problem.targets.some(target => tasks.filter(task => task.kind === 'goal' && task.proofPath === target.proofPath && task.theoremName === target.theoremName).length !== 1))
    throw new Error('math_plan_incomplete_original_coverage');
  const byId = new Map(tasks.map(task => [task.id, task]));
  const visiting = new Set<string>(), visited = new Set<string>();
  const visit = (id: string) => {
    if (visiting.has(id)) throw new Error('math_plan_dependency_cycle');
    if (visited.has(id)) return;
    const task = byId.get(id);
    if (!task) throw new Error('math_plan_missing_dependency');
    visiting.add(id); task.dependsOn.forEach(visit); visiting.delete(id); visited.add(id);
  };
  tasks.forEach(task => visit(task.id));
  for (const task of tasks) for (const id of task.dependsOn) {
    const dependency = byId.get(id)!;
    if (taskGroup(task) !== taskGroup(dependency) && dependency.sharing === 'group') throw new Error('math_plan_dependency_not_shared');
    if (task.kind === 'goal' && dependency.kind === 'goal' && task.proofPath === dependency.proofPath) {
      const declarations = problem.declarations[task.proofPath!]!;
      const position = (name: string) => declarations.findIndex(item => item.name.split('.').at(-1) === name.split('.').at(-1));
      if (position(dependency.theoremName!) > position(task.theoremName!))
        throw new Error(`math_plan_forward_goal_dependency: ${task.id} precedes ${dependency.id} in ${task.proofPath}. ` +
          'Extract the shared argument into a named lemma before both original goals; preserve original declaration order and other goal proofs.');
    }
  }
  const proofRoutes = parseProofRoutes(value.proofRoutes, tasks);
  return { tasks, groups, ...(proofRoutes.length ? { proofRoutes } : {}) };
}
