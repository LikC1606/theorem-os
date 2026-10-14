import type { SolverProblem } from './problem';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import type { TaskProof } from './cooperativeProof';
import type { StatementAction } from './statementReview';

export type CooperativeTask = Readonly<{ id: string; kind: 'research' | 'sketch' | 'lemma' | 'goal'; objective: string;
  dependsOn: readonly string[]; revision: number; proofPath?: string; theoremName?: string; type?: string;
  groupId?: string; sharing?: 'group' | 'problem'; status?: 'active' | 'paused' | 'stopped'; ownerId?: string; premises?: readonly string[];
  conditional?: boolean; statementReview?: boolean; informalStatement?: string }>;
export type RouteGroup = Readonly<{ id: string; objective: string; status: 'active' | 'paused' | 'stopped'; revision: number;
  engineerId?: string; maxTurns?: number; maxConcurrent?: number }>;
export type RouteRecord = { group: RouteGroup; turns: number; busy?: number };
export const taskGroup = (task: CooperativeTask): string => task.groupId ?? 'main';
export type TaskAssignment = { taskId: string; taskDigest: string; workerId: string; seedCommit: string; groupId?: string; canonicalCommit?: string;
  dependencies?: DeliveryRecord['dependencies'] };
export type TaskRecord = { task: CooperativeTask; status: 'pending' | 'running' | 'blocked' | 'conditional' | 'delivered' | 'integrated' | 'completed';
  attempts: number; assignment?: TaskAssignment; proof?: TaskProof; integratedCheck?: TaskProof; feedback?: string; finding?: string };
export type CooperativeAction = { kind: 'lead' | 'assemble'; seedCommit: string; planVersion?: string } |
  { kind: 'review'; seedCommit: string; sourceDigest: string } | { kind: 'task'; assignment: TaskAssignment; task: CooperativeTask } | StatementAction;

export const taskVersion = (task: CooperativeTask) => {
  const { status: _status, ownerId: _owner, ...mathematics } = task;
  return mathDigest(canonicalMathJson(mathematics));
};
// Object identity is process-local: archived references never authorize narrower dependency checks.
const checkedReferences = new WeakSet<TaskProof>();
export function taskReferenceDependencies(node: TaskRecord): DeliveryRecord['dependencies'] | undefined {
  const proof = node.integratedCheck, references = proof?.references;
  return node.status === 'integrated' && proof?.passed && !proof.conditions?.length &&
    proof.taskDigest === taskVersion(node.task) && checkedReferences.has(proof) && references?.tasks &&
    references.inputs.every(input => input.name) ? references.tasks : undefined;
}
export const markTaskReferences = (proof: TaskProof) => checkedReferences.add(proof);
export const hasTaskReferences = (proof: TaskProof) => checkedReferences.has(proof);

/** Compute invalidation before changing assignments or emitting any notifications. */
export function invalidatedTaskIds(previous: readonly TaskRecord[], tasks: readonly CooperativeTask[],
  changedGroups: ReadonlySet<string>, dependencies: ReadonlyMap<string, readonly string[]>): Set<string> {
  const proposed = new Map(tasks.map(task => [task.id, taskVersion(task)]));
  const invalidated = new Set(previous.filter(node => changedGroups.has(taskGroup(node.task)) ||
    proposed.get(node.task.id) !== taskVersion(node.task)).map(node => node.task.id));
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
  taskId: assignment.taskId, taskDigest: assignment.taskDigest, seedCommit: assignment.seedCommit }))}.jsonl`;

export const isAdvisoryTask = (task: CooperativeTask) => task.kind === 'research' || task.kind === 'sketch';

const validId = (value: unknown) => typeof value === 'string' && /^[a-zA-Z0-9_-]{1,64}$/u.test(value);
const optionalFields = (value: any, keys: readonly string[]) =>
  Object.fromEntries(keys.filter(key => value[key] !== undefined).map(key => [key, value[key]]));

export function parseCooperationPlan(problem: SolverProblem, value: any): { tasks: CooperativeTask[]; groups: RouteGroup[] } {
  if (!value || !Array.isArray(value.tasks) || value.tasks.length < 1)
    throw new Error('math_plan_invalid');
  const rawGroups = value.groups ?? [{ id: 'main', objective: 'Prove the original problem' }];
  if (!Array.isArray(rawGroups) || !rawGroups.length) throw new Error('math_plan_invalid_groups');
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
        (task.informalStatement !== undefined && (typeof task.informalStatement !== 'string' || !task.informalStatement.trim())) ||
        (task.statementReview === true && !task.informalStatement) ||
        (task.ownerId !== undefined && (!validId(task.ownerId))) ||
        (task.premises !== undefined && (!Array.isArray(task.premises) ||
          task.premises.some((premise: unknown) => typeof premise !== 'string')))) throw new Error('math_plan_invalid_task');
    if (!groups.some(group => group.id === (task.groupId ?? 'main')) ||
        (task.sharing !== undefined && !['group', 'problem'].includes(task.sharing))) throw new Error('math_plan_invalid_task_group');
    if (!isAdvisoryTask(task) && (!problem.ownedFiles.includes(task.proofPath) ||
        typeof task.theoremName !== 'string' || !/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(task.theoremName)))
      throw new Error('math_plan_invalid_proof_target');
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
      ...optionalFields(task, ['conditional', 'statementReview', 'informalStatement', 'status', 'ownerId', 'premises', 'groupId']),
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
  }
  return { tasks, groups };
}
