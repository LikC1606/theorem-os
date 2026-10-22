import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { inspectLeanDeclarationRegions, inspectLeanSource, inspectScopedLeanDeclarations } from '../math/leanSource';
import { isAdvisoryTask, taskGroup, taskReferenceDependencies, taskVersion,
  type CooperativeTask, type RouteRecord, type TaskAssignment, type TaskConnectionCheck, type TaskRecord } from './tasks';

type ConnectionIdentity = Pick<TaskConnectionCheck, 'environmentDigest' | 'problemReceiptDigest'>;
const referencesDigest = (assignment: TaskAssignment) => mathDigest(canonicalMathJson(assignment.dependencies ?? []));
const basisDigest = ({ basisDigest: _basis, ...basis }: TaskConnectionCheck) => mathDigest(canonicalMathJson(basis));
const routesDigest = (taskId: string, tasks: readonly TaskRecord[]) => mathDigest(canonicalMathJson(tasks
  .flatMap(node => node.alternativeRoutes ?? []).filter(route => route.targetTaskId === taskId ||
    route.closingTaskId === taskId || route.prerequisiteTaskIds.includes(taskId)).toSorted((a, b) => a.id.localeCompare(b.id))));

/** Recover missing assumptions from an immutable historical seed, with current contracts checked exactly. */
export function taskInputsMissingFromSeed(inputs: TaskConnectionCheck['inputs'], tasks: readonly TaskRecord[],
  readSource: (task: CooperativeTask) => string): TaskConnectionCheck['inputs'] {
  return inputs.filter(reference => {
    const dependency = tasks.find(node => node.task.id === reference.taskId)?.task;
    if (!dependency || dependency.kind !== 'lemma' || !dependency.type?.trim() || taskVersion(dependency) !== reference.taskDigest)
      throw new Error('math_task_condition_version_invalid');
    const source = readSource(dependency), declarations = inspectScopedLeanDeclarations(source).filter(declaration =>
      declaration.qualifiedName === dependency.theoremName || !dependency.theoremName!.includes('.') && declaration.name === dependency.theoremName);
    if (!declarations.length) return true;
    if (declarations.length !== 1) throw new Error('math_task_condition_version_invalid');
    if (declarations[0].kind !== 'theorem') return true;
    const region = inspectLeanDeclarationRegions(source).find(region => region.startOffset === declarations[0].startOffset)!;
    const inspected = inspectLeanSource(source.slice(region.startOffset, region.endOffset));
    return inspected.sorryCount > 0 || inspected.admitCount > 0;
  });
}

/** A declared dependency is a proposed application; its inputs need not already have proofs. */
export function automaticTaskConnection(task: CooperativeTask, tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  const nodes = new Map(tasks.map(node => [node.task.id, node])), node = nodes.get(task.id);
  if (isAdvisoryTask(task) || task.conditional === false || node?.alternativeRoutes?.length || node?.pendingValidation ||
      !task.dependsOn.length || task.kind !== 'goal' && !tasks.some(consumer => {
        if (isAdvisoryTask(consumer.task) || ['integrated', 'completed'].includes(consumer.status) ||
            consumer.routeParking?.length || (consumer.task.status ?? 'active') !== 'active') return false;
        const group = groups?.find(record => record.group.id === taskGroup(consumer.task));
        if (groups && (!group || group.group.status !== 'active' || group.turns >= (group.group.maxTurns ?? Infinity))) return false;
        return consumer.task.dependsOn.includes(task.id) || consumer.alternativeRoutes?.some(route =>
          route.closingTaskId === task.id && !consumer.parkedRoutes?.[route.id]?.length);
      })) return false;
  let unfinished = false;
  const visiting = new Set<string>(), visited = new Set<string>();
  const available = (id: string): boolean => {
    if (visiting.has(id)) return false;
    if (visited.has(id)) return true;
    const input = nodes.get(id);
    if (!input || input.pendingValidation || input.routeParking?.length || input.status === 'blocked') return false;
    const checked = ['integrated', 'completed'].includes(input.status);
    if (!checked && (input.task.kind !== 'lemma' || !input.task.type?.trim() ||
        (input.task.status ?? 'active') !== 'active' || taskGroup(input.task) !== taskGroup(task) && input.task.sharing === 'group')) return false;
    const group = groups?.find(record => record.group.id === taskGroup(input.task));
    if (!checked && groups && (!group || group.group.status !== 'active' || group.turns >= (group.group.maxTurns ?? Infinity))) return false;
    if (!checked) unfinished = true;
    visiting.add(id);
    const ready = (taskReferenceDependencies(input)?.map(reference => reference.taskId) ?? input.task.dependsOn).every(available);
    visiting.delete(id);
    if (ready) visited.add(id);
    return ready;
  };
  return task.dependsOn.every(available) && unfinished;
}

/** The permission belongs to a fixed host dispatch, never to a mutated task contract. */
export function createTaskConnectionCheck(task: CooperativeTask, assignment: TaskAssignment,
  tasks: readonly TaskRecord[], identity: ConnectionIdentity, readSeedSource?: (task: CooperativeTask) => string): TaskConnectionCheck {
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  const inputs = (assignment.dependencies ?? []).filter(reference => {
    const input = nodes.get(reference.taskId);
    return input?.task.kind === 'lemma' && Boolean(input.task.type?.trim()) && taskVersion(input.task) === reference.taskDigest;
  }).map(reference => ({ ...reference }));
  const missing = new Set(readSeedSource ? taskInputsMissingFromSeed(inputs, tasks, readSeedSource).map(input => input.taskId) : []);
  const check: TaskConnectionCheck = { schema: 'theorem-os.consumer-connection.v1',
    consumer: { taskId: task.id, taskDigest: taskVersion(task) }, inputs, seedCommit: assignment.seedCommit,
    assumedInputs: inputs.filter(reference => nodes.get(reference.taskId)!.status !== 'integrated' || missing.has(reference.taskId)),
    workerId: assignment.workerId, ...(assignment.assignmentId !== undefined ? { assignmentId: assignment.assignmentId } : {}),
    dependenciesDigest: referencesDigest(assignment), ...(assignment.routeId ? { routeId: assignment.routeId } : {}),
    routesDigest: routesDigest(task.id, tasks), ...identity, basisDigest: '' };
  return { ...check, basisDigest: basisDigest(check) };
}

/** M2 still checks every assumption's exact type and version and never accepts a conditional goal. */
export function hasTaskConnectionCheck(task: CooperativeTask, assignment: TaskAssignment): boolean {
  const check = assignment.connectionCheck;
  return Boolean(check && !isAdvisoryTask(task) && task.conditional !== false &&
    check.schema === 'theorem-os.consumer-connection.v1' && check.consumer?.taskId === task.id &&
    check.consumer.taskDigest === taskVersion(task) && assignment.taskId === task.id &&
    assignment.taskDigest === check.consumer.taskDigest && check.seedCommit === assignment.seedCommit &&
    check.routeId === assignment.routeId && check.dependenciesDigest === referencesDigest(assignment) &&
    (check.workerId === undefined || check.workerId === assignment.workerId) &&
    (check.assignmentId === undefined || check.assignmentId === assignment.assignmentId) &&
    check.environmentDigest && check.problemReceiptDigest && Array.isArray(check.inputs) && check.inputs.length &&
    new Set(check.inputs.map(input => input.taskId)).size === check.inputs.length &&
    check.inputs.every(input => assignment.dependencies?.some(reference => reference.taskId === input.taskId &&
      reference.taskDigest === input.taskDigest)) &&
    (check.assumedInputs === undefined || Array.isArray(check.assumedInputs) && check.workerId === assignment.workerId &&
      check.assignmentId === assignment.assignmentId &&
      new Set(check.assumedInputs.map(input => input.taskId)).size === check.assumedInputs.length &&
      check.assumedInputs.every(input => check.inputs.some(reference => reference.taskId === input.taskId &&
        reference.taskDigest === input.taskDigest))) && check.basisDigest === basisDigest(check));
}

export function taskConnectionCheckCurrent(task: CooperativeTask, assignment: TaskAssignment,
  tasks: readonly TaskRecord[], identity?: ConnectionIdentity): boolean {
  if (!hasTaskConnectionCheck(task, assignment)) return false;
  const check = assignment.connectionCheck!, nodes = new Map(tasks.map(node => [node.task.id, node]));
  return (!identity || check.environmentDigest === identity.environmentDigest &&
    check.problemReceiptDigest === identity.problemReceiptDigest) && check.routesDigest === routesDigest(task.id, tasks) &&
    check.inputs.every(reference => {
      const input = nodes.get(reference.taskId);
      return input?.task.kind === 'lemma' && Boolean(input.task.type?.trim()) && taskVersion(input.task) === reference.taskDigest;
    }) && (assignment.dependencies ?? []).every(reference => {
      const input = nodes.get(reference.taskId);
      return Boolean(input && taskVersion(input.task) === reference.taskDigest);
    });
}

/** Lifetime attempt counts include obsolete contracts and must not suppress their first application check. */
export function freshTaskConnection(node: TaskRecord, tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  return !node.proof && !node.assignment && (Boolean(node.task.conditional) || automaticTaskConnection(node.task, tasks, groups));
}
