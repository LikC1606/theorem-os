import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { routeBlockerBasis } from './routeControl';
import { checkedUnconditionally, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export const CAPACITY_EXPLORATION_FOCUSES = ['construction', 'interface', 'decomposition', 'boundary'] as const;
export type CapacityExplorationFocus = typeof CAPACITY_EXPLORATION_FOCUSES[number];
export type CapacityExploration = Readonly<{
  schema: 'theorem-os.capacity-exploration.v1';
  targetTaskId: string; targetTaskDigest: string; inputDigest: string; focus: CapacityExplorationFocus;
  workerId: string; taskDigest: string; environmentDigest: string; problemReceiptDigest: string;
}>;
type Identity = Readonly<{ environmentDigest: string; problemReceiptDigest: string }>;

const schema = 'theorem-os.capacity-exploration.v1';
const hash = (value: unknown) => mathDigest(canonicalMathJson(value));
const focusValid = (focus: unknown): focus is CapacityExplorationFocus =>
  CAPACITY_EXPLORATION_FOCUSES.includes(focus as CapacityExplorationFocus);
const nonempty = (value: unknown): value is string => typeof value === 'string' && Boolean(value.trim());

/** Host records remain in the execution graph, but never become the Lead's base plan. */
export function plannedTaskRecords(tasks: readonly TaskRecord[]): TaskRecord[] {
  return tasks.filter(node => !node.capacityExploration);
}

/** Only mathematical inputs in this consumer's dependency cone define another investigation. */
export function capacityExplorationInput(target: CooperativeTask, tasks: readonly TaskRecord[], identity: Identity): string {
  const explorations = new Set(tasks.filter(node => node.capacityExploration).map(node => node.task.id));
  const withoutExplorations = (task: CooperativeTask): CooperativeTask =>
    task.dependsOn.some(id => explorations.has(id)) ? { ...task, dependsOn: task.dependsOn.filter(id => !explorations.has(id)) } : task;
  const mathematicalTasks = plannedTaskRecords(tasks).map(node => ({ ...node, task: withoutExplorations(node.task) }));
  const routes = mathematicalTasks.find(node => node.task.id === target.id)?.alternativeRoutes ?? [];
  // Inspect every declared route rather than whichever route a worker happens to hold.
  const inputs = [...new Set([...target.dependsOn, ...routes.flatMap(route =>
    [...route.prerequisiteTaskIds, route.closingTaskId])])].filter(id => !explorations.has(id));
  const consumer = { ...target, dependsOn: inputs };
  return hash({ schema, targetTaskId: target.id,
    basis: routeBlockerBasis(consumer, mathematicalTasks, identity.environmentDigest, identity.problemReceiptDigest, '') });
}

/** Issuing every method is not exhaustion while any current investigation is unfinished. */
export function exhaustedCapacityExploration(target: CooperativeTask, tasks: readonly TaskRecord[], identity: Identity,
  inputs: readonly { targetTaskId: string; inputDigest: string; focus: CapacityExplorationFocus }[] = []): boolean {
  const inputDigest = capacityExplorationInput(target, tasks, identity);
  const current = tasks.filter(node => node.capacityExploration?.targetTaskId === target.id &&
    node.capacityExploration.inputDigest === inputDigest && currentCapacityExploration(node, tasks, identity));
  return current.every(node => node.status === 'completed') && CAPACITY_EXPLORATION_FOCUSES.every(focus =>
    inputs.some(input => input.targetTaskId === target.id && input.inputDigest === inputDigest && input.focus === focus) &&
    current.some(node => node.capacityExploration!.focus === focus && node.status === 'completed'));
}

const taskId = (marker: Pick<CapacityExploration, 'targetTaskId' | 'inputDigest' | 'focus' | 'environmentDigest' | 'problemReceiptDigest'>) =>
  'capacity_' + hash({ schema, targetTaskId: marker.targetTaskId, inputDigest: marker.inputDigest,
    focus: marker.focus, environmentDigest: marker.environmentDigest, problemReceiptDigest: marker.problemReceiptDigest }).slice(0, 40);

function targetAvailable(node: TaskRecord): boolean {
  return !node.capacityExploration && ['lemma', 'goal'].includes(node.task.kind) &&
    (node.task.kind === 'goal' || nonempty(node.task.type) && node.task.type.trim() !== 'FULL_CLOSED_LEAN_TYPE') &&
    nonempty(node.task.theoremName) && nonempty(node.task.proofPath) &&
    (node.task.status ?? 'active') === 'active' && node.status !== 'completed' && !checkedUnconditionally(node);
}

const focusInstructions: Record<CapacityExplorationFocus, string> = {
  construction: 'Explore a concrete construction or witness for this consumer. Give explicit definitions and a candidate ' +
    'argument, use small Lean scratch probes for uncertain steps, and identify the precise remaining proof obligation.',
  interface: 'Audit the exact Lean interfaces needed by this consumer. Locate applicable declarations or propose the smallest ' +
    'closed helper types, spell out every premise, and show their exact application to the consumer.',
  decomposition: 'Find an independent decomposition of this consumer into a small dependency DAG of exact typed obligations. ' +
    'Give the closing derivation back to the consumer and distinguish new obligations from work already in flight.',
  boundary: 'Audit boundary cases and hypotheses of this consumer: degenerate inputs, empty cases, casts and any ' +
    'finite/infinite distinction that actually applies. Record concrete Lean probes or precise unresolved conditions.',
};

function explorationTask(target: CooperativeTask, workerId: string, inputDigest: string,
  identity: Identity, focus: CapacityExplorationFocus): CooperativeTask {
  const marker = { targetTaskId: target.id, inputDigest, focus, ...identity };
  return { id: taskId(marker), kind: 'research', revision: 0, status: 'active', ownerId: workerId,
    dependsOn: [target.id], groupId: taskGroup(target), sharing: target.sharing ?? 'problem',
    objective: `Capacity exploration (${focus}) for consumer ${target.id}: ${target.theoremName}.\n` +
      `Consumer file: ${target.proofPath}. ` + (target.type?.trim() ? `Exact consumer type:\n${target.type}\n` :
        'Use the frozen original goal declaration supplied in the mandatory problem context.\n') +
      focusInstructions[focus] + '\n' +
      'Read the consumer and its declared inputs, including existing findings and in-flight work, before choosing an approach. ' +
      'Keep the original problem and consumer statement fixed. Do not repeat an existing investigation. ' +
      'Lean scratch experiments outside owned Lean sources are permitted. Deliver advisory findings only in RESEARCH.md; ' +
      'do not change owned Lean files. State the concrete result, reproducible probe commands and outcomes, remaining gaps, ' +
      'and how the result would be used by this exact consumer. If a new proof obligation is justified, publish precise ' +
      'lemmaRequests with full closed Lean types, premises and existing input dependencies in this group. ' +
      'Explain the application to the consumer, without assuming the unresolved consumer as a premise of its own helper. ' +
      'Do not claim a proposed lemma or scratch experiment is an accepted proof. ' +
      'If this focus yields no useful step, report that outcome with evidence and stop.' };
}

export function createCapacityExploration(target: TaskRecord, worker: { id: string }, tasks: readonly TaskRecord[],
  identity: Identity, focus: CapacityExplorationFocus): TaskRecord {
  const currentTarget = tasks.find(node => node.task.id === target.task.id);
  if (!focusValid(focus) || !nonempty(worker.id) || !nonempty(identity.environmentDigest) || !nonempty(identity.problemReceiptDigest) ||
      !currentTarget || !targetAvailable(target) || !targetAvailable(currentTarget) || taskVersion(currentTarget.task) !== taskVersion(target.task))
    throw new Error('math_capacity_exploration_target_invalid');
  const inputDigest = capacityExplorationInput(target.task, tasks, identity);
  const task = explorationTask(target.task, worker.id, inputDigest, identity, focus);
  return { task, status: 'pending', attempts: 0, capacityExploration: { schema, targetTaskId: target.task.id,
    targetTaskDigest: taskVersion(target.task), inputDigest, focus, workerId: worker.id, taskDigest: taskVersion(task), ...identity } };
}

/** This marker belongs to TaskRecord, never to a model-authored CooperativeTask. */
function validMarker(node: TaskRecord | undefined): node is TaskRecord & { capacityExploration: CapacityExploration } {
  if (!node?.capacityExploration) return false;
  const marker = node.capacityExploration, task = node.task;
  return marker.schema === schema && focusValid(marker.focus) &&
    [marker.targetTaskId, marker.targetTaskDigest, marker.inputDigest, marker.workerId, marker.taskDigest,
      marker.environmentDigest, marker.problemReceiptDigest].every(nonempty) &&
    [marker.targetTaskDigest, marker.inputDigest, marker.taskDigest].every(value => /^[a-f0-9]{64}$/u.test(value)) &&
    task.kind === 'research' && !task.type && !task.theoremName && !task.proofPath &&
    task.id === taskId(marker) && task.ownerId === marker.workerId &&
    task.dependsOn.length === 1 && task.dependsOn[0] === marker.targetTaskId &&
    marker.taskDigest === taskVersion(task);
}

export function currentCapacityExploration(node: TaskRecord, tasks: readonly TaskRecord[], identity: Identity): boolean {
  if (!validMarker(node)) return false;
  const marker = node.capacityExploration, target = tasks.find(item => item.task.id === marker.targetTaskId);
  return marker.environmentDigest === identity.environmentDigest && marker.problemReceiptDigest === identity.problemReceiptDigest &&
    Boolean(target && targetAvailable(target) && taskVersion(target.task) === marker.targetTaskDigest &&
      marker.inputDigest === capacityExplorationInput(target.task, tasks, identity) &&
      // Pause/stop are scheduling controls; current()/M3/M5 still enforce the actual status.
      canonicalMathJson({ ...node.task, status: 'active' }) ===
        canonicalMathJson(explorationTask(target.task, marker.workerId, marker.inputDigest, identity, marker.focus)));
}

/** Additional eligibility for Provers; ordinary research eligibility stays with M5. */
export function capacityExplorationWorkerCanTask(worker: { id: string; role: string }, task: CooperativeTask,
  node?: TaskRecord): boolean {
  return worker.role === 'prover' && validMarker(node) && node.capacityExploration.workerId === worker.id &&
    (task.status ?? 'active') === 'active' && task.ownerId === worker.id &&
    canonicalMathJson(node.task) === canonicalMathJson(task);
}
