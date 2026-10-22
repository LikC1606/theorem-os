import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { capacityExplorationInput, exhaustedCapacityExploration, type CapacityExplorationFocus } from './capacityExploration';
import { originalGoalTaskFocus } from './modules/search';
import { isAdvisoryTask, taskGroup, taskVersion, type RouteRecord, type TaskRecord } from './tasks';

export type StagnationWorker = { id: string; sessionTaskId?: string; sessionTaskVersion?: string;
  advisoryCheckpoint?: { noProgressStreak: number } };
type Input = { tasks: readonly TaskRecord[]; groups?: readonly RouteRecord[]; workers: readonly StagnationWorker[];
  identity: { environmentDigest: string; problemReceiptDigest: string }; sourceDigest: string; evidenceDigest: string;
  explorationInputs?: readonly { targetTaskId: string; inputDigest: string; focus: CapacityExplorationFocus }[] };

/** A scheduling diagnosis, not a proof failure, time limit, or reason to block a declaration. */
export function advisoryStagnation(input: Input) {
  const focus = originalGoalTaskFocus(input.tasks, input.groups, input.identity.environmentDigest);
  const targets = input.tasks.filter(node => focus.frontier.has(node.task.id) &&
    ['lemma', 'goal'].includes(node.task.kind) && !['integrated', 'completed'].includes(node.status));
  if (!targets.length) return;
  const groups = new Set(targets.map(node => taskGroup(node.task)));
  const stalled = input.workers.filter(worker => {
    if ((worker.advisoryCheckpoint?.noProgressStreak ?? 0) < 3) return false;
    const node = input.tasks.find(node => node.task.id === worker.sessionTaskId);
    return node && isAdvisoryTask(node.task) && ['running', 'pending', 'blocked'].includes(node.status) &&
      node.assignment?.workerId === worker.id && node.assignment.taskDigest === taskVersion(node.task) &&
      (!worker.sessionTaskVersion || worker.sessionTaskVersion === taskVersion(node.task)) && groups.has(taskGroup(node.task)) &&
      node.task.dependsOn.some(id => focus.support.has(id));
  });
  const exhausted = targets.some(node => exhaustedCapacityExploration(node.task, input.tasks, input.identity, input.explorationInputs));
  if (!stalled.length && !exhausted) return;
  const taskIds = targets.map(node => node.task.id).sort();
  // Dispatch ids, time, occupancy and counters do not create fresh mathematical input.
  const inputDigest = mathDigest(canonicalMathJson({ schema: 'theorem-os.advisory-stagnation.v1', ...input.identity,
    frontier: targets.map(node => [node.task.id, capacityExplorationInput(node.task, input.tasks, input.identity)])
      .sort(([a], [b]) => a.localeCompare(b)), sourceDigest: input.sourceDigest, evidenceDigest: input.evidenceDigest }));
  return { inputDigest, taskIds, workerIds: stalled.map(worker => worker.id).sort(),
    reason: stalled.length ? 'advisory-no-durable-progress' as const : 'frontier-not-decomposed' as const };
}
