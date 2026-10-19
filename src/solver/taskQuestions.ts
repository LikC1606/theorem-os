import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { isAdvisoryTask, taskGroup, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';

export type ParallelQuestion = Readonly<{
  taskId: string; taskDigest: string; kind: CooperativeTask['kind']; objective: string;
  theoremName?: string; workerId?: string; routeId?: string;
}>;

/** Exact research-input identity only; this makes no claim of mathematical equivalence. */
function questionDigest(task: CooperativeTask, tasks: readonly TaskRecord[]): string | undefined {
  if (!isAdvisoryTask(task) || task.reviewScope || task.id === 'independent_candidate_review') return;
  const nodes = new Map(tasks.map(node => [node.task.id, node]));
  return mathDigest(canonicalMathJson({ kind: task.kind, objective: task.objective.trim(), premises: task.premises ?? [],
    inputs: [...task.dependsOn].sort().map(id => {
      const node = nodes.get(id), proof = node?.integratedCheck ?? node?.proof;
      return { id, taskDigest: node && taskVersion(node.task), status: node?.status,
        finding: node?.finding, sourceDigest: proof?.sourceDigest, conditions: proof?.conditions };
    }) }));
}

export function hasRunningDuplicateQuestion(node: TaskRecord, tasks: readonly TaskRecord[]): boolean {
  const digest = questionDigest(node.task, tasks);
  return Boolean(digest && tasks.some(other => other.task.id !== node.task.id && other.status === 'running' &&
    (taskGroup(other.task) === taskGroup(node.task) || other.task.sharing !== 'group' && node.task.sharing !== 'group') &&
    questionDigest(other.task, tasks) === digest));
}

export function parallelQuestions(tasks: readonly TaskRecord[], task?: CooperativeTask): ParallelQuestion[] {
  return tasks.filter(node => node.status === 'running' && node.task.id !== task?.id &&
    (!task || taskGroup(node.task) === taskGroup(task) || node.task.sharing !== 'group'))
    .map(node => ({ taskId: node.task.id, taskDigest: taskVersion(node.task), kind: node.task.kind,
      objective: node.task.objective, theoremName: node.task.theoremName,
      workerId: node.assignment?.workerId, routeId: node.assignment?.routeId }));
}
