import { originalGoalTaskFocus, plannedTaskDependencyIds, taskDependenciesReady } from './search';
import { checkedUnconditionally, isAdvisoryTask, isFeasibilityReview, taskGroup, taskVersion,
  type CooperativeTask, type RouteGroup, type TaskRecord, type RouteRecord } from '../tasks';
import { hasRunningDuplicateQuestion } from '../taskQuestions';
import { createProofRoutePriority } from '../routePriority';
import { freshTaskConnection } from '../taskConnections';
import { capacityExplorationWorkerCanTask } from '../capacityExploration';

export const MAX_RESEARCH_WORKERS = 8;
export type ResearchRole = 'lead' | 'researcher' | 'prover' | 'engineer' | 'reviewer';
export type ResearchWorker = Readonly<{ id: string; role: ResearchRole; worktree: string; ownedFiles: readonly string[] }>;
export type ResponsibilityContext = Readonly<{
  tasks: readonly TaskRecord[];
  groups?: readonly RouteRecord[];
}>;
export type ResponsibilityAssessment =
  | Readonly<{ kind: 'matches' }>
  | Readonly<{ kind: 'blocked'; reason: 'role' | 'engineer' | 'owner' | 'saved-assignment' |
      'review-independence' | 'running-duplicate' }>;

/** Researchers and the Engineer retain their general task eligibility; Provers write typed helpers. */
export function researchWorkerCanTask(worker: Pick<ResearchWorker, 'role'>, task: CooperativeTask): boolean {
  return worker.role === 'researcher' || worker.role === 'engineer' ||
    worker.role === 'prover' && task.kind === 'lemma' && Boolean(task.type?.trim());
}

/** The only Prover advisory exception is an independently identified host exploration. */
export function researchWorkerCanNode(worker: Pick<ResearchWorker, 'id' | 'role'>, node: TaskRecord): boolean {
  return researchWorkerCanTask(worker, node.task) || capacityExplorationWorkerCanTask(worker, node.task, node);
}

export function researchTaskRole(task: CooperativeTask): ResearchRole {
  return isFeasibilityReview(task) ? 'reviewer' : task.kind === 'goal' ? 'engineer' : task.kind === 'lemma' ? 'prover' : 'researcher';
}

export function defaultResearchRouteConcurrency(workers: readonly Pick<ResearchWorker, 'role'>[]): number {
  return workers.length > 4 ? Math.max(1, workers.filter(worker => ['researcher', 'prover', 'engineer'].includes(worker.role)).length) : 3;
}

/** Save expanded capacity in the plan, so M3 and M5 use the same limit on every dispatch and resume. */
export function researchRouteGroups(groups: readonly RouteGroup[], workers: readonly Pick<ResearchWorker, 'role'>[]): RouteGroup[] {
  return groups.map(group => workers.length > 4 && group.maxConcurrent === undefined
    ? { ...group, maxConcurrent: defaultResearchRouteConcurrency(workers) } : { ...group });
}

export function independentFeasibilityWorker(node: TaskRecord, worker: Pick<ResearchWorker, 'id' | 'role'>,
  tasks: readonly TaskRecord[], groups?: readonly RouteRecord[]): boolean {
  if (!isFeasibilityReview(node.task)) return true;
  if (worker.role === 'lead') return false;
  return node.task.dependsOn.every(id => {
    const input = tasks.find(task => task.task.id === id);
    const engineerId = input?.task.kind === 'goal'
      ? groups?.find(group => group.group.id === taskGroup(input.task))?.group.engineerId : undefined;
    return input?.assignment?.workerId !== worker.id && input?.task.ownerId !== worker.id && engineerId !== worker.id;
  });
}

/** First responsibility mismatch only; matching does not establish readiness or proof acceptance. */
export function assessTaskResponsibility(node: TaskRecord, worker: Pick<ResearchWorker, 'id' | 'role'>,
  { tasks, groups }: ResponsibilityContext): ResponsibilityAssessment {
  if (!researchWorkerCanNode(worker, node)) return { kind: 'blocked', reason: 'role' };
  const engineerId = node.task.kind === 'goal'
    ? groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId : undefined;
  if (engineerId && engineerId !== worker.id) return { kind: 'blocked', reason: 'engineer' };
  if (node.task.ownerId && node.task.ownerId !== worker.id) return { kind: 'blocked', reason: 'owner' };
  if (node.assignment && node.assignment.workerId !== worker.id) return { kind: 'blocked', reason: 'saved-assignment' };
  if (!independentFeasibilityWorker(node, worker, tasks, groups)) return { kind: 'blocked', reason: 'review-independence' };
  if (hasRunningDuplicateQuestion(node, tasks)) return { kind: 'blocked', reason: 'running-duplicate' };
  return { kind: 'matches' };
}

function eligibleResearchTasks(ready: readonly TaskRecord[], worker: ResearchWorker, groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord[] {
  const context = { tasks, groups };
  return ready.filter(node => assessTaskResponsibility(node, worker, context).kind === 'matches');
}

/** Share ranked work, reserving a final available slot for independent work when the main frontier is occupied. */
export function assignSharedResearchTask(ready: readonly TaskRecord[], worker: ResearchWorker, live: readonly ResearchWorker[], groups?: readonly RouteRecord[],
  tasks: readonly TaskRecord[] = ready): TaskRecord | undefined {
  let eligible = eligibleResearchTasks(ready, worker, groups, tasks);
  if (live.some(peer => peer.role === 'prover')) {
    // Preserve M3 order within each responsibility while leaving spare generalists useful.
    const preferred = (node: TaskRecord) => worker.role === 'researcher' ? isAdvisoryTask(node.task)
      : worker.role === 'engineer' && node.task.kind === 'goal';
    eligible = [...eligible.filter(preferred), ...eligible.filter(node => !preferred(node))];
  }
  // Optional discovery never takes a slot from an executable planned obligation.
  const planned = eligible.filter(node => !node.capacityExploration);
  if (planned.length) eligible = planned;
  const first = eligible[0];
  if (!first || eligible.length === 1) return first;
  if (first.task.kind === 'goal' || !first.attempts && isFeasibilityReview(first.task) ||
      freshTaskConnection(first, tasks, groups)) return first;
  const proofWorkers = new Set(live.filter(peer => ['researcher', 'prover', 'engineer'].includes(peer.role)).map(peer => peer.id));
  const running = tasks.filter(node => node.status === 'running' && node.assignment &&
    node.assignment.taskId === node.task.id && node.assignment.taskDigest === taskVersion(node.task) &&
    proofWorkers.has(node.assignment.workerId));
  if (!running.length) return first;
  const occupied = new Set(running.map(node => node.assignment!.workerId));
  const group = groups?.find(route => route.group.id === taskGroup(first.task));
  const groupBusy = group?.busy ?? new Set(running.filter(node => taskGroup(node.task) === taskGroup(first.task))
    .map(node => node.assignment!.workerId)).size;
  const lastSlot = proofWorkers.size - occupied.size === 1;
  const lastGroupSlot = group && (group.group.maxConcurrent ?? 3) - groupBusy === 1;
  if (!lastSlot && !lastGroupSlot) return first;
  const checkedInput = (id: string) => checkedUnconditionally(tasks.find(node => node.task.id === id));
  if (first.task.type && taskDependenciesReady(first.task, tasks) &&
      plannedTaskDependencyIds(first, tasks).some(checkedInput)) return first;
  const focus = originalGoalTaskFocus(tasks, groups), preferred = focus.preferred.support;
  if (!preferred.has(first.task.id) || running.some(node => !preferred.has(node.task.id))) return first;
  // Different original goals share the support set. Give an uncovered goal a
  // slot before filling every worker with inputs to goals already in progress.
  const coveredGoals = new Set(running.flatMap(node => [...(focus.preferred.proofGoals.get(node.task.id) ?? [])]));
  const firstGoals = focus.preferred.proofGoals.get(first.task.id);
  if (firstGoals?.size && [...firstGoals].every(id => coveredGoals.has(id))) {
    const independent = eligible.find(node => [...(focus.preferred.proofGoals.get(node.task.id) ?? [])]
      .some(id => !coveredGoals.has(id)));
    if (independent) return independent;
  }
  const priority = createProofRoutePriority(tasks, { groups });
  return eligible.filter(node => !preferred.has(node.task.id)).toSorted((a, b) =>
    Number(focus.support.has(b.task.id)) - Number(focus.support.has(a.task.id)) ||
    priority.compareTasks(a, b) || a.attempts - b.attempts)[0] ?? first;
}

export function researchWorkers(worktree: string, ownedFiles: readonly string[], count: number): ResearchWorker[] {
  return Array.from({ length: count }, (_, index) => ({
    id: index === 0 ? 'solver' : index === count - 1 ? 'engineer' : index <= 2 ? `researcher-${index}` : `prover-${index - 2}`,
    role: index === 0 ? 'lead' : index === count - 1 ? 'engineer' : index <= 2 ? 'researcher' : 'prover',
    worktree: index === 0 ? worktree : `${worktree}-${index + 1}`, ownedFiles,
  }));
}

/** Reviewers inspect fixed work independently of its producer. */
export function assignResearchReviewer(live: readonly ResearchWorker[], producerId?: string): ResearchWorker | undefined {
  const eligible = live.filter(worker => worker.role !== 'lead' && worker.id !== producerId);
  return eligible.find(worker => worker.role === 'reviewer') ?? eligible.find(worker => worker.role === 'researcher') ?? eligible[0];
}
