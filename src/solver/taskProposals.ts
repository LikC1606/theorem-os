import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { SolverProblem } from './problem';
import { isAdvisoryTask, parseCooperationPlan, taskGroup, taskVersion, type CooperativeTask, type RouteGroup,
  type TaskAssignment, type TaskRecord } from './tasks';

/** A research artifact can propose a new contract; it grants no source or proof authority. */
export type ResearchLemmaProposal = Readonly<{
  id: string; source: { taskId: string; taskDigest: string; producer: string; commit: string };
  tasks: readonly CooperativeTask[];
  dependencies: readonly { taskId: string; taskDigest: string }[]; createdAt: number;
}>;

export function proposeResearchLemmas(problem: SolverProblem, records: readonly TaskRecord[], groups: readonly RouteGroup[],
  source: { task: CooperativeTask; assignment: TaskAssignment }, producer: string, commit: string, requests: unknown): ResearchLemmaProposal | undefined {
  if (requests === undefined) return;
  if (!Array.isArray(requests) || !requests.length || requests.length > 8 || Buffer.byteLength(JSON.stringify(requests)) > 128_000)
    throw new Error('math_research_lemma_proposal_invalid');
  const existing = new Map(records.map(node => [node.task.id, node.task]));
  const sourceTask = existing.get(source.task.id);
  if (!sourceTask || !isAdvisoryTask(sourceTask) || taskVersion(sourceTask) !== source.assignment.taskDigest ||
      taskVersion(source.task) !== source.assignment.taskDigest || source.assignment.taskId !== source.task.id ||
      source.assignment.workerId !== producer || !/^[a-f0-9]{40,64}$/u.test(commit) ||
      (source.assignment.dependencies ?? []).some(ref => !existing.has(ref.taskId) || taskVersion(existing.get(ref.taskId)!) !== ref.taskDigest))
    throw new Error('math_research_lemma_proposal_source_changed');
  const groupId = taskGroup(source.task);
  const candidates = requests.map(value => {
    if (!value || typeof value !== 'object' || value.kind !== 'lemma' || existing.has(value.id) ||
        typeof value.type !== 'string' || Buffer.byteLength(value.type) > 32_000 ||
        value.groupId !== undefined && value.groupId !== groupId ||
        value.ownerId !== undefined || value.status !== undefined && value.status !== 'active' ||
        source.task.sharing === 'group' && value.sharing === 'problem')
      throw new Error('math_research_lemma_proposal_outside_scope');
    return { ...value, groupId, sharing: value.sharing ?? source.task.sharing };
  });
  const plan = parseCooperationPlan(problem, { groups: groups.length ? groups : undefined,
    tasks: [...records.map(node => node.task), ...candidates] });
  const tasks = plan.tasks.filter(task => !existing.has(task.id));
  const dependencyIds = new Set([
    ...(source.assignment.dependencies ?? []).map(ref => ref.taskId),
    ...tasks.flatMap(task => [...task.dependsOn,
      ...(task.applications ?? []).flatMap(app => [app.consumer.taskId, ...(app.proofTask ? [app.proofTask.taskId] : [])]),
      ...(task.obligations ?? []).flatMap(premise => 'taskId' in premise.source ? [premise.source.taskId] : [])]),
  ].filter(id => existing.has(id)));
  const dependencies = [...dependencyIds].sort().map(taskId => ({ taskId, taskDigest: taskVersion(existing.get(taskId)!) }));
  const reference = { taskId: source.task.id, taskDigest: source.assignment.taskDigest, producer, commit };
  return { id: mathDigest(canonicalMathJson({ source: reference, tasks, dependencies })), source: reference,
    tasks, dependencies, createdAt: Date.now() };
}

export function researchLemmaProposalSummary(proposals: readonly ResearchLemmaProposal[], records: readonly TaskRecord[]) {
  const tasks = new Map(records.map(node => [node.task.id, node.task]));
  const current = (ref: { taskId: string; taskDigest: string }) => tasks.has(ref.taskId) && taskVersion(tasks.get(ref.taskId)!) === ref.taskDigest;
  return proposals.map(proposal => ({ ...proposal, evidence: 'advisory-proposal' as const,
    status: !current(proposal.source) || !proposal.dependencies.every(current) ? 'stale' as const :
      proposal.tasks.every(task => current({ taskId: task.id, taskDigest: taskVersion(task) })) ? 'adopted' as const :
      proposal.tasks.some(task => tasks.has(task.id)) ? 'stale' as const : 'proposed' as const }));
}
