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

export const assignmentDeliveryFile = (assignment: TaskAssignment) => `DELIVERIES-${mathDigest(canonicalMathJson({
  taskId: assignment.taskId, taskDigest: assignment.taskDigest, seedCommit: assignment.seedCommit }))}.jsonl`;
