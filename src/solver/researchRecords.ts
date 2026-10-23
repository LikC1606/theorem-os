import { z } from 'zod';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import type { DeliveryRecord } from './deliveries';
import { assignmentDeliveryFile, isAdvisoryTask, isFinalCandidateReview, taskVersion,
  type CooperativeTask, type TaskAssignment, type TaskRecord } from './tasks';

export type ResearchIdentity = Readonly<{ problemReceiptDigest: string; environmentDigest: string;
  retrievalDigest?: string; knowledgeDigest?: string }>;
type ResearchProof = NonNullable<TaskRecord['proof']>;
/** The advisory input view cannot convey proof acceptance or a live assignment. */
export type ResearchTaskView = Pick<TaskRecord, 'task' | 'status' | 'finding'> & {
  proof?: Pick<ResearchProof, 'passed' | 'taskDigest' | 'conditions'>;
  integratedCheck?: Pick<ResearchProof, 'passed' | 'taskDigest' | 'conditions'>;
};
export type ResearchView = ResearchIdentity & Readonly<{ sourceDigest: string;
  tasks: readonly ResearchTaskView[]; deliveries?: readonly DeliveryRecord[] }>;
type Reference = Readonly<{ taskId: string; taskDigest: string }>;
type Dependency = Readonly<{ taskId: string; taskDigest: string | null; findingDigest?: string;
  proof?: Readonly<{ state: 'integrated' | 'checked' | 'conditional'; taskDigest: string;
    conditions: readonly Reference[] }>; deliveries: readonly string[] }>;
export type ResearchBasis = ResearchIdentity & Readonly<{ schema: 'theorem-os.research-basis.v1';
  taskId: string; taskDigest: string; sourceDigest: string; dependencies: readonly Dependency[] }>;
export type ResearchRecord = Readonly<{ schema: 'theorem-os.research-record.v1'; id: string;
  taskId: string; taskDigest: string; assignmentKey: string; seedCommit: string; commit: string;
  basis: ResearchBasis; findingDigest: string; complete: boolean }>;

const identity = z.string().min(1), digest = z.string().regex(/^[a-f0-9]{64}$/u);
const referenceSchema = z.object({ taskId: identity, taskDigest: identity }).strict()
  .transform((value): Reference => ({ taskId: value.taskId, taskDigest: value.taskDigest }));
const proofSchema = z.object({ state: z.enum(['integrated', 'checked', 'conditional']), taskDigest: identity,
  conditions: z.array(referenceSchema) }).strict().transform((value): NonNullable<Dependency['proof']> => ({
    state: value.state, taskDigest: value.taskDigest, conditions: value.conditions }));
const dependencySchema = z.object({ taskId: identity, taskDigest: identity.nullable(), findingDigest: digest.optional(),
  proof: proofSchema.optional(), deliveries: z.array(digest) }).strict().transform((value): Dependency => ({
    ...value, taskId: value.taskId, taskDigest: value.taskDigest, deliveries: value.deliveries }));
export const researchBasisSchema = z.object({ schema: z.literal('theorem-os.research-basis.v1'),
  taskId: identity, taskDigest: identity, sourceDigest: identity, problemReceiptDigest: identity,
  environmentDigest: identity, retrievalDigest: identity.optional(), knowledgeDigest: identity.optional(),
  dependencies: z.array(dependencySchema) }).strict().transform((value): ResearchBasis => ({ ...value,
    schema: value.schema, taskId: value.taskId, taskDigest: value.taskDigest, sourceDigest: value.sourceDigest,
    problemReceiptDigest: value.problemReceiptDigest, environmentDigest: value.environmentDigest,
    dependencies: value.dependencies }));
export const researchRecordSchema = z.object({ schema: z.literal('theorem-os.research-record.v1'), id: identity,
  taskId: identity, taskDigest: identity, assignmentKey: identity, seedCommit: identity, commit: identity,
  basis: researchBasisSchema, findingDigest: digest, complete: z.boolean() }).strict()
  .refine(value => value.taskId === value.basis.taskId && value.taskDigest === value.basis.taskDigest,
    'Research completion must retain its captured task identity')
  .transform((value): ResearchRecord => ({ ...value, schema: value.schema, id: value.id, taskId: value.taskId,
    taskDigest: value.taskDigest, assignmentKey: value.assignmentKey, seedCommit: value.seedCommit,
    commit: value.commit, basis: value.basis, findingDigest: value.findingDigest, complete: value.complete }));

function immutable<T>(value: T): T {
  if (value && typeof value === 'object') {
    for (const child of Object.values(value)) immutable(child);
    Object.freeze(value);
  }
  return value;
}
const semanticDigest = (value: unknown) => mathDigest(canonicalMathJson(value));
const references = (values: readonly Reference[]) => [...new Map(values.map(value =>
  [canonicalMathJson([value.taskId, value.taskDigest]), { taskId: value.taskId, taskDigest: value.taskDigest }]))]
  .sort(([left], [right]) => left.localeCompare(right)).map(([, value]) => value);

/** Content and paths, independent of object insertion order or Git commit metadata. */
export function researchSourceDigest(sources: Readonly<Record<string, string>>): string {
  return semanticDigest(Object.entries(sources).sort(([left], [right]) => left.localeCompare(right))
    .map(([file, source]) => [file, mathDigest(source)]));
}

function proofInput(node: ResearchTaskView): Dependency['proof'] {
  const taskDigest = taskVersion(node.task);
  const proof = node.integratedCheck?.passed && node.integratedCheck.taskDigest === taskDigest ? node.integratedCheck : node.proof;
  if (!proof?.passed || proof.taskDigest !== taskDigest) return;
  const conditions = references(proof.conditions ?? []);
  return { state: conditions.length ? 'conditional' : node.status === 'integrated' ? 'integrated' : 'checked', taskDigest, conditions };
}

function researchDeliveryInput(delivery: DeliveryRecord) {
  return { statement: delivery.statement, premises: delivery.premises, dependencies: references(delivery.dependencies ?? []),
    remainingObligations: delivery.remainingObligations, summary: delivery.summary,
    findingDigest: typeof delivery.finding === 'string' ? mathDigest(delivery.finding) : delivery.findingDigest,
    evidenceRefs: [...new Set(delivery.evidenceRefs)].sort(), mathematicalGap: delivery.mathematicalGap,
    lemmaRequests: delivery.lemmaRequests?.map(taskVersion).sort() };
}

/** Capture the actual dispatch inputs once. Publication and continuation never reconstruct an old basis. */
export function captureResearchBasis(task: CooperativeTask, view: ResearchView): ResearchBasis {
  const nodes = new Map(view.tasks.map(node => [node.task.id, node])), inputs = new Set<string>();
  const visit = (id: string) => {
    if (id === task.id || inputs.has(id)) return;
    inputs.add(id); nodes.get(id)?.task.dependsOn.forEach(visit);
  };
  task.dependsOn.forEach(visit);
  const dependencies: Dependency[] = [...inputs].sort().map(taskId => {
    const node = nodes.get(taskId), taskDigest = node ? taskVersion(node.task) : null;
    const deliveries = (view.deliveries ?? []).filter(delivery => delivery.kind === 'research' &&
      delivery.status !== 'superseded' && delivery.taskId === taskId && delivery.taskDigest === taskDigest &&
      (delivery.dependencies ?? []).every(reference => {
        const input = nodes.get(reference.taskId);
        return input && taskVersion(input.task) === reference.taskDigest;
      })).map(delivery => semanticDigest(researchDeliveryInput(delivery)));
    return { taskId, taskDigest, ...(node?.finding === undefined ? {} : { findingDigest: mathDigest(node.finding) }),
      ...(node ? { proof: proofInput(node) } : {}), deliveries: [...new Set(deliveries)].sort() };
  });
  return immutable(researchBasisSchema.parse({ schema: 'theorem-os.research-basis.v1', taskId: task.id,
    taskDigest: taskVersion(task), sourceDigest: view.sourceDigest, problemReceiptDigest: view.problemReceiptDigest,
    environmentDigest: view.environmentDigest, retrievalDigest: view.retrievalDigest, knowledgeDigest: view.knowledgeDigest, dependencies }));
}

/** A new publication has its own identity even when it repeats the same finding text. */
export function settleResearch(input: { id: string; assignment: TaskAssignment; basis?: ResearchBasis;
  commit: string; finding: string; complete: boolean }): ResearchRecord | undefined {
  if (!input.basis) return;
  const basis = researchBasisSchema.parse(input.basis);
  if (basis.taskId !== input.assignment.taskId || basis.taskDigest !== input.assignment.taskDigest)
    throw new Error('math_research_basis_assignment_changed');
  return immutable(researchRecordSchema.parse({ schema: 'theorem-os.research-record.v1', id: input.id,
    taskId: input.assignment.taskId, taskDigest: input.assignment.taskDigest,
    assignmentKey: assignmentDeliveryFile(input.assignment), seedCommit: input.assignment.seedCommit,
    commit: input.commit, basis, findingDigest: mathDigest(input.finding), complete: input.complete }));
}

/** Completion is reusable advisory context. This result cannot authorize any proof acceptance. */
export function restoreResearch(record: ResearchRecord | undefined, task: CooperativeTask, view: ResearchView,
  finding?: string): { status: 'completed' | 'pending'; reason: string } {
  const pending = (reason: string) => ({ status: 'pending' as const, reason });
  if (!isAdvisoryTask(task) || task.reviewScope || isFinalCandidateReview(task)) return pending('not-ordinary-research');
  if (!record) return pending('missing-record');
  const parsed = researchRecordSchema.parse(record);
  if (!parsed.complete) return pending('incomplete');
  if (parsed.taskId !== task.id || parsed.taskDigest !== taskVersion(task)) return pending('task-changed');
  if (finding === undefined || parsed.findingDigest !== mathDigest(finding)) return pending('finding-changed');
  if (canonicalMathJson(parsed.basis) !== canonicalMathJson(captureResearchBasis(task, view))) return pending('inputs-changed');
  return { status: 'completed', reason: 'restored' };
}
