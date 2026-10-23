import fs from 'node:fs';
import path from 'node:path';
import { z } from 'zod';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { bindLeanPackages } from '../math/leanDiagnostics';
import { MATH_PROOF_ENVIRONMENT_ENV, MATH_PROOF_ENVIRONMENT_SANDBOX_ENV, prepareMathProofEnvironment } from '../math/mathProofEnvironment';
import { DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT } from '../math/mathProofEnvironmentCache';
import { assertMathCanonicalPath, repositoryRelativePath } from '../math/paths';
import { canonicalMathJson, mathDigest, readMathFile, readMathJson, withMathRuntimeLease, writeMathJsonDurable, type MathLease } from '../math/mathRuntimeIo';
import { resolveMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { resolveMathematicsLakePackagesCache } from '../math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from './archive';
import { checkTaskProofs, createTaskSourceProjector, isAttributedTaskProof, type TaskProof, type TaskProofRequest } from './cooperativeProof';
import { rejectionCode, taskSourceRejections } from './cooperationShared';
import { freezeContinuationInput, readContinuationSnapshot, type ContinuationManifest } from './continuationInput';
import { readRunInspection } from './inspection';
import type { DeliveryRecord } from './deliveries';
import { normalizedResearchHandoffDecisions, researchHandoffs, type ResearchHandoffDecision } from './researchHandoffs';
import { researchRecordSchema, researchSourceDigest, restoreResearch } from './researchRecords';
import { researchSourceTasks, scopedResearchSources, type ResearchSourceTask } from './researchSources';
import { mathematicalGapSchema } from './mathematicalGaps';
import { researchWorkerCanNode, researchWorkerCanTask } from './modules/organization';
import { CAPACITY_EXPLORATION_FOCUSES, currentCapacityExploration, plannedTaskRecords, type CapacityExploration } from './capacityExploration';
import { assertSolverSources, committedSource, commitSolverSources, git, readSolverProblem, withSolverWorktree, type SolverProblem } from './problem';
import { isAdvisoryTask, isFinalCandidateReview, parseCooperationPlan, taskVersion, type CooperativeTask, type TaskRecord } from './tasks';
import { createTaskConnectionCheck } from './taskConnections';

const hash = z.string().regex(/^[a-f0-9]{64}$/u), oid = z.string().regex(/^[a-f0-9]{40,64}$/u);
const id = z.string().regex(/^[a-zA-Z0-9_-]{1,64}$/u);
const seedBatchFallbacks = new Set([...taskSourceRejections, 'math_task_batch_projection_mismatch',
  'math_task_missing_declaration', 'math_task_condition_version_invalid']);
const maxSeedBatchSize = 32;
// This project permits undefined at the type level. Materialize validated required
// fields so Zod's optional-property inference does not weaken the runtime contract.
const capacityMarker = z.object({ schema: z.literal('theorem-os.capacity-exploration.v1'),
  targetTaskId: id, targetTaskDigest: hash, inputDigest: hash, focus: z.enum(CAPACITY_EXPLORATION_FOCUSES),
  workerId: id, taskDigest: hash, environmentDigest: hash, problemReceiptDigest: hash }).strict()
  .transform((value): CapacityExploration => ({ schema: value.schema, targetTaskId: value.targetTaskId,
    targetTaskDigest: value.targetTaskDigest, inputDigest: value.inputDigest, focus: value.focus,
    workerId: value.workerId, taskDigest: value.taskDigest, environmentDigest: value.environmentDigest,
    problemReceiptDigest: value.problemReceiptDigest }));
const capacityInput = z.object({ inputDigest: hash, focus: z.enum(CAPACITY_EXPLORATION_FOCUSES),
  targetTaskId: id, taskId: id }).strict().transform(value => ({ inputDigest: value.inputDigest,
    focus: value.focus, targetTaskId: value.targetTaskId, taskId: value.taskId }));
const capacityRecord = z.object({
  task: z.object({ id, kind: z.literal('research'), objective: z.string().min(1), dependsOn: z.array(id),
    revision: z.number().int().nonnegative() }).passthrough(),
  capacityExploration: capacityMarker,
  status: z.enum(['pending', 'running', 'blocked', 'conditional', 'delivered', 'integrated', 'completed']),
  finding: z.string().optional(), archived: z.literal(true).optional(),
}).strict().refine(value => taskVersion(value.task as CooperativeTask) === value.capacityExploration.taskDigest,
  'Capacity exploration task identity changed');
const capacitySource = z.object({ records: z.array(capacityRecord),
  inputs: z.array(capacityInput).optional(),
  notes: z.array(z.object({ taskId: id, taskDigest: hash, deliveryId: z.string().min(1), commit: oid,
    notes: z.string() }).strict()),
}).strict();
type CapacityRecord = z.infer<typeof capacityRecord>;
const handoffTask = z.object({ id, kind: z.enum(['research', 'sketch', 'lemma', 'goal']),
  objective: z.string().min(1), dependsOn: z.array(id), revision: z.number().int().nonnegative(),
  proofPath: z.string().optional(), theoremName: z.string().optional(), type: z.string().optional(),
  groupId: id.optional(), sharing: z.enum(['group', 'problem']).optional(), status: z.enum(['active', 'paused', 'stopped']).optional(),
  ownerId: id.optional(), premises: z.array(z.string()).optional(), conditional: z.boolean().optional(),
  statementReview: z.boolean().optional(), informalStatement: z.string().optional(),
  reviewScope: z.enum(['final-candidate', 'feasibility']).optional(),
}).strict().transform((value): CooperativeTask => ({ ...value, id: value.id, kind: value.kind,
  objective: value.objective, dependsOn: value.dependsOn, revision: value.revision }));
const continuableResearch = (task: CooperativeTask) => isAdvisoryTask(task) && !task.reviewScope && !isFinalCandidateReview(task);
const legacyCompletedResearchRecord = z.object({ task: handoffTask.refine(continuableResearch, 'Completion requires ordinary advisory research'),
  inputDigest: hash, finding: z.string().optional(), archived: z.literal(true).optional() }).strict();
const immutableCompletedResearchRecord = z.object({ task: handoffTask.refine(continuableResearch, 'Completion requires ordinary advisory research'),
  record: researchRecordSchema, finding: z.string().optional(), archived: z.literal(true).optional() }).strict();
const unboundCompletedResearchRecord = z.object({ task: handoffTask.refine(continuableResearch, 'Completion requires ordinary advisory research'),
  finding: z.string().optional(), archived: z.literal(true) }).strict();
const completedResearchRecord = z.union([immutableCompletedResearchRecord, legacyCompletedResearchRecord, unboundCompletedResearchRecord]);
type CompletedResearchRecord = z.infer<typeof completedResearchRecord>;
const handoffReference = z.object({ taskId: id, taskDigest: hash }).strict()
  .transform(value => ({ taskId: value.taskId, taskDigest: value.taskDigest }));
const researchDelivery = z.object({ id: z.string().min(1), producer: id, taskId: id, taskDigest: hash,
  groupId: id.optional(), kind: z.literal('research'), status: z.enum(['advisory', 'superseded']),
  statement: z.string(), premises: z.array(z.string()), dependencies: z.array(handoffReference),
  remainingObligations: z.array(z.string()), summary: z.string(), evidenceRefs: z.array(z.string()),
  createdAt: z.number().int().nonnegative(), commit: oid.optional(), sourceDigest: z.string().optional(),
  finding: z.string().optional(), findingDigest: hash.optional(),
  researchRecord: researchRecordSchema.optional(), mathematicalGap: mathematicalGapSchema.optional(),
  mathematicalGapScope: z.object({ problemReceiptDigest: hash, environmentDigest: hash,
    source: handoffTask, consumer: handoffTask, dependencies: z.array(handoffReference) }).strict()
    .transform(value => ({ ...value, problemReceiptDigest: value.problemReceiptDigest,
      environmentDigest: value.environmentDigest, source: value.source, consumer: value.consumer,
      dependencies: value.dependencies })).optional(),
  lemmaRequests: z.array(handoffTask.refine(task => task.kind === 'lemma' && Boolean(task.type?.trim()) &&
    Boolean(task.proofPath) && Boolean(task.theoremName), 'Handoff requires an exact typed lemma')).optional(),
}).strict().transform((value): DeliveryRecord => ({ ...value, id: value.id, producer: value.producer,
  taskId: value.taskId, taskDigest: value.taskDigest, kind: value.kind, status: value.status,
  statement: value.statement, premises: value.premises, dependencies: value.dependencies,
  remainingObligations: value.remainingObligations, summary: value.summary, evidenceRefs: value.evidenceRefs,
  createdAt: value.createdAt, lemmaRequests: value.lemmaRequests }));
const handoffDelivery = researchDelivery.refine(value => Boolean(value.lemmaRequests?.length),
  'Handoff requires an exact typed lemma');
const researchProofInput = z.object({ passed: z.boolean(), taskDigest: hash,
  conditions: z.array(handoffReference).optional() }).strict()
  .transform(value => ({ ...value, passed: value.passed, taskDigest: value.taskDigest }));
const researchTaskInput = z.object({ task: handoffTask,
  status: z.enum(['pending', 'running', 'blocked', 'conditional', 'delivered', 'integrated', 'completed']),
  finding: z.string().optional(), proof: researchProofInput.optional(), integratedCheck: researchProofInput.optional(),
  visibleDependencies: z.array(id), sourceDependencies: z.array(id), sourceHelpers: z.array(z.string()),
}).strict().transform((value): ResearchSourceTask => ({ ...value, task: value.task, status: value.status,
  visibleDependencies: value.visibleDependencies, sourceDependencies: value.sourceDependencies, sourceHelpers: value.sourceHelpers }));
const researchContext = z.object({ environmentDigest: hash, problemReceiptDigest: hash,
  tasks: z.array(researchTaskInput), deliveries: z.array(researchDelivery) }).strict();
const handoffDecision = z.object({ id: hash, deliveryId: z.string().min(1),
  status: z.enum(['adopted', 'rejected', 'deferred']), taskId: id.optional(), taskDigest: hash.optional(),
  reason: z.string().optional(), contextDigest: hash.optional(), waitsOn: z.array(handoffReference).nonempty().optional(),
}).strict().refine(value => value.status !== 'adopted' || Boolean(value.taskId && value.taskDigest),
  'Adoption requires an exact task contract').refine(value => !value.waitsOn || value.status === 'deferred',
  'Only deferred decisions may wait on tasks')
  .transform((value): ResearchHandoffDecision => ({ ...value, id: value.id, deliveryId: value.deliveryId, status: value.status }));
const handoffRecord = z.object({ delivery: handoffDelivery, sourceTask: handoffTask.optional(),
  environmentDigest: hash, problemReceiptDigest: hash,
  inputs: z.array(z.object({ taskId: id, taskDigest: hash.nullable() }).strict()
    .transform(value => ({ taskId: value.taskId, taskDigest: value.taskDigest }))),
}).strict().refine(value => !value.sourceTask || value.sourceTask.id === value.delivery.taskId &&
  taskVersion(value.sourceTask) === value.delivery.taskDigest, 'Handoff source task identity changed');
const handoffSource = z.object({ records: z.array(handoffRecord), decisions: z.array(handoffDecision),
  notes: z.array(z.object({ deliveryId: z.string().min(1), commit: oid, notes: z.string() }).strict()),
}).strict().refine(value => new Set(value.records.map(record => record.delivery.id)).size === value.records.length,
  'Handoff delivery identity repeated');
type HandoffSource = z.infer<typeof handoffSource>;
const sourceSchema = z.object({
  schema: z.literal('theorem-os.continuation-seed-source.v1'), capturedAt: z.number().int().nonnegative(),
  taskDigest: hash, problemReceiptDigest: hash, sourcePolicyDigest: hash,
  destination: z.object({ runId: z.string(), stateFile: z.string(), buildDigest: hash,
    methodDigest: z.string().optional(), environmentDigest: hash }).strict(),
  source: z.object({ runId: z.string(), stateFile: z.string(), stateDigest: hash, buildDigest: z.string(),
    methodDigest: z.string().optional(), canonicalCommit: oid, planVersion: z.string().optional() }).strict(),
  plan: z.unknown(), candidateIds: z.array(id), canonicalSources: z.record(z.string()),
  conditionalCandidates: z.array(z.object({ taskId: id, taskDigest: hash, commit: z.string(), seedCommit: z.string(),
    conditions: z.array(handoffReference).nonempty(), dependencies: z.array(handoffReference),
    sources: z.record(z.string()).optional(), seedSources: z.record(z.string()).optional(), captureError: z.string().optional() }).strict()).optional(),
  workers: z.array(z.object({ id, role: z.string(), headBefore: oid, headAfter: oid,
    sources: z.record(z.string()), notes: z.string().nullable(), assignment: z.unknown().optional() }).strict()),
  history: z.unknown(),
  capacityExplorations: capacitySource.optional(),
  researchHandoffs: handoffSource.optional(),
  completedResearch: z.array(completedResearchRecord).optional(),
  researchContext: researchContext.optional(),
}).strict();
type SeedSource = z.infer<typeof sourceSchema>;

export type ContinuationSeedReport = {
  schema: 'theorem-os.continuation-seed.v1'; sourceRunId: string; runId: string; sourceStateFile: string;
  stateFile: string; sourceDigest: string; snapshotDigest?: string; canonicalCommit?: string;
  stage: 'frozen' | 'installing' | 'checking' | 'complete' | 'interrupted'; sourcesInstalled?: boolean;
  candidates: string[]; checked: string[]; failed: string[]; error?: string;
  evidence: 'advisory-sources-require-recheck' | 'fresh-helper-receipts';
};

const sourcePolicy = (problem: SolverProblem) => ({ workspace: problem.workspace, projectRelative: problem.projectRelative,
  baseCommit: problem.baseCommit, receiptDigest: problem.receiptDigest, contract: problem.contract, targets: problem.targets,
  ownedFiles: problem.ownedFiles, trustedFiles: problem.trustedFiles, declarations: problem.declarations,
  sourceStructure: problem.sourceStructure, sourceImports: problem.sourceImports });
const policyDigest = (problem: SolverProblem) => mathDigest(canonicalMathJson(sourcePolicy(problem)));
const commonDirectory = (worktree: string) => git(worktree, ['rev-parse', '--path-format=absolute', '--git-common-dir']);

function textFile(file: string) {
  assertMathCanonicalPath(file);
  return new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(readMathFile(file, 16_000_000).bytes);
}

function assertPrepared(state: SolverRunState, stateFile: string, seeded: boolean) {
  const directory = path.dirname(stateFile);
  if (state.phase !== 'prepared' || state.turns !== 0 || state.solveStartedAt !== undefined ||
      state.solveFinishedAt !== undefined || state.threadId || state.previousThreadIds?.length || state.check ||
      state.candidate || state.winningWorker || state.lastActivity || state.lastFailure || state.lastContextManifest ||
      state.usage || state.usageBeforeThread || state.usageAccounting || state.requestUsageAccounting ||
      state.failures?.length || Object.values(state.dispatchCounts ?? {}).some(value => value !== 0) ||
      state.coordination !== 'cooperative' || !state.workers?.length || state.workerCount !== state.workers.length ||
      state.worktree !== path.join(directory, 'worktree') || state.workers[0].id !== 'solver' ||
      state.workers[0].role !== 'lead' || state.workers.some((worker, index) =>
        worker.worktree !== path.join(directory, index ? `worktree-${index + 1}` : 'worktree') ||
        worker.phase !== 'prepared' || worker.turns !== 0 || worker.threadId || worker.previousThreadIds?.length ||
        worker.sessionTaskId || worker.sessionTaskVersion || worker.sessionAssignmentId || worker.sessionRole || worker.sessionGroupId ||
        worker.sessionStatementReview || worker.lastActivity || worker.lastFailure || worker.lastContextManifest || worker.check || worker.candidate ||
        worker.usage || worker.usageBeforeThread || worker.usageAccounting || worker.requestUsageAccounting || worker.failures?.length ||
        Object.values(worker.dispatchCounts ?? {}).some(value => value !== 0)) ||
      (!seeded && (state.cooperation !== undefined || state.continuationDigest !== undefined)))
    throw new Error('math_continuation_seed_requires_fresh_prepared_run');
  assertMathCanonicalPath(directory);
  const stat = fs.statSync(directory);
  if ((stat.mode & 0o077) || (process.getuid && stat.uid !== process.getuid()))
    throw new Error('math_state_directory_not_private');
  for (const worker of state.workers) assertMathCanonicalPath(worker.worktree);
  if (!repositoryRelativePath(state.problem.projectRelative) ||
      state.problem.ownedFiles.some(file => !repositoryRelativePath(file))) throw new Error('math_continuation_seed_invalid_source_path');
  const current = readSolverProblem(state.problem.workspace, state.problem.activeProblemPath);
  if (policyDigest(current) !== policyDigest(state.problem)) throw new Error('math_continuation_seed_source_policy_changed');
}

function validatePlan(state: SolverRunState, value: unknown) {
  const plan = parseCooperationPlan(state.problem, value);
  for (const task of plan.tasks) if (task.ownerId && !state.workers!.some(worker => worker.id === task.ownerId &&
    researchWorkerCanTask(worker, task)))
    throw new Error('math_plan_task_owner_unavailable');
  for (const group of plan.groups) if (group.engineerId &&
    !state.workers!.some(worker => worker.id === group.engineerId && worker.role === 'engineer'))
    throw new Error('math_plan_group_engineer_unavailable');
  return plan;
}

function capturedCapacityRecords(state: SolverRunState): CapacityRecord[] {
  const records = new Map<string, CapacityRecord>();
  const add = (node: Partial<Pick<TaskRecord, 'task' | 'capacityExploration' | 'status' | 'finding'>>, archived = false) => {
    if (!node.capacityExploration) return;
    const record = capacityRecord.parse({ task: node.task, capacityExploration: node.capacityExploration,
      status: node.status ?? 'blocked', ...(node.finding === undefined ? {} : { finding: node.finding }),
      ...(archived ? { archived: true } : {}) });
    records.set(canonicalMathJson([record.task.id, record.capacityExploration]), record);
  };
  for (const item of state.cooperation?.history ?? []) add(item, true);
  for (const node of state.cooperation?.tasks ?? []) add(node);
  return [...records.values()];
}

function capturedCompletedResearch(state: SolverRunState,
  previous: readonly CompletedResearchRecord[] = []): CompletedResearchRecord[] {
  const key = (record: CompletedResearchRecord) => 'record' in record ? `record:${record.record.id}` :
    canonicalMathJson(['legacy', taskVersion(record.task), 'inputDigest' in record ? record.inputDigest : null, record.finding]);
  const records = new Map<string, CompletedResearchRecord>(previous.map(record => [key(record), { ...record, archived: true }]));
  for (const node of state.cooperation!.history ?? []) if (continuableResearch(node.task) && node.researchCompletion) {
    const record = immutableCompletedResearchRecord.parse({ task: node.task, finding: node.finding,
      record: node.researchCompletion, archived: true });
    records.set(key(record), record);
  }
  for (const node of plannedTaskRecords(state.cooperation!.tasks)) {
    if (!continuableResearch(node.task) || node.status !== 'completed') continue;
    // A completion's inputs are fixed when it is published, never reconstructed
    // from newer canonical sources or guessed from equal finding text.
    const record = node.researchCompletion ? immutableCompletedResearchRecord.parse({ task: node.task, finding: node.finding,
      record: node.researchCompletion }) : unboundCompletedResearchRecord.parse({ task: node.task, finding: node.finding, archived: true });
    records.set(key(record), record);
  }
  return [...records.values()];
}

function currentCompletedResearch(source: SeedSource, state: SolverRunState, tasks: readonly CooperativeTask[],
  checkedTasks?: readonly TaskRecord[], deliveries?: readonly DeliveryRecord[]) {
  const context = source.researchContext;
  if (!context) return new Map<string, z.infer<typeof immutableCompletedResearchRecord>>();
  const view = { problemReceiptDigest: state.problem.receiptDigest, environmentDigest: state.environmentDigest,
    retrievalDigest: state.retrievalDigest, knowledgeDigest: state.knowledgeDigest,
    tasks: context.tasks, deliveries: context.deliveries };
  const sourceDigest = (task: CooperativeTask) => researchSourceDigest(scopedResearchSources(state.problem, task,
    source.canonicalSources, context.tasks));
  const current = new Map<string, z.infer<typeof immutableCompletedResearchRecord>>();
  for (const record of source.completedResearch ?? []) {
    const task = tasks.find(task => task.id === record.task.id);
    if (record.archived || !('record' in record) || !task ||
        restoreResearch(record.record, task, { ...view, sourceDigest: sourceDigest(task) }, record.finding).status !== 'completed') continue;
    current.set(task.id, record);
  }
  if (checkedTasks) {
    // Rechecks may invalidate a previously passing dependency. Remove affected
    // completions and their dependent findings until the advisory view is stable.
    let changed: boolean;
    do {
      changed = false;
      const checkedView = { ...view, deliveries: deliveries ?? context.deliveries,
        tasks: checkedTasks.map(node => continuableResearch(node.task) && !node.capacityExploration ?
          { ...node, status: current.has(node.task.id) ? 'completed' as const : 'pending' as const,
            finding: current.get(node.task.id)?.finding } : node) };
      for (const [id, record] of current) if (restoreResearch(record.record,
        tasks.find(task => task.id === id)!, { ...checkedView,
          sourceDigest: sourceDigest(tasks.find(task => task.id === id)!) }, record.finding).status !== 'completed') {
        current.delete(id); changed = true;
      }
    } while (changed);
  }
  return current;
}

function completedResearchHistory(source: SeedSource,
  current: ReturnType<typeof currentCompletedResearch> = new Map()) {
  return (source.completedResearch ?? []).filter(record => current.get(record.task.id) !== record)
    .map(record => ({ task: record.task, status: 'completed', finding: record.finding,
      ...('record' in record ? { researchCompletion: record.record } : {}) }));
}

function capacityOrigin(records: readonly CapacityRecord[]) {
  return records.map(({ task, capacityExploration, finding }) => ({ task, capacityExploration,
    ...(finding === undefined ? {} : { finding }) })).sort((left, right) =>
    canonicalMathJson(left).localeCompare(canonicalMathJson(right)));
}

function archivedCapacity(record: CapacityRecord) {
  return { task: record.task as CooperativeTask, capacityExploration: record.capacityExploration,
    status: record.status, producer: record.capacityExploration.workerId,
    ...(record.finding === undefined ? {} : { finding: record.finding }) };
}

function advisoryResearchDelivery(delivery: DeliveryRecord): DeliveryRecord {
  // Publication provenance is useful; old proof evidence, references, artifacts,
  // assignment keys and acceptance statuses are never replayed into the new host.
  return researchDelivery.parse({ id: delivery.id, producer: delivery.producer, taskId: delivery.taskId,
    taskDigest: delivery.taskDigest, groupId: delivery.groupId, kind: 'research',
    status: delivery.status === 'superseded' ? 'superseded' : 'advisory', statement: delivery.statement,
    premises: delivery.premises, dependencies: delivery.dependencies, remainingObligations: delivery.remainingObligations,
    summary: delivery.summary, evidenceRefs: delivery.evidenceRefs, createdAt: delivery.createdAt,
    commit: delivery.commit, sourceDigest: delivery.sourceDigest, finding: delivery.finding,
    findingDigest: delivery.findingDigest, researchRecord: delivery.researchRecord,
    mathematicalGap: delivery.mathematicalGap, mathematicalGapScope: delivery.mathematicalGapScope,
    lemmaRequests: delivery.lemmaRequests });
}

function capturedResearchContext(state: SolverRunState): z.infer<typeof researchContext> {
  return researchContext.parse({ environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest,
    tasks: researchSourceTasks(state.cooperation!.tasks).map(node => ({ ...node,
      proof: node.proof?.taskDigest ? node.proof : undefined,
      integratedCheck: node.integratedCheck?.taskDigest ? node.integratedCheck : undefined })),
    deliveries: (state.cooperation!.deliveries ?? []).filter(delivery => delivery.kind === 'research' &&
      delivery.taskId && delivery.taskDigest).map(advisoryResearchDelivery) });
}

const handoffDeliveryOrigin = ({ status: _status, ...delivery }: DeliveryRecord) => delivery;
function adoptedHandoffInputs(state: Parameters<typeof researchHandoffs>[0]) {
  const inputs = new Map<string, Set<string>>();
  if (!state.researchDecisions?.length) return inputs;
  for (const handoff of researchHandoffs(state)) if (handoff.status === 'adopted') for (const source of handoff.sources) {
    const current = inputs.get(source.deliveryId) ?? new Set<string>();
    for (const id of handoff.proposal.dependsOn) current.add(id);
    inputs.set(source.deliveryId, current);
  }
  return inputs;
}
function currentHandoffRecord(record: HandoffSource['records'][number], state: SolverRunState,
  adoptedInputs: ReadonlyMap<string, ReadonlySet<string>>): boolean {
  const { delivery, sourceTask } = record, nodes = new Map(state.cooperation?.tasks.map(node => [node.task.id, node]));
  const source = nodes.get(delivery.taskId!);
  if (record.environmentDigest !== state.environmentDigest || record.problemReceiptDigest !== state.problem.receiptDigest ||
      !sourceTask || !source || taskVersion(source.task) !== taskVersion(sourceTask) ||
      delivery.taskDigest !== taskVersion(sourceTask) || delivery.dependencies.some(reference =>
        !nodes.has(reference.taskId) || taskVersion(nodes.get(reference.taskId)!.task) !== reference.taskDigest)) return false;
  const proposals = new Map(delivery.lemmaRequests!.map(task => [task.id, task]));
  const inputs = [...new Set(delivery.lemmaRequests!.flatMap(task => task.dependsOn))];
  if (record.inputs.length !== inputs.length || new Set(record.inputs.map(input => input.taskId)).size !== inputs.length ||
      inputs.some(id => {
        const task = nodes.get(id)?.task ?? proposals.get(id);
        // The original input pins remain provenance. A current, context-bound
        // adoption can also retain its obligation after scheduling metadata edits.
        return !task || !record.inputs.some(reference => reference.taskId === id && reference.taskDigest !== null &&
          (reference.taskDigest === taskVersion(task) || adoptedInputs.get(delivery.id)?.has(id)));
      })) return false;
  if (source.capacityExploration) {
    const owner = state.workers?.find(worker => worker.id === source.capacityExploration!.workerId);
    if (!owner || !researchWorkerCanNode(owner, source) || !currentCapacityExploration(source, state.cooperation!.tasks,
      { environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest })) return false;
  }
  return true;
}

function restoredHandoffDeliveries(source: HandoffSource, state: SolverRunState): DeliveryRecord[] {
  const adoptedInputs = adoptedHandoffInputs({ ...state.cooperation!,
    deliveries: source.records.map(record => record.delivery), researchDecisions: source.decisions });
  return source.records.map(record => ({ ...record.delivery,
    status: record.delivery.status === 'superseded' || !currentHandoffRecord(record, state, adoptedInputs) ? 'superseded' : 'advisory' }));
}

function restoredResearchDeliveries(source: SeedSource, state: SolverRunState): DeliveryRecord[] {
  const nodes = new Map(state.cooperation!.tasks.map(node => [node.task.id, node.task]));
  const deliveries = new Map((source.researchContext?.deliveries ?? []).map(delivery => {
    const task = nodes.get(delivery.taskId!);
    const current = source.researchContext!.environmentDigest === state.environmentDigest &&
      source.researchContext!.problemReceiptDigest === state.problem.receiptDigest && task &&
      taskVersion(task) === delivery.taskDigest && delivery.dependencies.every(input =>
        nodes.has(input.taskId) && taskVersion(nodes.get(input.taskId)!) === input.taskDigest);
    return [delivery.id, { ...delivery, status: current ? delivery.status : 'superseded' as const }];
  }));
  for (const delivery of source.researchHandoffs ? restoredHandoffDeliveries(source.researchHandoffs, state) : [])
    deliveries.set(delivery.id, delivery);
  return [...deliveries.values()];
}

function capturedHandoffs(state: SolverRunState, previous?: HandoffSource): HandoffSource | undefined {
  const deliveries = state.cooperation!.deliveries?.filter(delivery => delivery.kind === 'research' && delivery.lemmaRequests?.length) ?? [];
  if (!deliveries.length && !previous) return undefined;
  const records = new Map<string, HandoffSource['records'][number]>(), originals = new Map(previous?.records.map(record =>
    [record.delivery.id, record]));
  const nodes = new Map(state.cooperation!.tasks.map(node => [node.task.id, node.task]));
  const adoptedInputs = adoptedHandoffInputs(state.cooperation!);
  for (const item of deliveries) {
    const delivery = handoffDelivery.parse(advisoryResearchDelivery(item)), original = originals.get(delivery.id);
    if (original && canonicalMathJson(handoffDeliveryOrigin(original.delivery)) !== canonicalMathJson(handoffDeliveryOrigin(delivery)))
      throw new Error('math_continuation_seed_handoff_changed');
    const sourceTask = [...state.cooperation!.tasks, ...(state.cooperation!.history ?? [])].find(node =>
      node.task.id === delivery.taskId && taskVersion(node.task) === delivery.taskDigest)?.task;
    const proposals = new Map(delivery.lemmaRequests!.map(task => [task.id, task]));
    const record = original ? { ...original, delivery: { ...delivery,
      status: original.delivery.status === 'superseded' ? 'superseded' as const : delivery.status } } : handoffRecord.parse({
      delivery, sourceTask, environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest,
      inputs: [...new Set(delivery.lemmaRequests!.flatMap(task => task.dependsOn))].map(taskId => {
        const task = nodes.get(taskId) ?? proposals.get(taskId);
        return { taskId, taskDigest: task ? taskVersion(task) : null };
      }) });
    if (!currentHandoffRecord(record, state, adoptedInputs)) record.delivery = { ...record.delivery, status: 'superseded' };
    records.set(delivery.id, record);
  }
  for (const record of previous?.records ?? []) if (!records.has(record.delivery.id))
    records.set(record.delivery.id, { ...record, delivery: { ...record.delivery, status: 'superseded' } });
  const decisions = new Map(previous?.decisions.map(decision => [decision.id, decision]));
  for (const decision of normalizedResearchHandoffDecisions(state.cooperation!)) if (records.has(decision.deliveryId))
    decisions.set(decision.id, handoffDecision.parse({ id: decision.id, deliveryId: decision.deliveryId, status: decision.status,
      taskId: decision.taskId, taskDigest: decision.taskDigest, reason: decision.reason, contextDigest: decision.contextDigest,
      waitsOn: decision.waitsOn }));
  const notes = new Map(previous?.notes.map(note => [canonicalMathJson([note.deliveryId, note.commit]), note]));
  for (const { delivery } of records.values()) if (delivery.commit) {
    const key = canonicalMathJson([delivery.id, delivery.commit]);
    if (!notes.has(key)) notes.set(key, { deliveryId: delivery.id, commit: delivery.commit,
      notes: committedSource(state.worktree, delivery.commit, 'RESEARCH.md') });
  }
  return handoffSource.parse({ records: [...records.values()], decisions: [...decisions.values()], notes: [...notes.values()] });
}

function captureSource(sourceStateFile: string, stateFile: string, state: SolverRunState): SeedSource {
  const archived = readSolverRunState(sourceStateFile);
  if (archived.runId === state.runId || archived.taskDigest !== state.taskDigest ||
      archived.problem.receiptDigest !== state.problem.receiptDigest || policyDigest(archived.problem) !== policyDigest(state.problem))
    throw new Error('math_continuation_seed_identity_changed');
  if (!archived.cooperation?.canonicalCommit || !archived.workers?.length)
    throw new Error('math_continuation_seed_source_incomplete');
  const planned = plannedTaskRecords(archived.cooperation.tasks);
  const plan = validatePlan(state, { tasks: planned.map(node => node.task),
    groups: archived.cooperation.groups?.map(record => record.group), proofRoutes: archived.cooperation.proofRoutes });
  if (plan.tasks.some((task, index) => taskVersion(task) !== taskVersion(planned[index].task)))
    throw new Error('math_continuation_seed_task_identity_changed');
  const common = commonDirectory(state.worktree), sourceDirectory = path.dirname(sourceStateFile);
  if (archived.worktree !== path.join(sourceDirectory, 'worktree') || commonDirectory(archived.worktree) !== common)
    throw new Error('math_continuation_seed_repository_changed');
  for (const [file, expected] of Object.entries(state.problem.trustedFiles))
    if (mathDigest(committedSource(archived.worktree, archived.cooperation.canonicalCommit,
      `${state.problem.projectRelative}/${file}`)) !== expected) throw new Error('math_continuation_seed_source_policy_changed');
  const canonicalSources = Object.fromEntries(state.problem.ownedFiles.map(file => [file,
    committedSource(archived.worktree, archived.cooperation!.canonicalCommit!, `${state.problem.projectRelative}/${file}`)]));
  const workers = archived.workers.map((worker, index) => {
    if (!id.safeParse(worker.id).success || worker.worktree !== path.join(sourceDirectory, index ? `worktree-${index + 1}` : 'worktree'))
      throw new Error('math_continuation_seed_worker_path_changed');
    assertMathCanonicalPath(worker.worktree);
    if (commonDirectory(worker.worktree) !== common) throw new Error('math_continuation_seed_repository_changed');
    const headBefore = git(worker.worktree, ['rev-parse', 'HEAD']);
    const sources = Object.fromEntries(state.problem.ownedFiles.map(file => [file,
      textFile(path.join(worker.worktree, state.problem.projectRelative, file))]));
    const notesFile = path.join(worker.worktree, 'RESEARCH.md');
    const notes = fs.lstatSync(notesFile, { throwIfNoEntry: false }) ? textFile(notesFile) : null;
    const activeTask = archived.cooperation!.tasks.find(node => node.task.id === worker.sessionTaskId && node.assignment?.workerId === worker.id) ??
      archived.cooperation!.tasks.find(node => node.status === 'running' && node.assignment?.workerId === worker.id);
    return { id: worker.id, role: worker.role, headBefore, headAfter: git(worker.worktree, ['rev-parse', 'HEAD']), sources, notes,
      assignment: activeTask?.assignment };
  });
  const proofHistory = (proof: TaskProof | undefined) => proof && ({ commit: proof.commit, taskDigest: proof.taskDigest,
    seedCommit: proof.seedCommit, passed: proof.passed, conditions: proof.conditions,
    receiptIds: proof.verification.results.map(result => result.receiptId).filter(Boolean) });
  const capacities = capturedCapacityRecords(archived);
  let previousCapacity: z.infer<typeof capacitySource> | undefined;
  let previousHandoffs: HandoffSource | undefined;
  let previousResearch: CompletedResearchRecord[] | undefined;
  if (archived.continuationDigest) {
    const snapshot = readContinuationSnapshot(path.join(sourceDirectory, 'continuation.json'), archived.continuationDigest,
      { taskDigest: archived.taskDigest, problemReceiptDigest: archived.problem.receiptDigest });
    const attachment = snapshot.manifest.attachments.find(item => item.id === 'seed-capacity-explorations');
    if (attachment) {
      const bytes = readMathFile(path.join(sourceDirectory, attachment.contentPath), attachment.bytes).bytes;
      if (bytes.length !== attachment.bytes || mathDigest(bytes) !== attachment.sha256)
        throw new Error('math_continuation_content_changed');
      previousCapacity = capacitySource.parse(JSON.parse(bytes.toString('utf8')));
      const captured = new Set(capacities.map(record => canonicalMathJson([record.task.id, record.capacityExploration])));
      for (const record of previousCapacity.records)
        if (!captured.has(canonicalMathJson([record.task.id, record.capacityExploration]))) capacities.push({ ...record, archived: true });
    }
    const handoffs = snapshot.manifest.attachments.find(item => item.id === 'seed-research-handoffs');
    if (handoffs) {
      const bytes = readMathFile(path.join(sourceDirectory, handoffs.contentPath), handoffs.bytes).bytes;
      if (bytes.length !== handoffs.bytes || mathDigest(bytes) !== handoffs.sha256)
        throw new Error('math_continuation_content_changed');
      previousHandoffs = handoffSource.parse(JSON.parse(bytes.toString('utf8')));
    }
    const research = snapshot.manifest.attachments.find(item => item.id === 'seed-completed-research');
    if (research) {
      const bytes = readMathFile(path.join(sourceDirectory, research.contentPath), research.bytes).bytes;
      if (bytes.length !== research.bytes || mathDigest(bytes) !== research.sha256)
        throw new Error('math_continuation_content_changed');
      previousResearch = z.array(completedResearchRecord).parse(JSON.parse(bytes.toString('utf8')));
    }
  }
  const capacityVersions = new Set(capacities.map(record =>
    canonicalMathJson([record.task.id, record.capacityExploration.taskDigest])));
  const notes = new Map<string, z.infer<typeof capacitySource>['notes'][number]>();
  for (const note of previousCapacity?.notes ?? []) if (capacityVersions.has(canonicalMathJson([note.taskId, note.taskDigest])))
    notes.set(canonicalMathJson([note.taskId, note.taskDigest, note.commit]), note);
  for (const delivery of archived.cooperation.deliveries ?? []) {
    if (delivery.kind !== 'research' || !delivery.commit || !delivery.taskId || !delivery.taskDigest ||
        !capacityVersions.has(canonicalMathJson([delivery.taskId, delivery.taskDigest]))) continue;
    const key = canonicalMathJson([delivery.taskId, delivery.taskDigest, delivery.commit]);
    if (!notes.has(key)) notes.set(key, { taskId: delivery.taskId, taskDigest: delivery.taskDigest,
      deliveryId: delivery.id, commit: delivery.commit,
      notes: committedSource(archived.worktree, delivery.commit, 'RESEARCH.md') });
  }
  const handoffs = capturedHandoffs(archived, previousHandoffs);
  const completedResearch = capturedCompletedResearch(archived, previousResearch);
  const context = capturedResearchContext(archived);
  const conditionalCandidates = planned.filter(node => !isAdvisoryTask(node.task) &&
    !(node.proof?.passed && !node.proof.conditions?.length) &&
    !(node.integratedCheck?.passed && !node.integratedCheck.conditions?.length) &&
    (node.proof?.passed && node.proof.conditions?.length || node.integratedCheck?.passed && node.integratedCheck.conditions?.length))
    .map(node => {
      const proof = node.proof?.passed && node.proof.conditions?.length ? node.proof : node.integratedCheck!;
      const evidence = { taskId: node.task.id, taskDigest: proof.taskDigest, commit: proof.commit,
        seedCommit: proof.seedCommit, conditions: proof.conditions!, dependencies: node.assignment?.dependencies ?? [] };
      try {
        if (!oid.safeParse(proof.commit).success || !oid.safeParse(proof.seedCommit).success)
          throw new Error('math_continuation_seed_conditional_commit_invalid');
        const read = (commit: string) => Object.fromEntries(state.problem.ownedFiles.map(file => [file,
          committedSource(archived.worktree, commit, `${state.problem.projectRelative}/${file}`)]));
        return { ...evidence, sources: read(proof.commit), seedSources: read(proof.seedCommit) };
      } catch (error) {
        return { ...evidence, captureError: error instanceof Error ? error.message : 'math_task_source_unavailable' };
      }
    });
  const value = { schema: 'theorem-os.continuation-seed-source.v1', capturedAt: Date.now(), taskDigest: state.taskDigest,
    problemReceiptDigest: state.problem.receiptDigest, sourcePolicyDigest: policyDigest(state.problem),
    destination: { runId: state.runId, stateFile, buildDigest: state.buildDigest,
      methodDigest: state.methodDigest, environmentDigest: state.environmentDigest },
    source: { runId: archived.runId, stateFile: sourceStateFile, stateDigest: mathDigest(canonicalMathJson(archived)),
      buildDigest: archived.buildDigest, methodDigest: archived.methodDigest, canonicalCommit: archived.cooperation.canonicalCommit,
      planVersion: archived.cooperation.planVersion },
    plan, canonicalSources, workers, conditionalCandidates,
    candidateIds: planned.filter(node => !isAdvisoryTask(node.task) &&
      ((node.proof?.passed && !node.proof.conditions?.length) ||
        (node.integratedCheck?.passed && !node.integratedCheck.conditions?.length))).map(node => node.task.id),
    ...(capacities.length || archived.cooperation.capacityExplorationInputs !== undefined ? { capacityExplorations: {
      records: capacities, inputs: archived.cooperation.capacityExplorationInputs, notes: [...notes.values()] } } : {}),
    ...(handoffs ? { researchHandoffs: handoffs } : {}),
    ...(completedResearch.length ? { completedResearch } : {}),
    ...(completedResearch.length || context.deliveries.length ? { researchContext: context } : {}),
    history: { evidence: 'recorded-not-replayed', sourcePhase: archived.phase,
      tasks: archived.cooperation.tasks.map(node => ({ taskId: node.task.id, taskDigest: taskVersion(node.task), status: node.status,
        attempts: node.attempts, assignment: node.assignment, finding: node.finding,
        proof: proofHistory(node.proof), integratedCheck: proofHistory(node.integratedCheck) })),
      deliveries: archived.cooperation.deliveries?.map(delivery => ({ id: delivery.id, kind: delivery.kind, status: delivery.status,
        taskId: delivery.taskId, taskDigest: delivery.taskDigest, commit: delivery.commit, producer: delivery.producer,
        summary: delivery.summary, evidenceRefs: delivery.evidenceRefs })),
      history: archived.cooperation.history?.map(record => ({ task: record.task, producer: record.producer, finding: record.finding,
        researchCompletion: record.researchCompletion,
        proof: proofHistory(record.proof), integratedCheck: record.integratedCheck && {
          commit: record.integratedCheck.commit, passed: record.integratedCheck.passed } })) },
  };
  return sourceSchema.parse(value);
}

function freezeSource(source: SeedSource, directory: string) {
  const documents: { id: string; kind: ContinuationManifest['attachments'][number]['kind']; text: string; commit?: null }[] = [
    { id: 'seed-recovery-guide', kind: 'research-notes' as const, text:
      'The canonical owned sources and exact task graph were explicitly initialized in this new run. Historical proof flags, threads and assignments do not authorize work or acceptance. Only freshly checked helpers are integrated; conditional proofs retain their typed obligations.\n' +
      'For an unfinished task, inspect draft-WORKER_ID for its complete source strings and RESEARCH.md notes. Match the captured task id and digest to your current assignment before recovering useful code. Preserve the current canonical proofs; recovered drafts still require ordinary typed host checks.\n' +
      'The original run may still be progressing. Its canonical sources are pinned to the recorded commit; worker files are individually stable captured bytes, not a globally atomic observation. Repeated initialization uses this same frozen capture.\n' },
    { id: 'seed-canonical', kind: 'proof-source' as const, text: canonicalMathJson({ sources: source.canonicalSources }) },
    { id: 'seed-task-graph', kind: 'diagnostics' as const, text: canonicalMathJson(source.plan) },
    { id: 'seed-history', kind: 'diagnostics' as const, text: canonicalMathJson({ source: source.source, history: source.history,
      capturedAt: source.capturedAt, capture: 'canonical-commit-and-individually-stable-advisory-worker-files' }) },
    ...source.workers.map(worker => ({ id: `draft-${worker.id}`, kind: 'proof-source' as const, text: canonicalMathJson(worker) })),
    ...(source.conditionalCandidates ?? []).map(candidate => ({ id: `conditional-${candidate.taskId}`, kind: 'proof-source' as const,
      text: canonicalMathJson(candidate) })),
    ...(source.capacityExplorations ? [{ id: 'seed-capacity-explorations', kind: 'research-notes' as const,
      text: canonicalMathJson(source.capacityExplorations), commit: null }] : []),
    ...(source.researchHandoffs ? [{ id: 'seed-research-handoffs', kind: 'research-notes' as const,
      text: canonicalMathJson(source.researchHandoffs), commit: null }] : []),
    ...(source.completedResearch ? [{ id: 'seed-completed-research', kind: 'research-notes' as const,
      text: canonicalMathJson(source.completedResearch), commit: null }] : []),
    ...(source.researchContext ? [{ id: 'seed-research-context', kind: 'research-notes' as const,
      text: canonicalMathJson(source.researchContext), commit: null }] : []),
  ];
  const manifest: ContinuationManifest = { schema: 'theorem-os.continuation-snapshot.v1', taskDigest: source.taskDigest,
    problemReceiptDigest: source.problemReceiptDigest, attachments: documents.map(document => {
      const sha256 = mathDigest(document.text);
      return { id: document.id, kind: document.kind, path: `${document.id}.json`, bytes: Buffer.byteLength(document.text), sha256,
        provenance: { evidence: 'recorded-not-replayed', runId: source.source.runId,
          ...(document.commit === null ? {} : { commit: source.source.canonicalCommit }),
          source: source.source.stateFile }, contentPath: `continuation/${sha256}.txt` };
    }) };
  return freezeContinuationInput({ manifest, digest: mathDigest(canonicalMathJson(manifest)),
    contents: new Map(documents.map(document => [mathDigest(document.text), document.text])) }, directory);
}

/** Explicit initialization of a new, idle run. Historical acceptance is never execution authority. */
export async function seedSolverContinuation(options: {
  sourceRun: string; run: string; root: string; buildManifest: string; signal: AbortSignal; timeoutMs?: number;
  onProgress?: (event: string, details: Record<string, unknown>) => void;
  lease?: MathLease; preparedEnvironment?: NodeJS.ProcessEnv;
  onSeeded?: (state: SolverRunState, freshChecks: TaskProof[]) => void;
}): Promise<ContinuationSeedReport> {
  const target = readRunInspection(options.run), sourceStateFile = path.basename(path.resolve(options.sourceRun)) === 'state.json'
    ? path.resolve(options.sourceRun) : `${path.resolve(options.sourceRun)}.runtime/state.json`;
  const stateFile = target.stateFile, directory = path.dirname(stateFile);
  assertMathCanonicalPath(sourceStateFile);
  if (sourceStateFile === stateFile) throw new Error('math_continuation_seed_identity_changed');
  const seedWithLease = async (lease: MathLease): Promise<ContinuationSeedReport> => {
    const state = readRunInspection(options.run).state;
    const sourceFile = path.join(directory, 'continuation-seed-source.json'), reportFile = path.join(directory, 'continuation-seed.json');
    const seeded = Boolean(fs.lstatSync(sourceFile, { throwIfNoEntry: false }));
    assertPrepared(state, stateFile, seeded);
    const buildFile = fs.realpathSync(options.buildManifest);
    readMathBuildManifest(buildFile, options.root, path.join(options.root, 'out', 'main'));
    if (mathDigest(readMathFile(buildFile).bytes) !== state.buildDigest) throw new Error('math_continuation_seed_build_changed');
    let source: SeedSource;
    if (seeded) {
      assertMathCanonicalPath(sourceFile);
      if ((fs.lstatSync(sourceFile).mode & 0o777) !== 0o400) throw new Error('math_continuation_seed_source_not_frozen');
      source = sourceSchema.parse(readMathJson(sourceFile));
    } else source = captureSource(sourceStateFile, stateFile, state);
    if (source.taskDigest !== state.taskDigest || source.problemReceiptDigest !== state.problem.receiptDigest ||
        source.sourcePolicyDigest !== policyDigest(state.problem) || source.source.stateFile !== sourceStateFile ||
        source.destination.runId !== state.runId || source.destination.stateFile !== stateFile ||
        source.destination.buildDigest !== state.buildDigest || source.destination.methodDigest !== state.methodDigest ||
        source.destination.environmentDigest !== state.environmentDigest ||
        canonicalMathJson(Object.keys(source.canonicalSources).sort()) !== canonicalMathJson([...state.problem.ownedFiles].sort()))
      throw new Error('math_continuation_seed_identity_changed');
    const plan = validatePlan(state, source.plan);
    const conditional = source.conditionalCandidates ?? [];
    const candidateIds = [...source.candidateIds, ...conditional.map(candidate => candidate.taskId)];
    if (new Set(candidateIds).size !== candidateIds.length || candidateIds.some(candidate =>
      !plan.tasks.some(task => task.id === candidate && !isAdvisoryTask(task))) || conditional.some(candidate =>
      !candidate.captureError && (canonicalMathJson(Object.keys(candidate.sources ?? {}).sort()) !==
        canonicalMathJson([...state.problem.ownedFiles].sort()) ||
        canonicalMathJson(Object.keys(candidate.seedSources ?? {}).sort()) !==
          canonicalMathJson([...state.problem.ownedFiles].sort())))) throw new Error('math_continuation_seed_candidates_invalid');
    const planVersion = mathDigest(canonicalMathJson(plan));
    const pendingResearch = new Map<string, z.infer<typeof immutableCompletedResearchRecord>>();
    const restoredResearch = state.cooperation ? currentCompletedResearch(source, state, plan.tasks,
      state.cooperation.tasks, restoredResearchDeliveries(source, state)) : pendingResearch;
    const matchesResearch = (node: TaskRecord, records: typeof pendingResearch) => {
      const record = records.get(node.task.id);
      return node.status === (record ? 'completed' : 'pending') && node.finding === record?.finding &&
        canonicalMathJson(node.researchCompletion ?? null) === canonicalMathJson(record?.record ?? null);
    };
    if (seeded && state.cooperation && (state.cooperation.planVersion !== planVersion ||
        canonicalMathJson(plannedTaskRecords(state.cooperation.tasks).map(node => node.task)) !== canonicalMathJson(plan.tasks) ||
        canonicalMathJson(capacityOrigin(capturedCapacityRecords(state))) !==
          canonicalMathJson(capacityOrigin(source.capacityExplorations?.records ?? [])) ||
        canonicalMathJson(state.cooperation.capacityExplorationInputs ?? []) !==
          canonicalMathJson(source.capacityExplorations?.inputs ?? []) ||
        (source.researchHandoffs || source.researchContext) && (canonicalMathJson(state.cooperation.deliveries ?? []) !==
          canonicalMathJson(restoredResearchDeliveries(source, state)) ||
          canonicalMathJson(state.cooperation.researchDecisions ?? []) !== canonicalMathJson(source.researchHandoffs?.decisions ?? [])) ||
        source.completedResearch && ![pendingResearch, restoredResearch].some(records =>
          state.cooperation.tasks.filter(node => isAdvisoryTask(node.task) && !node.capacityExploration)
            .every(node => matchesResearch(node, records))) ||
        state.cooperation.tasks.some(node => node.assignment && !conditional.some(candidate =>
          candidate.taskId === node.task.id && node.status === 'conditional' &&
          node.assignment!.taskDigest === candidate.taskDigest && node.assignment!.workerId === 'continuation'))))
      throw new Error('math_continuation_seed_destination_changed');
    if (seeded && state.cooperation) {
      const previous = fs.existsSync(reportFile) ? readMathJson(reportFile) as Partial<ContinuationSeedReport> : undefined;
      const head = git(state.worktree, ['rev-parse', 'HEAD']);
      if (![state.problem.baseCommit, state.cooperation.canonicalCommit].includes(head) ||
          (previous?.sourcesInstalled && (head !== state.cooperation.canonicalCommit ||
            git(state.worktree, ['status', '--porcelain', '--untracked-files=no']))))
        throw new Error('math_continuation_seed_destination_changed');
    }
    if (!seeded && (git(state.worktree, ['rev-parse', 'HEAD']) !== state.problem.baseCommit ||
        git(state.worktree, ['status', '--porcelain', '--untracked-files=no']) || fs.existsSync(path.join(state.worktree, 'RESEARCH.md'))))
      throw new Error('math_continuation_seed_destination_changed');
    lease.assertHeld();
    if (!seeded) writeMathJsonDurable(sourceFile, source, 0o400);
    const report: ContinuationSeedReport = { schema: 'theorem-os.continuation-seed.v1', sourceRunId: source.source.runId,
      runId: state.runId, sourceStateFile, stateFile, sourceDigest: mathDigest(canonicalMathJson(source)), stage: 'frozen',
      candidates: candidateIds, checked: [], failed: [], evidence: 'advisory-sources-require-recheck' };
    const saveReport = () => { lease.assertHeld(); writeMathJsonDurable(reportFile, report); };
    const emit = (event: string, details: Record<string, unknown> = {}) => options.onProgress?.(event, details);
    let proofEnvironment: Awaited<ReturnType<typeof prepareMathProofEnvironment>> | undefined;
    try {
      const snapshot = freezeSource(source, directory);
      report.snapshotDigest = snapshot.digest;
      if (state.continuationDigest && state.continuationDigest !== snapshot.digest)
        throw new Error('math_continuation_seed_destination_changed');
      readContinuationSnapshot(snapshot.file, snapshot.digest, { taskDigest: state.taskDigest, problemReceiptDigest: state.problem.receiptDigest });
      saveReport();
      const canonical = await withSolverWorktree(state.worktree, state.problem.baseCommit, async checkout => {
        for (const [file, text] of Object.entries(source.canonicalSources)) {
          const target = path.join(checkout, state.problem.projectRelative, file); assertMathCanonicalPath(target);
          fs.mkdirSync(path.dirname(target), { recursive: true }); fs.writeFileSync(target, text);
        }
        assertSolverSources(state.problem, checkout);
        const commit = commitSolverSources(state.problem, checkout);
        git(state.worktree, ['update-ref', `refs/math/${state.runId}/continuation/source`, commit]);
        return commit;
      });
      lease.signal.throwIfAborted();
      report.canonicalCommit = canonical; report.stage = 'installing'; saveReport();
      const capacities = source.capacityExplorations?.records ?? [];
      const tasks: TaskRecord[] = plan.tasks.map(task => ({ task, attempts: 0,
        status: 'pending',
        ...(plan.proofRoutes?.length ? { alternativeRoutes: plan.proofRoutes.filter(route => route.targetTaskId === task.id) } : {}) }));
      for (const record of capacities.filter(item => !item.archived)) tasks.push({ task: record.task as CooperativeTask,
        capacityExploration: record.capacityExploration, attempts: 0,
        status: record.status === 'completed' ? 'completed' : 'pending',
        ...(record.finding === undefined ? {} : { finding: record.finding }) });
      state.continuationDigest = snapshot.digest;
      state.cooperation = { tasks, groups: plan.groups.map(group => ({ group, turns: 0 })), proofRoutes: plan.proofRoutes,
        canonicalCommit: canonical, leadSeedCommit: canonical, planVersion, planEdited: true,
        ...(source.capacityExplorations?.inputs === undefined ? {} : {
          capacityExplorationInputs: source.capacityExplorations.inputs.map(entry => ({ ...entry })) }),
        deliveries: [], history: [...capacities.filter(record => record.archived).map(archivedCapacity),
          ...completedResearchHistory(source)], edits: [], cursors: {} };
      state.cooperation.deliveries = restoredResearchDeliveries(source, state);
      if (source.researchHandoffs) {
        state.cooperation.researchDecisions = source.researchHandoffs.decisions.map(decision => ({ ...decision }));
      }
      // Publish pending obligations before installing sources; interruption cannot manufacture acceptance.
      writeSolverRunState(stateFile, state);
      git(state.worktree, ['reset', '--hard', canonical]);
      assertSolverSources(state.problem, state.worktree);
      report.sourcesInstalled = true; saveReport();
      emit('continuation_seed_installed', { sourceRunId: source.source.runId, runId: state.runId, tasks: tasks.length,
        candidates: candidateIds.length, snapshotDigest: snapshot.digest });
      const environmentFile = path.join(directory, 'environment-solver.json');
      assertMathCanonicalPath(environmentFile);
      if ((fs.lstatSync(environmentFile).mode & 0o777) !== 0o400) throw new Error('math_continuation_seed_environment_not_frozen');
      const staticEnv = { ...(options.preparedEnvironment ??
        resolveMathematicsRuntimeEnvironment({ DEEPSCIENTIST_MATH_ENV_FILE: environmentFile })) };
      // Startup-only already disposed its lease. Keep the frozen static identity and
      // authorized cache settings, but never resolve or reuse that temporary descriptor.
      if (!options.preparedEnvironment) {
        delete staticEnv[MATH_PROOF_ENVIRONMENT_ENV];
        delete staticEnv[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV];
      }
      const project = path.join(state.worktree, state.problem.projectRelative);
      const packages = resolveMathematicsLakePackagesCache(project, staticEnv);
      if (!packages) throw new Error('math_lake_packages_unavailable');
      bindLeanPackages(project, packages);
      const overrides = path.join(project, '.lake', 'package-overrides.json');
      assertMathCanonicalPath(overrides);
      fs.rmSync(overrides, { force: true });
      const timeoutMs = options.timeoutMs ?? 180_000;
      if (!options.preparedEnvironment) proofEnvironment = await prepareMathProofEnvironment(project, packages, { env: staticEnv, signal: lease.signal,
        deadlineAt: Number.isFinite(timeoutMs) ? Date.now() + timeoutMs : undefined,
        cacheRoot: DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT,
        onProgress: phase => emit('continuation_seed_proof_environment', { phase }) });
      const env = proofEnvironment ? { ...staticEnv, [MATH_PROOF_ENVIRONMENT_ENV]: proofEnvironment.environmentValue } : staticEnv;
      report.stage = 'checking'; saveReport();
      state.cooperation.recheck = { canonicalCommit: canonical, total: candidateIds.length, completed: 0 };
      writeSolverRunState(stateFile, state);
      const freshChecks: TaskProof[] = [];
      type Candidate = { node: TaskRecord; sourceCommit: string; request: TaskProofRequest;
        savedConditional?: (typeof conditional)[number] };
      const prepareCandidate = async (node: TaskRecord): Promise<Candidate> => {
        const taskId = node.task.id, savedConditional = conditional.find(candidate => candidate.taskId === taskId);
        let sourceCommit = canonical, assignment = { taskId, taskDigest: taskVersion(node.task),
          workerId: 'continuation', seedCommit: canonical } as NonNullable<TaskRecord['assignment']>;
        let conditions: CooperativeTask[] = [];
        if (savedConditional) {
          if (savedConditional.captureError) throw new Error(savedConditional.captureError);
          if (savedConditional.taskDigest !== taskVersion(node.task) || !savedConditional.sources ||
              !savedConditional.seedSources) throw new Error('math_task_condition_version_invalid');
          const byId = new Map(tasks.map(item => [item.task.id, item.task]));
          const references = (items: readonly { taskId: string; taskDigest: string }[]) => items.map(reference => {
            const task = byId.get(reference.taskId);
            if (!task || taskVersion(task) !== reference.taskDigest) throw new Error('math_task_condition_version_invalid');
            return task;
          });
          conditions = references(savedConditional.conditions);
          const dependencies = references(savedConditional.dependencies);
          if (!conditions.every(task => task.kind === 'lemma' && task.type?.trim() &&
              dependencies.some(dependency => dependency.id === task.id)) || new Set(conditions.map(task => task.id)).size !== conditions.length)
            throw new Error('math_task_condition_version_invalid');
          const frozen = await withSolverWorktree(state.worktree, state.problem.baseCommit, async checkout => {
            const write = (sources: Record<string, string>) => {
              for (const [file, text] of Object.entries(sources)) {
                const target = path.join(checkout, state.problem.projectRelative, file);
                assertMathCanonicalPath(target); fs.mkdirSync(path.dirname(target), { recursive: true }); fs.writeFileSync(target, text);
              }
              return commitSolverSources(state.problem, checkout);
            };
            const seedCommit = write(savedConditional.seedSources!);
            const proofCommit = write(savedConditional.sources!);
            return { seedCommit, proofCommit };
          });
          assignment = { ...assignment, seedCommit: frozen.seedCommit, dependencies: savedConditional.dependencies };
          if (!node.task.conditional) assignment.connectionCheck = createTaskConnectionCheck(node.task, assignment,
            tasks.map(item => conditions.some(condition => condition.id === item.task.id) ? { ...item, status: 'pending' } : item),
            { environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest },
            task => savedConditional.seedSources![task.proofPath!] ?? '');
          sourceCommit = frozen.proofCommit;
          git(state.worktree, ['update-ref', `refs/math/${state.runId}/continuation/conditional/${taskId}`, sourceCommit]);
        }
        return { node, savedConditional, sourceCommit, request: { task: node.task, retainedGoals: [], assignment,
          ...(conditions.length ? { conditions } : {}) } };
      };
      const blockCandidate = (node: TaskRecord, error: unknown) => {
        lease.signal.throwIfAborted(); lease.assertHeld();
        node.status = 'blocked'; node.integratedCheck = undefined; node.proof = undefined; node.assignment = undefined;
        node.feedback = error instanceof Error ? error.message : 'math_continuation_seed_helper_check_failed';
      };
      const completeCandidate = (node: TaskRecord) => {
        lease.signal.throwIfAborted(); lease.assertHeld();
        const taskId = node.task.id;
        report.checked.push(taskId);
        if (node.status === 'blocked') report.failed.push(taskId);
        if (node.status === 'integrated') report.evidence = 'fresh-helper-receipts';
        state.cooperation.recheck.completed++; state.cooperation.recheck.taskId = undefined;
        state.cooperation.deliveries = restoredResearchDeliveries(source, state);
        writeSolverRunState(stateFile, state); saveReport();
        emit('continuation_seed_checked', { taskId, passed: node.status === 'integrated' || node.status === 'conditional' });
      };
      const publishCandidate = (candidate: Candidate, proof: TaskProof) => {
        const { node, savedConditional, sourceCommit, request: { assignment } } = candidate;
        try {
          lease.signal.throwIfAborted(); lease.assertHeld();
          const fresh = proof.passed && isAttributedTaskProof(proof) &&
            proof.taskDigest === taskVersion(node.task) && proof.commit === sourceCommit && proof.seedCommit === assignment.seedCommit &&
            canonicalMathJson(proof.conditions ?? []) === canonicalMathJson(savedConditional?.conditions ?? []) &&
            proof.verification.status === 'kernel_verified' && proof.verification.results.length > 0 &&
            proof.verification.results.every(result => result.status === 'kernel_verified' && typeof result.receiptId === 'string' && result.receiptId);
          for (const commit of [proof.commit, proof.verification.targetCommit]) if (commit) {
            if (!oid.safeParse(commit).success) throw new Error('math_continuation_seed_invalid_receipt_commit');
            git(state.worktree, ['update-ref', `refs/math/${state.runId}/evidence/${commit}`, commit]);
          }
          if (savedConditional) {
            node.proof = proof;
            node.assignment = fresh ? assignment : undefined;
            node.status = fresh ? 'conditional' : 'blocked';
          } else {
            node.integratedCheck = proof;
            node.status = fresh ? 'integrated' : 'blocked';
            if (fresh) freshChecks.push(proof);
          }
          node.feedback = fresh ? undefined : 'math_continuation_seed_helper_not_verified';
        } catch (error) {
          blockCandidate(node, error);
        }
        completeCandidate(node);
      };
      const projectors = new Map<string, ReturnType<typeof createTaskSourceProjector>>();
      const groups = new Map<string, Candidate[]>();
      const batches: (Candidate[] | { node: TaskRecord; error: unknown })[] = [];
      for (const taskId of candidateIds) {
        lease.signal.throwIfAborted(); lease.assertHeld();
        const node = tasks.find(node => node.task.id === taskId)!;
        try {
          const candidate = await prepareCandidate(node), { sourceCommit, request } = candidate;
          lease.signal.throwIfAborted(); lease.assertHeld();
          let project = projectors.get(sourceCommit);
          if (!project) {
            project = createTaskSourceProjector(state.problem, state.worktree, sourceCommit);
            projectors.set(sourceCommit, project);
          }
          const projection = project(request.task, request.retainedGoals, request.conditions);
          const key = mathDigest(canonicalMathJson({ sourceCommit, sources: [...projection], retainedGoals: request.retainedGoals,
            conditions: request.conditions?.map(task => ({ taskId: task.id, taskDigest: taskVersion(task) })) ?? [],
            premises: request.task.premises ?? [], environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest }));
          let group = groups.get(key);
          if (!group || group.length === maxSeedBatchSize) { group = []; groups.set(key, group); batches.push(group); }
          group.push(candidate);
        } catch (error) {
          lease.signal.throwIfAborted(); lease.assertHeld();
          batches.push({ node, error });
        }
      }
      const checkBatch = async (batch: Candidate[]): Promise<void> => {
        lease.signal.throwIfAborted(); lease.assertHeld();
        let proofs: TaskProof[];
        try {
          proofs = await checkTaskProofs(state.problem, state.worktree, batch[0].sourceCommit, batch.map(candidate => candidate.request),
            env, lease.signal, timeoutMs, state.environmentDigest);
        } catch (error) {
          lease.signal.throwIfAborted(); lease.assertHeld();
          if (batch.length > 1 && error instanceof Error && seedBatchFallbacks.has(rejectionCode(error))) {
            for (const candidate of batch) await checkBatch([candidate]);
          } else for (const { node } of batch) { blockCandidate(node, error); completeCandidate(node); }
          return;
        }
        for (const [index, candidate] of batch.entries()) publishCandidate(candidate, proofs[index]);
      };
      // Groups run sequentially. A batch shares compilation, while every target
      // still publishes its own fresh receipt and durable progress independently.
      for (const batch of batches) {
        lease.signal.throwIfAborted(); lease.assertHeld();
        const nodes = Array.isArray(batch) ? batch.map(candidate => candidate.node) : [batch.node];
        state.cooperation.recheck.taskId = nodes[0].task.id; writeSolverRunState(stateFile, state);
        for (const node of nodes) emit('continuation_seed_check', { taskId: node.task.id, batchSize: nodes.length });
        if (Array.isArray(batch)) await checkBatch(batch);
        else { blockCandidate(batch.node, batch.error); completeCandidate(batch.node); }
      }
      // Rechecking typed inputs may retire a former investigation. Keep its frozen
      // provenance and tombstone without importing an old assignment or acceptance.
      for (const record of capacities.filter(item => !item.archived)) {
        const index = tasks.findIndex(node => node.task.id === record.task.id), node = tasks[index];
        const owner = state.workers!.find(worker => worker.id === record.capacityExploration.workerId);
        if (node && owner && researchWorkerCanNode(owner, node) && currentCapacityExploration(node, tasks,
          { environmentDigest: state.environmentDigest, problemReceiptDigest: state.problem.receiptDigest })) continue;
        if (index >= 0) tasks.splice(index, 1);
        state.cooperation.history!.push(archivedCapacity(record));
      }
      state.cooperation.deliveries = restoredResearchDeliveries(source, state);
      const completedResearch = currentCompletedResearch(source, state, plan.tasks, tasks, state.cooperation.deliveries);
      for (const node of tasks.filter(node => isAdvisoryTask(node.task) && !node.capacityExploration)) {
        const completion = completedResearch.get(node.task.id);
        node.status = completion ? 'completed' : 'pending';
        node.finding = completion?.finding; node.researchCompletion = completion?.record;
      }
      state.cooperation.history = [...state.cooperation.history!.filter(record => 'capacityExploration' in record),
        ...completedResearchHistory(source, completedResearch)];
      writeSolverRunState(stateFile, state);
      report.stage = 'complete'; saveReport();
      options.onSeeded?.(state, freshChecks);
      return report;
    } catch (error) {
      report.stage = 'interrupted'; report.error = error instanceof Error ? error.message : 'math_continuation_seed_failed';
      // Already published helper checks are fresh; every unchecked obligation remains pending.
      lease.assertOwned(); writeMathJsonDurable(reportFile, report);
      throw error;
    } finally {
      await proofEnvironment?.dispose();
    }
  };
  return options.lease ? seedWithLease(options.lease) :
    withMathRuntimeLease({ lockPath: path.join(directory, 'run.lock'), flockExecutable: '/usr/bin/flock', signal: options.signal }, seedWithLease);
}
