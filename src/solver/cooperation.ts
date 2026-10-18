import { parseCooperationPlan, isAdvisoryTask as advisory } from './tasks';
export { parseCooperationPlan } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, readMathText, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { limitMathOutput } from '../math/mathProcess';
import { mathGitResult } from '../math/mathGit';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../math/leanSource';
import type { LeanStatementContext } from '../math/leanStatementContext';
import { commitSolverSources, committedSource, git, solverProofImports, withSolverWorktree, type SolverProblem } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import type { SolverRunState } from './archive';
import { independentFeasibilityWorker, type ResearchWorker } from './modules/organization';
import type { ContextBundle } from './modules/context';
import { proofReceiptsMatch, type ProofCheck } from './modules/evidence';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { originalGoalTaskFocus, researchCanAdvance, routeAllowsTask, taskCanStart, taskDependenciesReady, plannedTaskDependencyIds, selectedTaskRoute } from './modules/search';
import { deliveryDetails, reviewVerdict, readDeliveryLines, readMathResponse as block, MAX_RESEARCH_NOTES_BYTES, type DeliveryRecord } from './deliveries';
import { applyTaskChanges, checkTaskProof, checkTaskProofs, omitTaskHelpers, ownedSourceDigest, projectTaskSources, taskChanges, type TaskProof } from './cooperativeProof';
import { assertStatementSnapshot, captureStatementContexts, isStatementAction, readBacktranslation, resetStatementReview, statementReviewSummary, statementSnapshot, writeStatementSnapshot,
  type StatementAction, type StatementReview } from './statementReview';
import { captureProofReferences, proofReferencesUnchanged, type ProofReferences } from './proofReferences';
import { buildProofContinuation } from './progress';
import { captureDeliveryArtifacts, diagnoseUnbackedLeanClaims, validateDeliveryArtifactClaims, type DeliveryArtifactManifest } from './deliveryArtifacts';
import { validateLemmaRequests } from './taskProposals';
import { recordRouteBlockers, refreshRouteBlockers, routeBlockerBasis, validateBlockerProposals, type BlockerBasis, type RouteBlocker } from './routeControl';
import { parseProofRoutes, type ProofRoute } from './proofRoutes';
import { attributeTaskReferences } from './taskReferenceAttribution';
import { pendingResearchHandoffs, retainedResearchHandoffs, researchHandoffs, resolveResearchHandoffs, selectResearchHandoffBatch, type ResearchHandoffDecision } from './researchHandoffs';
import { captureObligationSnapshot, diffObligationProgress, type ObligationSnapshot, type ObligationProgressReceipt } from './obligationProgress';
import { taskConsumerProjection, type TaskConsumerProjection } from './taskConsumers';

import { isFeasibilityReview, taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile, markTaskReferences, hasTaskReferences, markTaskAcceptance, hasTaskAcceptance, invalidatedTaskIds,
  type CooperativeTask, type RouteGroup, type RouteRecord, type TaskAssignment, type TaskRecord, type CooperativeAction } from './tasks';
export { taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile } from './tasks';
export type { CooperativeTask, RouteGroup, RouteRecord, TaskAssignment, TaskRecord, CooperativeAction } from './tasks';
const digest = taskVersion;
const taskSourceRejections = new Set(['math_task_source_outside_scope', 'math_task_ambiguous_declaration',
  'math_task_existing_declaration_removed', 'math_task_existing_declaration_changed', 'math_task_requires_theorem',
  'math_task_helper_is_original_declaration', 'math_task_conditional_header_unsupported',
  'math_original_declaration_changed', 'math_original_context_changed', 'math_local_module_import_cycle',
  'math_trusted_source_changed', 'math_source_outside_ownership']);
const integrationRejections = new Set([...taskSourceRejections, 'math_task_condition_version_invalid',
  'math_task_delivery_no_longer_checks', 'math_task_dependency_invalidated', 'math_task_merged_proof_failed',
  'math_task_integration_conflict', 'math_task_integration_missing_context', 'math_task_integration_missing_declaration',
  'math_task_missing_declaration', 'math_task_check_identity_changed']);
const directDeliveryRejections = new Set([...taskSourceRejections, 'math_task_missing_declaration', 'math_task_repeated_failed_input',
  'math_task_check_identity_changed',
  'math_research_delivery_invalid', 'math_research_delivery_unchanged', 'math_research_lemma_requests_invalid',
  'math_delivery_invalid', 'math_response_invalid', 'math_math-result_missing_or_too_large', 'math_math-result_requires_one_block',
  'math_delivery_artifact_not_regular_file', 'math_delivery_artifact_too_large', 'math_delivery_artifact_invalid_commit',
  'math_delivery_artifact_path_invalid', 'math_delivery_artifact_claim_invalid', 'math_delivery_artifact_required', 'math_route_blocker_invalid']);
const rejectionCode = (error: Error) => error.message.split(/[\n:]/u, 1)[0];

export type ReviewRecord = { commit: string; sourceDigest: string; status: 'pending' | 'running' | 'accepted' | 'changes_requested';
  workerId?: string; assignmentId?: string; summary?: string };
export type HumanEditRecord = { id: string; status: 'received' | 'applied' | 'rejected'; reason?: string;
  receivedAt?: number; appliedAt?: number; baseVersion?: string; planVersion?: string; affectedTasks?: string[]; pendingSync?: boolean;
  recheck?: { status: 'pending' | 'passed' | 'failed' | 'not-required' | 'superseded';
    tasks: { taskId: string; taskDigest: string; status: 'pending' | 'conditional' | 'passed' | 'failed' | 'removed' | 'superseded'; reason?: string;
      lastCheck?: { commit: string; sourceDigest: string; environmentDigest: string; passed: boolean; conditional: boolean; receiptIds: string[] } }[] } };
type FailedTaskInput = { id: string; taskId: string; taskDigest: string; inputDigest: string; basis: BlockerBasis;
  sourceDigest: string; targetDigest: string; seedSourceDigest: string; seedTargetDigest: string;
  canonicalSourceDigest: string; canonicalTargetDigest: string; feedback: string;
  repair?: { taskId: string; taskDigest: string; workerId: string; pending: boolean; startedAttempt?: number } };
export type CooperationState = { tasks: TaskRecord[]; groups?: RouteRecord[]; canonicalCommit?: string; leadSeedCommit?: string; review?: ReviewRecord; error?: string;
  /** Context-only reverse uses, projected from the full archive without expanding execution visibility. */
  consumerInterfaces?: TaskConsumerProjection;
  history?: { task: CooperativeTask; producer?: string; proof?: TaskProof; integratedCheck?: ProofCheck; finding?: string }[];
  deliveries?: DeliveryRecord[]; cursors?: Record<string, number>; edits?: HumanEditRecord[];
  researchDecisions?: ResearchHandoffDecision[];
  planVersion?: string; planEdited?: boolean; statementReviews?: StatementReview[];
  helpRequestDigest?: string;
  planRejection?: { proposalDigest: string; inputDigest: string; error: string; stalled: boolean };
  lastLeadInputDigest?: string;
  frontierRecoveries?: { id: string; taskIds: string[]; goalIds: string[];
    status: 'requested' | 'planned' | 'awaiting-input'; taskInputDigests: string[]; readyTaskIds?: string[]; reason?: string;
    investigationTaskId?: string }[];
  frontierWaiting?: { inputDigest: string; taskIds: string[]; goalIds: string[]; reason: 'awaiting-new-mathematical-input' };
  failedTaskInputs?: FailedTaskInput[];
  blockers?: RouteBlocker[];
  proofRoutes?: ProofRoute[];
  progressSnapshot?: ObligationSnapshot;
  progressReceipts?: ObligationProgressReceipt[];
  unchangedResearch?: Record<string, { taskDigest: string; notesBlob: string; count: number }>;
  researchCheckpoints?: Record<string, { taskDigest: string; inputDigest: string; outputDigest: string; count: number;
    paused?: boolean; blockerId?: string }>;
  researchDrafts?: Record<string, { taskDigest: string; workerId: string; assignmentId?: string; seedCommit: string; canonicalCommit?: string;
    commit: string; outputDigest: string; artifacts: DeliveryArtifactManifest; suspended?: boolean }>;
  recheck?: { canonicalCommit: string; total: number; completed: number; taskId?: string };
  initialPlanFallback?: { at: number; reason: string } };
type TaskVersions = ReadonlyMap<string, { task: CooperativeTask; version: string }>;

const bounded = (text: string, bytes: number) => limitMathOutput(text, bytes, 'head');
/** Model proposes tasks; the host validates coverage, exact targets and an acyclic dependency graph. */
export function readCooperationPlan(problem: SolverProblem, worktree: string): ReturnType<typeof parseCooperationPlan> {
  return parseCooperationPlan(problem, block(worktree, 'math-plan'));
}

/** Lead plans; workers claim distinct ready obligations; only checked source enters the canonical proof. */
export class CooperativeResearch {
  private readonly lead: ResearchWorker;
  private readonly archive: CooperationState;
  private needsLead = false;
  private lastAssembly?: string;
  private waiters = new Set<() => void>();
  private reservedTurns = new Set<string>();
  private liveWorkers: Set<string>;
  private checkedDeliveries = new WeakSet<TaskProof>();
  private checkedStatementReferences = new WeakSet<ProofReferences>();
  private statementContexts = new Map<string, LeanStatementContext>();
  private preparingStatements?: Promise<void>;
  private active = new Map<string, { action: CooperativeAction; interrupt: () => Promise<void>; notify: (message: string) => Promise<void>; cancelled?: boolean }>();
  private notifications = new Set<Promise<void>>();
  private pendingPulse?: Promise<ReadonlyMap<string, Promise<void>>>;
  private deliveryChecks = new Map<string, Promise<void>>();
  private leadEvidence = new WeakMap<CooperativeAction, string>();
  private checkingTaskInputs = new Map<string, Promise<void>>();
  private leanSourceDigests = new Map<string, string>();
  private timer?: NodeJS.Timeout;
  private stopping = false;
  private failure?: Error;
  private pinned = new Set<string>();
  constructor(private readonly input: { state: SolverRunState; workers: readonly ResearchWorker[];
    access: ReadonlyMap<string, WorkerAccess>; signal: AbortSignal; timeoutMs?: number;
    continuousResearch?: boolean;
    modelDispatchAllowed?: () => boolean;
    save: () => void; emit: (event: string, details?: Record<string, unknown>) => void;
    modules: SolverModules; exclusiveCheck: <T>(check: () => Promise<T>) => Promise<T> }) {
    this.lead = input.workers[0];
    this.archive = input.state.cooperation ??= { tasks: [] };
    this.archive.proofRoutes = parseProofRoutes(this.archive.proofRoutes, this.archive.tasks.map(node => node.task));
    this.syncProofRoutes();
    if (!this.archive.canonicalCommit) {
      this.archive.canonicalCommit = git(this.lead.worktree, ['rev-parse', 'HEAD']);
      if (!this.primaryLed) this.archive.leadSeedCommit ??= this.archive.canonicalCommit;
    }
    this.liveWorkers = new Set(input.workers.map(worker => worker.id));
    this.needsLead = !this.archive.tasks.length || Boolean(this.archive.error) ||
      pendingResearchHandoffs(this.archive).length > 0 ||
      (this.archive.tasks.some(node => node.status === 'blocked') && this.archive.lastLeadInputDigest !== this.planningInputDigest());
  }
  private get livePeers() { return this.input.workers.filter(worker => worker.id !== this.lead.id && this.liveWorkers.has(worker.id)); }
  private get primaryLed() { return this.input.modules.M5.primaryLed === true; }
  private syncProofRoutes() {
    for (const node of this.archive.tasks) node.alternativeRoutes = this.archive.proofRoutes?.filter(route => route.targetTaskId === node.task.id);
  }
  private syncEditChecks(nodes: ReadonlyMap<string, TaskRecord>, versions: TaskVersions) {
    for (const edit of this.archive.edits ?? []) {
      if (edit.status !== 'applied' || !edit.recheck) continue;
      const before = canonicalMathJson(edit.recheck);
      for (const result of edit.recheck.tasks) {
        if (['removed', 'superseded'].includes(result.status)) continue;
        const node = nodes.get(result.taskId);
        if (!node || versions.get(result.taskId)?.version !== result.taskDigest) {
          result.status = 'superseded';
          continue;
        }
        const proof = node.integratedCheck ?? node.proof;
        const fresh = proof && proof.taskDigest === result.taskDigest && this.checkedDeliveries.has(proof);
        result.status = node.status === 'blocked' ? 'failed' : fresh && node.status === 'integrated' && proof.passed && !proof.conditions?.length ? 'passed' :
          fresh && node.status === 'conditional' ? 'conditional' : 'pending';
        result.reason = node.status === 'blocked' ? node.feedback : undefined;
        if (fresh) result.lastCheck = { commit: proof.commit, sourceDigest: proof.sourceDigest,
          environmentDigest: this.input.state.environmentDigest, passed: proof.passed, conditional: Boolean(proof.conditions?.length),
          receiptIds: proof.verification.results.map(receipt => receipt.receiptId) };
      }
      const statuses = edit.recheck.tasks.map(result => result.status);
      edit.recheck.status = statuses.every(status => status === 'removed') ? 'not-required' :
        statuses.includes('failed') ? 'failed' : statuses.some(status => status === 'pending' || status === 'conditional') ? 'pending' :
        statuses.includes('superseded') ? 'superseded' : 'passed';
      if (before !== canonicalMathJson(edit.recheck)) this.input.emit('edit_recheck_updated', { id: edit.id, recheck: edit.recheck });
    }
  }
  private refreshFeasibilityAssignments() {
    let changed = false;
    for (const node of this.archive.tasks) {
      const assignment = node.assignment;
      if (!assignment || !isFeasibilityReview(node.task) || !['pending', 'running'].includes(node.status)) continue;
      const worker = this.input.workers.find(worker => worker.id === assignment.workerId);
      if (worker && independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups)) continue;
      node.status = 'pending'; node.assignment = undefined;
      node.feedback = 'math_feasibility_review_independence_lost: Reassign this advisory review to a peer who does not own or produce the inspected inputs.';
      const draft = this.archive.researchDrafts?.[node.task.id];
      if (draft?.assignmentId === assignment.assignmentId && draft.workerId === assignment.workerId) draft.suspended = true;
      const active = this.active.get(assignment.workerId);
      if (active?.action.kind === 'task' && active.action.assignment === assignment && !active.cancelled) {
        active.cancelled = true; void active.interrupt().catch(() => {});
      }
      if (node.task.ownerId) this.needsLead = true;
      this.input.emit('feasibility_review_reassigned', { taskId: node.task.id, workerId: assignment.workerId,
        assignmentId: assignment.assignmentId, reason: 'reviewer-no-longer-independent', draftCommit: draft?.commit });
      changed = true;
    }
    return changed;
  }
  private changed(edit?: HumanEditRecord) {
    this.refreshFeasibilityAssignments();
    this.refreshResearchCheckpoints();
    for (const blocker of refreshRouteBlockers(this.archive.blockers ?? [], this.archive.tasks,
      this.input.state.environmentDigest, this.input.state.problem.receiptDigest)) {
      this.needsLead = true;
      this.input.emit('route_reopened', { blockerId: blocker.id, taskId: blocker.taskId, reason: blocker.reopenedReason });
    }
    this.refreshFailedTaskInputs();
    const snapshot = captureObligationSnapshot(this.archive.tasks, { groups: this.archive.groups,
      environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes, blockers: this.archive.blockers });
    const progress = diffObligationProgress(this.archive.progressSnapshot, snapshot);
    this.archive.progressSnapshot = snapshot;
    if (progress) {
      this.archive.progressReceipts = [...(this.archive.progressReceipts ?? []), progress].slice(-64);
      this.input.emit('obligation_progress', { receipt: progress });
    }
    const nodes = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const versions = this.taskVersions();
    const busy = new Map<string, Set<string | undefined>>();
    const occupy = (groupId: string, workerId?: string) => {
      const owners = busy.get(groupId) ?? new Set<string | undefined>(); owners.add(workerId); busy.set(groupId, owners);
    };
    for (const node of this.archive.tasks) if (node.status === 'running') occupy(taskGroup(node.task), node.assignment?.workerId);
    for (const [id, active] of this.active) if (active.action.kind === 'task') occupy(taskGroup(active.action.task), id);
    for (const review of this.archive.statementReviews ?? []) {
      const node = nodes.get(review.taskId);
      if (node && ['translating', 'reviewing'].includes(review.status)) occupy(taskGroup(node.task), review.workerId);
    }
    for (const route of this.archive.groups ?? []) route.busy = busy.get(route.group.id)?.size ?? 0;
    this.archive.planVersion ??= this.planVersion();
    if (edit?.status === 'applied') edit.planVersion = this.archive.planVersion;
    this.syncEditChecks(nodes, versions);
    this.input.save();
    const agents = this.input.workers.map(peer => {
      const work = this.active.get(peer.id)?.action;
      return { id: peer.id, role: work && (work.kind === 'review' || isStatementAction(work) ||
        work.kind === 'task' && isFeasibilityReview(work.task)) ? 'reviewer' : peer.role,
        status: work ? 'working' : this.liveWorkers.has(peer.id) ? 'idle' : 'stopped',
        work: work && { kind: work.kind, taskId: work.kind === 'task' ? work.task.id : undefined,
          version: work.kind === 'task' ? work.assignment.taskDigest : work.seedCommit } };
    });
    for (const worker of this.input.workers) {
      const action = this.active.get(worker.id)?.action;
      const scoped = this.contextState(action, worker, versions);
      const visible = new Set(scoped.tasks);
      const deliveries = (scoped.deliveries ?? []).slice(-16);
      writeMathJsonDurable(path.join(worker.worktree, 'COOPERATION.json'), {
        planVersion: this.archive.planVersion,
        edits: (this.archive.edits ?? []).slice(-16),
        agents,
        peers: this.archive.tasks.map(node => ({ id: node.task.id, taskDigest: digest(node.task),
          objectiveDigest: mathDigest(node.task.objective), groupId: taskGroup(node.task), kind: node.task.kind,
          status: node.status, owner: node.assignment?.workerId ?? node.task.ownerId, dependsOn: node.task.dependsOn,
          ...(visible.has(node) ? { objective: node.task.objective, feedback: node.feedback,
            actualReferences: (node.integratedCheck ?? node.proof)?.references } : {}) })),
        deliveries: deliveries.map(({ evidence: _evidence, ...record }) => record),
        researchHandoffs: researchHandoffs(scoped),
        blockers: scoped.blockers ?? [],
        proofRoutes: scoped.proofRoutes ?? [],
        frontierRecoveries: scoped.frontierRecoveries ?? [],
        mathematicalChanges: scoped.progressReceipts?.slice(-16) ?? [],
        continuation: buildProofContinuation(scoped.tasks, { groups: scoped.groups, environmentDigest: this.input.state.environmentDigest,
          proofRoutes: scoped.proofRoutes }),
        statements: (scoped.statementReviews ?? []).map(statementReviewSummary),
      });
    }
    this.wake();
  }
  private wake() { for (const wake of this.waiters) wake(); this.waiters.clear(); }
  modelBudgetChanged() { this.wake(); }
  activate(worker: ResearchWorker, action: CooperativeAction, interrupt: () => Promise<void>, notify: (message: string) => Promise<void>) {
    this.active.set(worker.id, { action, interrupt, notify }); this.changed();
  }
  deactivate(worker: ResearchWorker) { this.active.delete(worker.id); this.changed(); }
  current(action: CooperativeAction) {
    if ((action.kind === 'lead' || action.kind === 'solve') && action.handoffActivations) {
      const pending = new Map(pendingResearchHandoffs(this.archive).map(item => [item.id, item.activationDigest]));
      if (action.handoffIds?.some(id => pending.has(id) && pending.get(id) !== action.handoffActivations![id])) return false;
    }
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      const node = this.node(action.taskId);
      return Boolean(review && review.status === (action.kind === 'backtranslate' ? 'translating' : 'reviewing') &&
        review.assignmentId === action.assignmentId &&
        review.taskDigest === action.taskDigest && review.commit === action.seedCommit &&
        review.snapshotDigest === action.snapshotDigest && review.workspace === action.workspace && node &&
        digest(node.task) === action.taskDigest && (node.task.status ?? 'active') === 'active' &&
        this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.status === 'active');
    }
    if (action.kind === 'lead') return action.planVersion === undefined || action.planVersion === this.archive.planVersion;
    if (action.kind === 'review') {
      const review = this.archive.review;
      return Boolean(review && review.status === 'running' && review.commit === action.seedCommit &&
        review.sourceDigest === action.sourceDigest && review.assignmentId === action.assignmentId);
    }
    return action.kind !== 'task' || this.archive.tasks.some(node => node.assignment === action.assignment && digest(node.task) === action.assignment.taskDigest &&
      (!isFeasibilityReview(node.task) || this.input.workers.some(worker => worker.id === action.assignment.workerId &&
        independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups))) &&
      (taskReferenceDependencies(node) ?? action.assignment.dependencies ?? []).every(dependency => this.archive.tasks.some(item => item.task.id === dependency.taskId && digest(item.task) === dependency.taskDigest)) &&
      (node.task.status ?? 'active') === 'active' && this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.status === 'active');
  }
  private taskVersions() {
    return new Map(this.archive.tasks.map(({ task }) => [task.id, { task, version: digest(task) }]));
  }
  private deliveryVisible(record: DeliveryRecord, task: CooperativeTask | undefined, versions: TaskVersions) {
    if (record.status === 'superseded') return false;
    if (!record.taskId) return !task;
    const node = versions.get(record.taskId);
    return node && node.version === record.taskDigest && record.dependencies.every(dependency =>
      versions.get(dependency.taskId)?.version === dependency.taskDigest) &&
      (!task || taskGroup(node.task) === taskGroup(task) || node.task.sharing !== 'group');
  }
  private inform(record: DeliveryRecord) {
    const versions = this.taskVersions();
    for (const [id, active] of this.active) {
      if (id === record.producer) continue;
      if (isStatementAction(active.action)) continue;
      const task = active.action.kind === 'task' ? active.action.task : undefined;
      if (task && record.taskId && !this.deliveryVisible(record, task, versions)) continue;
      const notice = `Cooperation update: ${record.kind} ${record.id}, task ${record.taskId ?? 'original'}, status ${record.status}. Read COOPERATION.json for peer state and current-version references; use M4 to choose relevant material. This notification grants no proof acceptance.`;
      const pending = active.notify(notice).catch(() => { this.input.emit('notification_deferred', { workerId: id, deliveryId: record.id }); });
      this.notifications.add(pending); void pending.finally(() => this.notifications.delete(pending));
    }
    this.input.emit('delivery_published', { deliveryId: record.id, taskId: record.taskId, kind: record.kind, status: record.status });
  }
  private pin(commit?: string) {
    if (!commit || this.pinned.has(commit)) return;
    if (!/^[a-f0-9]{40,64}$/u.test(commit)) throw new Error('math_delivery_invalid_commit');
    git(this.lead.worktree, ['update-ref', `refs/math/${this.input.state.runId}/evidence/${commit}`, commit]);
    this.pinned.add(commit);
  }
  private record(worker: ResearchWorker, task: CooperativeTask | undefined, kind: DeliveryRecord['kind'], status: DeliveryRecord['status'],
    summary: string, options: Partial<DeliveryRecord> = {}) {
    const inputs = task && status !== 'superseded' ? this.dependencies(task) : [];
    const references = task && kind === 'proof' && status === 'verified' ? taskReferenceDependencies(this.node(task.id)) : undefined;
    const dependencies = references ?? inputs.map(node => ({ taskId: node.task.id, taskDigest: digest(node.task) }));
    const remaining = inputs.filter(node => !['integrated', 'completed'].includes(node.status)).map(node => node.task.id);
    const record: DeliveryRecord = { id: crypto.randomUUID(), producer: worker.id, taskId: task?.id, taskDigest: task && digest(task),
      groupId: task && taskGroup(task), kind, status, statement: task?.type ?? task?.objective ?? this.input.state.problem.contract.formalStatement,
      premises: task?.premises ?? this.input.state.problem.contract.assumptions, dependencies, remainingObligations: remaining,
      summary: bounded(summary, 5000), evidenceRefs: [], createdAt: Date.now(), ...options };
    if (record.evidence) {
      const { passed, verification: { status, targetCommit, results } } = record.evidence;
      // Proof records own the receipts; deliveries refer to their immutable IDs.
      record.evidence = { passed, verification: { status, targetCommit,
        results: results.map(({ receiptId }) => ({ receiptId })) } };
    }
    this.pin(record.commit); this.pin(record.evidence?.verification.targetCommit);
    (this.archive.deliveries ??= []).push(record); this.changed();
    if (status !== 'superseded') this.inform(record);
    return record;
  }
  private reportBlockers(task: CooperativeTask, value: unknown) {
    const proposals = validateBlockerProposals(value, task, this.archive.tasks);
    for (const blocker of recordRouteBlockers(this.archive.blockers ??= [], proposals, task, this.archive.tasks,
      this.input.state.environmentDigest, this.input.state.problem.receiptDigest)) {
      this.needsLead = true;
      this.input.emit(blocker.status === 'parked' ? 'route_parked' : 'route_blocker_recorded', {
        blockerId: blocker.id, taskId: blocker.taskId, groupId: blocker.groupId, count: blocker.count,
        scope: blocker.scope, evidenceStatus: blocker.evidenceStatus, reopenOn: blocker.reopenOn });
    }
  }
  start() {
    this.timer = setInterval(() => { void this.inputs().catch(error => {
      this.input.emit('cooperation_poll_failed', { reason: error instanceof Error ? error.message : 'unknown' });
      if (error instanceof Error && error.message === 'math_verifier_unavailable') { this.failure = error; this.changed(); }
    }); }, 200);
    this.timer.unref();
  }
  private syncPlanNotes() {
    if (!this.archive.planEdited) return;
    const file = path.join(this.lead.worktree, 'RESEARCH.md');
    const source = fs.existsSync(file) ? readMathText(file, MAX_RESEARCH_NOTES_BYTES) : '';
    const plan = '```math\n' + JSON.stringify({ tasks: this.archive.tasks.map(node => node.task), groups: this.archive.groups?.map(route => route.group),
      ...(this.archive.proofRoutes?.length ? { proofRoutes: this.archive.proofRoutes } : {}) }) + '\n```';
    fs.writeFileSync(file, /```(?:math|math-plan)\s*\n[\s\S]*?\n```/u.test(source)
      ? source.replace(/```(?:math|math-plan)\s*\n[\s\S]*?\n```/u, () => plan) : plan + '\n' + bounded(source, 8000));
    this.archive.planEdited = false;
  }
  private planningInputDigest() {
    const versions = new Map(this.archive.tasks.map(node => [node.task.id, digest(node.task)]));
    const deliveries = [...new Set((this.archive.deliveries ?? []).filter(record => record.status !== 'superseded' &&
      (!record.taskId || versions.get(record.taskId) === record.taskDigest)).map(record => canonicalMathJson({
        taskId: record.taskId, taskDigest: record.taskDigest, kind: record.kind, status: record.status,
        summary: record.summary, evidenceRefs: record.evidenceRefs, dependencies: record.dependencies,
        remainingObligations: record.remainingObligations, lemmaRequests: record.lemmaRequests,
      })))].sort();
    return mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      environmentDigest: this.input.state.environmentDigest, planVersion: this.archive.planVersion,
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      liveWorkers: this.input.workers.filter(worker => this.liveWorkers.has(worker.id)).map(({ id, role }) => ({ id, role })),
      progress: captureObligationSnapshot(this.archive.tasks, { groups: this.archive.groups,
        environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes, blockers: this.archive.blockers }).digest,
      tasks: this.archive.tasks.map(node => ({ id: node.task.id, status: node.status, feedback: node.feedback })),
      researchDecisions: this.archive.researchDecisions,
      pendingHandoffActivations: pendingResearchHandoffs(this.archive).map(item => [item.id, item.activationDigest]), deliveries }));
  }
  private planningEvidenceDigest() {
    // Plan invalidation can supersede old deliveries, so compare their immutable content.
    return mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      environmentDigest: this.input.state.environmentDigest,
      liveWorkers: this.input.workers.filter(worker => this.liveWorkers.has(worker.id)).map(({ id, role }) => ({ id, role })),
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      deliveries: (this.archive.deliveries ?? []).filter(record => record.producer !== this.lead.id)
        .map(({ status: _status, evidence: _evidence, ...record }) => record) }));
  }
  private checkpointInputDigest(task: CooperativeTask, workerId: string) {
    const versions = this.taskVersions();
    const deliveries = [...new Set((this.archive.deliveries ?? []).filter(record => record.producer !== workerId &&
      this.deliveryVisible(record, task, versions)).map(record => canonicalMathJson({
        taskId: record.taskId, taskDigest: record.taskDigest, kind: record.kind, status: record.status,
        summary: record.summary, evidenceRefs: record.evidenceRefs, dependencies: record.dependencies,
        remainingObligations: record.remainingObligations, lemmaRequests: record.lemmaRequests,
      })))].sort();
    return mathDigest(canonicalMathJson({ taskDigest: digest(task), environmentDigest: this.input.state.environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest,
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      dependencies: captureObligationSnapshot(this.dependencies(task), { environmentDigest: this.input.state.environmentDigest }).digest,
      deliveries }));
  }
  private checkpointOutputDigest(worktree: string, commit: string) {
    return mathDigest(canonicalMathJson({ sourceDigest: ownedSourceDigest(this.input.state.problem, worktree, commit),
      notesBlob: git(worktree, ['ls-tree', '--format=%(objectname)', commit, '--', 'RESEARCH.md']) }));
  }
  private leanSourceDigest(worktree: string, commit: string) {
    const key = `${worktree}\0${commit}`, cached = this.leanSourceDigests.get(key);
    if (cached) return cached;
    const problem = this.input.state.problem;
    const value = mathDigest(canonicalMathJson(problem.ownedFiles.filter(file => file.endsWith('.lean')).sort().map(file =>
      [file, mathDigest(committedSource(worktree, commit, `${problem.projectRelative}/${file}`))])));
    this.leanSourceDigests.set(key, value);
    if (this.leanSourceDigests.size > 256) this.leanSourceDigests.delete(this.leanSourceDigests.keys().next().value!);
    return value;
  }
  private taskSourceDigest(task: CooperativeTask, worktree: string, commit: string) {
    const source = committedSource(worktree, commit, `${this.input.state.problem.projectRelative}/${task.proofPath}`);
    const targets = inspectLeanDeclarationRegions(source).filter(region =>
      region.name.split('.').at(-1) === task.theoremName?.split('.').at(-1));
    if (targets.length !== 1) return `declaration-count:${targets.length}`;
    // Selecting a different saved proof is new input; renaming the same declaration is not.
    const target = source.slice(targets[0].startOffset, targets[0].endOffset)
      .replace(/^(theorem|lemma)(\s+)[^\s([{:\n]+/u, '$1$2__task_target');
    return mathDigest(canonicalMathJson({ file: task.proofPath, offset: targets[0].startOffset, source: target }));
  }
  private failedTaskBasis(task: CooperativeTask, conditions?: readonly CooperativeTask[]): { basis: BlockerBasis; inputDigest: string } {
    const normalized = task.kind === 'lemma' ? { ...task, theoremName: undefined, proofPath: undefined } : task;
    conditions ??= task.conditional ? this.dependencies(task).filter(node => node.task.kind === 'lemma' && node.status !== 'integrated')
      .map(node => node.task) : [];
    const node = this.node(task.id), routeId = node && selectedTaskRoute(node, this.archive.tasks)?.id;
    const raw = routeBlockerBasis(normalized, this.archive.tasks, this.input.state.environmentDigest,
      this.input.state.problem.receiptDigest, routeId);
    const contractDigest = mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      kind: normalized.kind, proofPath: normalized.proofPath, theoremName: normalized.theoremName,
      type: normalized.type, premises: normalized.premises ?? [], conditional: Boolean(normalized.conditional),
      conditions: conditions.map(task => ({ kind: task.kind, type: task.type, premises: task.premises ?? [] })) }));
    const environmentDigest = mathDigest(canonicalMathJson({ environmentDigest: this.input.state.environmentDigest,
      buildDigest: this.input.state.buildDigest, evaluatorDigest: this.input.state.evaluatorDigest,
      environment: projectMathematicsRuntimeEnvironment(this.input.access.get(this.lead.id)?.environment ?? {}) }));
    const previous = this.archive.failedTaskInputs?.findLast(record => record.basis.contractDigest === contractDigest &&
      record.basis.environmentDigest === environmentDigest);
    const basis: BlockerBasis = { contractDigest, environmentDigest,
      dependencies: Object.fromEntries(Object.entries(raw.dependencies).map(([id, entry]) => {
        const dependency = this.node(id), proof = dependency?.integratedCheck;
        const fresh = dependency?.status === 'integrated' && proof && hasTaskAcceptance(proof) &&
          proof.taskDigest === digest(dependency.task) && !proof.conditions?.length;
        const prior = previous?.basis.dependencies[id] ?? Object.values(previous?.basis.dependencies ?? {})
          .find(candidate => candidate.contractDigest === entry.contractDigest);
        return [id, { ...entry, evidenceDigest: fresh ? entry.evidenceDigest :
          prior?.contractDigest === entry.contractDigest ? prior.evidenceDigest : undefined }];
      })) };
    // Dependency task IDs, revision counters and replayed receipts do not change the mathematics.
    const inputDigest = mathDigest(canonicalMathJson({ contractDigest, environmentDigest,
      dependencies: Object.values(basis.dependencies).map(entry => canonicalMathJson(entry)).sort() }));
    return { basis, inputDigest };
  }
  private failedTaskInput(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string, conditions?: readonly CooperativeTask[]) {
    const { basis, inputDigest } = this.failedTaskBasis(task, conditions), sourceDigest = this.leanSourceDigest(worktree, commit);
    const targetDigest = this.taskSourceDigest(task, worktree, commit);
    return { id: mathDigest(canonicalMathJson({ inputDigest, sourceDigest, targetDigest })), taskId: task.id, taskDigest: digest(task),
      inputDigest, basis, sourceDigest, targetDigest, seedSourceDigest: this.leanSourceDigest(worktree, assignment.seedCommit),
      seedTargetDigest: this.taskSourceDigest(task, worktree, assignment.seedCommit),
      canonicalSourceDigest: this.leanSourceDigest(this.lead.worktree, this.archive.canonicalCommit!),
      canonicalTargetDigest: this.taskSourceDigest(task, this.lead.worktree, this.archive.canonicalCommit!) };
  }
  private rememberTaskFailure(candidate: Omit<FailedTaskInput, 'feedback' | 'repair'>, feedback: string, repair?: FailedTaskInput['repair']) {
    const records = this.archive.failedTaskInputs ??= [];
    const previous = records.find(record => record.id === candidate.id);
    if (previous) return previous;
    const record: FailedTaskInput = { ...candidate, feedback: bounded(feedback, 8000), ...(repair ? { repair } : {}) };
    records.push(record);
    this.input.emit('task_failed_input_recorded', { taskId: record.taskId, taskDigest: record.taskDigest,
      failureId: record.id, inputDigest: record.inputDigest, sourceDigest: record.sourceDigest });
    this.input.save();
    return record;
  }
  private deterministicTaskFailure(proof: TaskProof) {
    return !proof.passed && proof.verification.status === 'failed' && Boolean(proof.verification.targetCommit) &&
      proof.verification.results.length > 0 && proof.verification.results.every(result => !result.cleanupError &&
        ['failed', 'kernel_verified'].includes(result.status) &&
        !/(?:timed?\s*out|timeout|rate[- ]limit|unauthenticated|unauthorized|authentication|request (?:failed|error)|stream disconnected)/iu.test(result.error ?? '')) &&
      proof.verification.results.some(result => result.status === 'failed' &&
        ((result.sorryCount ?? 0) > 0 || (result.admitCount ?? 0) > 0 ||
          /^.+\.lean:\d+:\d+:\s*error:/mu.test(`${result.stdoutPreview || ''}\n${result.stderrPreview || ''}`)));
  }
  private pendingTaskRepair(node: TaskRecord, record: FailedTaskInput) {
    const repair = record.repair;
    return Boolean(repair?.pending && repair.taskId === node.task.id && repair.taskDigest === digest(node.task) &&
      node.assignment?.workerId === repair.workerId && node.assignment.taskDigest === repair.taskDigest);
  }
  private repeatedTaskFeedback(record: FailedTaskInput) {
    return 'math_task_repeated_failed_input\nThe same Lean source and mathematical inputs already failed. ' +
      'Save a changed proof or supply new premises, checked dependency evidence, or verifier inputs before retrying.\n' + record.feedback;
  }
  private refreshFailedTaskInputs() {
    if (!this.archive.failedTaskInputs?.length) return false;
    let changed = false;
    const canonicalSourceDigest = this.leanSourceDigest(this.lead.worktree, this.archive.canonicalCommit!);
    for (const node of this.archive.tasks) {
      if (advisory(node.task) || !['pending', 'blocked'].includes(node.status) ||
          [node.proof, node.integratedCheck].some(proof => proof?.passed && proof.taskDigest === digest(node.task))) continue;
      const { inputDigest } = this.failedTaskBasis(node.task);
      const worker = this.input.workers.find(worker => worker.id === node.assignment?.workerId);
      const session = worker && this.input.state.workers?.find(record => record.id === worker.id);
      const active = worker && this.active.get(worker.id)?.action;
      const ownsOutput = worker && node.assignment?.taskDigest === digest(node.task) &&
        (!session || session.sessionTaskId === node.task.id && (!session.sessionTaskVersion || session.sessionTaskVersion === digest(node.task))) &&
        (!active || active.kind === 'task' && active.task.id === node.task.id && active.assignment === node.assignment) &&
        !this.archive.tasks.some(other => other !== node && other.status === 'running' && other.assignment?.workerId === worker.id);
      const sourceDigest = ownsOutput ? this.leanSourceDigest(worker.worktree, git(worker.worktree, ['rev-parse', 'HEAD'])) : canonicalSourceDigest;
      const targetDigest = ownsOutput ? this.taskSourceDigest(node.task, worker.worktree, git(worker.worktree, ['rev-parse', 'HEAD'])) :
        this.taskSourceDigest(node.task, this.lead.worktree, this.archive.canonicalCommit!);
      const record = this.archive.failedTaskInputs.findLast(record => record.inputDigest === inputDigest &&
        (record.sourceDigest === sourceDigest && record.targetDigest === targetDigest || !ownsOutput &&
          (record.seedSourceDigest === sourceDigest && record.seedTargetDigest === targetDigest ||
            record.canonicalSourceDigest === sourceDigest && record.canonicalTargetDigest === targetDigest)));
      if (record && !this.pendingTaskRepair(node, record)) {
        const feedback = this.repeatedTaskFeedback(record);
        if (node.status === 'blocked' && node.feedback === feedback) continue;
        node.status = 'blocked'; node.feedback = feedback; this.needsLead = true; changed = true;
        this.input.emit('task_repeated_input_blocked', { taskId: node.task.id, taskDigest: digest(node.task),
          failureId: record.id, inputDigest, sourceDigest });
      } else if (!record && node.status === 'blocked' && node.feedback?.startsWith('math_task_repeated_failed_input\n')) {
        node.status = 'pending'; node.feedback = undefined; changed = true;
        this.input.emit('task_failed_input_reopened', { taskId: node.task.id, inputDigest, sourceDigest });
      }
    }
    return changed;
  }
  private refreshResearchCheckpoints() {
    for (const [taskId, checkpoint] of Object.entries(this.archive.researchCheckpoints ?? {})) {
      if (!checkpoint.paused) continue;
      const node = this.node(taskId), worker = this.input.workers.find(worker => worker.id === node?.assignment?.workerId);
      if (!node || digest(node.task) !== checkpoint.taskDigest) { delete this.archive.researchCheckpoints![taskId]; continue; }
      if (!worker || node.status !== 'blocked' || !node.feedback?.startsWith('math_research_checkpoint_unchanged')) continue;
      const inputChanged = this.checkpointInputDigest(node.task, worker.id) !== checkpoint.inputDigest;
      // Another responsibility can reuse this worktree without advancing the paused task.
      const session = this.input.state.workers?.find(record => record.id === worker.id), active = this.active.get(worker.id)?.action;
      const ownsOutput = (!session || session.sessionTaskId === taskId &&
        (!session.sessionTaskVersion || session.sessionTaskVersion === checkpoint.taskDigest)) &&
        (!active || active.kind === 'task' && active.task.id === taskId && active.assignment.taskDigest === checkpoint.taskDigest) &&
        !this.archive.tasks.some(other => other.task.id !== taskId && other.status === 'running' && other.assignment?.workerId === worker.id);
      const outputChanged = ownsOutput &&
        this.checkpointOutputDigest(worker.worktree, git(worker.worktree, ['rev-parse', 'HEAD'])) !== checkpoint.outputDigest;
      if (!inputChanged && !outputChanged) continue;
      const blocker = this.archive.blockers?.find(record => record.id === checkpoint.blockerId);
      if (blocker) { blocker.status = 'reopened'; blocker.reopenedReason = inputChanged ? 'checkpoint-input-changed' : 'checkpoint-output-changed'; }
      node.status = 'pending'; node.feedback = undefined;
      delete this.archive.researchCheckpoints![taskId];
      this.input.emit('research_checkpoint_reopened', { taskId, reason: inputChanged ? 'new-input' : 'new-output' });
    }
  }
  private preserveResearchDraft(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, artifacts: DeliveryArtifactManifest) {
    (this.archive.researchDrafts ??= {})[action.task.id] = { taskDigest: action.assignment.taskDigest,
      workerId: worker.id, assignmentId: action.assignment.assignmentId,
      seedCommit: action.assignment.seedCommit, canonicalCommit: action.assignment.canonicalCommit,
      commit, outputDigest: this.checkpointOutputDigest(worker.worktree, commit), artifacts };
    this.pin(commit);
  }
  private suspendResearchDrafts(worker: ResearchWorker, taskId?: string) {
    let changed = false;
    for (const [id, draft] of Object.entries(this.archive.researchDrafts ?? {}))
      if (draft.workerId === worker.id && id !== taskId && !draft.suspended) { draft.suspended = true; changed = true; }
    // Persist ownership before a different responsibility overwrites the worktree.
    if (changed) this.input.save();
  }
  private researchWorkspaceChanged(worker: ResearchWorker, node: TaskRecord) {
    const session = this.input.state.workers?.find(record => record.id === worker.id);
    if (session?.sessionTaskId) return session.sessionTaskId !== node.task.id ||
      Boolean(session.sessionTaskVersion && session.sessionTaskVersion !== digest(node.task));
    if (session?.sessionStatementReview || session?.sessionRole && session.sessionRole !== 'researcher') return true;
    const checkpoint = this.archive.researchCheckpoints?.[node.task.id];
    return Boolean(checkpoint && checkpoint.outputDigest !==
      this.checkpointOutputDigest(worker.worktree, git(worker.worktree, ['rev-parse', 'HEAD'])));
  }
  private async restoreResearchDraft(worker: ResearchWorker, node: TaskRecord): Promise<boolean> {
    const draft = this.archive.researchDrafts?.[node.task.id], assignment = node.assignment!;
    if (!draft || draft.taskDigest !== digest(node.task) || draft.workerId !== worker.id ||
        draft.assignmentId !== assignment.assignmentId || draft.seedCommit !== assignment.seedCommit ||
        draft.artifacts?.problemReceiptDigest !== this.input.state.problem.receiptDigest ||
        draft.artifacts?.taskId !== node.task.id || draft.artifacts?.taskDigest !== draft.taskDigest ||
        draft.artifacts?.seedCommit !== draft.seedCommit || draft.artifacts?.commit !== draft.commit) return false;
    const problem = this.input.state.problem;
    try {
      const saved = await withSolverWorktree(this.lead.worktree, draft.commit, async checkout => {
        const feedback = solverSourceFeedback(problem, checkout);
        if (feedback) throw new Error(feedback);
        if (this.checkpointOutputDigest(checkout, draft.commit) !== draft.outputDigest)
          throw new Error('math_research_draft_output_changed');
        captureDeliveryArtifacts({ problem, worktree: checkout, commit: draft.commit, assignment });
        return { notes: git(checkout, ['ls-tree', '--format=%(objectname)', draft.commit, '--', 'RESEARCH.md'])
          ? committedSource(checkout, draft.commit, 'RESEARCH.md') : '',
          sources: new Map(problem.ownedFiles.map(file => [file,
            committedSource(checkout, draft.commit, `${problem.projectRelative}/${file}`)])),
          canonicalSourceDigest: ownedSourceDigest(problem, checkout, draft.canonicalCommit ?? draft.seedCommit) };
      });
      if (!this.archive.tasks.includes(node) || node.assignment !== assignment || digest(node.task) !== draft.taskDigest ||
          node.status !== 'pending' || assignment.workerId !== worker.id || node.task.ownerId && node.task.ownerId !== worker.id ||
          !independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups) ||
          !taskCanStart(node.task, this.archive.tasks) || !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups)) return false;
      const canonicalChanged = ownedSourceDigest(problem, this.lead.worktree, this.archive.canonicalCommit!) !== saved.canonicalSourceDigest;
      this.suspendResearchDrafts(worker, node.task.id);
      if (canonicalChanged) {
        if (draft.artifacts.artifacts.some(artifact => artifact.kind === 'owned-source'))
          this.record(worker, node.task, 'progress', 'advisory',
            'Saved research source draft retained separately while the canonical proof advanced; it requires independent checking.',
            { commit: draft.commit, artifacts: draft.artifacts, remainingObligations: [node.task.id] });
        fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '');
        const seedCommit = this.seed(worker, this.archive.canonicalCommit!, node.task);
        node.assignment = { ...assignment, assignmentId: crypto.randomUUID(), seedCommit, canonicalCommit: this.archive.canonicalCommit };
      } else for (const [file, source] of saved.sources)
        fs.writeFileSync(path.join(worker.worktree, problem.projectRelative, file), source);
      fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), saved.notes);
      const commit = commitSolverSources(problem, worker.worktree);
      this.preserveResearchDraft(worker, { kind: 'task', task: node.task, assignment: node.assignment! }, commit,
        captureDeliveryArtifacts({ problem, worktree: worker.worktree, commit, assignment: node.assignment! }));
      this.input.emit('research_draft_restored', { taskId: node.task.id, commit, canonicalChanged });
      this.input.save();
      return true;
    } catch (error) {
      this.input.signal.throwIfAborted();
      this.input.emit('research_draft_restore_failed', { taskId: node.task.id,
        reason: error instanceof Error ? error.message : 'math_research_draft_restore_failed' });
      return false;
    }
  }
  private researchCheckpoint(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string) {
    const node = this.node(action.task.id), taskDigest = digest(node.task);
    const inputDigest = this.checkpointInputDigest(node.task, worker.id), outputDigest = this.checkpointOutputDigest(worker.worktree, commit);
    const previous = this.archive.researchCheckpoints?.[node.task.id];
    const count = previous?.taskDigest === taskDigest && previous.inputDigest === inputDigest && previous.outputDigest === outputDigest
      ? previous.count + 1 : 1;
    const checkpoint = (this.archive.researchCheckpoints ??= {})[node.task.id] = { taskDigest, inputDigest, outputDigest, count, paused: count >= 2 };
    this.input.emit('research_checkpoint_recorded', { taskId: node.task.id, taskDigest, inputDigest, outputDigest, count, paused: checkpoint.paused });
    if (checkpoint.paused) {
      const scope = `assigned-local-inference/checkpoint:${mathDigest(canonicalMathJson({ inputDigest, outputDigest }))}`;
      this.reportBlockers(node.task, [{ mechanism: 'unchanged-research-checkpoint', scope }]);
      Object.assign(checkpoint, { blockerId: this.archive.blockers?.find(record => record.taskId === node.task.id && record.scope === scope)?.id });
      this.rejected(action, 'math_research_checkpoint_unchanged: The same checkpoint has no new saved notes, draft, or task input. Wait for new input or revise the investigation.', commit);
    } else this.interrupted(worker, action);
  }
  private activeGoalFrontier() {
    const continuation = buildProofContinuation(this.archive.tasks, { groups: this.archive.groups,
      environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes });
    return continuation.frontier.filter(item => item.control === 'active' &&
      (!this.archive.groups || this.archive.groups.some(route => route.group.id === taskGroup(this.node(item.taskId).task) &&
        route.group.status === 'active' && route.turns < (route.group.maxTurns ?? Infinity))));
  }
  private resumeUnattemptedFrontier(frontier: ReturnType<CooperativeResearch['activeGoalFrontier']>) {
    const candidates = new Set(frontier.map(item => this.node(item.taskId)));
    const seen = new Set<string>();
    const visit = (node: TaskRecord) => {
      if (seen.has(node.task.id) || !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
          ['integrated', 'completed'].includes(node.status)) return;
      seen.add(node.task.id);
      if (node.status === 'blocked') candidates.add(node);
      for (const id of plannedTaskDependencyIds(node, this.archive.tasks)) {
        const dependency = this.archive.tasks.find(item => item.task.id === id);
        if (dependency) visit(dependency);
      }
    };
    // An explicitly pending supporting task can have unfinished prerequisites outside the original-goal cone.
    for (const node of this.archive.tasks) if (node.status === 'pending') visit(node);
    const resumed = [...candidates].filter(node => node.status === 'blocked' && node.attempts === 0 &&
      !node.assignment && !node.proof && !node.integratedCheck &&
      !node.feedback?.startsWith('math_task_repeated_failed_input\n') &&
      !this.archive.blockers?.some(blocker => blocker.taskId === node.task.id && blocker.status === 'parked') &&
      routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) && taskCanStart(node.task, this.archive.tasks) &&
      this.livePeers.some(worker => this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node));
    if (!resumed.length) return false;
    // A planning assessment is not an execution attempt at an imported unresolved obligation.
    for (const node of resumed) node.status = 'pending';
    this.input.emit('unattempted_frontier_resumed', { taskIds: resumed.map(node => node.task.id),
      goalIds: [...new Set(frontier.flatMap(item => item.goalIds))] });
    this.changed();
    return true;
  }
  private recoveryTaskInput(node: TaskRecord, tasks = this.archive.tasks) {
    // Moving or renaming the same helper does not supply a new mathematical inference.
    const task = node.task.kind === 'lemma' ? { ...node.task, theoremName: undefined, proofPath: undefined } : node.task;
    return mathDigest(canonicalMathJson({ basis: routeBlockerBasis(task, tasks, this.input.state.environmentDigest,
      this.input.state.problem.receiptDigest), ...(advisory(node.task) ? { objective: node.task.objective.trim() } : {}) }));
  }
  private requestFrontierRecovery(frontier: ReturnType<CooperativeResearch['activeGoalFrontier']>): CooperativeAction | undefined {
    // Lead planning does not consume a proof slot; all other route controls still bind.
    const planningGroups = this.archive.groups?.map(route => ({ ...route, busy: 0 }));
    const failed = frontier.map(item => this.node(item.taskId)).filter(node => node.status === 'blocked' && node.attempts > 0 &&
      !node.routeParking?.length && routeAllowsTask(node.task, this.archive.tasks, planningGroups));
    if (!failed.length) return;
    const taskInputDigests = failed.map(node => this.recoveryTaskInput(node)).sort();
    const id = mathDigest(canonicalMathJson(taskInputDigests));
    let recovery = this.archive.frontierRecoveries?.find(item => item.id === id);
    if (recovery && recovery.status !== 'requested') return;
    if (!recovery) {
      recovery = { id, taskIds: failed.map(node => node.task.id), goalIds: [...new Set(frontier.flatMap(item => item.goalIds))],
        taskInputDigests, status: 'requested' };
      (this.archive.frontierRecoveries ??= []).push(recovery);
      this.input.emit('frontier_recovery_requested', { recoveryId: id, taskIds: recovery.taskIds, goalIds: recovery.goalIds });
    }
    const action: CooperativeAction = { kind: 'lead', seedCommit: this.seed(this.lead, this.archive.canonicalCommit!),
      planVersion: this.archive.planVersion, planningInputDigest: this.planningInputDigest(),
      ...this.handoffDispatch(),
      recovery: { id, taskIds: recovery.taskIds, goalIds: recovery.goalIds } };
    this.leadEvidence.set(action, this.planningEvidenceDigest());
    this.changed();
    return action;
  }
  private async investigateFrontierRecovery(frontier: ReturnType<CooperativeResearch['activeGoalFrontier']>) {
    if (!this.input.continuousResearch) return false;
    const inputs = new Set(frontier.map(item => this.recoveryTaskInput(this.node(item.taskId))));
    const recovery = this.archive.frontierRecoveries?.find(item => item.status === 'awaiting-input' &&
      !item.investigationTaskId && item.taskInputDigests.every(input => inputs.has(input)));
    if (!recovery) return false;
    const tasks = recovery.taskIds.map(id => this.node(id)).filter(node => node && node.status === 'blocked');
    if (!tasks.length) return false;
    const task: CooperativeTask = { id: `frontier_input_${recovery.id.slice(0, 40)}`, kind: 'research', revision: 0,
      groupId: taskGroup(tasks[0].task), dependsOn: tasks.map(node => node.task.id),
      objective: `Independently investigate new mathematical inputs for the unresolved original-goal frontier ${tasks.map(node => node.task.id).join(', ')}. ` +
        `The previous recovery could not supply an executable step: ${recovery.reason ?? 'The original inference remains unresolved.'} ` +
        'Inspect relevant mathematical references, available library results, and distinct constructions. Report concrete evidence, exact hypotheses, and unresolved gaps; findings remain advisory. ' +
        'Do not resubmit the unchanged failed proof, rename the same obligation, or claim that a proposed input has been proved.' };
    const node: TaskRecord = { task, status: 'pending', attempts: 0 };
    if (!routeAllowsTask(task, [...this.archive.tasks, node], this.archive.groups) ||
        !this.livePeers.some(worker => this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node)) return false;
    // The marker shares the accepted-plan checkpoint so restarting cannot create another investigation of this input.
    recovery.investigationTaskId = task.id;
    if (!this.archive.tasks.some(node => node.task.id === task.id)) {
      const evidence = this.planningEvidenceDigest();
      try {
        await this.acceptPlan(parseCooperationPlan(this.input.state.problem, {
          tasks: [...this.archive.tasks.map(node => node.task), task], groups: this.archive.groups?.map(route => route.group),
          ...(this.archive.proofRoutes?.length ? { proofRoutes: this.archive.proofRoutes } : {}),
        }));
      } catch (error) { delete recovery.investigationTaskId; throw error; }
      this.archive.lastLeadInputDigest = evidence === this.planningEvidenceDigest()
        ? this.planningInputDigest() : this.archive.lastLeadInputDigest;
      this.archive.planEdited = true; this.syncPlanNotes();
    }
    this.archive.frontierWaiting = undefined;
    this.input.emit('frontier_investigation_requested', { recoveryId: recovery.id, taskId: task.id, taskIds: recovery.taskIds,
      goalIds: recovery.goalIds, evidenceStatus: 'advisory' });
    this.changed();
    return true;
  }
  private async waitForFrontierInput(frontier: ReturnType<CooperativeResearch['activeGoalFrontier']>, inputDigest: string) {
    if (!this.input.continuousResearch || !frontier.length) return false;
    if (this.stopping || this.input.modelDispatchAllowed?.() === false || inputDigest !== this.planningInputDigest()) return true;
    if (this.archive.frontierWaiting?.inputDigest !== inputDigest) {
      this.archive.frontierWaiting = { inputDigest, taskIds: frontier.map(item => item.taskId),
        goalIds: [...new Set(frontier.flatMap(item => item.goalIds))], reason: 'awaiting-new-mathematical-input' };
      this.input.emit('frontier_recovery_waiting', { ...this.archive.frontierWaiting });
      this.changed();
    }
    await this.wait();
    return true;
  }
  private validateRecoveryPlan(action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' | 'solve' }>,
    plan: ReturnType<typeof parseCooperationPlan>, response: any) {
    const recovery = this.archive.frontierRecoveries?.find(item => item.id === action.recovery?.id);
    if (!recovery || recovery.status !== 'requested') throw new Error('math_frontier_recovery_superseded');
    if (response?.status === 'awaiting-input' && typeof response.reason === 'string' && response.reason.trim())
      return { recovery, taskIds: [] as string[], reason: bounded(response.reason.trim(), 4000) };
    const previous = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const invalidated = this.planInvalidation(plan);
    const projected: TaskRecord[] = plan.tasks.map(task => {
      const old = previous.get(task.id);
      const node: TaskRecord = { ...(old && !invalidated.has(task.id) ? old : { status: 'pending' as const, attempts: old?.attempts ?? 0 }),
        task, alternativeRoutes: plan.proofRoutes?.filter(route => route.targetTaskId === task.id) };
      const owner = task.ownerId ?? (task.kind === 'goal' ? plan.groups.find(group => group.id === taskGroup(task))?.engineerId : undefined);
      if (owner && node.assignment && node.assignment.workerId !== owner && ['pending', 'running'].includes(node.status)) {
        node.status = 'pending'; node.assignment = undefined;
      }
      return node;
    });
    const groups = plan.groups.map(group => ({ group, turns: this.archive.groups?.find(item => item.group.id === group.id)?.turns ?? 0 }));
    refreshRouteBlockers(structuredClone(this.archive.blockers ?? []), projected,
      this.input.state.environmentDigest, this.input.state.problem.receiptDigest);
    const connected = new Set<string>();
    const visit = (id: string) => {
      if (connected.has(id)) return;
      connected.add(id);
      const node = projected.find(item => item.task.id === id);
      if (node) for (const dependency of plannedTaskDependencyIds(node, projected)) visit(dependency);
    };
    for (const id of recovery.goalIds) visit(id);
    const oldInputs = new Set(this.archive.tasks.filter(node => node.attempts > 0 || ['integrated', 'completed'].includes(node.status))
      .map(node => this.recoveryTaskInput(node)));
    const requested: unknown = response?.taskIds;
    const ready = this.input.modules.M3.ready(projected, groups).filter(node =>
      (connected.has(node.task.id) || advisory(node.task) && recovery.taskIds.some(id => node.task.dependsOn.includes(id))) &&
      !oldInputs.has(this.recoveryTaskInput(node, projected)) &&
      this.livePeers.some(worker => this.input.modules.M5.assign([node], worker, this.livePeers, groups, projected) === node));
    const taskIds = ready.filter(node => Array.isArray(requested) && requested.includes(node.task.id)).map(node => node.task.id);
    if (response?.status !== 'planned' || !taskIds.length) throw new Error('math_frontier_recovery_no_executable_step');
    return { recovery, taskIds, reason: undefined };
  }
  private proposedPlanDigest() {
    try {
      const { tasks, groups, proofRoutes, recovery, handoffDecisions } = block(this.lead.worktree, 'math-plan');
      return mathDigest(canonicalMathJson({ tasks, groups, proofRoutes, recovery, handoffDecisions }));
    } catch {
      // A notes-only commit must not make an identical malformed response new input.
      const file = path.join(this.lead.worktree, 'RESEARCH.md');
      return fs.existsSync(file) ? git(this.lead.worktree, ['hash-object', '--', file]) : 'missing';
    }
  }
  private rejectPlan(error: unknown) {
    const reason = error instanceof Error ? error.message : 'math_plan_invalid';
    const proposalDigest = this.proposedPlanDigest(), inputDigest = this.planningInputDigest();
    const previous = this.archive.planRejection;
    const stalled = previous?.proposalDigest === proposalDigest && previous.inputDigest === inputDigest && previous.error === reason;
    this.archive.error = reason;
    this.archive.planRejection = { proposalDigest, inputDigest, error: reason, stalled };
    this.needsLead = !stalled;
    this.input.emit('plan_rejected', { ...this.archive.planRejection });
  }
  async stop() {
    this.stopping = true; this.wake();
    clearInterval(this.timer);
    let pending: ReadonlyMap<string, Promise<void>> | undefined;
    try { pending = await this.pendingPulse; } catch (error) { if (!this.input.signal.aborted) throw error; }
    const checks = await Promise.allSettled(new Set([...(pending?.values() ?? []), ...this.deliveryChecks.values()]));
    const failed = checks.find(result => result.status === 'rejected');
    if (failed?.status === 'rejected' && !this.input.signal.aborted) throw failed.reason;
    await Promise.allSettled([...this.notifications]);
    this.syncPlanNotes();
    if (!this.input.signal.aborted && !this.primaryLed) this.archive.canonicalCommit = this.seed(this.lead, this.archive.canonicalCommit!);
    this.input.save();
  }
  async pulse(workerId?: string): Promise<void> {
    if (workerId) await this.deliveryChecks.get(workerId);
    const pending = await this.inputs();
    const checks = await Promise.allSettled(workerId ? [pending.get(workerId)] : [...pending.values()]);
    const failed = checks.find(result => result.status === 'rejected');
    if (failed?.status === 'rejected') throw failed.reason;
  }
  private inputs() {
    return this.pendingPulse ??= this.readInputs().finally(() => { this.pendingPulse = undefined; });
  }
  /** Serialize input edits while allowing independent proof checks to continue. */
  private async readInputs(): Promise<ReadonlyMap<string, Promise<void>>> {
    if (this.primaryLed) await this.input.exclusiveCheck(() => this.readHelpRequest());
    const cursors = this.archive.cursors ??= {};
    const file = path.join(path.dirname(this.lead.worktree), 'edits.jsonl');
    const edits = readDeliveryLines(file, cursors.edits ?? 0);
    const advance = (offset: number) => { cursors.edits = offset; this.input.save(); };
    for (const entry of edits.entries!) {
      this.input.signal.throwIfAborted();
      let id = crypto.randomUUID();
      let record: HumanEditRecord | undefined;
      try {
        if (!entry.line?.trim()) { advance(entry.offset); continue; }
        let edit: any;
        try { edit = JSON.parse(entry.line); }
        catch { throw new Error('math_edit_invalid_json'); }
        if (!edit || typeof edit !== 'object' || Array.isArray(edit)) throw new Error('math_edit_invalid');
        if (typeof edit.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(edit.id)) throw new Error('math_edit_invalid_id');
        id = edit.id;
        record = this.archive.edits?.find(previous => previous.id === id);
        if (record && record.status !== 'received') {
          if (record.status === 'applied' && record.pendingSync) await this.input.exclusiveCheck(async () => {
            const statements = this.prepareStatementContexts(); if (statements) await statements;
            this.syncStatementReviews(); record!.pendingSync = undefined; this.changed();
            this.input.emit('edit_applied', { id, planVersion: record!.planVersion, affectedTasks: record!.affectedTasks, recheck: record!.recheck });
          });
          advance(entry.offset); continue;
        }
        if (!record) {
          record = { id, status: 'received', receivedAt: Date.now(),
            ...(typeof edit.baseVersion === 'string' ? { baseVersion: bounded(edit.baseVersion, 128) } : {}) };
          (this.archive.edits ??= []).push(record); this.changed();
          this.input.emit('edit_received', { id, baseVersion: record.baseVersion });
        }
        if (edit.baseVersion !== this.archive.planVersion) throw new Error('math_edit_version_conflict');
        await this.input.exclusiveCheck(() => {
          if (edit.baseVersion !== this.archive.planVersion) throw new Error('math_edit_version_conflict');
          return this.acceptPlan(parseCooperationPlan(this.input.state.problem, edit), record);
        });
        for (const [workerId, active] of this.active) {
          if (isStatementAction(active.action)) continue;
          const pending = active.notify(`Human edit ${id} applied at plan version ${this.archive.planVersion}; this does not mean the affected proofs passed. Read the edit's separate recheck results in COOPERATION.json. Superseded assignments must stop; unrelated work continues.`)
            .catch(() => { this.input.emit('notification_deferred', { workerId, editId: id }); });
          this.notifications.add(pending); void pending.finally(() => this.notifications.delete(pending));
        }
        this.input.emit('edit_applied', { id, planVersion: record.planVersion, affectedTasks: record.affectedTasks, recheck: record.recheck });
      } catch (error) {
        this.input.signal.throwIfAborted();
        const reason = error instanceof Error ? error.message : 'math_edit_invalid';
        if (record?.status === 'applied' || !(error instanceof Error) || error.name === 'AbortError' ||
            !/^math_(?:edit_(?:invalid(?:_json|_id)?|version_conflict)$|plan_[a-z_]+(?:$|:)|help_original_goals_owned_by_primary$)/u.test(reason)) throw error;
        if (record) { record.status = 'rejected'; record.reason = reason; }
        else (this.archive.edits ??= []).push({ id, status: 'rejected', reason, receivedAt: Date.now() });
        this.changed();
        this.input.emit('edit_rejected', { id, reason });
      }
      advance(entry.offset);
    }
    for (const worker of this.input.workers) {
      if (this.deliveryChecks.has(worker.id)) continue;
      const active = this.active.get(worker.id);
      if (active?.action.kind !== 'task') continue;
      const check = this.readWorkerDeliveries(worker, active.action, cursors);
      this.deliveryChecks.set(worker.id, check);
      void check.catch(error => {
        this.input.emit('cooperation_poll_failed', { reason: error instanceof Error ? error.message : 'unknown' });
        if (error instanceof Error && error.message === 'math_verifier_unavailable') { this.failure = error; this.changed(); }
      }).finally(() => {
        if (this.deliveryChecks.get(worker.id) === check) this.deliveryChecks.delete(worker.id);
      }).catch(() => {});
    }
    return new Map(this.deliveryChecks);
  }
  private async readHelpRequest(dispatch?: CooperativeAction) {
    if (this.archive.review && this.archive.review.status !== 'changes_requested') return;
    const action = dispatch ?? this.active.get(this.lead.id)?.action;
    if (!action && pendingResearchHandoffs(this.archive).length) return;
    const notes = path.join(this.lead.worktree, 'RESEARCH.md');
    if (!fs.existsSync(notes)) return;
    const fingerprint = mathDigest(canonicalMathJson({ notes: readMathText(notes, MAX_RESEARCH_NOTES_BYTES),
      handoffActivations: action?.kind === 'solve' ? action.handoffActivations : undefined }));
    if (fingerprint === this.archive.helpRequestDigest) return;
    this.archive.helpRequestDigest = fingerprint;
    try {
      const { requests, handoffDecisions } = block(this.lead.worktree, 'math-help');
      if (requests === undefined) return;
      if (!Array.isArray(requests) || requests.length > this.input.workers.length - 1 ||
          requests.some(task => !task || !['lemma', 'research', 'sketch'].includes(task.kind) ||
            task.ownerId === this.lead.id || task.statementReview)) throw new Error('math_help_invalid_requests');
      const goals = this.input.state.problem.targets.map((target, index) => ({
        id: `original_goal_${index + 1}`, kind: 'goal', objective: `Primary solver owns ${target.theoremName}.`,
        theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused',
      }));
      const shown = action?.kind === 'solve' ? action.handoffIds ?? [] : [];
      const plan = this.helpPlan([...goals, ...requests], shown, handoffDecisions);
      const decisions = resolveResearchHandoffs(this.archive, shown,
        plan.tasks, handoffDecisions, action?.kind === 'solve' ? action.handoffActivations : undefined);
      this.preserveHandoffBacklog(plan, decisions);
      await this.acceptPlan(plan);
      this.recordHandoffDecisions(decisions);
      this.input.emit('help_requested', { taskIds: requests.map(task => task.id) });
    } catch (error) {
      const reason = error instanceof Error ? error.message : 'math_help_invalid_requests';
      if (reason.endsWith('_requires_one_block')) return;
      this.archive.error = reason;
      this.input.emit('help_request_rejected', { reason }); this.changed();
    }
  }
  private helpPlan(tasks: readonly CooperativeTask[], shownIds: readonly string[], decisions?: unknown) {
    const proposed = new Map(tasks.map(task => [task.id, task]));
    const retained = new Map<string, CooperativeTask>();
    const current = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const visited = new Set<string>();
    let normalized = false;
    const retain = (id: string) => {
      if (visited.has(id)) return;
      visited.add(id);
      const requested = proposed.get(id), node = current.get(id);
      const task = requested ?? node?.task;
      if (!task) return;
      if (!requested) retained.set(id, task);
      for (const dependency of task.dependsOn ?? []) retain(dependency);
      if (normalized && node && digest(task) === digest(node.task)) {
        const references = taskReferenceDependencies(node);
        const inputs = references && proofReferencesUnchanged(this.input.state.problem, this.lead.worktree,
          this.archive.canonicalCommit!, node.integratedCheck!.references!, this.input.state.environmentDigest) ? references :
          node.assignment?.taskDigest === digest(task) ? node.assignment.dependencies ?? [] : [];
        for (const dependency of inputs) retain(dependency.taskId);
      }
    };
    // Current requests own their contracts; retained prerequisites keep their original execution controls.
    for (const task of tasks) retain(task.id);
    const shown = new Set(shownIds);
    const deferring = new Map<string, string[]>((Array.isArray(decisions) ? decisions : []).filter(decision =>
      decision?.status === 'deferred' && typeof decision.id === 'string' && Array.isArray(decision.waitsOn) && decision.waitsOn.length)
      .map(decision => [decision.id, decision.waitsOn.filter((id: unknown) => typeof id === 'string')]));
    const dismissing = new Set<string>((Array.isArray(decisions) ? decisions : []).filter(decision =>
      decision && typeof decision.id === 'string' && (decision.status === 'rejected' ||
        decision.status === 'deferred' && decision.waitsOn === undefined)).map(decision => decision.id));
    // Completed sources remain completed without pausing unfinished inputs needed by a later batch.
    for (const handoff of retainedResearchHandoffs(this.archive)) if (!dismissing.has(handoff.id) &&
        (!shown.has(handoff.id) || deferring.has(handoff.id))) {
      retain(handoff.sourceTaskId);
      for (const dependency of this.archive.deliveries?.find(item => item.id === handoff.deliveryId)?.dependencies ?? []) retain(dependency.taskId);
      for (const dependency of handoff.proposal.dependsOn) retain(dependency);
      const waitsOn = deferring.get(handoff.id) ?? handoff.decision?.waitsOn?.map(input => input.taskId) ?? [];
      for (const id of waitsOn) retain(id);
    }
    const groups = this.archive.groups?.map(record => record.group);
    const parse = () => parseCooperationPlan(this.input.state.problem, { tasks: [...proposed.values(), ...retained.values()],
      ...(groups?.length ? { groups: groups.some(group => group.id === 'main') ? groups :
        [...groups, { id: 'main', objective: 'Prove the original problem' }] } : {}) });
    const plan = parse();
    // Omitted request defaults must compare as the same parsed mathematical contract.
    for (const task of plan.tasks) if (proposed.has(task.id)) proposed.set(task.id, task);
    normalized = true;
    visited.clear();
    for (const task of plan.tasks) retain(task.id);
    return parse();
  }
  private preserveHandoffBacklog(plan: ReturnType<typeof parseCooperationPlan>, decisions: readonly ResearchHandoffDecision[]) {
    const decided = new Map(decisions.map(decision => [decision.id, decision]));
    const remaining = researchHandoffs(this.archive).filter(item => {
      const decision = decided.get(item.id) ?? item.decision;
      return decision?.status === 'deferred' && decision.waitsOn?.length || (item.status === 'pending' && !decided.has(item.id));
    });
    if (!remaining.length) return;
    const invalidated = this.planInvalidation(plan);
    const affected = remaining.find(item => invalidated.has(item.sourceTaskId) ||
      [...item.proposal.dependsOn, ...(this.archive.deliveries?.find(delivery => delivery.id === item.deliveryId)?.dependencies ?? []).map(input => input.taskId)]
        .some(id => invalidated.has(id)) ||
      (decided.get(item.id)?.waitsOn ?? item.decision?.waitsOn ?? []).some(reference => invalidated.has(reference.taskId) &&
        !((decided.get(item.id)?.waitsOn ?? []).some(updated => updated.taskId === reference.taskId &&
          plan.tasks.some(task => task.id === updated.taskId && digest(task) === updated.taskDigest)))));
    if (affected) throw new Error('math_handoff_backlog_source_required:' + affected.sourceTaskId +
      ': retain its mathematical contract, prerequisites and group until the queued proposals are decided.');
  }
  private async readWorkerDeliveries(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, cursors: Record<string, number>) {
    const invalidInput = new Set([...taskSourceRejections, 'math_delivery_invalid', 'math_delivery_invalid_commit',
      'math_delivery_requires_fixed_proof', 'math_delivery_unfinished_dependencies', 'math_route_blocker_invalid']);
    let advanced = false;
    const reject = (reason: string) => this.input.emit('delivery_rejected', { workerId: worker.id, reason });
    try {
      for (const log of [assignmentDeliveryFile(action.assignment), 'DELIVERIES.jsonl']) {
        const scoped = log !== 'DELIVERIES.jsonl', key = scoped ? `${worker.id}/${log}` : worker.id;
        const discardKey = `${key}/discardingOversized`;
        const batch = readDeliveryLines(path.join(worker.worktree, log), cursors[key] ?? 0,
          { discardingOversized: cursors[discardKey] === 1 });
        for (const entry of batch.entries!) {
          this.input.signal.throwIfAborted();
          if (entry.error) reject(entry.error);
          else if (entry.line?.trim()) {
            let value: unknown;
            try { value = JSON.parse(entry.line); }
            catch { reject('math_delivery_invalid_json'); }
            if (value !== undefined) {
              try { await this.receive(worker, action, value, scoped); }
              catch (error) {
                this.input.signal.throwIfAborted();
                if (!(error instanceof Error) || !invalidInput.has(rejectionCode(error))) throw error;
                reject(error.message);
              }
            }
          }
          cursors[key] = entry.offset;
          cursors[discardKey] = entry.discardingOversized ? 1 : 0;
          advanced = true;
        }
        if (cursors[key] !== batch.offset || (cursors[discardKey] === 1) !== batch.discardingOversized) advanced = true;
        cursors[key] = batch.offset;
        cursors[discardKey] = batch.discardingOversized ? 1 : 0;
      }
    } finally { if (advanced) this.input.save(); }
  }
  private async receive(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, value: any, scoped = false) {
    if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_delivery_invalid');
    const assignmentKey = assignmentDeliveryFile(action.assignment);
    const automaticId = scoped ? mathDigest(canonicalMathJson({ file: assignmentKey, value })) : undefined;
    if (scoped) value = { id: automaticId, kind: 'progress', taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, ...value };
    const details = deliveryDetails(value);
    if (!value || typeof value.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(value.id) ||
        !['progress', 'proof'].includes(value.kind) || value.taskId !== action.task.id || value.taskDigest !== action.assignment.taskDigest) throw new Error('math_delivery_invalid');
    // Legacy automatic ids already bind the assignment; unscoped old ids cannot identify a new seed.
    if (this.archive.deliveries?.some(record => record.producer === worker.id && record.submissionId === value.id &&
      record.taskId === action.task.id && record.taskDigest === action.assignment.taskDigest &&
      (record.assignmentKey === assignmentKey || record.assignmentKey === undefined && scoped && value.id === automaticId))) {
      if (value.kind === 'proof' && this.current(action)) await this.input.exclusiveCheck(() => this.integrateReady());
      return;
    }
    if (!this.current(action)) {
      this.record(worker, action.task, value.kind, 'superseded', details.summary, { ...details, submissionId: value.id, assignmentKey,
        taskDigest: action.assignment.taskDigest, premises: action.task.premises ?? [], dependencies: action.assignment.dependencies ?? [],
        remainingObligations: details.remainingObligations ?? [] });
      return;
    }
    const node = this.node(action.task.id);
    if (value.kind === 'progress') {
      this.reportBlockers(node.task, value.blockers);
      const remaining = [...new Set([...(value.remainingObligations ?? []),
        ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])] as string[];
      if (value.needsDecision === true) this.needsLead = true;
      this.record(worker, node.task, 'progress', remaining.length || node.task.kind === 'sketch' ? 'conditional' : 'advisory', details.summary,
        { ...details, submissionId: value.id, assignmentKey, remainingObligations: remaining });
      return;
    }
    if (advisory(node.task) || typeof value.commit !== 'string' || !/^[a-f0-9]{40,64}$/u.test(value.commit)) throw new Error('math_delivery_requires_fixed_proof');
    if (!taskCanStart(node.task, this.archive.tasks)) throw new Error('math_delivery_unfinished_dependencies');
    this.input.signal.throwIfAborted();
    const fixed = mathGitResult(worker.worktree, ['rev-parse', '--verify', '--quiet', `${value.commit}^{commit}`], { maxBuffer: 4096 });
    if (fixed.error) throw fixed.error;
    if (fixed.status === 1) throw new Error('math_delivery_invalid_commit');
    if (fixed.status !== 0) throw new Error('math_delivery_commit_unavailable');
    const ancestry = mathGitResult(worker.worktree,
      ['merge-base', '--is-ancestor', this.input.state.problem.baseCommit, value.commit], { maxBuffer: 4096 });
    if (ancestry.error) throw ancestry.error;
    if (ancestry.status === 1) throw new Error('math_delivery_invalid_commit');
    if (ancestry.status !== 0) throw new Error('math_delivery_commit_unavailable');
    try {
      await this.publishTaskProof(worker, action, value.commit, details.summary,
        { submissionId: value.id, assignmentKey, evidenceRefs: value.evidenceRefs });
    } catch (error) {
      if (error instanceof Error && /^math_task_(?:missing_declaration|repeated_failed_input)\n/u.test(error.message) && this.current(action)) {
        this.rejected(action, error.message, value.commit); return;
      }
      throw error;
    }
  }
  private async wait() {
    const signal = this.input.signal; signal.throwIfAborted();
    await new Promise<void>(resolve => {
      const wake = () => { signal.removeEventListener('abort', wake); this.waiters.delete(wake); resolve(); };
      this.waiters.add(wake); signal.addEventListener('abort', wake, { once: true });
    });
    signal.throwIfAborted();
  }
  private node(id: string) { return this.archive.tasks.find(node => node.task.id === id)!; }
  private dependencies(task: CooperativeTask, tasks: readonly TaskRecord[] = this.archive.tasks): TaskRecord[] {
    const nodes = new Map(tasks.map(node => [node.task.id, node]));
    const found = new Set<string>();
    const ids = (node: TaskRecord) => taskReferenceDependencies(node)?.map(reference => reference.taskId) ?? plannedTaskDependencyIds(node, tasks);
    const visit = (id: string) => { if (found.has(id)) return; found.add(id); ids(nodes.get(id)!).forEach(visit); };
    const node = nodes.get(task.id);
    (node?.task === task ? ids(node) : task.dependsOn).forEach(visit);
    return [...found].map(id => nodes.get(id)!);
  }
  private async check(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string,
    conditions?: readonly CooperativeTask[], checked?: TaskProof, reuseDeliveryFailure = false, incompleteDelivery = false): Promise<TaskProof> {
    this.input.signal.throwIfAborted();
    if (reuseDeliveryFailure && !checked) {
      const candidate = this.failedTaskInput(task, assignment, worktree, commit, conditions);
      const previous = this.archive.failedTaskInputs?.find(record => record.id === candidate.id);
      if (previous) {
        this.input.emit('task_failure_check_reused', { taskId: task.id, taskDigest: digest(task), commit, failureId: previous.id });
        throw new Error(this.repeatedTaskFeedback(previous));
      }
      const pending = this.checkingTaskInputs.get(candidate.id);
      if (pending) {
        await pending;
        return this.check(task, assignment, worktree, commit, conditions, checked, true, incompleteDelivery);
      }
      let finish!: () => void;
      const checking = new Promise<void>(resolve => { finish = resolve; });
      this.checkingTaskInputs.set(candidate.id, checking);
      const reserveRepair = () => {
        const node = this.node(task.id);
        return node?.assignment === assignment && digest(node.task) === candidate.taskDigest && (incompleteDelivery || node.attempts === 1)
          ? { taskId: task.id, taskDigest: candidate.taskDigest, workerId: assignment.workerId, pending: true } : undefined;
      };
      try {
        const proof = await this.check(task, assignment, worktree, commit, conditions, checked);
        if (this.deterministicTaskFailure(proof)) this.rememberTaskFailure(candidate, solverProofFeedback(proof), reserveRepair());
        return proof;
      } catch (error) {
        if (error instanceof Error && error.message.startsWith('math_task_missing_declaration\n'))
          this.rememberTaskFailure(candidate, error.message, reserveRepair());
        throw error;
      } finally {
        this.checkingTaskInputs.delete(candidate.id); finish();
      }
    }
    const tasks = this.archive.tasks.map(node => ({ ...node }));
    const dependencies = this.dependencies(task), taskDigest = digest(task);
    conditions ??= task.conditional ? dependencies.filter(node => node.task.kind === 'lemma' && node.status !== 'integrated').map(node => node.task) : [];
    const retainedGoals = dependencies.filter(node => node.task.kind === 'goal' && node.status === 'integrated').map(node => node.task.theoremName!);
    const checker = this.input.modules.M2.checkTask ?? checkTaskProof;
    const environment = this.input.access.get(this.lead.id)!.environment;
    const proof = checked ?? await checker(this.input.state.problem, worktree, commit, task, assignment, retainedGoals,
      environment, this.input.signal, this.input.timeoutMs, conditions, this.input.state.environmentDigest);
    const declarationHash = proof.passed && proof.verification.targetCommit && hashMathFormalSourceDeclaration(
      committedSource(worktree, proof.verification.targetCommit, `${this.input.state.problem.projectRelative}/${task.proofPath}`), task.theoremName!);
    const projected = proof.passed && projectTaskSources(this.input.state.problem, worktree, commit, task,
      retainedGoals, conditions);
    const allowed = new Set(this.input.state.problem.ownedFiles.map(file => `${this.input.state.problem.projectRelative}/${file}`));
    allowed.add('RESEARCH.md');
    const projectionMatches = projected && proof.verification.targetCommit &&
      [...projected].every(([file, source]) => source === committedSource(worktree, proof.verification.targetCommit!,
        `${this.input.state.problem.projectRelative}/${file}`)) &&
      git(worktree, ['diff', '--no-renames', '--name-only', '-z', commit, proof.verification.targetCommit, '--'])
        .split('\0').filter(Boolean).every(file => allowed.has(file));
    if (proof.commit !== commit || proof.taskDigest !== taskDigest || proof.seedCommit !== assignment.seedCommit ||
        proof.sourceDigest !== ownedSourceDigest(this.input.state.problem, worktree, commit) ||
        canonicalMathJson(proof.conditions ?? []) !== canonicalMathJson(conditions.map(task => ({ taskId: task.id, taskDigest: digest(task) }))) ||
        (proof.passed && (!projectionMatches || !declarationHash || !proofReceiptsMatch(proof.verification, proof.verification.targetCommit,
          [{ proofPath: task.proofPath!, theoremName: task.theoremName!, expectedSourceDeclarationHash: declarationHash,
            statementHash: taskDigest, leanStatementHash: taskDigest, claim: 'statement' }]))))
      throw new Error('math_task_check_identity_changed');
    if (proof.references) {
      const references = proof.references;
      references.tasks = attributeTaskReferences(references, tasks);
      markTaskReferences(proof);
    }
    this.pin(proof.commit); this.pin(proof.verification.targetCommit);
    this.checkedDeliveries.add(proof); markTaskAcceptance(proof);
    return proof;
  }
  /** Check isolated sources concurrently; only publishing and canonical integration are serialized. */
  private async publishTaskProof(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, summary: string, options: Partial<DeliveryRecord> = {}, recovering = false) {
    const previous = this.node(action.task.id);
    const proof = previous?.proof?.commit === commit && ['delivered', 'conditional', 'integrated'].includes(previous.status) &&
      this.checkedDeliveries.has(previous.proof) ? previous.proof :
      await this.check(action.task, action.assignment, worker.worktree, commit, undefined, undefined, true, recovering);
    return this.input.exclusiveCheck(async () => {
      if (!this.current(action) || !(proof.references?.tasks ?? []).every(reference =>
          this.archive.tasks.some(node => node.task.id === reference.taskId && digest(node.task) === reference.taskDigest))) {
        this.record(worker, action.task, 'proof', 'superseded', 'Assignment changed while its proof was being checked.',
          { ...options, commit, taskDigest: action.assignment.taskDigest, dependencies: action.assignment.dependencies ?? [] });
        this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
        return;
      }
      const node = this.node(action.task.id);
      if (['conditional', 'integrated'].includes(node.status)) {
        if (node.status === 'integrated') {
          const statements = this.prepareStatementContexts(); if (statements) await statements;
          this.syncStatementReviews();
        }
        if (node.proof?.commit === commit) {
          await this.finishProofDelivery(worker, node, node.proof, summary, options);
          return node.proof;
        }
        await this.integrateReady();
        return;
      }
      if (recovering && !proof.passed && proof.verification.status === 'failed') {
        node.feedback = solverProofFeedback(proof);
        if (this.deterministicTaskFailure(proof)) this.continueTaskCheckpoint(worker, node, commit);
        this.interrupted(worker, action);
        return proof;
      }
      await this.deliverProof(worker, node, proof, summary, options);
      return proof;
    });
  }
  private retryTaskLocally(node: TaskRecord, commit?: string): boolean {
    if (!node.assignment || !this.liveWorkers.has(node.assignment.workerId)) return false;
    const worker = this.input.workers.find(worker => worker.id === node.assignment!.workerId);
    const candidate = worker && this.failedTaskInput(node.task, node.assignment, worker.worktree,
      commit ?? node.proof?.commit ?? git(worker.worktree, ['rev-parse', 'HEAD']));
    const failed = candidate && this.archive.failedTaskInputs?.find(record => record.id === candidate.id);
    if (failed?.repair ? !this.pendingTaskRepair(node, failed) : node.attempts !== 1) return false;
    if (failed && !failed.repair) failed.repair = { taskId: node.task.id, taskDigest: digest(node.task),
      workerId: node.assignment.workerId, pending: true };
    node.status = 'pending';
    this.input.emit('task_repair_requested', { taskId: node.task.id, workerId: node.assignment.workerId,
      taskDigest: node.assignment.taskDigest });
    return true;
  }
  private restoreInterruptedRepair(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string) {
    const node = this.node(action.task.id), candidate = this.failedTaskInput(action.task, action.assignment, worker.worktree, commit);
    const failed = this.archive.failedTaskInputs?.find(record => record.id === candidate.id), repair = failed?.repair;
    if (!repair || repair.pending || repair.taskId !== node.task.id || repair.taskDigest !== digest(node.task) ||
        repair.workerId !== worker.id || repair.startedAttempt !== node.attempts) return false;
    repair.pending = true; delete repair.startedAttempt;
    node.feedback = failed!.feedback; node.status = 'pending';
    this.input.emit('task_repair_interrupted', { taskId: node.task.id, workerId: worker.id, failureId: failed!.id });
    this.changed(); return true;
  }
  private continueTaskCheckpoint(worker: ResearchWorker, node: TaskRecord, commit: string) {
    const candidate = this.failedTaskInput(node.task, node.assignment!, worker.worktree, commit);
    const failed = this.archive.failedTaskInputs?.find(record => record.id === candidate.id);
    if (!failed) return;
    this.settleTaskRepair(node);
    failed.repair ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id, pending: true };
    this.input.emit('task_checkpoint_continuation_requested', { taskId: node.task.id, workerId: worker.id, failureId: failed.id });
  }
  private settleTaskRepair(node: TaskRecord) {
    for (const { repair } of this.archive.failedTaskInputs ?? []) if (repair && !repair.pending &&
        repair.taskId === node.task.id && repair.taskDigest === digest(node.task) &&
        repair.workerId === node.assignment?.workerId && repair.startedAttempt === node.attempts) delete repair.startedAttempt;
  }
  private async deliverProof(worker: ResearchWorker, node: TaskRecord, proof: TaskProof, summary: string, options: Partial<DeliveryRecord> = {}) {
    node.proof = proof;
    if (['unavailable', 'blocked'].includes(proof.verification.status)) throw new Error('math_verifier_unavailable');
    if (proof.passed || this.deterministicTaskFailure(proof)) this.settleTaskRepair(node);
    node.status = proof.passed ? proof.conditions?.length ? 'conditional' : 'delivered' : 'blocked';
    if (!proof.passed) {
      node.feedback = solverProofFeedback(proof);
      const repairable = this.deterministicTaskFailure(proof) || proof.verification.status === 'failed' && proof.verification.results.some(result =>
        result.status === 'failed' && ((result.sorryCount ?? 0) > 0 || result.error === 'Lean exited with status 1.'));
      if (!repairable || !this.retryTaskLocally(node, proof.commit)) this.needsLead = true;
    }
    this.input.emit('task_checked', { taskId: node.task.id, passed: proof.passed, conditional: Boolean(proof.conditions?.length), commit: proof.commit });
    if (node.status === 'delivered') await this.integrate(node);
    await this.finishProofDelivery(worker, node, proof, summary, options);
  }
  private async finishProofDelivery(worker: ResearchWorker, node: TaskRecord, proof: TaskProof, summary: string, options: Partial<DeliveryRecord>) {
    const status = this.node(node.task.id).status;
    const verdict = status === 'integrated' ? 'verified' : status === 'conditional' ? 'conditional' : 'failed';
    const assignmentKey = options.assignmentKey ?? assignmentDeliveryFile(node.assignment!);
    if (!this.archive.deliveries?.some(record => record.producer === worker.id && record.kind === 'proof' && record.status === verdict &&
        record.taskId === node.task.id && record.taskDigest === digest(node.task) && record.assignmentKey === assignmentKey &&
        (record.commit === proof.commit || verdict === 'verified' && record.commit === node.integratedCheck?.commit)))
      this.record(worker, node.task, 'proof', verdict, node.feedback ?? summary,
        { ...options, assignmentKey, commit: proof.commit, sourceDigest: proof.sourceDigest, evidence: proof, actualReferences: proof.references });
    await this.integrateReady();
  }
  private async integrateReady() {
    const publish = (node: TaskRecord) => {
      const producer = this.input.workers.find(worker => worker.id === node.assignment!.workerId) ?? this.lead;
      this.record(producer, node.task, 'proof', node.status === 'integrated' ? 'verified' : 'failed',
        node.feedback ?? 'Conditional parent rechecked with proved dependencies and integrated.',
        { assignmentKey: assignmentDeliveryFile(node.assignment!),
          commit: node.integratedCheck?.commit ?? node.proof!.commit, sourceDigest: node.integratedCheck?.sourceDigest,
          evidence: node.integratedCheck ?? node.proof, actualReferences: (node.integratedCheck ?? node.proof)?.references });
    };
    for (;;) {
      // A parent can reach canonical acceptance before a later snapshot or publication fails.
      const unpublished = this.archive.tasks.find(item => item.status === 'integrated' && item.proof && item.assignment &&
        item.integratedCheck?.passed && item.integratedCheck.taskDigest === digest(item.task) && this.checkedDeliveries.has(item.integratedCheck) &&
        !this.archive.deliveries?.some(record => record.taskId === item.task.id && record.taskDigest === digest(item.task) &&
          record.kind === 'proof' && record.status === 'verified' &&
          (record.commit === item.proof!.commit || record.commit === item.integratedCheck!.commit)));
      if (unpublished) {
        const statements = this.prepareStatementContexts(); if (statements) await statements;
        this.syncStatementReviews(); publish(unpublished); continue;
      }
      const node = this.archive.tasks.find(item => item.status === 'conditional' && taskDependenciesReady(item.task, this.archive.tasks));
      if (!node) return;
      await this.integrate(node);
      publish(node);
    }
  }
  private async recheckIntegrated(canonical: string, changedOnly = false) {
    // Persisted receipts and receipts for different sources cannot authorize dependent dispatch.
    const pending = this.archive.tasks.filter(node => node.status === 'integrated');
    const checked = new Set<string>();
    const batched = new Map<TaskRecord, TaskProof>();
    const batchAttempted = new Set<TaskRecord>();
    const request = (node: TaskRecord) => ({ task: node.task,
      assignment: { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical },
      retainedGoals: this.dependencies(node.task).filter(item => item.task.kind === 'goal' && item.status === 'integrated')
        .map(item => item.task.theoremName!) });
    const projection = (node: TaskRecord) => canonicalMathJson([...projectTaskSources(this.input.state.problem,
      this.lead.worktree, canonical, node.task, request(node).retainedGoals)]);
    const progress = this.archive.recheck = { canonicalCommit: canonical, total: pending.length, completed: 0, taskId: undefined as string | undefined };
    const finish = (node: TaskRecord) => {
      checked.add(node.task.id); progress.completed++; progress.taskId = undefined;
      this.input.emit('task_recheck_finished', { ...progress, taskId: node.task.id, passed: node.status === 'integrated' });
      this.input.save();
    };
    while (pending.length) {
      const index = pending.findIndex(node => node.task.dependsOn.every(id => this.node(id).status !== 'integrated' || checked.has(id)));
      if (index < 0) throw new Error('math_plan_dependency_cycle');
      const [node] = pending.splice(index, 1);
      progress.taskId = node.task.id;
      this.input.emit('task_recheck_started', { ...progress }); this.input.save();
      if (changedOnly && taskReferenceDependencies(node) && taskDependenciesReady(node.task, this.archive.tasks) && node.integratedCheck?.references &&
          proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, canonical, node.integratedCheck.references, this.input.state.environmentDigest)) {
        this.input.emit('task_check_reused', { taskId: node.task.id, commit: node.integratedCheck.commit, canonicalCommit: canonical });
        finish(node); continue;
      }
      const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical };
      try {
        if (!changedOnly && !batchAttempted.has(node) && (this.input.modules.M2.checkTask ?? checkTaskProof) === checkTaskProof) {
          const source = projection(node);
          const group = [node, ...pending.filter(item => {
            if (batchAttempted.has(item)) return false;
            try { return projection(item) === source; } catch { return false; }
          })].slice(0, 32);
          if (group.length > 1) {
            group.forEach(item => batchAttempted.add(item));
            this.input.emit('task_recheck_batch_started', { taskIds: group.map(item => item.task.id) });
            try {
              const proofs = await checkTaskProofs(this.input.state.problem, this.lead.worktree, canonical, group.map(request),
                this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs, this.input.state.environmentDigest);
              if (proofs.every(proof => proof.passed)) group.forEach((item, index) => batched.set(item, proofs[index]!));
              else this.input.emit('task_recheck_batch_fallback', { taskIds: group.map(item => item.task.id) });
            } catch (error) {
              this.input.signal.throwIfAborted();
              this.input.emit('task_recheck_batch_fallback', { taskIds: group.map(item => item.task.id),
                reason: bounded(error instanceof Error ? error.message : String(error), 1000) });
            }
          }
        }
        const receipt = await this.check(node.task, assignment, this.lead.worktree, canonical, [], batched.get(node));
        this.input.signal.throwIfAborted();
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.status = 'blocked'; node.feedback = solverProofFeedback(receipt); this.needsLead = true; }
        else if (!taskDependenciesReady(node.task, this.archive.tasks)) {
          node.status = 'blocked'; node.feedback = 'math_task_dependency_invalidated'; this.needsLead = true;
        }
      } catch (error) {
        this.input.signal.throwIfAborted();
        if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
        node.status = 'blocked'; node.feedback = error instanceof Error ? error.message : 'math_task_recheck_failed'; this.needsLead = true;
      }
      finish(node);
    }
  }
  private supersedeStatementReview(review: StatementReview) {
    review.status = 'superseded';
    for (const record of this.archive.deliveries ?? []) if (record.statementReviewId === review.id) record.status = 'superseded';
  }
  private prepareStatementContexts(nodes: readonly TaskRecord[] = this.archive.tasks): Promise<void> | undefined {
    if (this.preparingStatements) return this.preparingStatements.then(() => this.prepareStatementContexts(nodes));
    const tasks = nodes.filter(node => node.task.statementReview).map(node => node.task);
    const keys = new Map(tasks.map(task => [task.id, statementSnapshot(this.input.state.problem, task, this.lead.worktree,
      this.archive.canonicalCommit!, this.input.state.environmentDigest, this.dependencies(task, nodes).map(dependency =>
        ({ task: dependency.task, taskDigest: digest(dependency.task) }))).snapshotDigest]));
    const missing = tasks.filter(task => !this.statementContexts.has(keys.get(task.id)!));
    if (!missing.length) return;
    const pending = captureStatementContexts(this.input.state.problem, missing, this.lead.worktree,
      this.archive.canonicalCommit!, this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs)
      .then(contexts => { for (const task of missing) this.statementContexts.set(keys.get(task.id)!, contexts.get(task.id)!); })
      .finally(() => { if (this.preparingStatements === pending) this.preparingStatements = undefined; });
    this.preparingStatements = pending;
    return pending;
  }
  private syncStatementReviews(invalidated = new Set<string>()) {
    if (!this.archive.statementReviews?.length && !this.archive.tasks.some(node => node.task.statementReview)) return;
    const reviews = this.archive.statementReviews ??= [];
    const tasks = this.archive.tasks.filter(node => node.task.statementReview).map(node => node.task);
    const snapshots = new Map(tasks.map(task => [task.id,
      statementSnapshot(this.input.state.problem, task, this.lead.worktree, this.archive.canonicalCommit!,
        this.input.state.environmentDigest, this.dependencies(task).map(dependency =>
          ({ task: dependency.task, taskDigest: digest(dependency.task) }))) ]));
    for (const task of tasks) snapshots.set(task.id, statementSnapshot(this.input.state.problem, task, this.lead.worktree,
      this.archive.canonicalCommit!, this.input.state.environmentDigest, this.dependencies(task).map(dependency =>
        ({ task: dependency.task, taskDigest: digest(dependency.task) })), this.statementContexts.get(snapshots.get(task.id)!.snapshotDigest)));
    for (const review of reviews.filter(item => item.status !== 'superseded')) {
      const node = this.node(review.taskId), snapshot = snapshots.get(review.taskId);
      const reuse = review.status === 'accepted' && node?.task.kind === 'goal' && snapshot?.snapshotDigest === review.snapshotDigest &&
          review.intendedStatement === node.task.informalStatement &&
          canonicalMathJson(review.premises) === canonicalMathJson(node.task.premises ?? this.input.state.problem.contract.assumptions);
      if (reuse) {
        if (invalidated.has(review.taskId) || review.taskDigest !== digest(node.task)) {
          review.taskDigest = digest(node.task); review.dependencies = [];
          this.record(this.lead, node.task, 'statement-review', 'accepted', review.summary ?? 'Fixed original statement review reused.',
            { statementReviewId: review.id, taskDigest: review.taskDigest, statement: review.leanStatement,
              premises: review.premises, dependencies: [], remainingObligations: [], commit: review.commit, sourceDigest: review.snapshotDigest });
          this.input.emit('statement_review_reused', { taskId: review.taskId, reviewId: review.id });
        }
      }
      if ((!reuse && (invalidated.has(review.taskId) || !node || digest(node.task) !== review.taskDigest)) || !snapshot ||
          review.intendedStatement !== node?.task.informalStatement ||
          canonicalMathJson(review.premises) !== canonicalMathJson(node?.task.premises ?? this.input.state.problem.contract.assumptions) ||
          (snapshot.snapshotDigest !== review.snapshotDigest && (!review.references || !this.checkedStatementReferences.has(review.references) ||
            !proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!, review.references, this.input.state.environmentDigest)))) {
        this.supersedeStatementReview(review);
      }
      if (review.status !== 'superseded' && (!review.references || !this.checkedStatementReferences.has(review.references)) && snapshot?.snapshotDigest === review.snapshotDigest) {
        const proof = node?.integratedCheck;
        const references = snapshot.references ?? (proof?.references && hasTaskReferences(proof)
          ? captureProofReferences(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!, proof.references.root,
            { statement: proof.references.statement, proof: [] }, this.input.state.environmentDigest, 'statement') : undefined);
        if (references) { review.references = references; this.checkedStatementReferences.add(references); }
      }
    }
    for (const [taskId, snapshot] of snapshots) {
      if (reviews.some(review => review.taskId === taskId && review.status !== 'superseded')) continue;
      const task = this.node(taskId).task, id = crypto.randomUUID();
      const workspace = path.join(path.dirname(this.lead.worktree), 'statement-reviews', id);
      reviews.push({ id, taskId, taskDigest: digest(task), snapshotDigest: snapshot.snapshotDigest,
        environmentDigest: this.input.state.environmentDigest, commit: this.archive.canonicalCommit!,
        leanStatement: snapshot.input.leanStatement, intendedStatement: task.informalStatement!,
        premises: task.premises ?? this.input.state.problem.contract.assumptions,
        dependencies: task.kind === 'goal' ? [] : this.dependencies(task).map(node => ({ taskId: node.task.id, taskDigest: digest(node.task) })),
        ...(snapshot.references ? { references: snapshot.references } : {}),
        workspace, files: writeStatementSnapshot(workspace, snapshot), status: 'pending' });
      if (snapshot.references) this.checkedStatementReferences.add(snapshot.references);
      this.input.emit('statement_review_requested', { taskId, reviewId: id, snapshotDigest: snapshot.snapshotDigest });
    }
    for (const active of this.active.values()) if (isStatementAction(active.action) && !this.current(active.action) && !active.cancelled) {
      const reviewId = active.action.reviewId;
      const review = reviews.find(item => item.id === reviewId);
      if (review && ['translating', 'reviewing'].includes(review.status)) resetStatementReview(review);
      active.cancelled = true; void active.interrupt().catch(() => {});
    }
  }
  private async mergeLeadSources(commit: string, seedCommit: string) {
    const problem = this.input.state.problem;
    git(this.lead.worktree, ['merge-base', '--is-ancestor', seedCommit, commit]);
    const changes = taskChanges(problem, this.lead.worktree, commit, undefined, { seedCommit });
    const imports = problem.ownedFiles.filter(file => file.endsWith('.lean')).flatMap(file => {
      const before = solverProofImports(problem, committedSource(this.lead.worktree, seedCommit, `${problem.projectRelative}/${file}`));
      return solverProofImports(problem, committedSource(this.lead.worktree, commit, `${problem.projectRelative}/${file}`))
        .filter(module => !before.includes(module)).map(module => ({ file, module }));
    });
    return withSolverWorktree(this.lead.worktree, this.archive.canonicalCommit!, async checkout => {
      applyTaskChanges(problem, checkout, changes, imports);
      const merged = commitSolverSources(problem, checkout);
      this.pin(merged);
      return merged;
    });
  }
  private preserveLeadDraft(commit: string, seedCommit: string | undefined, reason: string) {
    const summary = `Saved Lead draft pending integration: ${reason}. ` +
      `Inspect git show ${commit}:PROJECT_RELATIVE_PATH and reapply the useful declarations against the current canonical sources. ` +
      'This draft has no proof acceptance.';
    if (!this.archive.deliveries?.some(record => record.producer === this.lead.id && record.kind === 'progress' &&
        record.commit === commit && record.summary.startsWith('Saved Lead draft pending integration:'))) {
      this.record(this.lead, undefined, 'progress', 'advisory', summary, { commit });
    }
    this.archive.error = reason; this.needsLead = true;
    this.input.emit('lead_draft_preserved', { commit, seedCommit, canonicalCommit: this.archive.canonicalCommit, reason });
  }
  private async restoreLeadSources() {
    const problem = this.input.state.problem;
    const seed = this.archive.leadSeedCommit;
    const draft = commitSolverSources(problem, this.lead.worktree);
    this.pin(draft);
    if (ownedSourceDigest(problem, this.lead.worktree, draft) !==
        ownedSourceDigest(problem, this.lead.worktree, this.archive.canonicalCommit!)) {
      try {
        if (!seed) throw new Error('math_lead_recovery_seed_unknown');
        this.archive.canonicalCommit = await this.mergeLeadSources(draft, seed);
        this.input.emit('lead_draft_restored', { commit: draft, seedCommit: seed, canonicalCommit: this.archive.canonicalCommit });
      } catch (error) {
        this.input.signal.throwIfAborted();
        this.preserveLeadDraft(draft, seed, error instanceof Error ? error.message : 'math_lead_recovery_failed');
      }
    }
    this.archive.canonicalCommit = this.seed(this.lead, this.archive.canonicalCommit!);
  }
  async restore() {
    if (this.refreshFeasibilityAssignments()) this.changed();
    for (const failed of this.archive.failedTaskInputs ?? []) {
      let repair = failed.repair;
      const node = this.node(repair?.taskId ?? failed.taskId);
      if (!repair && node && node.attempts === 1 && ['pending', 'running'].includes(node.status) &&
          failed.taskDigest === digest(node.task) && node.assignment?.taskDigest === failed.taskDigest) {
        repair = failed.repair = { taskId: node.task.id, taskDigest: failed.taskDigest,
          workerId: node.assignment.workerId, pending: true };
        this.input.emit('task_repair_requested', { taskId: node.task.id, workerId: repair.workerId,
          taskDigest: repair.taskDigest, reason: 'failed-check-restored' });
      }
      if (!repair || repair.pending || !node || !['pending', 'running'].includes(node.status) ||
          repair.taskDigest !== digest(node.task) || repair.workerId !== node.assignment?.workerId || repair.startedAttempt !== node.attempts) continue;
      repair.pending = true; delete repair.startedAttempt;
      this.input.emit('task_repair_interrupted', { taskId: node.task.id, workerId: repair.workerId, failureId: failed.id, reason: 'process-restored' });
    }
    this.syncPlanNotes();
    for (const review of this.archive.statementReviews ?? []) if (review.status !== 'superseded') {
      try { assertStatementSnapshot(review); }
      catch { this.supersedeStatementReview(review); continue; }
      resetStatementReview(review);
    }
    // A resumed review must inspect the fixed version again.
    if (this.archive.review) { this.archive.review.status = 'pending'; this.archive.review.workerId = undefined; }
    if (!this.primaryLed &&
        !this.archive.frontierRecoveries?.some(record => record.status !== 'planned') &&
        fs.existsSync(path.join(this.lead.worktree, 'RESEARCH.md'))) {
      try {
        const rejection = this.archive.planRejection;
        if (!rejection?.stalled || rejection.proposalDigest !== this.proposedPlanDigest() ||
            rejection.inputDigest !== this.planningInputDigest()) {
          const plan = readCooperationPlan(this.input.state.problem, this.lead.worktree);
          this.preserveHandoffBacklog(plan, []);
          const initial = !this.archive.tasks.length;
          await this.acceptPlan(plan);
          if (initial) this.needsLead = false;
        }
      } catch (error) { this.rejectPlan(error); }
    }
    if (!solverSourceFeedback(this.input.state.problem, this.lead.worktree)) {
      if (!this.primaryLed) await this.restoreLeadSources();
      await this.input.exclusiveCheck(() => this.recheckIntegrated(this.archive.canonicalCommit!));
    } else {
      for (const node of this.archive.tasks.filter(node => node.status === 'integrated')) {
        node.status = 'blocked'; node.feedback = 'math_canonical_source_invalid';
      }
      this.needsLead = true;
    }
    for (const node of this.archive.tasks) if (node.status === 'running') node.status = 'pending';
    for (const node of this.archive.tasks.filter(node => node.status === 'delivered')) await this.input.exclusiveCheck(() => this.integrate(node));
    await this.input.exclusiveCheck(() => this.integrateReady());
    const statements = this.prepareStatementContexts(); if (statements) await statements;
    this.syncStatementReviews();
    this.changed();
  }
  private planInvalidation({ tasks, groups, proofRoutes }: ReturnType<typeof parseCooperationPlan>) {
    const previousGroups = new Map(this.archive.groups?.map(record => [record.group.id, record]));
    const changedGroups = new Set(groups.filter(group => {
      const previous = previousGroups.get(group.id)?.group;
      return previous && (previous.objective !== group.objective || previous.revision !== group.revision);
    }).map(group => group.id));
    const dependencies = new Map(this.archive.tasks.map(node => {
      const references = taskReferenceDependencies(node);
      return [node.task.id, references && proofReferencesUnchanged(this.input.state.problem, this.lead.worktree,
        this.archive.canonicalCommit!, node.integratedCheck!.references!, this.input.state.environmentDigest)
        ? references.map(reference => reference.taskId)
        : [...node.task.dependsOn, ...(node.alternativeRoutes?.flatMap(route => [...route.prerequisiteTaskIds, route.closingTaskId]) ?? []),
          ...(node.assignment?.dependencies?.map(dependency => dependency.taskId) ?? [])]];
    }));
    const routeChanges = new Set(this.archive.tasks.filter(node => node.status !== 'integrated' &&
      canonicalMathJson(node.alternativeRoutes ?? []) !== canonicalMathJson(proofRoutes?.filter(route => route.targetTaskId === node.task.id) ?? []))
      .map(node => node.task.id));
    return invalidatedTaskIds(this.archive.tasks, tasks, changedGroups, dependencies, routeChanges);
  }
  private async acceptPlan(plan = readCooperationPlan(this.input.state.problem, this.lead.worktree), edit?: HumanEditRecord) {
    const { tasks, groups, proofRoutes } = plan;
    if (this.primaryLed && tasks.some(task => task.kind === 'goal' && task.status !== 'paused'))
      throw new Error('math_help_original_goals_owned_by_primary');
    for (const task of tasks) if (task.ownerId) {
      const owner = this.input.workers.find(worker => worker.id === task.ownerId);
      if (!owner || (task.kind === 'goal' ? !['engineer', 'researcher'].includes(owner.role) : owner.role !== 'researcher'))
        throw new Error('math_plan_task_owner_unavailable');
    }
    const previousGroups = new Map(this.archive.groups?.map(record => [record.group.id, record]));
    const configuredGroups = groups.map(group => {
      if (group.engineerId && !this.input.workers.some(worker => worker.id === group.engineerId && worker.role === 'engineer'))
        throw new Error('math_plan_group_engineer_unavailable');
      return { ...group };
    });
    const current = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const invalidated = this.planInvalidation(plan);
    const proposed: TaskRecord[] = tasks.map(task => {
      const previous = current.get(task.id);
      const node: TaskRecord = previous && !invalidated.has(task.id) ? { ...previous, task } :
        { task, status: 'pending', attempts: previous?.attempts ?? 0 };
      node.alternativeRoutes = proofRoutes?.filter(route => route.targetTaskId === task.id);
      const owner = task.ownerId ?? (task.kind === 'goal' ? configuredGroups.find(group => group.id === taskGroup(task))?.engineerId : undefined);
      if (owner && node.assignment && node.assignment.workerId !== owner && ['pending', 'running'].includes(node.status)) {
        node.status = 'pending'; node.assignment = undefined;
      }
      return node;
    });
    const statements = this.prepareStatementContexts(proposed); if (statements) await statements;
    this.input.signal.throwIfAborted();
    for (const id of invalidated) if (this.archive.unchangedResearch) delete this.archive.unchangedResearch[id];
    for (const id of invalidated) if (this.archive.researchCheckpoints) delete this.archive.researchCheckpoints[id];
    for (const previousEdit of this.archive.edits ?? []) for (const result of previousEdit.recheck?.tasks ?? [])
      if (invalidated.has(result.taskId) && result.status !== 'removed') result.status = 'superseded';
    for (const record of this.archive.deliveries ?? []) if (record.taskId && invalidated.has(record.taskId)) record.status = 'superseded';
    for (const id of invalidated) {
      const previous = current.get(id);
      if (previous) (this.archive.history ??= []).push(
        { task: previous.task, producer: previous.assignment?.workerId, proof: previous.proof, integratedCheck: previous.integratedCheck, finding: previous.finding });
    }
    this.archive.tasks = tasks.map(task => {
      const previous = current.get(task.id);
      if (previous && !invalidated.has(task.id)) {
        previous.task = task;
        const owner = task.ownerId ?? (task.kind === 'goal' ? configuredGroups.find(group => group.id === taskGroup(task))?.engineerId : undefined);
        if (owner && previous.assignment && previous.assignment.workerId !== owner && ['pending', 'running'].includes(previous.status)) {
          previous.status = 'pending'; previous.assignment = undefined;
        }
        return previous;
      }
      return { task, status: 'pending', attempts: previous?.attempts ?? 0 };
    });
    this.archive.groups = configuredGroups.map(group => ({ group, turns: previousGroups.get(group.id)?.turns ?? 0 }));
    this.archive.proofRoutes = proofRoutes;
    this.syncProofRoutes();
    if (invalidated.size) { this.archive.review = undefined; this.lastAssembly = undefined; }
    for (const [id, active] of this.active) {
      if (active.action.kind === 'review' && !this.archive.review && !active.cancelled) { active.cancelled = true; void active.interrupt().catch(() => {}); }
      if (active.action.kind !== 'task') continue;
      const action = active.action;
      const node = this.archive.tasks.find(item => item.task.id === action.task.id);
      const group = configuredGroups.find(route => route.id === (node && taskGroup(node.task)));
      if (!node || invalidated.has(action.task.id) || (node.task.status ?? 'active') !== 'active' || group?.status !== 'active' ||
          (node.task.ownerId && node.task.ownerId !== id) ||
          (node.task.kind === 'goal' && group.engineerId && group.engineerId !== id)) {
        if (node && !invalidated.has(node.task.id) && node.status === 'running') {
          node.status = 'pending';
          if ((node.task.ownerId && node.task.ownerId !== id) || (node.task.kind === 'goal' && group?.engineerId && group.engineerId !== id)) node.assignment = undefined;
        }
        if (!active.cancelled) { active.cancelled = true; void active.interrupt().catch(() => {}); }
      }
    }
    this.archive.error = undefined;
    this.archive.planRejection = undefined;
    if (edit) {
      edit.status = 'applied'; edit.appliedAt = Date.now(); edit.pendingSync = true;
      edit.affectedTasks = [...new Set([...invalidated, ...tasks.filter(task => !current.has(task.id)).map(task => task.id)])];
      edit.recheck = { status: 'pending', tasks: edit.affectedTasks.filter(id => {
        const task = this.node(id)?.task ?? current.get(id)?.task;
        return task && !advisory(task);
      }).map(id => ({ taskId: id, taskDigest: digest((this.node(id) ?? current.get(id)!).task),
        status: this.node(id) ? 'pending' : 'removed' })) };
      this.archive.planEdited = true;
    }
    this.archive.planVersion = this.planVersion();
    // Persist the accepted graph before writing recoverable review snapshots.
    this.changed(edit);
    this.input.emit('plan_updated', { groups: this.archive.groups, tasks: tasks.map(task =>
      ({ id: task.id, kind: task.kind, dependsOn: task.dependsOn, groupId: taskGroup(task), sharing: task.sharing ?? 'problem' })), invalidated: [...invalidated] });
    this.syncStatementReviews(invalidated);
    if (edit) edit.pendingSync = undefined;
    this.changed(edit);
  }
  /** A planning checkpoint without a graph must not leave every peer idle. */
  async startInitialTasks() {
    if (this.archive.tasks.length) return;
    const reason = this.archive.error ?? 'math_initial_plan_checkpoint';
    const researchers = this.input.workers.filter(worker => worker.role === 'researcher' && this.liveWorkers.has(worker.id));
    const targets = this.input.state.problem.targets;
    const tasks = [
      ...targets.map((target, index) => ({ id: `initial_goal_${index + 1}`, kind: 'goal',
        objective: `Prove the frozen original target ${target.theoremName}; use researcher findings as advisory guidance.`,
        proofPath: target.proofPath, theoremName: target.theoremName })),
      ...researchers.map((worker, index) => ({ id: `initial_research_${index + 1}`, kind: 'research', ownerId: worker.id,
        objective: `Investigate proof routes and difficult library connections for ${targets.filter((_, i) => i % researchers.length === index)
          .map(target => target.theoremName).join(', ') || 'the original targets'}. Report concrete evidence and unresolved gaps; findings are advisory.` })),
    ];
    await this.acceptPlan(parseCooperationPlan(this.input.state.problem, { tasks }));
    this.needsLead = false;
    this.archive.initialPlanFallback = { at: Date.now(), reason };
    this.archive.planEdited = true;
    this.syncPlanNotes();
    this.input.emit('initial_plan_fallback', { reason, planVersion: this.archive.planVersion });
    this.changed();
  }
  private planVersion() {
    return mathDigest(canonicalMathJson({ tasks: this.archive.tasks.map(node => node.task),
      groups: this.archive.groups?.map(route => route.group),
      ...(this.archive.proofRoutes?.length ? { proofRoutes: this.archive.proofRoutes } : {}) }));
  }
  private async integrate(node: TaskRecord) {
    const problem = this.input.state.problem;
    let integrated = false;
    try {
      await withSolverWorktree(this.lead.worktree, this.archive.canonicalCommit!, async checkout => {
        // Only archived deliveries need a second delivery check; merged sources always get their own check.
        const submitted = this.checkedDeliveries.has(node.proof!) ? node.proof! :
          await this.check(node.task, node.assignment!, checkout, node.proof!.commit, (node.proof!.conditions ?? []).map(condition => {
            const dependency = this.node(condition.taskId);
            if (!dependency || digest(dependency.task) !== condition.taskDigest) throw new Error('math_task_condition_version_invalid');
            return dependency.task;
          }));
        this.input.signal.throwIfAborted();
        node.proof = submitted;
        if (['unavailable', 'blocked'].includes(submitted.verification.status)) throw new Error('math_verifier_unavailable');
        if (!submitted.passed) throw new Error('math_task_delivery_no_longer_checks');
        if (!taskDependenciesReady(node.task, this.archive.tasks))
          throw new Error('math_task_dependency_invalidated');
        applyTaskChanges(problem, checkout, submitted.changes, submitted.imports);
        const merged = commitSolverSources(problem, checkout);
        const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: merged };
        const receipt = await this.check(node.task, assignment, checkout, merged);
        this.input.signal.throwIfAborted();
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.feedback = solverProofFeedback(receipt); throw new Error('math_task_merged_proof_failed'); }
        this.archive.canonicalCommit = merged;
        node.status = 'integrated';
        integrated = true;
        this.input.emit('task_integrated', { taskId: node.task.id, groupId: taskGroup(node.task), sharing: node.task.sharing ?? 'problem', commit: merged });
        const statements = this.prepareStatementContexts(); if (statements) await statements;
        this.syncStatementReviews();
      });
    } catch (error) {
      this.input.signal.throwIfAborted();
      if (integrated || !(error instanceof Error) || error.name === 'AbortError' || !integrationRejections.has(rejectionCode(error))) throw error;
      node.status = 'blocked'; node.feedback = `${error instanceof Error ? error.message : 'math_task_integration_failed'}\n${node.feedback ?? ''}`;
      this.needsLead = true;
    } finally { this.changed(); }
  }
  async next(worker: ResearchWorker, budget: { maxTurns: number; remainingMs: number }): Promise<CooperativeAction | undefined> {
    for (;;) {
      if (this.stopping) return;
      this.input.signal.throwIfAborted();
      if (this.failure) throw this.failure;
      if (this.refreshFeasibilityAssignments()) this.changed();
      this.refreshResearchCheckpoints();
      if (this.refreshFailedTaskInputs()) this.changed();
      if (this.archive.frontierWaiting && this.archive.frontierWaiting.inputDigest !== this.planningInputDigest()) {
        this.archive.frontierWaiting = undefined; this.changed();
      }
      if (!this.liveWorkers.has(this.lead.id)) return;
      // Publish complete fixed snapshots before assigning work against a newly changed plan.
      if (this.preparingStatements) { await this.preparingStatements.catch(() => {}); continue; }
      const modelAllowed = this.input.modelDispatchAllowed?.() !== false;
      if (worker.id === this.lead.id) {
        if (this.primaryLed) {
          const review = this.archive.review;
          if (review && ['pending', 'running'].includes(review.status)) {
            if (!this.livePeers.length) return;
            if (review.status === 'pending' &&
                ((this.input.state.turns >= budget.maxTurns && !this.reservedTurns.size) || budget.remainingMs <= 0 || !modelAllowed)) {
              if (!modelAllowed && this.active.size) { await this.wait(); continue; }
              return;
            }
            await this.wait(); continue;
          }
          if (this.reviewed() && this.lastAssembly !== review!.commit) {
            this.lastAssembly = review!.commit;
            return { kind: 'assemble', seedCommit: review!.commit };
          }
          if (this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0 || !modelAllowed) {
            const pending = modelAllowed && budget.remainingMs > 0 && this.waitForTurn(budget.maxTurns);
            if (pending) { await pending; continue; }
            if (!modelAllowed && (this.active.size || this.archive.tasks.some(node => ['running', 'delivered'].includes(node.status)))) {
              await this.wait(); continue;
            }
            return;
          }
          return { kind: 'solve', seedCommit: git(worker.worktree, ['rev-parse', 'HEAD']), ...this.handoffDispatch() };
        }
        const head = this.archive.canonicalCommit!;
        const goals = this.archive.tasks.filter(node => node.task.kind === 'goal');
        if (((goals.length && goals.every(node => node.status === 'integrated')) || this.reviewed()) && this.lastAssembly !== head) {
          this.syncPlanNotes();
          const seed = this.seed(worker, head); this.archive.canonicalCommit = seed;
          this.lastAssembly = seed; return { kind: 'assemble', seedCommit: seed };
        }
        const running = this.active.size > 0 || this.archive.tasks.some(node => ['running', 'delivered'].includes(node.status) ||
          (node.status === 'conditional' && taskDependenciesReady(node.task, this.archive.tasks))) || this.archive.review?.status === 'running' ||
          this.archive.statementReviews?.some(review => ['translating', 'reviewing'].includes(review.status) ||
            (modelAllowed && this.input.state.turns < budget.maxTurns && budget.remainingMs > 0 &&
              ['pending', 'translated'].includes(review.status) && this.livePeers.length > 0 &&
              routeAllowsTask(this.node(review.taskId).task, this.archive.tasks, this.archive.groups)));
        if (this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0 || !modelAllowed) {
          const pending = modelAllowed && budget.remainingMs > 0 && this.waitForTurn(budget.maxTurns);
          if (pending) { await pending; continue; }
          if (running) { await this.wait(); continue; }
          return;
        }
        if (!running && !this.livePeers.length) return;
        if (this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) { await this.wait(); continue; }
        const rejection = this.archive.planRejection;
        if (rejection?.stalled) {
          if (rejection.inputDigest === this.planningInputDigest() && rejection.proposalDigest === this.proposedPlanDigest()) {
            this.needsLead = false;
            if (!running && !this.canAdvance()) {
              this.input.emit('plan_stalled', { ...rejection }); return;
            }
            await this.wait(); continue;
          }
          this.needsLead = true;
        }
        const pendingHandoffs = selectResearchHandoffBatch(this.archive);
        if (pendingHandoffs.length) this.needsLead = true;
        if (!this.needsLead && this.archive.tasks.length) {
          const support = originalGoalTaskFocus(this.archive.tasks, this.archive.groups).support;
          const supportingWork = this.archive.tasks.some(node => support.has(node.task.id) &&
            (['running', 'delivered'].includes(node.status) ||
              node.status === 'conditional' && taskDependenciesReady(node.task, this.archive.tasks))) ||
            this.archive.statementReviews?.some(review => support.has(review.taskId) &&
              ['pending', 'translating', 'translated', 'reviewing'].includes(review.status));
          // Independent work must not defer reconsidering a stalled original argument.
          if (!supportingWork && !this.hasAssignableTask(support) && !this.canAdvance(support)) {
            const frontier = this.activeGoalFrontier();
            if (frontier.some(item => item.status === 'blocked' && item.attempts > 0)) {
              const recovery = this.requestFrontierRecovery(frontier);
              if (recovery) return recovery;
              if (await this.investigateFrontierRecovery(frontier)) continue;
            }
          }
        }
        if (!running && !this.needsLead && this.archive.tasks.length && (!this.archive.review || this.archive.review.status === 'changes_requested') &&
            !this.canAdvance()) {
          // Parking prevents repeating an inference, not reconsidering its unfinished original goal.
          const frontier = this.activeGoalFrontier();
          const inputDigest = this.planningInputDigest();
          const goalIds = [...new Set(frontier.flatMap(item => item.goalIds))];
          if (!frontier.length || inputDigest === this.archive.lastLeadInputDigest) {
            if (this.resumeUnattemptedFrontier(frontier)) continue;
            const recovery = this.requestFrontierRecovery(frontier);
            if (recovery) return recovery;
            if (await this.investigateFrontierRecovery(frontier)) continue;
            if (await this.waitForFrontierInput(frontier, inputDigest)) continue;
            this.input.emit('routes_idle', { groups: this.archive.groups, goalIds, frontier,
              reason: frontier.length ? 'unchanged-mathematical-input' : 'no-active-goal-frontier', inputDigest }); return;
          }
          this.needsLead = true;
          this.input.emit('blocked_tasks_reconsidered', { taskIds: frontier.map(item => item.taskId), goalIds, inputDigest });
        }
        if (this.needsLead || (!running && (!this.livePeers.length ||
            !this.hasAssignableTask()))) {
          this.needsLead = false;
          const inputDigest = this.planningInputDigest();
          if (inputDigest === this.archive.lastLeadInputDigest && !this.archive.error && !pendingHandoffs.length) {
            if (!running && !this.hasAssignableTask()) {
              const frontier = this.activeGoalFrontier(), goalIds = [...new Set(frontier.flatMap(item => item.goalIds))];
              if (this.resumeUnattemptedFrontier(frontier)) continue;
              const recovery = this.requestFrontierRecovery(frontier);
              if (recovery) return recovery;
              if (await this.investigateFrontierRecovery(frontier)) continue;
              if (await this.waitForFrontierInput(frontier, inputDigest)) continue;
              this.input.emit('routes_idle', { groups: this.archive.groups, goalIds, frontier,
                reason: frontier.length ? 'unchanged-mathematical-input' : 'no-active-goal-frontier', inputDigest }); return;
            }
            continue;
          }
          if (this.archive.frontierRecoveries?.some(record => record.status === 'requested')) {
            const recovery = this.requestFrontierRecovery(this.activeGoalFrontier());
            if (recovery) return recovery;
          }
          this.syncPlanNotes();
          const action: CooperativeAction = { kind: 'lead', seedCommit: this.seed(worker, head), planVersion: this.archive.planVersion,
            planningInputDigest: inputDigest, ...this.handoffDispatch(pendingHandoffs) };
          this.leadEvidence.set(action, this.planningEvidenceDigest());
          return action;
        }
      } else {
        if (budget.remainingMs <= 0 || !modelAllowed) return;
        if (this.input.state.turns >= budget.maxTurns) {
          const pending = this.waitForTurn(budget.maxTurns);
          if (pending) { await pending; continue; }
          return;
        }
        const review = this.archive.review;
        const reviewer = this.reviewer();
        const statement = reviewer?.id === worker.id && this.archive.statementReviews?.find(item =>
          ['pending', 'translated'].includes(item.status) && routeAllowsTask(this.node(item.taskId).task, this.archive.tasks, this.archive.groups) &&
          ![...this.active.values()].some(active => isStatementAction(active.action) && active.action.reviewId === item.id));
        if (statement) {
          const kind = statement.status === 'pending' ? 'backtranslate' : 'statement-review';
          fs.rmSync(path.join(statement.workspace, 'RESEARCH.md'), { force: true });
          statement.status = kind === 'backtranslate' ? 'translating' : 'reviewing'; statement.workerId = worker.id;
          statement.assignmentId = crypto.randomUUID();
          this.input.emit('statement_review_assigned', { workerId: worker.id, taskId: statement.taskId, reviewId: statement.id, kind, role: 'reviewer' });
          this.changed(); return { kind, reviewId: statement.id, taskId: statement.taskId, taskDigest: statement.taskDigest,
            snapshotDigest: statement.snapshotDigest, seedCommit: statement.commit, workspace: statement.workspace,
            assignmentId: statement.assignmentId };
        }
        if (review?.status === 'pending' && reviewer?.id === worker.id) {
          this.seed(worker, review.commit);
          const notes = path.join(worker.worktree, 'RESEARCH.md');
          if (fs.existsSync(notes)) fs.writeFileSync(notes, fs.readFileSync(notes, 'utf8').replace(/```(?:math|math-review)\s*\n[\s\S]*?\n```/gu, ''));
          review.workerId = worker.id; review.status = 'running'; review.assignmentId = crypto.randomUUID();
          this.input.emit('review_assigned', { workerId: worker.id, commit: review.commit, role: 'reviewer' });
          this.changed(); return { kind: 'review', seedCommit: review.commit, sourceDigest: review.sourceDigest,
            assignmentId: review.assignmentId };
        }
        const ready = this.input.modules.M3.ready(this.archive.tasks, this.archive.groups);
        const node = this.input.modules.M5.assign(ready, worker,
          this.livePeers, this.archive.groups, this.archive.tasks);
        if (node) {
          const engineerId = node.task.kind === 'goal' && this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId;
          if (!ready.includes(node) || !this.archive.tasks.includes(node) || node.status !== 'pending' ||
              !taskCanStart(node.task, this.archive.tasks) ||
              !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
              !independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups) ||
              (node.task.ownerId && node.task.ownerId !== worker.id) || (engineerId && engineerId !== worker.id) ||
              (node.assignment && node.assignment.workerId !== worker.id)) throw new Error('math_task_assignment_invalid');
          const selectedRoute = selectedTaskRoute(node, this.archive.tasks);
          if (node.assignment && node.alternativeRoutes?.length && node.assignment.routeId !== selectedRoute?.id)
            node.assignment = undefined;
          let resuming = node.assignment?.workerId === worker.id;
          if (resuming && advisory(node.task) &&
              (this.archive.researchDrafts?.[node.task.id]?.suspended || this.researchWorkspaceChanged(worker, node))) {
            const previousAssignment = node.assignment;
            const restored = await this.restoreResearchDraft(worker, node);
            if (!this.archive.tasks.includes(node) || node.status !== 'pending' ||
                !restored && node.assignment !== previousAssignment ||
                node.task.ownerId && node.task.ownerId !== worker.id ||
                !independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups) ||
                !taskCanStart(node.task, this.archive.tasks) || !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups)) continue;
            if (!restored) {
              fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '');
              node.assignment = undefined; resuming = false;
              if (this.archive.researchCheckpoints) delete this.archive.researchCheckpoints[node.task.id];
              node.feedback = 'math_research_draft_unavailable: No matching saved draft is available; continue from the current canonical sources and save findings for this assignment.';
              this.input.emit('research_draft_unavailable', { taskId: node.task.id, workerId: worker.id });
            }
          }
          this.suspendResearchDrafts(worker, node.task.id);
          const seed = this.archive.canonicalCommit!;
          let scopedSeed = seed;
          if (!resuming) {
            scopedSeed = this.seed(worker, seed, node.task);
          }
          node.assignment ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id,
            seedCommit: scopedSeed, assignmentId: crypto.randomUUID(), canonicalCommit: seed, groupId: taskGroup(node.task),
            routeId: selectedRoute?.id,
            dependencies: this.dependencies(node.task).map(item => ({ taskId: item.task.id, taskDigest: digest(item.task) })) };
          node.status = 'running';
          const route = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
          this.input.emit('task_assigned', { taskId: node.task.id, workerId: worker.id, kind: node.task.kind,
            groupId: taskGroup(node.task), groupTurns: route?.turns, seedCommit: node.assignment.seedCommit });
          this.changed(); return { kind: 'task', assignment: node.assignment, task: node.task };
        }
        if (!this.liveWorkers.has(worker.id)) return;
      }
      await this.wait();
    }
  }
  private canAdvance(taskIds?: ReadonlySet<string>) {
    return researchCanAdvance(this.archive.tasks, this.archive.groups, this.liveWorkers, node =>
      this.livePeers.some(worker => this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node), taskIds);
  }
  private hasAssignableTask(taskIds?: ReadonlySet<string>) {
    return this.input.modules.M3.ready(this.archive.tasks, this.archive.groups).some(node => (!taskIds || taskIds.has(node.task.id)) && this.archive.tasks.includes(node) &&
      this.livePeers.some(worker => this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node));
  }
  private handoffDispatch(batch = selectResearchHandoffBatch(this.archive)) {
    return { handoffIds: batch.map(item => item.id),
      handoffActivations: Object.fromEntries(batch.map(item => [item.id, item.activationDigest])) };
  }
  private recordHandoffDecisions(decisions: readonly ResearchHandoffDecision[]) {
    if (!decisions.length) return;
    const records = new Map(this.archive.researchDecisions?.map(item => [item.id, item]));
    for (const decision of decisions) {
      records.set(decision.id, decision);
      this.input.emit('research_handoff_decided', { ...decision });
    }
    this.archive.researchDecisions = [...records.values()];
    this.changed();
  }
  private visible(task: CooperativeTask): TaskRecord[] {
    const nodes = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const visible = new Set(this.archive.tasks.filter(node => taskGroup(node.task) === taskGroup(task) ||
      (node.task.sharing !== 'group' && ['integrated', 'completed'].includes(node.status))));
    const seen = new Set<string>();
    const visit = (node: TaskRecord) => {
      if (seen.has(node.task.id)) return; seen.add(node.task.id);
      for (const id of plannedTaskDependencyIds(node, this.archive.tasks)) {
        const input = nodes.get(id);
        if (!input || (taskGroup(input.task) !== taskGroup(task) && input.task.sharing === 'group')) continue;
        visible.add(input); visit(input);
      }
    };
    const current = nodes.get(task.id); if (current) visit(current);
    return this.archive.tasks.filter(node => visible.has(node));
  }
  private seed(worker: ResearchWorker, commit: string, task?: CooperativeTask): string {
    this.suspendResearchDrafts(worker, task?.id);
    const session = this.input.state.workers?.find(record => record.id === worker.id);
    const previousGroup = session?.sessionGroupId;
    if (task && (previousGroup && previousGroup !== taskGroup(task) || session?.sessionTaskId && session.sessionTaskId !== task.id) ||
        !task && worker.id !== this.lead.id) fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '');
    const visible = new Set(task ? this.visible(task) : this.archive.tasks);
    // A shared wrapper keeps the private implementation prerequisites needed to compile its checked source.
    for (const node of [...visible]) for (const dependency of this.dependencies(node.task)) visible.add(dependency);
    const hidden = this.archive.tasks.filter(node => !visible.has(node)).flatMap(node => [
      ...(node.task.kind === 'lemma' ? [node.task.theoremName!] : []),
      ...(node.proof?.changes.filter(change => !change.before).map(change => change.name) ?? []),
    ]);
    for (const file of this.input.state.problem.ownedFiles) {
      let source = committedSource(this.lead.worktree, commit, `${this.input.state.problem.projectRelative}/${file}`);
      if (file.endsWith('.lean')) source = omitTaskHelpers(this.input.state.problem, file, source, hidden);
      fs.writeFileSync(path.join(worker.worktree, this.input.state.problem.projectRelative, file), source);
    }
    const seed = commitSolverSources(this.input.state.problem, worker.worktree);
    if (worker.id === this.lead.id && !this.primaryLed) {
      this.archive.leadSeedCommit = seed; this.pin(seed); this.input.save();
    }
    return seed;
  }
  reviewed(check?: ProofCheck) {
    return this.archive.review?.status === 'accepted' && this.archive.review.commit === this.archive.canonicalCommit &&
      (!check || (check.commit === this.archive.review.commit && check.sourceDigest === this.archive.review.sourceDigest)) &&
      this.archive.tasks.filter(node => node.task.statementReview).every(node => this.archive.statementReviews?.some(review =>
        review.taskId === node.task.id && review.taskDigest === digest(node.task) && review.status === 'accepted'));
  }
  requireReview(check: ProofCheck) {
    if (this.primaryLed) {
      this.archive.canonicalCommit = check.commit;
      for (const node of this.archive.tasks) {
        node.task = { ...node.task, status: 'paused' };
        if (node.status === 'running') node.status = 'pending';
      }
      this.archive.planVersion = this.planVersion();
      for (const active of this.active.values()) if (active.action.kind === 'task' && !active.cancelled) {
        active.cancelled = true; void active.interrupt().catch(() => {});
      }
    }
    if (this.archive.review?.commit !== check.commit) {
      this.archive.review = { commit: check.commit, sourceDigest: check.sourceDigest, status: 'pending' };
      this.input.emit('review_requested', { commit: check.commit });
    }
    this.changed();
  }
  contextState(action?: CooperativeAction, worker?: ResearchWorker, versions: TaskVersions = this.taskVersions()): CooperationState {
    const record = worker && this.input.state.workers?.find(item => item.id === worker.id);
    const ordinaryWorker = !action && worker && worker.id !== this.lead.id;
    const task = action?.kind === 'task' ? action.task : ordinaryWorker ?
      this.archive.tasks.find(node => node.status === 'running' && node.assignment?.workerId === worker.id)?.task ??
      this.archive.tasks.find(node => node.task.id === record?.sessionTaskId)?.task : undefined;
    const tasks = task ? this.visible(task) : ordinaryWorker ?
      this.archive.tasks.filter(node => node.task.sharing !== 'group' && ['integrated', 'completed'].includes(node.status)) : this.archive.tasks;
    const visibleIds = new Set(tasks.map(node => node.task.id));
    const visible = (id: string, version: string) => visibleIds.has(id) && versions.get(id)?.version === version;
    const deliveries = this.archive.deliveries?.filter(item => this.deliveryVisible(item, task, versions) &&
      (task || tasks === this.archive.tasks || !item.taskId || versions.get(item.taskId)?.task.sharing !== 'group')) ?? [];
    const deliveryIds = new Set(deliveries.map(item => item.id));
    return { ...this.archive, tasks,
      consumerInterfaces: task ? taskConsumerProjection(task, this.archive.tasks, this.archive.proofRoutes) : undefined,
      researchDecisions: this.archive.researchDecisions?.filter(item => deliveryIds.has(item.deliveryId)),
      frontierRecoveries: tasks === this.archive.tasks ? this.archive.frontierRecoveries : undefined,
      failedTaskInputs: this.archive.failedTaskInputs?.filter(record => tasks === this.archive.tasks || visible(record.taskId, record.taskDigest)),
      progressSnapshot: tasks === this.archive.tasks ? this.archive.progressSnapshot : undefined,
      progressReceipts: tasks === this.archive.tasks ? this.archive.progressReceipts : undefined,
      blockers: this.archive.blockers?.filter(blocker => tasks === this.archive.tasks ||
        (visibleIds.has(blocker.taskId) && task && blocker.groupId === taskGroup(task))),
      proofRoutes: this.archive.proofRoutes?.filter(route => visibleIds.has(route.targetTaskId) &&
        [route.closingTaskId, ...route.prerequisiteTaskIds].every(id => visibleIds.has(id))),
      unchangedResearch: this.archive.unchangedResearch && Object.fromEntries(Object.entries(this.archive.unchangedResearch)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      researchCheckpoints: this.archive.researchCheckpoints && Object.fromEntries(Object.entries(this.archive.researchCheckpoints)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      researchDrafts: this.archive.researchDrafts && Object.fromEntries(Object.entries(this.archive.researchDrafts)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      // Public progress can steer another route before its proof is complete; it remains advisory.
      deliveries,
      history: tasks === this.archive.tasks ? this.archive.history : this.archive.history?.filter(item => visible(item.task.id, digest(item.task))),
      statementReviews: this.archive.statementReviews?.filter(item => item.status !== 'superseded' && visible(item.taskId, item.taskDigest)) };
  }
  statementContext(action: StatementAction): ContextBundle {
    const review = this.archive.statementReviews!.find(review => review.id === action.reviewId)!;
    // The blind hook receives only the formal snapshot, never the intended mathematics or saved translation.
    const visible = action.kind === 'backtranslate' ? { ...review, intendedStatement: '', premises: [], translation: undefined } : review;
    const fixed = this.input.modules.M4.statement(visible, action, this.input.state.problem.receiptDigest);
    if (fixed.scope !== 'fixed-statement' || fixed.sources.problemReceiptDigest !== this.input.state.problem.receiptDigest)
      throw new Error('math_statement_context_invalid');
    return fixed;
  }
  async deliverStatement(worker: ResearchWorker, action: StatementAction): Promise<{ checkWhole: false }> {
    const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
    if (!review) throw new Error('math_statement_review_unknown');
    const kind = action.kind === 'backtranslate' ? 'backtranslation' : 'statement-review';
    const options = { statementReviewId: review.id, taskId: review.taskId, taskDigest: review.taskDigest, statement: review.leanStatement,
      premises: review.premises, dependencies: review.dependencies, commit: review.commit, sourceDigest: review.snapshotDigest };
    if (!this.current(action) || review.workerId !== worker.id) {
      this.record(worker, undefined, kind, 'superseded', 'Statement delivery belongs to a superseded assignment.', options);
      return { checkWhole: false };
    }
    let evidenceRefs: readonly string[] = [];
    try {
      assertStatementSnapshot(review);
      const result = block(review.workspace, action.kind === 'backtranslate' ? 'math-backtranslation' : 'math-statement-review',
        { reviewId: review.id, snapshotDigest: review.snapshotDigest }, action.kind === 'backtranslate' ? 'mathematics' : undefined);
      if (result.reviewId !== review.id || result.snapshotDigest !== review.snapshotDigest) throw new Error('math_statement_review_identity_changed');
      if (action.kind === 'backtranslate') {
        review.translation = readBacktranslation(result); review.status = 'translated';
        review.summary = 'Independent backtranslation saved; mathematical comparison remains pending.';
        evidenceRefs = review.translation.evidenceRefs;
      } else {
        const details = deliveryDetails(result);
        if (!review.translation) throw new Error('math_statement_review_invalid');
        review.status = reviewVerdict(result.verdict, 'math_statement_review_invalid');
        review.summary = details.summary; evidenceRefs = details.evidenceRefs;
      }
    } catch (error) {
      review.status = 'changes_requested'; review.summary = error instanceof Error ? error.message : 'math_statement_review_failed';
    }
    review.workerId = undefined;
    if (review.status === 'accepted') this.lastAssembly = undefined;
    if (review.status === 'changes_requested') { this.archive.error = review.summary; this.needsLead = true; }
    this.record(worker, this.node(review.taskId).task, kind, review.status === 'translated' ? 'advisory' : review.status,
      review.summary ?? '', { ...options, evidenceRefs });
    this.input.emit('statement_review_completed', { workerId: worker.id, taskId: review.taskId, reviewId: review.id, kind, status: review.status });
    return { checkWhole: false };
  }
  async deliver(worker: ResearchWorker, action: CooperativeAction, commit: string, recovering = false,
    recoveryKind: 'checkpoint' | 'request-failure' = 'checkpoint'): Promise<{ check?: ProofCheck; checkWhole: boolean; savedPlan?: boolean }> {
    if (isStatementAction(action)) return this.deliverStatement(worker, action);
    if (action.kind === 'solve') {
      if (!this.current(action)) {
        this.input.emit('research_handoff_superseded', { workerId: worker.id }); return { checkWhole: false };
      }
      if (!recovering && pendingResearchHandoffs(this.archive).some(item => action.handoffIds?.includes(item.id))) {
        await this.readHelpRequest(action);
        if (pendingResearchHandoffs(this.archive).some(item => action.handoffIds?.includes(item.id))) {
          try {
            const response = block(worker.worktree, 'math-help');
            this.recordHandoffDecisions(resolveResearchHandoffs(this.archive, action.handoffIds ?? [],
              this.archive.tasks.map(node => node.task), response.handoffDecisions, action.handoffActivations));
            this.archive.error = undefined; this.changed();
          } catch (error) {
            const reason = error instanceof Error ? error.message : 'invalid response';
            this.archive.error = reason.startsWith('math_handoff_') ? reason : 'math_handoff_decision_invalid: ' + reason;
            this.input.emit('research_handoff_rejected', { reason: this.archive.error }); this.changed();
            return { checkWhole: false };
          }
        }
      }
      return { checkWhole: true };
    }
    if (action.kind === 'review') {
      const review = this.archive.review;
      if (!review || !this.current(action) || review.workerId !== worker.id) {
        this.record(worker, undefined, 'review', 'superseded', 'The reviewed version is no longer current.', { commit: action.seedCommit });
        return { checkWhole: false };
      }
      if (recovering) { this.interrupted(worker, action); return { checkWhole: false }; }
      let evidenceRefs: readonly string[] = [];
      try {
        if (ownedSourceDigest(this.input.state.problem, worker.worktree, commit) !== action.sourceDigest)
          throw new Error('math_review_source_changed');
        const result = block(worker.worktree, 'math-review', { commit: action.seedCommit });
        if (result.commit !== action.seedCommit) throw new Error('math_review_delivery_invalid');
        const status = reviewVerdict(result.verdict, 'math_review_delivery_invalid');
        const details = deliveryDetails(result);
        review.status = status; review.summary = details.summary;
        evidenceRefs = details.evidenceRefs;
        this.input.emit('review_completed', { commit: review.commit, verdict: review.status, workerId: worker.id });
      } catch (error) {
        review.status = 'changes_requested'; review.summary = error instanceof Error ? error.message : 'math_review_failed';
      }
      review.workerId = undefined;
      if (review.status === 'accepted') this.lastAssembly = undefined;
      else { this.archive.error = review.summary; this.needsLead = true; }
      this.record(worker, undefined, 'review', review.status, review.summary ?? '', { commit: review.commit, sourceDigest: review.sourceDigest, evidenceRefs });
      return { checkWhole: false };
    }
    if (action.kind === 'assemble') {
      this.changed();
      return { checkWhole: true };
    }
    if (action.kind !== 'task') {
      if (!this.current(action)) {
        this.input.emit('lead_decision_superseded', { commit }); this.syncPlanNotes(); this.needsLead = true; this.changed();
        return { checkWhole: false };
      }
      if (action.recovery && recovering) {
        this.interrupted(worker, action);
        return { checkWhole: false };
      }
      const sourceChanged = ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
        ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
      let recoveryPlan: ReturnType<typeof parseCooperationPlan> | undefined;
      let resolution: ReturnType<CooperativeResearch['validateRecoveryPlan']> | undefined;
      if (action.recovery) {
        const recovery = this.archive.frontierRecoveries?.find(item => item.id === action.recovery!.id);
        try {
          const response = block(worker.worktree, 'math-plan');
          recoveryPlan = parseCooperationPlan(this.input.state.problem, response);
          resolution = this.validateRecoveryPlan(action, recoveryPlan, response.recovery);
        } catch (error) {
          if (!recovery || recovery.status !== 'requested') {
            this.input.emit('lead_decision_superseded', { commit }); this.needsLead = true; this.changed();
            return { checkWhole: false };
          }
          if (!(error instanceof Error && error.message === 'math_frontier_recovery_no_executable_step')) {
            this.rejectPlan(error);
            if (!this.archive.planRejection?.stalled) { this.changed(); return { checkWhole: false }; }
          }
          resolution = { recovery, taskIds: [], reason: error instanceof Error ? error.message : 'math_frontier_recovery_invalid' };
        }
        if (!resolution.taskIds.length) {
          if (action.handoffIds?.length) {
            try {
              const response = block(worker.worktree, 'math-plan');
              this.recordHandoffDecisions(resolveResearchHandoffs(this.archive, action.handoffIds,
                this.archive.tasks.map(node => node.task), response.handoffDecisions, action.handoffActivations));
            } catch (error) {
              this.rejectPlan(error); this.changed(); return { checkWhole: false };
            }
          }
          resolution.recovery.status = 'awaiting-input'; resolution.recovery.reason = resolution.reason;
          this.archive.planRejection = undefined; this.archive.error = undefined;
          this.archive.lastLeadInputDigest = this.leadEvidence.get(action) === this.planningEvidenceDigest()
            ? this.planningInputDigest() : action.planningInputDigest;
          this.needsLead = false;
          this.archive.planEdited = true; this.syncPlanNotes();
          this.input.emit('frontier_recovery_waiting', { recoveryId: resolution.recovery.id,
            taskIds: resolution.recovery.taskIds, reason: resolution.reason });
          this.changed(); return { checkWhole: false };
        }
      }
      let accepted = false;
      const previousPlanVersion = this.planVersion();
      const previousDecisions = canonicalMathJson(this.archive.researchDecisions ?? []);
      try {
        if (action.handoffIds?.length || retainedResearchHandoffs(this.archive).length) {
          const response = block(worker.worktree, 'math-plan');
          const plan = recoveryPlan ?? parseCooperationPlan(this.input.state.problem, response);
          const decisions = resolveResearchHandoffs(this.archive, action.handoffIds ?? [], plan.tasks, response.handoffDecisions, action.handoffActivations);
          this.preserveHandoffBacklog(plan, decisions);
          await this.acceptPlan(plan);
          this.recordHandoffDecisions(decisions);
        } else await this.acceptPlan(recoveryPlan);
        accepted = true;
      } catch (error) {
        this.rejectPlan(error);
        if (!this.archive.tasks.length && !(recovering && recoveryKind === 'request-failure')) {
          try { await this.startInitialTasks(); }
          catch (fallbackError) { this.input.emit('initial_plan_fallback_failed', {
            reason: fallbackError instanceof Error ? fallbackError.message : 'math_initial_plan_failed' }); }
        }
      }
      const savedPlan = recovering && recoveryKind === 'request-failure' && accepted && (previousPlanVersion !== this.planVersion() ||
        previousDecisions !== canonicalMathJson(this.archive.researchDecisions ?? []));
      if (accepted && resolution) {
        resolution.recovery.status = 'planned'; resolution.recovery.readyTaskIds = resolution.taskIds;
        this.input.emit('frontier_recovery_planned', { recoveryId: resolution.recovery.id,
          taskIds: resolution.recovery.taskIds, readyTaskIds: resolution.taskIds });
        this.changed();
      }
      if (sourceChanged) {
        try {
          this.archive.canonicalCommit = await this.mergeLeadSources(commit, action.seedCommit);
          await this.recheckIntegrated(this.archive.canonicalCommit, true);
          this.archive.canonicalCommit = this.seed(worker, this.archive.canonicalCommit);
          const statements = this.prepareStatementContexts(); if (statements) await statements;
          this.syncStatementReviews();
        } catch (error) {
          this.input.signal.throwIfAborted();
          if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
          this.preserveLeadDraft(commit, action.seedCommit, error instanceof Error ? error.message : 'math_lead_integration_failed');
          this.changed(); return { checkWhole: false, ...(savedPlan ? { savedPlan: true } : {}) };
        }
      }
      if (accepted && !recovering && action.planningInputDigest) this.archive.lastLeadInputDigest =
        this.leadEvidence.get(action) === this.planningEvidenceDigest() ? this.planningInputDigest() : action.planningInputDigest;
      this.changed(); return { checkWhole: sourceChanged, ...(savedPlan ? { savedPlan: true } : {}) };
    }
    const node = this.node(action.task.id);
    if (!this.current(action)) {
      this.record(worker, action.task, advisory(action.task) ? 'research' : 'proof', 'superseded', 'Delivery belongs to a superseded assignment.',
        { taskDigest: action.assignment.taskDigest, premises: action.task.premises ?? [], dependencies: action.assignment.dependencies ?? [], commit });
      this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
      return { checkWhole: false };
    }
    let unchangedNotesBlob: string | undefined;
    let artifacts: DeliveryArtifactManifest | undefined;
    try {
      artifacts = captureDeliveryArtifacts({ problem: this.input.state.problem, worktree: worker.worktree, commit, assignment: action.assignment });
      if (advisory(node.task)) {
        if (recovering) {
          this.preserveResearchDraft(worker, action, commit, artifacts);
          if (recoveryKind === 'request-failure') this.interrupted(worker, action);
          else this.researchCheckpoint(worker, action, commit);
          return { checkWhole: false };
        }
        taskChanges(this.input.state.problem, worker.worktree, commit, node.task, action.assignment);
        const notesBlob = (version: string) => git(worker.worktree, ['ls-tree', '--format=%(objectname)', version, '--', 'RESEARCH.md']);
        const inherited = notesBlob(action.assignment.seedCommit);
        if (inherited === notesBlob(commit)) {
          unchangedNotesBlob = inherited;
          throw new Error('math_research_delivery_unchanged: Replace inherited RESEARCH.md with findings for the current task.');
        }
        const finding = block(worker.worktree, 'math-result', { taskId: node.task.id, conclusion: 'inconclusive' }, 'summary');
        const details = deliveryDetails(finding);
        if (finding?.taskId !== node.task.id || !details.summary.trim() || !['supporting', 'refuted', 'inconclusive'].includes(finding.conclusion))
          throw new Error('math_research_delivery_invalid');
        artifacts = { ...artifacts, reportedChecks: validateDeliveryArtifactClaims(finding, artifacts) };
        const artifactWarning = diagnoseUnbackedLeanClaims(finding, artifacts);
        const lemmaRequests = validateLemmaRequests(this.input.state.problem, this.archive.tasks.map(node => node.task),
          this.archive.groups?.map(route => route.group) ?? [], node.task, finding.lemmaRequests);
        this.reportBlockers(node.task, finding.blockers ?? (finding.conclusion === 'refuted' ? [{
          mechanism: 'reported-local-refutation', scope: 'assigned-local-inference', evidenceRefs: details.evidenceRefs,
        }] : undefined));
        node.finding = JSON.stringify(finding); node.status = 'completed'; node.feedback = undefined;
        if (this.archive.unchangedResearch) delete this.archive.unchangedResearch[node.task.id];
        if (this.archive.researchCheckpoints) delete this.archive.researchCheckpoints[node.task.id];
        if (finding.needsDecision === true || finding.conclusion === 'refuted' || lemmaRequests.length || artifactWarning) this.needsLead = true;
        const remaining = [...new Set([...(details.remainingObligations ?? []),
          ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])];
        this.record(worker, node.task, 'research', !remaining.length && node.task.kind !== 'sketch' ? 'advisory' : 'conditional', details.summary,
          { ...details, remainingObligations: remaining, commit, artifacts, lemmaRequests, findingDigest: mathDigest(node.finding),
            ...(artifactWarning ? { artifactWarning } : {}) });
        this.input.emit('research_delivered', { taskId: node.task.id, conclusion: finding.conclusion });
      } else {
        const proof = await this.publishTaskProof(worker, action, commit,
          'Fixed declaration checked; unresolved lemma assumptions remain obligations.', { artifacts }, recovering);
        return { check: proof, checkWhole: false };
      }
    } catch (error) {
      this.input.signal.throwIfAborted();
      if (!(error instanceof Error) || error.name === 'AbortError' ||
          ['delivered', 'conditional', 'integrated'].includes(node.status) ||
          !(error instanceof SyntaxError) && !directDeliveryRejections.has(rejectionCode(error))) throw error;
      if (!this.current(action)) return { checkWhole: false };
      const feedback = error instanceof Error ? error.message : 'math_task_delivery_failed';
      if (artifacts?.artifacts.length) this.record(worker, node.task, 'progress', 'advisory',
        'Recoverable supporting code retained after an incomplete or rejected delivery; it still requires typed host checking.',
        { commit, artifacts, remainingObligations: [node.task.id] });
      if (recovering && recoveryKind === 'request-failure' && feedback.startsWith('math_task_repeated_failed_input\n') &&
          this.restoreInterruptedRepair(worker, action, commit)) {
        return { checkWhole: false };
      }
      if (recovering && feedback.startsWith('math_task_missing_declaration\n')) {
        this.continueTaskCheckpoint(worker, node, commit);
        node.feedback = feedback; this.interrupted(worker, action); return { checkWhole: false };
      }
      if (/^math_task_(?:missing_declaration|repeated_failed_input)\n/u.test(feedback)) this.rejected(action, feedback, commit);
      else if (recovering) { node.feedback = feedback; this.interrupted(worker, action); }
      else if (unchangedNotesBlob !== undefined) {
        this.reportBlockers(node.task, [{ mechanism: 'unchanged-research-delivery', scope: 'assigned-local-inference' }]);
        const previous = this.archive.unchangedResearch?.[node.task.id];
        const count = previous?.taskDigest === action.assignment.taskDigest && previous.notesBlob === unchangedNotesBlob ? previous.count + 1 : 1;
        (this.archive.unchangedResearch ??= {})[node.task.id] = { taskDigest: action.assignment.taskDigest, notesBlob: unchangedNotesBlob, count };
        this.input.emit('research_delivery_unchanged', { taskId: node.task.id, taskDigest: action.assignment.taskDigest, count, needsDecision: count >= 2 });
        if (count >= 2) this.rejected(action, feedback, commit);
        else { node.feedback = feedback; this.interrupted(worker, action); }
      } else this.rejected(action, feedback, commit);
    }
    return { checkWhole: false };
  }
  interrupted(worker: ResearchWorker, action: CooperativeAction) {
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      if (review && this.current(action) && review.workerId === worker.id) resetStatementReview(review);
    } else if (action.kind === 'task') {
      const node = this.node(action.task.id);
      if (this.current(action) && node.status === 'running' && node.assignment?.workerId === worker.id) node.status = 'pending';
    }
    else if (action.kind === 'review') {
      const review = this.archive.review;
      if (review && this.current(action) && review.workerId === worker.id) { review.status = 'pending'; review.workerId = undefined; }
    }
    else this.needsLead = true;
    this.changed();
  }
  rejected(action: CooperativeAction, feedback: string, commit?: string) {
    if (['task', 'lead', 'review'].includes(action.kind) && !this.current(action)) return;
    let localRepair = false;
    let reviewWorker: ResearchWorker | undefined;
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      if (!review || !this.current(action)) return;
      review.status = 'changes_requested'; review.summary = feedback;
      const worker = this.input.workers.find(item => item.id === review.workerId);
      review.workerId = undefined;
      this.archive.error = feedback; this.needsLead = true;
      if (worker) this.record(worker, this.node(review.taskId).task, 'failure', 'failed', feedback,
        { sourceDigest: review.snapshotDigest, commit: review.commit });
      else this.changed();
      return;
    } else if (action.kind === 'task') {
      const node = this.node(action.task.id); node.status = 'blocked'; node.feedback = feedback;
      if (/^math_task_(?:missing_declaration|repeated_failed_input)\n/u.test(feedback)) {
        const worker = this.input.workers.find(worker => worker.id === action.assignment.workerId);
        if (worker && commit && feedback.startsWith('math_task_missing_declaration\n'))
          this.rememberTaskFailure(this.failedTaskInput(action.task, action.assignment, worker.worktree, commit), feedback);
        localRepair = this.retryTaskLocally(node, commit);
        if (!localRepair) this.settleTaskRepair(node);
      }
    } else if (action.kind === 'review') {
      reviewWorker = this.input.workers.find(item => item.id === this.archive.review!.workerId);
      this.archive.review!.status = 'changes_requested'; this.archive.review!.summary = feedback;
      this.archive.review!.workerId = undefined;
    } else this.archive.error = feedback;
    const worker = action.kind === 'task' ? this.input.workers.find(item => item.id === action.assignment.workerId) :
      action.kind === 'review' ? reviewWorker : this.lead;
    if (!localRepair) this.needsLead = true;
    if (worker) this.record(worker, action.kind === 'task' ? action.task : undefined, 'failure', 'failed', feedback, { commit });
    else this.changed();
  }
  assemblyFailed(check: ProofCheck) { this.archive.error = solverProofFeedback(check); this.needsLead = true; this.changed(); }
  /** A reserved turn may still be refunded; the caller rechecks synchronously after waking. */
  waitForTurn(maxTurns: number): Promise<void> | undefined {
    return this.input.state.turns >= maxTurns && this.reservedTurns.size ? this.wait() : undefined;
  }
  reserveTurn(worker: ResearchWorker) { this.reservedTurns.add(worker.id); }
  settleTurn(worker: ResearchWorker) { if (this.reservedTurns.delete(worker.id)) this.wake(); }
  release(worker: ResearchWorker, action: CooperativeAction) {
    if (action.kind === 'task' && this.current(action)) {
      const node = this.node(action.task.id);
      if (!node.attempts) node.assignment = undefined;
      if (node.status === 'running') node.status = 'pending';
      this.changed();
    } else this.interrupted(worker, action);
  }
  private reviewer(): ResearchWorker | undefined {
    const available = this.livePeers.filter(worker => !this.active.has(worker.id) &&
      !(this.archive.review?.status === 'running' && this.archive.review.workerId === worker.id) &&
      !this.archive.tasks.some(node => node.status === 'running' && node.assignment?.workerId === worker.id) &&
      !this.archive.statementReviews?.some(review => review.workerId === worker.id && ['translating', 'reviewing'].includes(review.status)));
    const selected = this.input.modules.M5.reviewer(available, this.lead.id);
    if (selected && (!available.includes(selected) || selected.role === 'lead')) throw new Error('math_review_assignment_invalid');
    return selected;
  }
  /** Assignments reserve concurrency immediately; charge only when a model turn actually starts. */
  started(worker: ResearchWorker, action: CooperativeAction): boolean {
    if (this.refreshFeasibilityAssignments()) this.changed();
    if (!this.current(action)) return false;
    if (action.kind === 'task' && action.assignment.workerId !== worker.id) throw new Error('math_task_assignment_invalid');
    if (action.kind === 'review' && this.archive.review?.workerId !== worker.id) throw new Error('math_review_assignment_invalid');
    if (isStatementAction(action) && this.archive.statementReviews?.find(item => item.id === action.reviewId)?.workerId !== worker.id)
      throw new Error('math_statement_review_assignment_invalid');
    const task = action.kind === 'task' ? action.task : isStatementAction(action) ? this.node(action.taskId).task : undefined;
    const route = task && this.archive.groups?.find(record => record.group.id === taskGroup(task));
    if (route && (route.group.status !== 'active' || route.turns >= (route.group.maxTurns ?? Infinity))) return false;
    if (route) route.turns++;
    if (action.kind === 'task') {
      const node = this.node(action.task.id);
      for (const record of this.archive.failedTaskInputs ?? []) if (this.pendingTaskRepair(node, record)) {
        record.repair!.pending = false; record.repair!.startedAttempt = node.attempts + 1;
      }
      node.attempts++;
    }
    this.changed(); return true;
  }
  stopped(worker: ResearchWorker, error?: string) {
    this.liveWorkers.delete(worker.id);
    if (this.archive.review?.status === 'running' && this.archive.review.workerId === worker.id) {
      this.archive.review.status = 'pending'; this.archive.review.workerId = undefined;
    }
    for (const review of this.archive.statementReviews ?? [])
      if (review.workerId === worker.id && ['translating', 'reviewing'].includes(review.status)) resetStatementReview(review);
    for (const node of this.archive.tasks.filter(node => node.status === 'running' && node.assignment?.workerId === worker.id)) {
      node.status = 'pending'; node.feedback = error;
      if (error) this.needsLead = true;
    }
    this.changed();
  }
}
