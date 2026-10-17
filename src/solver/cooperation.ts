import { parseCooperationPlan, isAdvisoryTask as advisory } from './tasks';
export { parseCooperationPlan } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, readMathText, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { limitMathOutput } from '../math/mathProcess';
import { hashMathFormalSourceDeclaration } from '../math/leanSource';
import type { LeanStatementContext } from '../math/leanStatementContext';
import { commitSolverSources, committedSource, git, withSolverWorktree, type SolverProblem } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import type { SolverRunState } from './archive';
import type { ResearchWorker } from './modules/organization';
import type { ContextBundle } from './modules/context';
import { proofReceiptsMatch, type ProofCheck } from './modules/evidence';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { researchCanAdvance, routeAllowsTask, taskCanStart, taskDependenciesReady, plannedTaskDependencyIds, selectedTaskRoute } from './modules/search';
import { deliveryDetails, reviewVerdict, readDeliveryLines, readMathResponse as block, MAX_RESEARCH_NOTES_BYTES, type DeliveryRecord } from './deliveries';
import { applyTaskChanges, checkTaskProof, checkTaskProofs, omitTaskHelpers, ownedSourceDigest, projectTaskSources, taskChanges, type TaskProof } from './cooperativeProof';
import { assertStatementSnapshot, captureStatementContexts, isStatementAction, readBacktranslation, resetStatementReview, statementReviewSummary, statementSnapshot, writeStatementSnapshot,
  type StatementAction, type StatementReview } from './statementReview';
import { captureProofReferences, proofReferencesUnchanged, type ProofReferences } from './proofReferences';
import { buildProofContinuation } from './progress';
import { captureDeliveryArtifacts, diagnoseUnbackedLeanClaims, validateDeliveryArtifactClaims, type DeliveryArtifactManifest } from './deliveryArtifacts';
import { validateLemmaRequests } from './taskProposals';
import { recordRouteBlockers, refreshRouteBlockers, validateBlockerProposals, type RouteBlocker } from './routeControl';
import { parseProofRoutes, type ProofRoute } from './proofRoutes';
import { captureObligationSnapshot, diffObligationProgress, type ObligationSnapshot, type ObligationProgressReceipt } from './obligationProgress';

import { taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile, markTaskReferences, hasTaskReferences, markTaskAcceptance, invalidatedTaskIds,
  type CooperativeTask, type RouteGroup, type RouteRecord, type TaskAssignment, type TaskRecord, type CooperativeAction } from './tasks';
export { taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile } from './tasks';
export type { CooperativeTask, RouteGroup, RouteRecord, TaskAssignment, TaskRecord, CooperativeAction } from './tasks';
const digest = taskVersion;

export type ReviewRecord = { commit: string; sourceDigest: string; status: 'pending' | 'running' | 'accepted' | 'changes_requested';
  workerId?: string; summary?: string };
export type HumanEditRecord = { id: string; status: 'received' | 'applied' | 'rejected'; reason?: string;
  receivedAt?: number; appliedAt?: number; baseVersion?: string; planVersion?: string; affectedTasks?: string[];
  recheck?: { status: 'pending' | 'passed' | 'failed' | 'not-required' | 'superseded';
    tasks: { taskId: string; taskDigest: string; status: 'pending' | 'conditional' | 'passed' | 'failed' | 'removed' | 'superseded'; reason?: string;
      lastCheck?: { commit: string; sourceDigest: string; environmentDigest: string; passed: boolean; conditional: boolean; receiptIds: string[] } }[] } };
export type CooperationState = { tasks: TaskRecord[]; groups?: RouteRecord[]; canonicalCommit?: string; review?: ReviewRecord; error?: string;
  history?: { task: CooperativeTask; producer?: string; proof?: TaskProof; integratedCheck?: ProofCheck; finding?: string }[];
  deliveries?: DeliveryRecord[]; cursors?: Record<string, number>; edits?: HumanEditRecord[];
  planVersion?: string; planEdited?: boolean; statementReviews?: StatementReview[];
  helpRequestDigest?: string;
  planRejection?: { proposalDigest: string; inputDigest: string; error: string; stalled: boolean };
  lastLeadInputDigest?: string;
  blockers?: RouteBlocker[];
  proofRoutes?: ProofRoute[];
  progressSnapshot?: ObligationSnapshot;
  progressReceipts?: ObligationProgressReceipt[];
  unchangedResearch?: Record<string, { taskDigest: string; notesBlob: string; count: number }>;
  researchCheckpoints?: Record<string, { taskDigest: string; inputDigest: string; outputDigest: string; count: number;
    paused?: boolean; blockerId?: string }>;
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
  private failedDeliveryChecks = new Map<string, { checker: typeof checkTaskProof; proof: TaskProof }>();
  private timer?: NodeJS.Timeout;
  private failure?: Error;
  private pinned = new Set<string>();
  constructor(private readonly input: { state: SolverRunState; workers: readonly ResearchWorker[];
    access: ReadonlyMap<string, WorkerAccess>; signal: AbortSignal; timeoutMs?: number;
    modelDispatchAllowed?: () => boolean;
    save: () => void; emit: (event: string, details?: Record<string, unknown>) => void;
    modules: SolverModules; exclusiveCheck: <T>(check: () => Promise<T>) => Promise<T> }) {
    this.lead = input.workers[0];
    this.archive = input.state.cooperation ??= { tasks: [] };
    this.archive.proofRoutes = parseProofRoutes(this.archive.proofRoutes, this.archive.tasks.map(node => node.task));
    this.syncProofRoutes();
    this.archive.canonicalCommit ??= git(this.lead.worktree, ['rev-parse', 'HEAD']);
    this.liveWorkers = new Set(input.workers.map(worker => worker.id));
    this.needsLead = !this.archive.tasks.length || Boolean(this.archive.error) ||
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
  private changed(edit?: HumanEditRecord) {
    this.refreshResearchCheckpoints();
    for (const blocker of refreshRouteBlockers(this.archive.blockers ?? [], this.archive.tasks,
      this.input.state.environmentDigest, this.input.state.problem.receiptDigest)) {
      this.needsLead = true;
      this.input.emit('route_reopened', { blockerId: blocker.id, taskId: blocker.taskId, reason: blocker.reopenedReason });
    }
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
      return { id: peer.id, role: work && (work.kind === 'review' || isStatementAction(work)) ? 'reviewer' : peer.role,
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
        peers: this.archive.tasks.map(node => ({ id: node.task.id, groupId: taskGroup(node.task), kind: node.task.kind,
          status: node.status, owner: node.assignment?.workerId ?? node.task.ownerId, dependsOn: node.task.dependsOn,
          ...(visible.has(node) ? { objective: node.task.objective, feedback: node.feedback,
            actualReferences: (node.integratedCheck ?? node.proof)?.references } : {}) })),
        deliveries: deliveries.map(({ evidence: _evidence, ...record }) => record),
        blockers: scoped.blockers ?? [],
        proofRoutes: scoped.proofRoutes ?? [],
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
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      const node = this.node(action.taskId);
      return Boolean(review && review.status === (action.kind === 'backtranslate' ? 'translating' : 'reviewing') &&
        review.taskDigest === action.taskDigest && review.commit === action.seedCommit &&
        review.snapshotDigest === action.snapshotDigest && review.workspace === action.workspace && node &&
        digest(node.task) === action.taskDigest && (node.task.status ?? 'active') === 'active' &&
        this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.status === 'active');
    }
    return action.kind !== 'task' || this.archive.tasks.some(node => node.assignment === action.assignment && digest(node.task) === action.assignment.taskDigest &&
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
      ? source.replace(/```(?:math|math-plan)\s*\n[\s\S]*?\n```/u, plan) : plan + '\n' + bounded(source, 8000));
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
      progress: captureObligationSnapshot(this.archive.tasks, { groups: this.archive.groups,
        environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes, blockers: this.archive.blockers }).digest,
      tasks: this.archive.tasks.map(node => ({ id: node.task.id, status: node.status, feedback: node.feedback })), deliveries }));
  }
  private planningEvidenceDigest() {
    // Plan invalidation can supersede old deliveries, so compare their immutable content.
    return mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      environmentDigest: this.input.state.environmentDigest,
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
  private proposedPlanDigest() {
    try {
      const { tasks, groups, proofRoutes } = block(this.lead.worktree, 'math-plan');
      return mathDigest(canonicalMathJson({ tasks, groups, proofRoutes }));
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
    for (const line of edits.lines) {
      let id = crypto.randomUUID();
      let record: HumanEditRecord | undefined;
      try {
        const edit = JSON.parse(line);
        if (typeof edit.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(edit.id)) throw new Error('math_edit_invalid_id');
        id = edit.id;
        record = this.archive.edits?.find(previous => previous.id === id);
        if (record && record.status !== 'received') continue;
        if (!record) {
          record = { id, status: 'received', receivedAt: Date.now(),
            ...(typeof edit.baseVersion === 'string' ? { baseVersion: bounded(edit.baseVersion, 128) } : {}) };
          (this.archive.edits ??= []).push(record); this.changed();
          this.input.emit('edit_received', { id, baseVersion: record.baseVersion });
        }
        if (edit.baseVersion !== this.archive.planVersion) throw new Error('math_edit_version_conflict');
        await this.input.exclusiveCheck(() => this.acceptPlan(parseCooperationPlan(this.input.state.problem, edit), record));
        for (const [workerId, active] of this.active) {
          if (isStatementAction(active.action)) continue;
          const pending = active.notify(`Human edit ${id} applied at plan version ${this.archive.planVersion}; this does not mean the affected proofs passed. Read the edit's separate recheck results in COOPERATION.json. Superseded assignments must stop; unrelated work continues.`)
            .catch(() => { this.input.emit('notification_deferred', { workerId, editId: id }); });
          this.notifications.add(pending); void pending.finally(() => this.notifications.delete(pending));
        }
        this.input.emit('edit_applied', { id, planVersion: record.planVersion, affectedTasks: record.affectedTasks, recheck: record.recheck });
      } catch (error) {
        const reason = error instanceof Error ? error.message : 'math_edit_invalid';
        if (record?.status === 'applied') throw error;
        if (record) { record.status = 'rejected'; record.reason = reason; }
        else (this.archive.edits ??= []).push({ id, status: 'rejected', reason, receivedAt: Date.now() });
        this.changed();
        this.input.emit('edit_rejected', { id, reason });
      }
    }
    cursors.edits = edits.offset;
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
    if (edits.lines.length) this.input.save();
    return new Map(this.deliveryChecks);
  }
  private async readHelpRequest() {
    if (this.archive.review && this.archive.review.status !== 'changes_requested') return;
    const notes = path.join(this.lead.worktree, 'RESEARCH.md');
    if (!fs.existsSync(notes)) return;
    const fingerprint = mathDigest(readMathText(notes, MAX_RESEARCH_NOTES_BYTES));
    if (fingerprint === this.archive.helpRequestDigest) return;
    this.archive.helpRequestDigest = fingerprint;
    try {
      const { requests } = block(this.lead.worktree, 'math-help');
      if (requests === undefined) return;
      if (!Array.isArray(requests) || requests.length > this.input.workers.length - 1 ||
          requests.some(task => !task || !['lemma', 'research', 'sketch'].includes(task.kind) ||
            task.ownerId === this.lead.id || task.statementReview)) throw new Error('math_help_invalid_requests');
      const goals = this.input.state.problem.targets.map((target, index) => ({
        id: `original_goal_${index + 1}`, kind: 'goal', objective: `Primary solver owns ${target.theoremName}.`,
        theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused',
      }));
      await this.acceptPlan(parseCooperationPlan(this.input.state.problem, { tasks: [...goals, ...requests] }));
      this.input.emit('help_requested', { taskIds: requests.map(task => task.id) });
    } catch (error) {
      const reason = error instanceof Error ? error.message : 'math_help_invalid_requests';
      if (reason.endsWith('_requires_one_block')) return;
      this.archive.error = reason;
      this.input.emit('help_request_rejected', { reason }); this.changed();
    }
  }
  private async readWorkerDeliveries(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, cursors: Record<string, number>) {
    let consumed = false;
    for (const log of [assignmentDeliveryFile(action.assignment), 'DELIVERIES.jsonl']) {
      const scoped = log !== 'DELIVERIES.jsonl', key = scoped ? `${worker.id}/${log}` : worker.id;
      const batch = readDeliveryLines(path.join(worker.worktree, log), cursors[key] ?? 0);
      consumed ||= batch.lines.length > 0;
      for (const line of batch.lines) {
        try { await this.receive(worker, action, JSON.parse(line), scoped); }
        catch (error) {
          if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
          this.input.emit('delivery_rejected', { workerId: worker.id,
            reason: error instanceof Error ? error.message : 'math_delivery_invalid' });
        }
      }
      cursors[key] = batch.offset;
    }
    if (consumed) this.input.save();
  }
  private async receive(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, value: any, scoped = false) {
    if (scoped) value = { id: mathDigest(canonicalMathJson({ file: assignmentDeliveryFile(action.assignment), value })), kind: 'progress', taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, ...value };
    const details = deliveryDetails(value);
    if (!value || typeof value.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(value.id) ||
        !['progress', 'proof'].includes(value.kind) || value.taskId !== action.task.id || value.taskDigest !== action.assignment.taskDigest) throw new Error('math_delivery_invalid');
    if (this.archive.deliveries?.some(record => record.producer === worker.id && record.submissionId === value.id)) return;
    if (!this.current(action)) {
      this.record(worker, action.task, value.kind, 'superseded', details.summary, { ...details, submissionId: value.id,
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
      this.record(worker, node.task, 'progress', remaining.length || node.task.kind === 'sketch' ? 'conditional' : 'advisory', value.summary,
        { ...details, submissionId: value.id, remainingObligations: remaining });
      return;
    }
    if (advisory(node.task) || typeof value.commit !== 'string' || !/^[a-f0-9]{40,64}$/u.test(value.commit)) throw new Error('math_delivery_requires_fixed_proof');
    if (!taskCanStart(node.task, this.archive.tasks)) throw new Error('math_delivery_unfinished_dependencies');
    if (['conditional', 'integrated'].includes(node.status)) return;
    await this.publishTaskProof(worker, action, value.commit, value.summary,
      { submissionId: value.id, evidenceRefs: value.evidenceRefs });
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
  private dependencies(task: CooperativeTask): TaskRecord[] {
    const nodes = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const found = new Set<string>();
    const ids = (node: TaskRecord) => taskReferenceDependencies(node)?.map(reference => reference.taskId) ?? plannedTaskDependencyIds(node, this.archive.tasks);
    const visit = (id: string) => { if (found.has(id)) return; found.add(id); ids(nodes.get(id)!).forEach(visit); };
    const node = nodes.get(task.id);
    (node?.task === task ? ids(node) : task.dependsOn).forEach(visit);
    return [...found].map(id => nodes.get(id)!);
  }
  private async check(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string,
    conditions?: readonly CooperativeTask[], checked?: TaskProof, reuseDeliveryFailure = false) {
    this.input.signal.throwIfAborted();
    const tasks = this.archive.tasks.map(node => ({ ...node }));
    const dependencies = this.dependencies(task), taskDigest = digest(task);
    conditions ??= task.conditional ? dependencies.filter(node => node.task.kind === 'lemma' && node.status !== 'integrated').map(node => node.task) : [];
    const retainedGoals = dependencies.filter(node => node.task.kind === 'goal' && node.status === 'integrated').map(node => node.task.theoremName!);
    const checker = this.input.modules.M2.checkTask ?? checkTaskProof;
    const environment = this.input.access.get(this.lead.id)!.environment;
    const cacheKey = reuseDeliveryFailure ? mathDigest(canonicalMathJson({ worktree, commit, assignment, taskDigest,
      sourceDigest: ownedSourceDigest(this.input.state.problem, worktree, commit), environment,
      timeoutMs: this.input.timeoutMs === Infinity ? 'unlimited' : this.input.timeoutMs,
      environmentDigest: this.input.state.environmentDigest, problemReceiptDigest: this.input.state.problem.receiptDigest,
      conditions: conditions.map(task => ({ taskId: task.id, taskDigest: digest(task) })), retainedGoals,
      dependencies: dependencies.map(node => ({ taskDigest: digest(node.task), status: node.status, proof: node.integratedCheck ?? node.proof })) })) : undefined;
    const cached = cacheKey && this.failedDeliveryChecks.get(cacheKey);
    const reused = cached && cached.checker === checker ? cached.proof : undefined;
    const proof = checked ?? reused ?? await checker(this.input.state.problem, worktree, commit, task, assignment, retainedGoals,
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
      references.tasks = tasks.filter(node => node.task.id !== task.id && this.referencesTask(references, node))
        .map(node => ({ taskId: node.task.id, taskDigest: digest(node.task) }));
      markTaskReferences(proof);
    }
    this.pin(proof.commit); this.pin(proof.verification.targetCommit);
    this.checkedDeliveries.add(proof); markTaskAcceptance(proof);
    if (reused) this.input.emit('task_failure_check_reused', { taskId: task.id, taskDigest, commit });
    else if (cacheKey && !proof.passed && proof.verification.status === 'failed' && proof.verification.targetCommit &&
        proof.verification.results.length && proof.verification.results.every(result => !result.cleanupError &&
          ['failed', 'kernel_verified'].includes(result.status)) && proof.verification.results.some(result => result.status === 'failed' &&
          /^.+\.lean:\d+:\d+:\s*error:/mu.test(`${result.stdoutPreview || ''}\n${result.stderrPreview || ''}`))) {
      this.failedDeliveryChecks.set(cacheKey, { checker, proof });
      if (this.failedDeliveryChecks.size > 64) this.failedDeliveryChecks.delete(this.failedDeliveryChecks.keys().next().value!);
    }
    return proof;
  }
  /** Check isolated sources concurrently; only publishing and canonical integration are serialized. */
  private async publishTaskProof(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, summary: string, options: Partial<DeliveryRecord> = {}, recovering = false) {
    const proof = await this.check(action.task, action.assignment, worker.worktree, commit, undefined, undefined, true);
    return this.input.exclusiveCheck(async () => {
      if (!this.current(action) || !(proof.references?.tasks ?? []).every(reference =>
          this.archive.tasks.some(node => node.task.id === reference.taskId && digest(node.task) === reference.taskDigest))) {
        this.record(worker, action.task, 'proof', 'superseded', 'Assignment changed while its proof was being checked.',
          { ...options, commit, taskDigest: action.assignment.taskDigest, dependencies: action.assignment.dependencies ?? [] });
        this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
        return;
      }
      const node = this.node(action.task.id);
      if (['conditional', 'integrated'].includes(node.status)) return;
      if (recovering && !proof.passed && proof.verification.status === 'failed') {
        node.feedback = solverProofFeedback(proof);
        this.interrupted(worker, action);
        return proof;
      }
      await this.deliverProof(worker, node, proof, summary, options);
      return proof;
    });
  }
  private referencesTask(references: ProofReferences, node: TaskRecord) {
    const declarations = [{ file: node.task.proofPath, name: node.task.theoremName }, ...(node.proof?.changes ?? [])];
    // Fingerprint inputs include the root; only Lean-reported uses establish outward dependencies.
    return [...references.statement, ...references.proof].some(reference =>
      (reference.file !== references.root.file || reference.name !== references.root.name) &&
      declarations.some(declaration => declaration.file === reference.file &&
        declaration.name?.split('.').at(-1) === reference.name.split('.').at(-1)));
  }
  private retryTaskLocally(node: TaskRecord): boolean {
    if (node.attempts !== 1 || !node.assignment || !this.liveWorkers.has(node.assignment.workerId)) return false;
    node.status = 'pending';
    this.input.emit('task_repair_requested', { taskId: node.task.id, workerId: node.assignment.workerId,
      taskDigest: node.assignment.taskDigest });
    return true;
  }
  private async deliverProof(worker: ResearchWorker, node: TaskRecord, proof: TaskProof, summary: string, options: Partial<DeliveryRecord> = {}) {
    node.proof = proof;
    if (['unavailable', 'blocked'].includes(proof.verification.status)) throw new Error('math_verifier_unavailable');
    node.status = proof.passed ? proof.conditions?.length ? 'conditional' : 'delivered' : 'blocked';
    if (!proof.passed) {
      node.feedback = solverProofFeedback(proof);
      const repairable = proof.verification.status === 'failed' && proof.verification.results.some(result =>
        result.status === 'failed' && ((result.sorryCount ?? 0) > 0 || result.error === 'Lean exited with status 1.'));
      if (!repairable || !this.retryTaskLocally(node)) this.needsLead = true;
    }
    this.input.emit('task_checked', { taskId: node.task.id, passed: proof.passed, conditional: Boolean(proof.conditions?.length), commit: proof.commit });
    if (node.status === 'delivered') await this.integrate(node);
    const status = this.node(node.task.id).status;
    this.record(worker, node.task, 'proof', status === 'integrated' ? 'verified' : status === 'conditional' ? 'conditional' : 'failed',
      node.feedback ?? summary, { ...options, commit: proof.commit, sourceDigest: proof.sourceDigest, evidence: proof, actualReferences: proof.references });
    await this.integrateReady();
  }
  private async integrateReady() {
    for (;;) {
      const node = this.archive.tasks.find(item => item.status === 'conditional' && taskDependenciesReady(item.task, this.archive.tasks));
      if (!node) return;
      await this.integrate(node);
      const producer = this.input.workers.find(worker => worker.id === node.assignment!.workerId) ?? this.lead;
      this.record(producer, node.task, 'proof', node.status === 'integrated' ? 'verified' : 'failed',
        node.feedback ?? 'Conditional parent rechecked with proved dependencies and integrated.',
        { commit: node.integratedCheck?.commit ?? node.proof!.commit, sourceDigest: node.integratedCheck?.sourceDigest,
          evidence: node.integratedCheck ?? node.proof, actualReferences: (node.integratedCheck ?? node.proof)?.references });
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
  private prepareStatementContexts(): Promise<void> | undefined {
    if (this.preparingStatements) return this.preparingStatements;
    const tasks = this.archive.tasks.filter(node => node.task.statementReview).map(node => node.task);
    const keys = new Map(tasks.map(task => [task.id, statementSnapshot(this.input.state.problem, task, this.lead.worktree,
      this.archive.canonicalCommit!, this.input.state.environmentDigest, this.dependencies(task).map(dependency =>
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
  async restore() {
    this.syncPlanNotes();
    for (const review of this.archive.statementReviews ?? []) if (review.status !== 'superseded') {
      try { assertStatementSnapshot(review); }
      catch { this.supersedeStatementReview(review); continue; }
      resetStatementReview(review);
    }
    // A resumed review must inspect the fixed version again.
    if (this.archive.review) this.archive.review.status = 'pending';
    if (!this.primaryLed && this.archive.tasks.length && fs.existsSync(path.join(this.lead.worktree, 'RESEARCH.md'))) {
      try { await this.acceptPlan(); } catch (error) { this.rejectPlan(error); }
    }
    if (!solverSourceFeedback(this.input.state.problem, this.lead.worktree)) {
      if (!this.primaryLed && this.archive.canonicalCommit !== git(this.lead.worktree, ['rev-parse', 'HEAD']) &&
          !git(this.lead.worktree, ['diff', 'HEAD', '--name-only', '--', ...this.input.state.problem.ownedFiles.map(file => path.join(this.input.state.problem.projectRelative, file))])) {
        this.seed(this.lead, this.archive.canonicalCommit!);
      }
      if (!this.primaryLed) this.archive.canonicalCommit = commitSolverSources(this.input.state.problem, this.lead.worktree);
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
      const engineerId = group.engineerId;
      if (engineerId && !this.input.workers.some(worker => worker.id === engineerId && worker.role === 'engineer'))
        throw new Error('math_plan_group_engineer_unavailable');
      return { ...group };
    });
    const changedGroups = new Set(configuredGroups.filter(group => {
      const previous = previousGroups.get(group.id)?.group;
      return previous && (previous.objective !== group.objective || previous.revision !== group.revision);
    }).map(group => group.id));
    const current = new Map(this.archive.tasks.map(node => [node.task.id, node]));
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
    const invalidated = invalidatedTaskIds(this.archive.tasks, tasks, changedGroups, dependencies, routeChanges);
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
    const statements = this.prepareStatementContexts(); if (statements) await statements;
    this.syncStatementReviews(invalidated);
    if (edit) {
      edit.status = 'applied'; edit.appliedAt = Date.now();
      edit.affectedTasks = [...new Set([...invalidated, ...tasks.filter(task => !current.has(task.id)).map(task => task.id)])];
      edit.recheck = { status: 'pending', tasks: edit.affectedTasks.filter(id => {
        const task = this.node(id)?.task ?? current.get(id)?.task;
        return task && !advisory(task);
      }).map(id => ({ taskId: id, taskDigest: digest((this.node(id) ?? current.get(id)!).task),
        status: this.node(id) ? 'pending' : 'removed' })) };
      this.archive.planEdited = true;
    }
    this.archive.planVersion = this.planVersion();
    this.input.emit('plan_updated', { groups: this.archive.groups, tasks: tasks.map(task =>
      ({ id: task.id, kind: task.kind, dependsOn: task.dependsOn, groupId: taskGroup(task), sharing: task.sharing ?? 'problem' })), invalidated: [...invalidated] });
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
    try {
      await withSolverWorktree(this.lead.worktree, this.archive.canonicalCommit!, async checkout => {
        // Only archived deliveries need a second delivery check; merged sources always get their own check.
        const submitted = this.checkedDeliveries.has(node.proof!) ? node.proof! :
          await this.check(node.task, node.assignment!, checkout, node.proof!.commit, (node.proof!.conditions ?? []).map(condition => {
            const dependency = this.node(condition.taskId);
            if (!dependency || digest(dependency.task) !== condition.taskDigest) throw new Error('math_task_condition_version_invalid');
            return dependency.task;
          }));
        node.proof = submitted;
        if (['unavailable', 'blocked'].includes(submitted.verification.status)) throw new Error('math_verifier_unavailable');
        if (!submitted.passed) throw new Error('math_task_delivery_no_longer_checks');
        if (!taskDependenciesReady(node.task, this.archive.tasks))
          throw new Error('math_task_dependency_invalidated');
        applyTaskChanges(problem, checkout, submitted.changes, submitted.imports);
        const merged = commitSolverSources(problem, checkout);
        const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: merged };
        const receipt = await this.check(node.task, assignment, checkout, merged);
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.feedback = solverProofFeedback(receipt); throw new Error('math_task_merged_proof_failed'); }
        this.archive.canonicalCommit = merged;
        node.status = 'integrated';
        const statements = this.prepareStatementContexts(); if (statements) await statements;
        this.syncStatementReviews();
        this.input.emit('task_integrated', { taskId: node.task.id, groupId: taskGroup(node.task), sharing: node.task.sharing ?? 'problem', commit: merged });
      });
    } catch (error) {
      node.status = 'blocked'; node.feedback = `${error instanceof Error ? error.message : 'math_task_integration_failed'}\n${node.feedback ?? ''}`;
      this.needsLead = true;
      if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
    } finally { this.changed(); }
  }
  async next(worker: ResearchWorker, budget: { maxTurns: number; remainingMs: number }): Promise<CooperativeAction | undefined> {
    for (;;) {
      this.input.signal.throwIfAborted();
      if (this.failure) throw this.failure;
      this.refreshResearchCheckpoints();
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
            if (!modelAllowed && (this.active.size || this.archive.tasks.some(node => ['running', 'delivered'].includes(node.status)))) {
              await this.wait(); continue;
            }
            return;
          }
          return { kind: 'solve', seedCommit: git(worker.worktree, ['rev-parse', 'HEAD']) };
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
          if (running) { await this.wait(); continue; }
          return;
        }
        if (!running && !this.livePeers.length) return;
        if (this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) { await this.wait(); continue; }
        const rejection = this.archive.planRejection;
        if (rejection?.stalled) {
          if (rejection.inputDigest === this.planningInputDigest() && rejection.proposalDigest === this.proposedPlanDigest()) {
            this.needsLead = false;
            if (!running && !researchCanAdvance(this.archive.tasks, this.archive.groups, this.liveWorkers)) {
              this.input.emit('plan_stalled', { ...rejection }); return;
            }
            await this.wait(); continue;
          }
          this.needsLead = true;
        }
        if (!running && !this.needsLead && this.archive.tasks.length && (!this.archive.review || this.archive.review.status === 'changes_requested') &&
            !researchCanAdvance(this.archive.tasks, this.archive.groups, this.liveWorkers)) {
          // Parking prevents repeating an inference, not reconsidering its unfinished original goal.
          const frontier = this.activeGoalFrontier();
          const inputDigest = this.planningInputDigest();
          const goalIds = [...new Set(frontier.flatMap(item => item.goalIds))];
          if (!frontier.length || inputDigest === this.archive.lastLeadInputDigest) {
            this.input.emit('routes_idle', { groups: this.archive.groups, goalIds, frontier,
              reason: frontier.length ? 'unchanged-mathematical-input' : 'no-active-goal-frontier', inputDigest }); return;
          }
          this.needsLead = true;
          this.input.emit('blocked_tasks_reconsidered', { taskIds: frontier.map(item => item.taskId), goalIds, inputDigest });
        }
        if (this.needsLead || (!running && (!this.livePeers.length ||
            !this.input.modules.M3.ready(this.archive.tasks, this.archive.groups).some(node => this.archive.tasks.includes(node))))) {
          this.needsLead = false;
          const inputDigest = this.planningInputDigest();
          if (inputDigest === this.archive.lastLeadInputDigest && !this.archive.error) {
            if (!running && !this.input.modules.M3.ready(this.archive.tasks, this.archive.groups)
              .some(node => this.archive.tasks.includes(node))) {
              const frontier = this.activeGoalFrontier(), goalIds = [...new Set(frontier.flatMap(item => item.goalIds))];
              this.input.emit('routes_idle', { groups: this.archive.groups, goalIds, frontier,
                reason: frontier.length ? 'unchanged-mathematical-input' : 'no-active-goal-frontier', inputDigest }); return;
            }
            continue;
          }
          this.syncPlanNotes();
          const action: CooperativeAction = { kind: 'lead', seedCommit: this.seed(worker, head), planVersion: this.archive.planVersion, planningInputDigest: inputDigest };
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
          this.input.emit('statement_review_assigned', { workerId: worker.id, taskId: statement.taskId, reviewId: statement.id, kind, role: 'reviewer' });
          this.changed(); return { kind, reviewId: statement.id, taskId: statement.taskId, taskDigest: statement.taskDigest,
            snapshotDigest: statement.snapshotDigest, seedCommit: statement.commit, workspace: statement.workspace };
        }
        if (review?.status === 'pending' && reviewer?.id === worker.id) {
          this.seed(worker, review.commit);
          const notes = path.join(worker.worktree, 'RESEARCH.md');
          if (fs.existsSync(notes)) fs.writeFileSync(notes, fs.readFileSync(notes, 'utf8').replace(/```(?:math|math-review)\s*\n[\s\S]*?\n```/gu, ''));
          review.workerId = worker.id; review.status = 'running';
          this.input.emit('review_assigned', { workerId: worker.id, commit: review.commit, role: 'reviewer' });
          this.changed(); return { kind: 'review', seedCommit: review.commit, sourceDigest: review.sourceDigest };
        }
        const ready = this.input.modules.M3.ready(this.archive.tasks, this.archive.groups);
        const node = this.input.modules.M5.assign(ready, worker,
          this.livePeers, this.archive.groups);
        if (node) {
          const engineerId = node.task.kind === 'goal' && this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId;
          if (!ready.includes(node) || !this.archive.tasks.includes(node) || node.status !== 'pending' ||
              !taskCanStart(node.task, this.archive.tasks) ||
              !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
              (node.task.ownerId && node.task.ownerId !== worker.id) || (engineerId && engineerId !== worker.id) ||
              (node.assignment && node.assignment.workerId !== worker.id)) throw new Error('math_task_assignment_invalid');
          const selectedRoute = selectedTaskRoute(node, this.archive.tasks);
          if (node.assignment && node.alternativeRoutes?.length && node.assignment.routeId !== selectedRoute?.id)
            node.assignment = undefined;
          const seed = this.archive.canonicalCommit!;
          const resuming = node.assignment?.workerId === worker.id;
          let scopedSeed = seed;
          if (!resuming) {
            scopedSeed = this.seed(worker, seed, node.task);
          }
          node.assignment ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id,
            seedCommit: scopedSeed, canonicalCommit: seed, groupId: taskGroup(node.task),
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
    const previousGroup = this.input.state.workers?.find(record => record.id === worker.id)?.sessionGroupId;
    if (task && previousGroup && previousGroup !== taskGroup(task)) fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '');
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
    return commitSolverSources(this.input.state.problem, worker.worktree);
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
    return { ...this.archive, tasks,
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
      // Public progress can steer another route before its proof is complete; it remains advisory.
      deliveries: this.archive.deliveries?.filter(item => this.deliveryVisible(item, task, versions) &&
        (task || tasks === this.archive.tasks || !item.taskId || versions.get(item.taskId)?.task.sharing !== 'group')) ?? [],
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
  async deliver(worker: ResearchWorker, action: CooperativeAction, commit: string, recovering = false): Promise<{ check?: ProofCheck; checkWhole: boolean }> {
    if (isStatementAction(action)) return this.deliverStatement(worker, action);
    if (action.kind === 'solve') return { checkWhole: true };
    if (action.kind === 'review') {
      if (recovering) { this.interrupted(worker, action); return { checkWhole: false }; }
      const review = this.archive.review;
      if (!review || review.commit !== action.seedCommit || review.workerId !== worker.id || review.status !== 'running') {
        this.record(worker, undefined, 'review', 'superseded', 'The reviewed version is no longer current.', { commit: action.seedCommit });
        return { checkWhole: false };
      }
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
      if (action.planVersion !== undefined && action.planVersion !== this.archive.planVersion) {
        this.input.emit('lead_decision_superseded', { commit }); this.syncPlanNotes(); this.needsLead = true; this.changed();
        return { checkWhole: false };
      }
      const sourceChanged = ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
        ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
      let accepted = false;
      try { await this.acceptPlan(); accepted = true; } catch (error) {
        this.rejectPlan(error);
        if (!this.archive.tasks.length) {
          try { await this.startInitialTasks(); }
          catch (fallbackError) { this.input.emit('initial_plan_fallback_failed', {
            reason: fallbackError instanceof Error ? fallbackError.message : 'math_initial_plan_failed' }); }
        }
      }
      if (sourceChanged) {
        try {
          await withSolverWorktree(worker.worktree, this.archive.canonicalCommit!, async checkout => {
            applyTaskChanges(this.input.state.problem, checkout, taskChanges(this.input.state.problem, worker.worktree, commit, undefined, action));
            this.archive.canonicalCommit = commitSolverSources(this.input.state.problem, checkout);
            await this.recheckIntegrated(this.archive.canonicalCommit, true);
            this.archive.canonicalCommit = this.seed(worker, this.archive.canonicalCommit);
            const statements = this.prepareStatementContexts(); if (statements) await statements;
            this.syncStatementReviews();
          });
        } catch (error) {
          this.archive.error = error instanceof Error ? error.message : 'math_lead_integration_failed'; this.needsLead = true;
          this.changed(); return { checkWhole: false };
        }
      }
      if (accepted && !recovering && action.planningInputDigest) this.archive.lastLeadInputDigest =
        this.leadEvidence.get(action) === this.planningEvidenceDigest() ? this.planningInputDigest() : action.planningInputDigest;
      this.changed(); return { checkWhole: sourceChanged };
    }
    const node = this.node(action.task.id);
    if (!this.current(action)) {
      this.record(worker, action.task, advisory(action.task) ? 'research' : 'proof', 'superseded', 'Delivery belongs to a superseded assignment.',
        { taskDigest: action.assignment.taskDigest, premises: action.task.premises ?? [], dependencies: action.assignment.dependencies ?? [], commit });
      this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
      return { checkWhole: false };
    }
    if (['conditional', 'integrated'].includes(node.status)) return { checkWhole: false };
    let unchangedNotesBlob: string | undefined;
    let artifacts: DeliveryArtifactManifest | undefined;
    try {
      artifacts = captureDeliveryArtifacts({ problem: this.input.state.problem, worktree: worker.worktree, commit, assignment: action.assignment });
      if (advisory(node.task)) {
        if (recovering) { this.researchCheckpoint(worker, action, commit); return { checkWhole: false }; }
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
        node.finding = bounded(JSON.stringify(finding), 5000); node.status = 'completed'; node.feedback = undefined;
        if (this.archive.unchangedResearch) delete this.archive.unchangedResearch[node.task.id];
        if (this.archive.researchCheckpoints) delete this.archive.researchCheckpoints[node.task.id];
        if (finding.needsDecision === true || finding.conclusion === 'refuted' || lemmaRequests.length || artifactWarning) this.needsLead = true;
        const remaining = [...new Set([...(details.remainingObligations ?? []),
          ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])];
        this.record(worker, node.task, 'research', !remaining.length && node.task.kind !== 'sketch' ? 'advisory' : 'conditional', details.summary,
          { ...details, remainingObligations: remaining, commit, artifacts, lemmaRequests,
            ...(artifactWarning ? { artifactWarning } : {}) });
        this.input.emit('research_delivered', { taskId: node.task.id, conclusion: finding.conclusion });
      } else {
        const proof = await this.publishTaskProof(worker, action, commit,
          'Fixed declaration checked; unresolved lemma assumptions remain obligations.', { artifacts }, recovering);
        return { check: proof, checkWhole: false };
      }
    } catch (error) {
      if (!this.current(action)) return { checkWhole: false };
      const feedback = error instanceof Error ? error.message : 'math_task_delivery_failed';
      if (artifacts?.artifacts.length) this.record(worker, node.task, 'progress', 'advisory',
        'Recoverable supporting code retained after an incomplete or rejected delivery; it still requires typed host checking.',
        { commit, artifacts, remainingObligations: [node.task.id] });
      if (feedback === 'math_verifier_unavailable') { this.rejected(action, feedback, commit); throw error; }
      if (recovering) { node.feedback = feedback; this.interrupted(worker, action); }
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
      if (review?.commit === action.seedCommit && review.workerId === worker.id) { review.status = 'pending'; review.workerId = undefined; }
    }
    else this.needsLead = true;
    this.changed();
  }
  rejected(action: CooperativeAction, feedback: string, commit?: string) {
    let localRepair = false;
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
      if (feedback.startsWith('math_task_missing_declaration\n')) localRepair = this.retryTaskLocally(node);
    } else if (action.kind === 'review') {
      this.archive.review!.status = 'changes_requested'; this.archive.review!.summary = feedback;
    } else this.archive.error = feedback;
    const worker = action.kind === 'task' ? this.input.workers.find(item => item.id === action.assignment.workerId) : this.lead;
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
    if (!this.current(action)) return false;
    if (action.kind === 'task' && action.assignment.workerId !== worker.id) throw new Error('math_task_assignment_invalid');
    const task = action.kind === 'task' ? action.task : isStatementAction(action) ? this.node(action.taskId).task : undefined;
    const route = task && this.archive.groups?.find(record => record.group.id === taskGroup(task));
    if (route && (route.group.status !== 'active' || route.turns >= (route.group.maxTurns ?? Infinity))) return false;
    if (route) route.turns++;
    if (action.kind === 'task') this.node(action.task.id).attempts++;
    this.changed(); return true;
  }
  stopped(worker: ResearchWorker, error?: string) {
    this.liveWorkers.delete(worker.id);
    if (this.archive.review?.status === 'running' && this.archive.review.workerId === worker.id) this.archive.review.status = 'pending';
    for (const review of this.archive.statementReviews ?? [])
      if (review.workerId === worker.id && ['translating', 'reviewing'].includes(review.status)) resetStatementReview(review);
    for (const node of this.archive.tasks.filter(node => node.status === 'running' && node.assignment?.workerId === worker.id)) {
      node.status = error ? 'blocked' : 'pending'; node.feedback = error;
      if (error) this.needsLead = true;
    }
    this.changed();
  }
}
