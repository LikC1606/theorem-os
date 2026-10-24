import { parseCooperationPlan } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { LeanStatementContext } from '../math/leanStatementContext';
import { commitSolverSources, committedSource, git } from './problem';
import type { DispatchWaitObservation, SolverRunState } from './archive';
import { independentFeasibilityWorker, type ResearchWorker } from './modules/organization';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { originalGoalTaskFocus, originalGoalFrontierSnapshot, plannedTaskDependencyIds } from './modules/search';
import { type DeliveryRecord } from './deliveries';
import { rejectedDeliveryReceipt, deliveryReceiptFeedback, type DeliveryReceipt } from './deliveryReceipts';
import { proofReadyRecord, type ProofReadyRecord } from './proofReady';
import type { ProofCheck } from './modules/evidence';
import { createTaskSourceProjector, isAttributedTaskProof, ownedSourceDigest, TaskProofCache, type TaskProof } from './cooperativeProof';
import { researchSourceTasks, scopedResearchSources } from './researchSources';
import { isStatementAction, statementReviewSummary } from './statementReview';
import { type ProofReferences } from './proofReferences';
import { attributeTaskReferences } from './taskReferenceAttribution';
import { buildProofContinuation } from './progress';
import { recordRouteBlockers, refreshRouteBlockers, validateBlockerProposals } from './routeControl';
import { parseProofRoutes } from './proofRoutes';
import { createProofRoutePriorityIndex } from './routePriority';
import { pendingResearchHandoffs, researchHandoffs, selectResearchHandoffBatch } from './researchHandoffs';
import { pendingResearchChallenges, researchChallenges, selectResearchChallengeBatch } from './researchChallenges';
import { captureObligationSnapshot, diffObligationProgress } from './obligationProgress';
import { bindMathematicalGap, mathematicalGapVisible } from './mathematicalGaps';
import { taskConnectionCheckCurrent } from './taskConnections';
import { TaskTypePreflightCache } from './taskTypePreflight';
import { currentCapacityExploration, plannedTaskRecords } from './capacityExploration';
import { assignmentDeliveryFile, isFeasibilityReview, markTaskAcceptance, markTaskReferences, taskGroup, taskReferenceDependencies, type CooperativeTask, type TaskRecord, type CooperativeAction } from './tasks';
import { digest, ReviewRecord, HumanEditRecord, CooperationState, TaskVersions, RETRY_DISPATCH, bounded } from './cooperationShared';

/** Shared cooperation state, scheduling primitives and the per-worker context projection. */
export abstract class CooperationCore {
  protected readonly lead: ResearchWorker;
  protected readonly archive: CooperationState;
  protected needsLead = false;
  protected lastAssembly?: string;
  private waiters = new Set<() => void>();
  protected reservedTurns = new Set<string>();
  protected liveWorkers: Set<string>;
  protected checkedDeliveries = new WeakSet<TaskProof>();
  protected readonly taskProofCache = new TaskProofCache();
  protected readonly rejectedIntegrationBatches = new Set<string>();
  protected readonly taskTypePreflight = new TaskTypePreflightCache();
  protected preparingTaskTypes = new Map<TaskRecord, {
    workerId: string; controller: AbortController; current: () => boolean; settled: Promise<void>;
  }>();
  protected invalidTaskTypes = new Map<TaskRecord, { canonical: string; environment: string; taskDigest: string;
    dependencies: string; project: string; workerId: string; environmentIdentity?: string }>();
  protected preparedSources?: { identity: string; project: ReturnType<typeof createTaskSourceProjector> };
  protected checkedStatementReferences = new WeakSet<ProofReferences>();
  protected fixedReviewScope?: { review: ReviewRecord; commit: string; sourceDigest: string; environmentDigest: string;
    tasksDigest: string; required: ReadonlyMap<string, string> };
  protected statementContexts = new Map<string, LeanStatementContext>();
  protected preparingStatements?: Promise<void>;
  protected preparingStatementTasks = new Set<string>();
  protected planSynchronization?: Promise<void>;
  protected planSynchronizations = new Set<Promise<void>>();
  protected leadDeliveries = new Set<Promise<unknown>>();
  protected active = new Map<string, { action: CooperativeAction; interrupt: () => Promise<void>; notify: (message: string) => Promise<void>;
    requestReady?: () => Promise<void>; cancelled?: boolean }>();
  private freshProofReady = new WeakMap<CooperativeAction, string>();
  protected notifications = new Set<Promise<void>>();
  private deliveryReceiptNotifications = new Set<string>();
  protected pendingPulse?: Promise<ReadonlyMap<string, Promise<void>>>;
  protected deliveryChecks = new Map<string, Promise<void>>();
  protected proofPublications = new Map<string, Promise<TaskProof | undefined>>();
  protected proofDeliveryChecks = new Set<Promise<void>>();
  protected integrationQueue = Promise.resolve();
  protected leadEvidence = new WeakMap<CooperativeAction, string>();
  protected publishedPlans = new WeakMap<CooperativeAction, { plan: ReturnType<typeof parseCooperationPlan>; version: string; responseDigest: string }>();
  protected checkingTaskInputs = new Map<string, Promise<void>>();
  protected leanSourceDigests = new Map<string, string>();
  protected timer?: NodeJS.Timeout;
  protected stopping = false;
  protected failure?: Error;
  private pinned = new Set<string>();
  // Implemented by later layers; listed here because this layer calls them.
  protected abstract statementReviewAllowed(task: CooperativeTask, dispatch?: boolean): boolean;
  protected abstract syncEditChecks(nodes: ReadonlyMap<string, TaskRecord>, versions: TaskVersions): void;
  protected abstract refreshFeasibilityAssignments(): boolean;
  protected abstract planningInputDigest(): string;
  protected abstract markCapacityRefillAssessed(action: CooperativeAction): void;
  protected abstract leadAssessmentInput(kind: import('./leadAssessment').LeadAssessmentKind):
    { inputDigest: string; evidenceDigest: string } | undefined;
  protected abstract refreshFailedTaskInputs(): boolean;
  protected abstract refreshResearchCheckpoints(): void;
  protected abstract suspendResearchDrafts(worker: ResearchWorker, taskId?: string): void;
  protected abstract planVersion(): string;
  protected abstract canAssemble(commit: string): boolean;
  abstract contextState(action?: CooperativeAction, worker?: ResearchWorker, versions?: TaskVersions): CooperationState;
  constructor(protected readonly input: { state: SolverRunState; workers: readonly ResearchWorker[];
    access: ReadonlyMap<string, WorkerAccess>; signal: AbortSignal; timeoutMs?: number;
    /** Fresh, unconditional continuation checks already verified in this process. */
    freshContinuationChecks?: readonly TaskProof[];
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
      this.archive.leadSeedCommit ??= this.archive.canonicalCommit;
    }
    // Continuation seeding and this cooperation instance share the proof objects.
    // Record only those exact objects that are attached to an integrated task; this
    // keeps the restore path able to reuse a fresh receipt without trusting a
    // deserialized or otherwise unrelated proof value.
    for (const proof of input.freshContinuationChecks ?? []) {
      const node = this.archive.tasks.find(node => node.status === 'integrated' && node.integratedCheck === proof);
      if (!node || !proof.passed || proof.conditions?.length || proof.taskDigest !== digest(node.task) ||
          proof.commit !== this.archive.canonicalCommit || !isAttributedTaskProof(proof) ||
          proof.references && proof.references.environmentDigest !== input.state.environmentDigest) continue;
      if (proof.references) {
        proof.references.tasks = attributeTaskReferences(proof.references, this.archive.tasks);
        markTaskReferences(proof);
      }
      this.checkedDeliveries.add(proof); markTaskAcceptance(proof);
    }
    this.liveWorkers = new Set(input.workers.map(worker => worker.id));
    this.needsLead = !this.archive.tasks.length || Boolean(this.archive.error) ||
      pendingResearchHandoffs(this.archive).length > 0 || pendingResearchChallenges(this.archive).length > 0 ||
      (this.archive.tasks.some(node => node.status === 'blocked') && this.archive.lastLeadInputDigest !== this.planningInputDigest());
  }
  protected get livePeers() { return this.input.workers.filter(worker => worker.id !== this.lead.id && this.liveWorkers.has(worker.id)); }
  protected get allocationPeers() {
    const occupied = new Set([...this.active].filter(([, active]) => active.action.kind !== 'task').map(([id]) => id));
    if (this.archive.review?.status === 'running' && this.archive.review.workerId) occupied.add(this.archive.review.workerId);
    for (const review of this.archive.statementReviews ?? []) if (review.workerId && ['translating', 'reviewing'].includes(review.status))
      occupied.add(review.workerId);
    for (const worker of this.input.state.workers ?? []) if (worker.recovery?.phase === 'cooling-down') occupied.add(worker.id);
    return this.livePeers.filter(worker => !occupied.has(worker.id));
  }
  protected get explorationIdentity() {
    return { environmentDigest: this.input.state.environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest };
  }
  /** The CAS plan belongs to Lead; host advisory capacity is a separate execution overlay. */
  protected plannedTasks() { return plannedTaskRecords(this.archive.tasks); }
  protected refreshCapacityExplorations() {
    let changed = false;
    for (const node of this.archive.tasks) {
      if (!node.capacityExploration || (node.task.status ?? 'active') !== 'active' ||
          currentCapacityExploration(node, this.archive.tasks, this.explorationIdentity)) continue;
      node.task = { ...node.task, status: 'stopped' };
      node.status = 'blocked'; node.feedback = 'math_capacity_exploration_expired: Its frozen target or mathematical inputs are no longer current.';
      for (const record of this.archive.deliveries ?? []) if (record.taskId === node.task.id) record.status = 'superseded';
      const active = node.assignment && this.active.get(node.assignment.workerId);
      if (active?.action.kind === 'task' && active.action.assignment === node.assignment && !active.cancelled) {
        active.cancelled = true; void active.interrupt().catch(() => {});
      }
      this.input.emit('capacity_exploration_expired', { taskId: node.task.id,
        targetTaskId: node.capacityExploration.targetTaskId, inputDigest: node.capacityExploration.inputDigest });
      changed = true;
    }
    return changed;
  }
  protected capacityPlanView(plan: ReturnType<typeof parseCooperationPlan>): TaskRecord[] {
    const existing = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    return plan.tasks.map(task => {
      const previous = existing.get(task.id);
      return { ...(previous && digest(previous.task) === digest(task) ? previous : { status: 'pending' as const, attempts: 0 }),
        task, alternativeRoutes: plan.proofRoutes?.filter(route => route.targetTaskId === task.id) };
    });
  }
  protected includeCapacityExplorations(plan: ReturnType<typeof parseCooperationPlan>) {
    const existing = new Map(this.archive.tasks.map(node => [node.task.id, node]));
    const hostIds = new Set(this.archive.tasks.filter(node => node.capacityExploration).map(node => node.task.id));
    for (const task of plan.tasks) {
      const previous = existing.get(task.id);
      if (previous?.capacityExploration) {
        if (digest(task) !== digest(previous.task) || task.ownerId !== previous.capacityExploration.workerId)
          throw new Error('math_plan_host_exploration_changed: create a separate typed task for an adopted interface.');
      } else if (task.dependsOn.some(id => hostIds.has(id)))
        throw new Error('math_plan_host_exploration_dependency: use the actual typed inputs, not advisory exploration IDs.');
    }
    const proposed = this.capacityPlanView(plan);
    plan.tasks = plan.tasks.filter(task => {
      const previous = existing.get(task.id);
      return !previous?.capacityExploration || digest(previous.task) !== digest(task) ||
        currentCapacityExploration({ ...previous, task }, proposed, this.explorationIdentity);
    });
    const ids = new Set(plan.tasks.map(task => task.id));
    for (const node of this.archive.tasks) if (node.capacityExploration && !ids.has(node.task.id) &&
        plan.groups.some(group => group.id === taskGroup(node.task)) &&
        currentCapacityExploration(node, proposed, this.explorationIdentity)) {
      plan.tasks.push(node.task); ids.add(node.task.id);
    }
    return plan;
  }
  /** Preview expiry for inbox validation; rejected plans must leave the live archive untouched. */
  protected advisoryArchiveForPlan(plan: ReturnType<typeof parseCooperationPlan>) {
    const proposed = new Map(plan.tasks.map(task => [task.id, digest(task)]));
    const retired = new Set(this.archive.tasks.filter(node => node.capacityExploration &&
      proposed.get(node.task.id) !== digest(node.task)).map(node => node.task.id));
    return retired.size ? { ...this.archive, deliveries: this.archive.deliveries?.map(record =>
      record.taskId && retired.has(record.taskId) ? { ...record, status: 'superseded' as const } : record) } : this.archive;
  }
  protected syncProofRoutes() {
    for (const node of this.archive.tasks) node.alternativeRoutes = this.archive.proofRoutes?.filter(route => route.targetTaskId === node.task.id);
  }
  protected recordDispatchWait(worker: ResearchWorker,
    observation: Omit<DispatchWaitObservation, 'observedAt' | 'endedAt' | 'planVersion'>) {
    const record = this.input.state.workers?.find(item => item.id === worker.id);
    if (!record) return;
    const basis = { ...observation, planVersion: this.archive.planVersion ?? this.planVersion() };
    const previous = record.scheduling?.wait;
    if (previous) {
      const { observedAt: _at, endedAt, ...prior } = previous;
      if (endedAt === undefined && canonicalMathJson(prior) === canonicalMathJson(basis)) return;
      this.clearDispatchWait(worker, 'changed');
    }
    const wait: DispatchWaitObservation = { ...basis, observedAt: Date.now() };
    record.scheduling ??= { status: 'idle', since: wait.observedAt };
    record.scheduling.wait = wait;
    this.input.emit('dispatch_wait', { workerId: worker.id, ...wait });
    this.changed();
  }
  protected clearDispatchWait(worker: ResearchWorker, reason: 'changed' | 'selected' | 'stopped') {
    const scheduling = this.input.state.workers?.find(item => item.id === worker.id)?.scheduling;
    if (!scheduling?.wait) return;
    const wait = scheduling.wait;
    if (reason !== 'stopped') delete scheduling.wait;
    if (wait.endedAt !== undefined) return;
    wait.endedAt = Date.now();
    this.input.emit('dispatch_wait_ended', { workerId: worker.id, observedAt: wait.observedAt,
      endedAt: wait.endedAt, planVersion: wait.planVersion, stage: wait.stage, reason });
  }
  protected changed(edit?: HumanEditRecord) {
    this.refreshCapacityExplorations();
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
    // A new inbox can supersede an assessment-only Lead without publishing a plan.
    // Reclaim its running turn as well as rejecting stale decisions.
    const lead = this.active.get(this.lead.id);
    if (lead?.action.kind === 'lead' && !lead.cancelled && !this.current(lead.action)) {
      lead.cancelled = true; void lead.interrupt().catch(() => {});
    }
    const agents = this.input.workers.map(peer => {
      const active = this.active.get(peer.id), work = active?.action;
      const preparation = [...this.preparingTaskTypes].find(([, item]) => item.workerId === peer.id)?.[0];
      const status = !this.liveWorkers.has(peer.id) ? 'stopped' as const
        : active && (active.cancelled || !this.current(active.action)) ? 'stopping' as const
        : work ? 'working' as const : preparation ? 'preparing' as const : 'idle' as const;
      const action = work?.kind ?? (preparation ? 'task' : undefined);
      const taskId = work?.kind === 'task' ? work.task.id : preparation?.task.id;
      const record = this.input.state.workers?.find(worker => worker.id === peer.id);
      if (record) {
        if (work || preparation) this.clearDispatchWait(peer, 'selected');
        const previous = record.scheduling;
        const same = previous?.status === status && previous.action === action && previous.taskId === taskId;
        record.scheduling = { status, action, taskId, since: same ? previous.since : Date.now(), wait: previous?.wait };
      }
      return { id: peer.id, role: work && (work.kind === 'review' || isStatementAction(work) ||
        work.kind === 'task' && isFeasibilityReview(work.task)) ? 'reviewer' : peer.role,
        status,
        work: work && { kind: work.kind, taskId: work.kind === 'task' ? work.task.id : undefined,
          version: work.kind === 'task' ? work.assignment.taskDigest : work.seedCommit } };
    });
    this.input.save();
    for (const worker of this.input.workers) {
      const action = this.active.get(worker.id)?.action;
      const scoped = this.contextState(action, worker, versions);
      const visible = new Set(scoped.tasks.map(node => node.task.id));
      const deliveries = (scoped.deliveries ?? []).slice(-16);
      const handoffs = researchHandoffs(scoped);
      writeMathJsonDurable(path.join(worker.worktree, 'COOPERATION.json'), {
        planVersion: this.archive.planVersion,
        edits: (this.archive.edits ?? []).slice(-16),
        agents,
        dispatchWaits: (this.input.state.workers ?? []).flatMap(peer => {
          const wait = peer.scheduling?.wait;
          if (!wait) return [];
          const candidates = wait.candidates.filter(item => visible.has(item.taskId));
          return [{ workerId: peer.id, ...wait, candidates,
            omittedCandidates: wait.omittedCandidates + wait.candidates.length - candidates.length }];
        }),
        ...(worker.id === this.lead.id && scoped.lastCapacityRefill ? { lastCapacityRefill: scoped.lastCapacityRefill } : {}),
        ...(worker.id === this.lead.id && scoped.lastStagnationRecovery ? { lastStagnationRecovery: scoped.lastStagnationRecovery } : {}),
        capacityExplorations: scoped.tasks.filter(node => node.capacityExploration).map(node => ({
          taskId: node.task.id, status: node.status, ...node.capacityExploration })),
        parallelQuestions: scoped.parallelQuestions ?? [],
        peers: this.archive.tasks.map(node => ({ id: node.task.id, taskDigest: digest(node.task),
          objectiveDigest: mathDigest(node.task.objective), groupId: taskGroup(node.task), kind: node.task.kind,
          status: node.status, owner: node.assignment?.workerId ?? node.task.ownerId, dependsOn: node.task.dependsOn,
          ...(visible.has(node.task.id) ? { objective: node.task.objective, feedback: node.feedback,
            actualReferences: (node.integratedCheck ?? node.proof)?.references } : {}) })),
        deliveries: deliveries.map(({ evidence: _evidence, researchRecord: _researchRecord, ...record }) => record),
        deliveryReceipts: scoped.deliveryReceipts ?? [],
        proofReadyRecords: scoped.proofReadyRecords ?? [],
        researchHandoffs: handoffs,
        researchChallenges: researchChallenges(scoped),
        mathematicalGaps: scoped.mathematicalGaps ?? [],
        blockers: scoped.blockers ?? [],
        proofRoutes: scoped.proofRoutes ?? [],
        routePriority: createProofRoutePriorityIndex(scoped.tasks, { groups: scoped.groups,
          environmentDigest: this.input.state.environmentDigest, proofRoutes: scoped.proofRoutes }),
        frontierFocus: originalGoalFrontierSnapshot(originalGoalTaskFocus(scoped.tasks, scoped.groups, this.input.state.environmentDigest)),
        frontierRecoveries: scoped.frontierRecoveries ?? [],
        mathematicalChanges: scoped.progressReceipts?.slice(-16) ?? [],
        continuation: buildProofContinuation(scoped.tasks, { groups: scoped.groups, environmentDigest: this.input.state.environmentDigest,
          proofRoutes: scoped.proofRoutes, researchHandoffs: handoffs }),
        statements: (scoped.statementReviews ?? []).map(statementReviewSummary),
      });
    }
    this.wake();
  }
  protected cancelStaleTaskTypes() {
    for (const pending of this.preparingTaskTypes.values())
      if (!pending.controller.signal.aborted && !pending.current()) pending.controller.abort();
  }
  protected wake() {
    this.cancelStaleTaskTypes();
    for (const wake of this.waiters) wake();
    this.waiters.clear();
  }
  modelBudgetChanged() { this.wake(); }
  protected rejectWorkerDelivery(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    submission: string, error: Error): DeliveryReceipt {
    const receipt = rejectedDeliveryReceipt({ assignment: action.assignment, workerId: worker.id,
      environmentDigest: this.input.state.environmentDigest, submission, error, now: Date.now(),
      receipts: this.archive.deliveryReceipts });
    const receipts = this.archive.deliveryReceipts ??= [];
    const previous = receipts.find(item => item.id === receipt.id);
    if (previous) return previous;
    receipts.push(receipt);
    const node = this.node(action.task.id);
    if (this.current(action) && node) node.feedback = deliveryReceiptFeedback(receipt);
    return receipt;
  }
  protected async notifyDeliveryReceipts(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>) {
    const active = this.active?.get(worker.id);
    if (!active || active.action !== action || !this.current(action)) return;
    const notified = this.deliveryReceiptNotifications ??= new Set();
    for (const receipt of this.archive.deliveryReceipts ?? []) {
      if (receipt.status !== 'needs-correction' || receipt.workerId !== worker.id || receipt.assignmentKey !== assignmentDeliveryFile(action.assignment) ||
          receipt.environmentDigest !== this.input.state.environmentDigest || notified.has(receipt.id)) continue;
      try { await active.notify(deliveryReceiptFeedback(receipt)); notified.add(receipt.id); }
      catch { this.input.emit('delivery_receipt_notification_deferred', { workerId: worker.id, receiptId: receipt.id }); }
    }
  }
  protected resolveDeliveryReceipts(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    replacesReceipt?: unknown, complete = false) {
    const scoped = (this.archive.deliveryReceipts ?? []).filter(receipt => receipt.workerId === worker.id &&
      receipt.assignmentKey === assignmentDeliveryFile(action.assignment) && receipt.taskId === action.assignment.taskId &&
      receipt.taskDigest === action.assignment.taskDigest && receipt.seedCommit === action.assignment.seedCommit &&
      receipt.environmentDigest === this.input.state.environmentDigest);
    const byId = new Map(scoped.map(receipt => [receipt.id, receipt]));
    const replaced = new Set<string>();
    let id = typeof replacesReceipt === 'string' ? replacesReceipt : undefined;
    while (id && !replaced.has(id)) {
      const receipt = byId.get(id);
      if (!receipt || receipt.status === 'superseded') break;
      replaced.add(id); id = receipt.replacesReceipt;
    }
    for (const receipt of scoped) {
      if (receipt.status !== 'needs-correction' || !complete && !replaced.has(receipt.id)) continue;
      receipt.status = 'recorded';
      const node = this.node(action.task.id);
      if (node.feedback === deliveryReceiptFeedback({ ...receipt, status: 'needs-correction' }))
        node.feedback = undefined;
    }
    const pending = this.archive.deliveryReceipts?.findLast(receipt => receipt.status === 'needs-correction' &&
      receipt.workerId === worker.id && receipt.assignmentKey === assignmentDeliveryFile(action.assignment) &&
      receipt.environmentDigest === this.input.state.environmentDigest);
    const node = this.node(action.task.id);
    if (pending && !node.feedback) node.feedback = deliveryReceiptFeedback(pending);
  }
  protected receiveProofReady(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, submissionId: string) {
    const created = proofReadyRecord({ assignment: action.assignment, workerId: worker.id, submissionId,
      problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest, now: Date.now() });
    const records = this.archive.proofReadyRecords ??= [];
    let record = records.find(item => item.id === created.id);
    if (record && ['checked', 'failed', 'superseded'].includes(record.status)) return;
    if (!record) { records.push(created); record = created; }
    if (!this.current(action) || worker.id !== action.assignment.workerId) {
      record.status = 'superseded'; record.reason = 'Assignment changed before readiness intake.'; this.changed(); return;
    }
    const fresh = this.freshProofReady.get(action) === record.id;
    for (const other of records) if (other !== record && other.assignmentKey === record.assignmentKey &&
        other.workerId === worker.id && other.status === 'awaiting-freeze') {
      other.status = 'superseded'; other.reason = 'A later readiness event replaced this request.';
    }
    // Only a newly consumed event can grant this process permission to freeze a live workspace.
    this.freshProofReady.set(action, record.id);
    this.changed();
    const active = this.active.get(worker.id);
    if (!fresh && record.status === 'awaiting-freeze' && active?.action === action && active.requestReady) {
      const pending = active.requestReady().catch(() => {
        this.input.emit('proof_ready_notification_deferred', { workerId: worker.id, receiptId: record!.id });
      });
      this.notifications.add(pending); void pending.finally(() => this.notifications.delete(pending));
    }
  }
  private proofReadyCurrent(record: ProofReadyRecord, worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>) {
    return record.workerId === worker.id && worker.id === action.assignment.workerId &&
      record.assignmentKey === assignmentDeliveryFile(action.assignment) && record.taskId === action.task.id &&
      record.taskDigest === action.assignment.taskDigest && record.seedCommit === action.assignment.seedCommit &&
      record.problemReceiptDigest === this.input.state.problem.receiptDigest &&
      record.environmentDigest === this.input.state.environmentDigest && this.current(action);
  }
  pendingProofReady(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>): ProofReadyRecord | undefined {
    const records = (this.archive.proofReadyRecords ?? []).filter(record => record.workerId === worker.id &&
      record.assignmentKey === assignmentDeliveryFile(action.assignment) && ['awaiting-freeze', 'frozen'].includes(record.status));
    let changed = false;
    for (const record of records) if (!this.proofReadyCurrent(record, worker, action)) {
      record.status = 'superseded'; record.reason = 'Assignment or frozen input identity changed.'; changed = true;
    }
    if (changed) this.changed();
    return records.findLast(record => record.status === 'frozen' || record.status === 'awaiting-freeze' &&
      this.freshProofReady.get(action) === record.id);
  }
  proofReadyFrozen(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string): ProofReadyRecord | undefined {
    const record = this.pendingProofReady(worker, action);
    if (!record) return;
    if (record.snapshotCommit) {
      if (record.snapshotCommit !== commit) throw new Error('math_proof_ready_snapshot_changed');
      return record;
    }
    // Callers stop the writer first. Every read here addresses the host's immutable commit.
    const sourceDigest = ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
    this.pin(commit);
    Object.assign(record, { status: 'frozen', snapshotCommit: commit, sourceDigest, frozenAt: Date.now() });
    this.changed();
    this.input.emit('proof_ready_frozen', { readyId: record.id, taskId: record.taskId, taskDigest: record.taskDigest,
      workerId: record.workerId, assignmentKey: record.assignmentKey, seedCommit: record.seedCommit,
      commit, snapshotCommit: commit, sourceDigest, frozenAt: record.frozenAt });
    return record;
  }
  proofReadyCompleted(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    proof?: ProofCheck & { conditions?: TaskProof['conditions'] }, reason?: string): void {
    const record = this.pendingProofReady(worker, action);
    if (!record) return;
    if (!proof || !proof.passed) {
      record.status = 'failed'; record.reason = reason ?? 'The fixed declaration did not pass independent checking.';
    } else {
      if (record.status !== 'frozen' || proof.commit !== record.snapshotCommit || proof.sourceDigest !== record.sourceDigest ||
          !this.checkedDeliveries.has(proof as TaskProof) || !proof.verification.results.length)
        throw new Error('math_proof_ready_check_identity_changed');
      Object.assign(record, { status: 'checked', evidence: proof.conditions?.length ? 'conditional' : 'unconditional',
        conditions: proof.conditions ? [...proof.conditions] : [], receiptIds: proof.verification.results.map(result => result.receiptId) });
      delete record.reason;
    }
    this.freshProofReady.delete(action); this.changed();
  }
  proofReadyFailedFreeze(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, reason: string): void {
    const record = this.pendingProofReady(worker, action);
    if (!record || record.snapshotCommit) return;
    record.status = 'failed'; record.reason = 'Freeze unconfirmed: ' + reason;
    this.freshProofReady.delete(action); this.changed();
  }
  activate(worker: ResearchWorker, action: CooperativeAction, interrupt: () => Promise<void>, notify: (message: string) => Promise<void>,
    requestReady?: () => Promise<void>) {
    this.active.set(worker.id, { action, interrupt, notify, requestReady }); this.changed();
  }
  deactivate(worker: ResearchWorker) { this.active.delete(worker.id); this.changed(); }
  current(action: CooperativeAction) {
    if (action.kind === 'assemble') return !this.failure && !this.stopping && this.liveWorkers.has(this.lead.id) && this.canAssemble(action.seedCommit);
    if (action.kind === 'lead' && (action.planNonce || action.initialPlanNonce) && !this.leadEvidence.has(action)) return false;
    if (action.kind === 'lead' && action.coordination && !action.handoffIds?.length && !action.challengeIds?.length &&
        !this.publishedPlans.has(action) && (pendingResearchHandoffs(this.archive).length || pendingResearchChallenges(this.archive).length))
      return false; // An assessment-only dispatch must yield to newly arrived inbox work before consuming another turn.
    if (action.kind === 'lead' && action.handoffActivations) {
      const pending = new Map(pendingResearchHandoffs(this.archive).flatMap(item =>
        item.sources.map(source => [source.handoffId, item.activationDigest] as const)));
      if (action.handoffIds?.some(id => pending.has(id) && pending.get(id) !== action.handoffActivations![id])) return false;
    }
    if (action.kind === 'lead' && action.challengeActivations) {
      const pending = new Map(pendingResearchChallenges(this.archive).map(item => [item.id, item.activationDigest]));
      if (action.challengeIds?.some(id => pending.has(id) && pending.get(id) !== action.challengeActivations![id])) return false;
    }
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      const node = this.node(action.taskId);
      return Boolean(review && review.status === (action.kind === 'backtranslate' ? 'translating' : 'reviewing') &&
        review.assignmentId === action.assignmentId &&
        review.taskDigest === action.taskDigest && review.commit === action.seedCommit &&
        review.snapshotDigest === action.snapshotDigest && review.workspace === action.workspace && node &&
        digest(node.task) === action.taskDigest && this.statementReviewAllowed(node.task));
    }
    if (action.kind === 'lead') {
      const version = this.publishedPlans.get(action)?.version ?? action.planVersion;
      return version === undefined || version === this.archive.planVersion;
    }
    if (action.kind === 'review') {
      const review = this.archive.review;
      return Boolean(review && review.status === 'running' && review.commit === action.seedCommit &&
        review.sourceDigest === action.sourceDigest && review.assignmentId === action.assignmentId);
    }
    return action.kind !== 'task' || this.archive.tasks.some(node => node.assignment === action.assignment && digest(node.task) === action.assignment.taskDigest &&
      (!node.capacityExploration || currentCapacityExploration(node, this.archive.tasks, this.explorationIdentity)) &&
      (!action.assignment.connectionCheck || taskReferenceDependencies(node) || taskConnectionCheckCurrent(node.task,
        action.assignment, this.archive.tasks, { environmentDigest: this.input.state.environmentDigest,
          problemReceiptDigest: this.input.state.problem.receiptDigest })) &&
      (!isFeasibilityReview(node.task) || this.input.workers.some(worker => worker.id === action.assignment.workerId &&
        independentFeasibilityWorker(node, worker, this.archive.tasks, this.archive.groups))) &&
      (taskReferenceDependencies(node) ?? action.assignment.dependencies ?? []).every(dependency => this.archive.tasks.some(item => item.task.id === dependency.taskId && digest(item.task) === dependency.taskDigest)) &&
      (node.task.status ?? 'active') === 'active' && this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.status === 'active');
  }
  protected taskVersions() {
    return new Map(this.archive.tasks.map(({ task }) => [task.id, { task, version: digest(task) }]));
  }
  protected deliveryVisible(record: DeliveryRecord, task: CooperativeTask | undefined, versions: TaskVersions, gapViewer = task) {
    if (record.status === 'superseded') return false;
    if (!mathematicalGapVisible(record, this.archive, gapViewer)) return false;
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
    this.input.emit('delivery_published', { deliveryId: record.id, producer: record.producer, workerId: record.producer,
      taskId: record.taskId, taskDigest: record.taskDigest, assignmentKey: record.assignmentKey,
      commit: record.commit, sourceDigest: record.sourceDigest,
      receiptIds: record.evidence?.verification.results.map(result => result.receiptId),
      kind: record.kind, status: record.status });
  }
  protected pin(commit?: string) {
    if (!commit || this.pinned.has(commit)) return;
    if (!/^[a-f0-9]{40,64}$/u.test(commit)) throw new Error('math_delivery_invalid_commit');
    git(this.lead.worktree, ['update-ref', `refs/math/${this.input.state.runId}/evidence/${commit}`, commit]);
    this.pinned.add(commit);
  }
  protected record(worker: ResearchWorker, task: CooperativeTask | undefined, kind: DeliveryRecord['kind'], status: DeliveryRecord['status'],
    summary: string, options: Partial<DeliveryRecord> = {}) {
    const record = this.createDeliveryRecord(worker, task, kind, status, summary, options);
    (this.archive.deliveries ??= []).push(record);
    this.publishDeliveryRecord(record);
    return record;
  }
  protected createDeliveryRecord(worker: ResearchWorker, task: CooperativeTask | undefined, kind: DeliveryRecord['kind'], status: DeliveryRecord['status'],
    summary: string, options: Partial<DeliveryRecord> = {}): DeliveryRecord {
    if (options.mathematicalGap && task) options = { ...options, mathematicalGapScope: bindMathematicalGap(options.mathematicalGap, task,
      this.archive, { problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest }) };
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
    this.pin(record.commit); this.pin(record.artifacts?.commit); this.pin(record.evidence?.verification.targetCommit);
    return record;
  }
  protected publishDeliveryRecord(record: DeliveryRecord) {
    this.changed();
    if (record.status !== 'superseded') this.inform(record);
  }
  protected reportBlockers(task: CooperativeTask, value: unknown) {
    const proposals = validateBlockerProposals(value, task, this.archive.tasks);
    for (const blocker of recordRouteBlockers(this.archive.blockers ??= [], proposals, task, this.archive.tasks,
      this.input.state.environmentDigest, this.input.state.problem.receiptDigest)) {
      this.needsLead = true;
      this.input.emit(blocker.status === 'parked' ? 'route_parked' : 'route_blocker_recorded', {
        blockerId: blocker.id, taskId: blocker.taskId, groupId: blocker.groupId, count: blocker.count,
        scope: blocker.scope, evidenceStatus: blocker.evidenceStatus, reopenOn: blocker.reopenOn });
    }
  }
  protected async wait() {
    const signal = this.input.signal; signal.throwIfAborted();
    await new Promise<void>(resolve => {
      const wake = () => { signal.removeEventListener('abort', wake); this.waiters.delete(wake); resolve(); };
      this.waiters.add(wake); signal.addEventListener('abort', wake, { once: true });
    });
    signal.throwIfAborted();
  }
  protected node(id: string) { return this.archive.tasks.find(node => node.task.id === id)!; }
  protected dependencies(task: CooperativeTask, tasks: readonly TaskRecord[] = this.archive.tasks): TaskRecord[] {
    const nodes = new Map(tasks.map(node => [node.task.id, node]));
    const found = new Set<string>();
    const ids = (node: TaskRecord) => taskReferenceDependencies(node)?.map(reference => reference.taskId) ?? plannedTaskDependencyIds(node, tasks);
    const visit = (id: string) => { if (found.has(id)) return; found.add(id); ids(nodes.get(id)!).forEach(visit); };
    const node = nodes.get(task.id);
    (node?.task === task ? ids(node) : task.dependsOn).forEach(visit);
    return [...found].map(id => nodes.get(id)!);
  }
  protected synchronizationBlocked(task: CooperativeTask): boolean {
    return [this.node(task.id), ...this.dependencies(task)].some(node => node &&
      (node.pendingValidation || this.preparingStatementTasks.has(node.task.id)));
  }
  protected async waitForDispatch(): Promise<typeof RETRY_DISPATCH> {
    await this.wait();
    return RETRY_DISPATCH;
  }
  protected handoffDispatch(batch = selectResearchHandoffBatch(this.archive),
    limits?: { maxItems?: number; maxBytes?: number }) {
    const challenges = selectResearchChallengeBatch(this.archive, limits);
    return { handoffIds: batch.map(item => item.id),
      handoffActivations: Object.fromEntries(batch.map(item => [item.id, item.activationDigest])),
      challengeIds: challenges.map(item => item.id),
      challengeActivations: Object.fromEntries(challenges.map(item => [item.id, item.activationDigest])) };
  }
  protected visible(task: CooperativeTask): TaskRecord[] {
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
  protected seed(worker: ResearchWorker, commit: string, task?: CooperativeTask): string {
    this.suspendResearchDrafts(worker, task?.id);
    const session = this.input.state.workers?.find(record => record.id === worker.id);
    const previousGroup = session?.sessionGroupId;
    if (task && (previousGroup && previousGroup !== taskGroup(task) || session?.sessionTaskId && session.sessionTaskId !== task.id) ||
        !task && worker.id !== this.lead.id) fs.writeFileSync(path.join(worker.worktree, 'RESEARCH.md'), '');
    const sources = Object.fromEntries(this.input.state.problem.ownedFiles.map(file => [file,
      committedSource(this.lead.worktree, commit, `${this.input.state.problem.projectRelative}/${file}`)]));
    for (const [file, source] of Object.entries(scopedResearchSources(this.input.state.problem, task, sources,
      researchSourceTasks(this.archive.tasks)))) {
      fs.writeFileSync(path.join(worker.worktree, this.input.state.problem.projectRelative, file), source);
    }
    const problem = this.input.state.problem;
    if (fs.existsSync(path.join(worker.worktree, problem.projectRelative, '.lake/source-constraints.json'))) {
      writeMathJsonDurable(path.join(worker.worktree, problem.projectRelative, '.lake/source-constraints.json'),
        { trustedFiles: problem.trustedFiles, declarations: problem.declarations,
          sourceStructure: problem.sourceStructure, sourceImports: problem.sourceImports }, 0o400);
    }
    const seed = commitSolverSources(this.input.state.problem, worker.worktree);
    if (worker.id === this.lead.id) {
      this.archive.leadSeedCommit = seed; this.pin(seed); this.input.save();
    }
    return seed;
  }
}
