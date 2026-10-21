import { parseCooperationPlan } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import type { LeanStatementContext } from '../math/leanStatementContext';
import { commitSolverSources, committedSource, git } from './problem';
import type { SolverRunState } from './archive';
import { independentFeasibilityWorker, type ResearchWorker } from './modules/organization';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { originalGoalTaskFocus, originalGoalFrontierSnapshot, plannedTaskDependencyIds } from './modules/search';
import { type DeliveryRecord } from './deliveries';
import { createTaskSourceProjector, omitTaskHelpers, TaskProofCache, type TaskProof } from './cooperativeProof';
import { isStatementAction, statementReviewSummary } from './statementReview';
import { type ProofReferences } from './proofReferences';
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
import { isFeasibilityReview, taskGroup, taskReferenceDependencies, type CooperativeTask, type TaskRecord, type CooperativeAction } from './tasks';
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
    controller: AbortController; current: () => boolean; settled: Promise<void>;
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
  protected active = new Map<string, { action: CooperativeAction; interrupt: () => Promise<void>; notify: (message: string) => Promise<void>; cancelled?: boolean }>();
  protected notifications = new Set<Promise<void>>();
  protected pendingPulse?: Promise<ReadonlyMap<string, Promise<void>>>;
  protected deliveryChecks = new Map<string, Promise<void>>();
  protected proofPublications = new Map<string, Promise<TaskProof | undefined>>();
  protected integrationQueue = Promise.resolve();
  protected leadEvidence = new WeakMap<CooperativeAction, string>();
  protected initialPlans = new WeakMap<CooperativeAction, { plan: ReturnType<typeof parseCooperationPlan>; version: string }>();
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
  protected abstract refreshFailedTaskInputs(): boolean;
  protected abstract refreshResearchCheckpoints(): void;
  protected abstract suspendResearchDrafts(worker: ResearchWorker, taskId?: string): void;
  protected abstract planVersion(): string;
  protected abstract canAssemble(commit: string): boolean;
  abstract contextState(action?: CooperativeAction, worker?: ResearchWorker, versions?: TaskVersions): CooperationState;
  constructor(protected readonly input: { state: SolverRunState; workers: readonly ResearchWorker[];
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
      this.archive.leadSeedCommit ??= this.archive.canonicalCommit;
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
  protected syncProofRoutes() {
    for (const node of this.archive.tasks) node.alternativeRoutes = this.archive.proofRoutes?.filter(route => route.targetTaskId === node.task.id);
  }
  protected changed(edit?: HumanEditRecord) {
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
      const visible = new Set(scoped.tasks.map(node => node.task.id));
      const deliveries = (scoped.deliveries ?? []).slice(-16);
      const handoffs = researchHandoffs(scoped);
      writeMathJsonDurable(path.join(worker.worktree, 'COOPERATION.json'), {
        planVersion: this.archive.planVersion,
        edits: (this.archive.edits ?? []).slice(-16),
        agents,
        parallelQuestions: scoped.parallelQuestions ?? [],
        peers: this.archive.tasks.map(node => ({ id: node.task.id, taskDigest: digest(node.task),
          objectiveDigest: mathDigest(node.task.objective), groupId: taskGroup(node.task), kind: node.task.kind,
          status: node.status, owner: node.assignment?.workerId ?? node.task.ownerId, dependsOn: node.task.dependsOn,
          ...(visible.has(node.task.id) ? { objective: node.task.objective, feedback: node.feedback,
            actualReferences: (node.integratedCheck ?? node.proof)?.references } : {}) })),
        deliveries: deliveries.map(({ evidence: _evidence, ...record }) => record),
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
  activate(worker: ResearchWorker, action: CooperativeAction, interrupt: () => Promise<void>, notify: (message: string) => Promise<void>) {
    this.active.set(worker.id, { action, interrupt, notify }); this.changed();
  }
  deactivate(worker: ResearchWorker) { this.active.delete(worker.id); this.changed(); }
  current(action: CooperativeAction) {
    if (action.kind === 'assemble') return !this.failure && !this.stopping && this.liveWorkers.has(this.lead.id) && this.canAssemble(action.seedCommit);
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
      const version = this.initialPlans.get(action)?.version ?? action.planVersion;
      return version === undefined || version === this.archive.planVersion;
    }
    if (action.kind === 'review') {
      const review = this.archive.review;
      return Boolean(review && review.status === 'running' && review.commit === action.seedCommit &&
        review.sourceDigest === action.sourceDigest && review.assignmentId === action.assignmentId);
    }
    return action.kind !== 'task' || this.archive.tasks.some(node => node.assignment === action.assignment && digest(node.task) === action.assignment.taskDigest &&
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
    this.input.emit('delivery_published', { deliveryId: record.id, taskId: record.taskId, kind: record.kind, status: record.status });
  }
  protected pin(commit?: string) {
    if (!commit || this.pinned.has(commit)) return;
    if (!/^[a-f0-9]{40,64}$/u.test(commit)) throw new Error('math_delivery_invalid_commit');
    git(this.lead.worktree, ['update-ref', `refs/math/${this.input.state.runId}/evidence/${commit}`, commit]);
    this.pinned.add(commit);
  }
  protected record(worker: ResearchWorker, task: CooperativeTask | undefined, kind: DeliveryRecord['kind'], status: DeliveryRecord['status'],
    summary: string, options: Partial<DeliveryRecord> = {}) {
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
    (this.archive.deliveries ??= []).push(record); this.changed();
    if (status !== 'superseded') this.inform(record);
    return record;
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
  protected handoffDispatch(batch = selectResearchHandoffBatch(this.archive)) {
    const challenges = selectResearchChallengeBatch(this.archive);
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
    if (worker.id === this.lead.id) {
      this.archive.leadSeedCommit = seed; this.pin(seed); this.input.save();
    }
    return seed;
  }
}
