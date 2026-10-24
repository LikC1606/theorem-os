import { parseCooperationPlan, isAdvisoryTask as advisory } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, readMathText, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { inspectLeanDeclarationRegions } from '../math/leanSource';
import { commitSolverSources, committedSource, git } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import { assessTaskResponsibility, assignSharedResearchTask, independentFeasibilityWorker, type ResearchWorker } from './modules/organization';
import type { DispatchWaitObservation } from './archive';
import { CAPACITY_EXPLORATION_FOCUSES, capacityExplorationInput, createCapacityExploration,
  currentCapacityExploration } from './capacityExploration';
import { advisoryStagnation } from './advisoryStagnation';
import { finishLeadAssessment, leadAssessmentCovered, prepareLeadAssessment, reopenLegacyLeadAssessment } from './leadAssessment';
import { hasFreshSolverCheck, proofReceiptsMatch, type ProofCheck } from './modules/evidence';
import { originalGoalTaskFocus, readyResearchTasks, researchCanAdvance, routeAllowsTask, taskCanStart, taskDependenciesReady, selectedTaskRoute } from './modules/search';
import { deliveryDetails, reviewVerdict, readMathResponse as block, MAX_RESEARCH_NOTES_BYTES } from './deliveries';
import { ownedSourceDigest, taskChanges } from './cooperativeProof';
import { assertStatementSnapshot, isStatementAction, resetStatementReview } from './statementReview';
import { captureProofReferences } from './proofReferences';
import { captureDeliveryArtifacts, type DeliveryArtifactManifest } from './deliveryArtifacts';
import { attributeTaskReferences } from './taskReferenceAttribution';
import { normalizedResearchHandoffDecisions, retainedResearchHandoffs, scopeResearchHandoffDecisions, selectResearchHandoffBatch } from './researchHandoffs';
import { COORDINATION_INLINE_FINDING_BYTES, pendingResearchChallenges, retainedResearchChallenges } from './researchChallenges';
import { taskConsumerProjection } from './taskConsumers';
import { parallelQuestions } from './taskQuestions';
import { mathematicalGaps, mathematicalGapVisible } from './mathematicalGaps';
import { automaticTaskConnection, createTaskConnectionCheck } from './taskConnections';
import { taskTypePreflightEnvironmentIdentity, type TaskTypePreflight } from './taskTypePreflight';
import { captureObligationSnapshot } from './obligationProgress';
import { assignmentDeliveryFile, groupOpen, isFeasibilityReview, taskGroup, taskProofContractVersion, type CapacityOwnershipCandidate, type CooperativeTask, type CooperativeAction, type TaskRecord } from './tasks';
import { digest, directDeliveryRejections, isTaskSourceRepairFeedback, rejectionCode, CooperationState, TaskVersions, DispatchBudget, RETRY_DISPATCH, DispatchResult, bounded,
  deliveryInputFields, readCooperationPlan } from './cooperationShared';
import { CooperationInputs } from './cooperationInputs';
import { ResearchAdmissionError } from './researchAdmission';
import type { CooperationPlanning } from './cooperationPlanning';
export { parseCooperationPlan } from './tasks';
export { taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile } from './tasks';
export type { CooperativeTask, RouteGroup, RouteRecord, TaskAssignment, TaskRecord, CooperativeAction } from './tasks';
export { readCooperationPlan } from './cooperationShared';
export type { ReviewRecord, HumanEditRecord, InitialPlanPublication, CooperationState } from './cooperationShared';

/** Lead plans; workers claim distinct ready obligations; only checked source enters the canonical proof. */
export class CooperativeResearch extends CooperationInputs {
  /** Optional advisory supply for otherwise idle expanded teams, without a Lead graph mutation. */
  private async requestCapacityExploration(worker: ResearchWorker, budget: DispatchBudget, previousReady: readonly TaskRecord[]) {
    if (!this.input.continuousResearch || this.input.workers.length <= 4 ||
        !['prover', 'researcher'].includes(worker.role) || budget.maxTurns !== Infinity || budget.remainingMs !== Infinity) return false;
    return this.input.exclusiveCheck(async () => {
      if (this.stopping || this.failure || this.input.signal.aborted || this.input.modelDispatchAllowed?.() === false ||
          !this.liveWorkers.has(this.lead.id) || !this.allocationPeers.some(peer => peer.id === worker.id) ||
          this.active.has(worker.id) || this.reservedTurns.has(worker.id) || this.deliveryChecks.has(worker.id) ||
          [...this.preparingTaskTypes.values()].some(pending => pending.workerId === worker.id) ||
          this.pendingFixedStatementReviews() || this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) return false;
      const ready = readyResearchTasks(this.archive.tasks, this.archive.groups)
        .filter(node => !this.preparingTaskTypes.has(node) && !this.synchronizationBlocked(node.task) &&
          (!node.capacityExploration || currentCapacityExploration(node, this.archive.tasks, this.explorationIdentity)));
      // A peer may have published real work while this request waited for the archive transaction.
      const newlyReady = assignSharedResearchTask(ready, worker, this.allocationPeers, this.archive.groups, this.archive.tasks);
      if (newlyReady) return !previousReady.includes(newlyReady);
      const focus = originalGoalTaskFocus(this.plannedTasks(), this.archive.groups, this.input.state.environmentDigest);
      const targets = [...focus.frontier].map(id => this.node(id)).filter(node => node &&
        ['lemma', 'goal'].includes(node.task.kind) && !['integrated', 'completed', 'delivered'].includes(node.status) &&
        !this.synchronizationBlocked(node.task) && routeAllowsTask(node.task, this.archive.tasks, this.archive.groups));
      for (const method of CAPACITY_EXPLORATION_FOCUSES) for (const target of targets) {
        const inputDigest = capacityExplorationInput(target.task, this.archive.tasks, this.explorationIdentity);
        if (this.archive.capacityExplorationInputs?.some(input => input.targetTaskId === target.task.id &&
            input.inputDigest === inputDigest && input.focus === method)) continue;
        const node = createCapacityExploration(target, worker, this.archive.tasks, this.explorationIdentity, method);
        if (this.archive.tasks.some(existing => existing.task.id === node.task.id) ||
            !currentCapacityExploration(node, this.archive.tasks, this.explorationIdentity) ||
            !routeAllowsTask(node.task, [...this.archive.tasks, node], this.archive.groups)) continue;
        // Marker and tombstone become durable together. No Lead files or CAS base are rewritten.
        (this.archive.capacityExplorationInputs ??= []).push({ inputDigest, focus: method,
          targetTaskId: target.task.id, taskId: node.task.id });
        this.archive.tasks.push(node);
        this.input.emit('capacity_exploration_requested', { workerId: worker.id, taskId: node.task.id,
          targetTaskId: target.task.id, inputDigest, focus: method, evidenceStatus: 'advisory' });
        this.changed(); return true;
      }
      return false;
    });
  }
  /** A normal advisory checkpoint preserves the draft before the new typed task takes priority. */
  shouldYieldCapacityExploration(worker: ResearchWorker, action: CooperativeAction): boolean {
    if (action.kind !== 'task' || !this.current(action)) return false;
    const node = this.node(action.task.id);
    if (!node?.capacityExploration || worker.role !== 'prover') return false;
    const groups = this.archive.groups?.map(route => ({ ...route,
      busy: Math.max(0, (route.busy ?? 0) - Number(route.group.id === taskGroup(node.task))) }));
    const ready = readyResearchTasks(this.archive.tasks, groups).filter(candidate => !candidate.capacityExploration &&
      !advisory(candidate.task) && !this.preparingTaskTypes.has(candidate) && !this.synchronizationBlocked(candidate.task));
    return Boolean(assignSharedResearchTask(ready, worker, this.allocationPeers, groups, this.archive.tasks));
  }
  private stagnationInput() {
    const { evidenceDigest } = this.capacityRefillInput();
    const recovery = advisoryStagnation({ tasks: this.archive.tasks, groups: this.archive.groups,
      workers: this.input.state.workers ?? [], identity: this.explorationIdentity,
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      evidenceDigest, explorationInputs: this.archive.capacityExplorationInputs });
    return recovery && { ...recovery, evidenceDigest };
  }
  private stagnationRecovery() {
    if (this.active.has(this.lead.id) || this.reservedTurns.has(this.lead.id) || this.leadDeliveries.size) return;
    const recovery = this.stagnationInput();
    if (!recovery || leadAssessmentCovered(this.archive.lastStagnationRecovery, recovery.inputDigest)) return;
    return recovery;
  }
  private capacityAvailability() {
    const groups = this.archive.groups?.map(route => ({ ...route,
      busy: route.busy ?? this.archive.tasks.filter(node => node.status === 'running' &&
        taskGroup(node.task) === route.group.id).length }));
    const occupied = new Set([...this.active.keys(), ...this.reservedTurns.keys(), ...this.deliveryChecks.keys(),
      ...[...this.preparingTaskTypes.values()].map(pending => pending.workerId),
      ...this.archive.tasks.filter(node => ['running', 'delivered'].includes(node.status) && node.assignment &&
        node.assignment.taskDigest === digest(node.task)).map(node => node.assignment!.workerId)]);
    const peers = this.allocationPeers;
    const ready = readyResearchTasks(this.archive.tasks, groups)
      .filter(node => !this.preparingTaskTypes.has(node) && !this.synchronizationBlocked(node.task));
    return { groups, occupied, peers, ready };
  }
  /** Propose a Lead-owned reassignment; the actual task and every scheduling gate stay unchanged. */
  private capacityOwnershipCandidates({ groups, occupied, peers, ready } = this.capacityAvailability()): CapacityOwnershipCandidate[] {
    const idle = peers.filter(worker => ['researcher', 'engineer'].includes(worker.role) && !occupied.has(worker.id) &&
      !assignSharedResearchTask(ready, worker, peers, groups, this.archive.tasks));
    return ready.flatMap(node => {
      if (!node.task.ownerId || !occupied.has(node.task.ownerId) || node.assignment || node.capacityExploration) return [];
      const candidate = { ...node, task: { ...node.task, ownerId: undefined } };
      const eligibleWorkerIds = idle.filter(worker =>
        assignSharedResearchTask([candidate], worker, peers, groups, this.archive.tasks) === candidate).map(worker => worker.id).sort();
      return eligibleWorkerIds.length ? [{ taskId: node.task.id, taskDigest: digest(node.task),
        ownerId: node.task.ownerId, eligibleWorkerIds }] : [];
    }).sort((a, b) => a.taskId.localeCompare(b.taskId));
  }
  private capacityRefillInput(ownershipCandidates = this.capacityOwnershipCandidates()) {
    const snapshot = captureObligationSnapshot(this.archive.tasks, { groups: this.archive.groups,
      environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes, blockers: this.archive.blockers });
    const versions = this.taskVersions();
    const external = (this.archive.deliveries ?? []).filter(record => record.producer !== this.lead.id &&
      ['research', 'proof', 'failure'].includes(record.kind));
    const finding = (record: (typeof external)[number]) => canonicalMathJson(deliveryInputFields(record));
    const source = ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!);
    const findings = [...new Set(external.filter(record => this.deliveryVisible(record, undefined, versions)).map(finding))].sort();
    // External content detects arrivals while Lead works, independently of its own plan revisions.
    const evidence = [...new Set(external.map(record => {
      const { status: _status, ...content } = deliveryInputFields(record);
      return canonicalMathJson(content);
    }))].sort();
    return { inputDigest: mathDigest(canonicalMathJson({ problem: this.input.state.problem.receiptDigest,
      environment: this.input.state.environmentDigest, mathematics: snapshot.digest, source, findings,
      ...(ownershipCandidates.length ? { ownershipCandidates } : {}) })),
    evidenceDigest: mathDigest(canonicalMathJson({ source, evidence })) };
  }
  private capacityRefill() {
    if (this.active.has(this.lead.id) || this.reservedTurns.has(this.lead.id) || this.leadDeliveries.size) return;
    const { groups, occupied, peers, ready } = this.capacityAvailability();
    const available = () => !groups || groups.some(route => groupOpen(route) &&
      (route.busy ?? 0) < (route.group.maxConcurrent ?? 3));
    if (!originalGoalTaskFocus(this.archive.tasks, this.archive.groups, this.input.state.environmentDigest).frontier.size ||
        !available()) return;
    const ownershipCandidates = this.capacityOwnershipCandidates({ groups, occupied, peers, ready });
    const idle = peers.filter(worker => ['prover', 'researcher', 'engineer'].includes(worker.role) && !occupied.has(worker.id))
      // Estimate the narrow Prover responsibility before generalists can claim the same helper.
      .sort((a, b) => Number(b.role === 'prover') - Number(a.role === 'prover'));
    if (!idle.length && !ownershipCandidates.length) return;
    // Capacity estimation is host-owned and must not consume a configurable scheduler's state.
    const workerIds = new Set<string>();
    for (const worker of idle) {
      const candidates = ready.filter(node => routeAllowsTask(node.task, this.archive.tasks, groups));
      const node = assignSharedResearchTask(candidates, worker, peers, groups, this.archive.tasks);
      if (!node) { workerIds.add(worker.id); continue; }
      // Simulate distinct claims so one shared task cannot occupy several idle workers.
      ready.splice(ready.indexOf(node), 1);
      const route = groups?.find(route => route.group.id === taskGroup(node.task));
      if (route) route.busy = (route.busy ?? 0) + 1;
    }
    for (const candidate of ownershipCandidates) for (const id of candidate.eligibleWorkerIds) workerIds.add(id);
    if (!workerIds.size || !available()) return;
    const input = this.capacityRefillInput(ownershipCandidates);
    const previous = this.archive.lastCapacityRefill;
    // An unfinished request can be retried after admission failure or process restore.
    if (leadAssessmentCovered(previous, input.inputDigest)) return;
    return { ...input, workerIds: [...workerIds], ...(ownershipCandidates.length ? { ownershipCandidates } : {}) };
  }
  private leadExecutableWork = new WeakMap<CooperativeAction, Set<string>>();
  private executableWork() {
    const { groups, peers, ready } = this.capacityAvailability();
    return this.archive.tasks.filter(node => !node.capacityExploration && (node.status === 'running' && node.assignment &&
      node.assignment.taskDigest === digest(node.task) && (node.task.status ?? 'active') === 'active' ||
      ready.includes(node) && peers.some(worker =>
        assignSharedResearchTask([node], worker, peers, groups, this.archive.tasks) === node)));
  }
  private capacityRequestWork(action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>): string[] | undefined {
    if (!action.capacityRefill) return;
    const { groups, occupied, peers, ready } = this.capacityAvailability();
    const fulfilled: string[] = [];
    for (const id of action.capacityRefill.workerIds) {
      const running = this.archive.tasks.find(node => node.status === 'running' && node.assignment?.workerId === id &&
        node.assignment.taskDigest === digest(node.task) && !node.capacityExploration);
      if (running) { fulfilled.push(running.task.id); continue; }
      const worker = peers.find(worker => worker.id === id);
      if (!worker || occupied.has(id)) return;
      const node = assignSharedResearchTask(ready.filter(node => !node.capacityExploration), worker, peers, groups, this.archive.tasks);
      if (!node) return;
      fulfilled.push(node.task.id);
      ready.splice(ready.indexOf(node), 1);
      const route = groups?.find(route => route.group.id === taskGroup(node.task));
      if (route) route.busy = (route.busy ?? 0) + 1;
    }
    return fulfilled;
  }
  protected leadAssessmentInput(kind: 'capacity' | 'stagnation') {
    return kind === 'capacity' ? this.capacityRefillInput() : this.stagnationInput();
  }
  /** Publishing a graph resolves only the scheduling obligation it actually fulfills. */
  protected markCapacityRefillAssessed(action: CooperativeAction): void {
    if (action.kind !== 'lead') return;
    const nonce = action.planNonce ?? action.initialPlanNonce;
    const previous = this.leadExecutableWork.get(action);
    const support = originalGoalTaskFocus(this.archive.tasks, this.archive.groups, this.input.state.environmentDigest).support;
    const decomposed = previous && this.executableWork().filter(node => !advisory(node.task) && support.has(node.task.id) &&
      !previous.has(taskProofContractVersion(node.task))).map(node => node.task.id);
    if (decomposed?.length && finishLeadAssessment(this.archive.lastStagnationRecovery, action.stagnationRecovery, nonce,
      { at: Date.now(), outcome: 'plan-published', fulfilledTaskIds: decomposed, currentInput: this.stagnationInput() }))
      this.input.emit('stagnation_recovery_assessed', { ...this.archive.lastStagnationRecovery, evidenceStatus: 'advisory' });
    const filled = this.capacityRequestWork(action);
    if (filled?.length && finishLeadAssessment(this.archive.lastCapacityRefill, action.capacityRefill, nonce,
      { at: Date.now(), outcome: 'plan-published', fulfilledTaskIds: filled, currentInput: this.capacityRefillInput() }))
      this.input.emit('capacity_refill_assessed', { ...this.archive.lastCapacityRefill });
  }
  private leadResponsibilityDigest(): string {
    const focus = originalGoalTaskFocus(this.archive.tasks, this.archive.groups, this.input.state.environmentDigest);
    return mathDigest(canonicalMathJson({ schema: 'theorem-os.lead-responsibility.v1', ...this.explorationIdentity,
      frontier: this.archive.tasks.filter(node => focus.frontier.has(node.task.id)).map(node =>
        [node.task.id, capacityExplorationInput(node.task, this.archive.tasks, this.explorationIdentity)])
        .sort(([a], [b]) => a.localeCompare(b)) }));
  }
  private acknowledgedAssessmentDraft(): boolean {
    try {
      const response = block(this.lead.worktree, 'math-plan');
      if (response.kind !== 'assessment' || response.baseVersion !== this.archive.planVersion ||
          typeof response.dispatchNonce !== 'string' || !Array.isArray(response.assessments) ||
          !response.assessments.length || response.assessments.length > 2) return false;
      const seen = new Set<string>();
      return response.assessments.every((item: any) => {
        const receipt = item?.kind === 'capacity' ? this.archive.lastCapacityRefill :
          item?.kind === 'stagnation' ? this.archive.lastStagnationRecovery : undefined;
        if (!receipt || seen.has(item.kind)) return false;
        seen.add(item.kind);
        return receipt.status === 'assessed' && receipt.outcome === 'no-independent-work' &&
          receipt.requestId === item.requestId && receipt.inputDigest === item.inputDigest &&
          receipt.dispatchNonce === response.dispatchNonce && receipt.decisionReason === item.reason;
      });
    } catch { return false; }
  }
  protected refreshFeasibilityAssignments() {
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
  /** A live publication never authorizes a superseded dispatch or changed decisions. */
  planSnapshot(action: CooperativeAction) {
    return this.current(action) ? this.publishedPlans.get(action)?.plan : undefined;
  }
  initialPlanSnapshot(action: CooperativeAction) { return this.planSnapshot(action); }
  start() {
    this.timer = setInterval(() => { void this.inputs().catch(error => {
      this.input.emit('cooperation_poll_failed', { reason: error instanceof Error ? error.message : 'unknown' });
      if (error instanceof Error && error.message === 'math_verifier_unavailable') { this.failure = error; this.changed(); }
    }); }, 200);
    this.timer.unref();
  }
  async stop() {
    this.stopping = true;
    for (const worker of this.input.workers) this.clearDispatchWait(worker, 'stopped');
    this.wake();
    clearInterval(this.timer);
    let pending: ReadonlyMap<string, Promise<void>> | undefined;
    try { pending = await this.pendingPulse; } catch (error) { if (!this.input.signal.aborted) throw error; }
    const drained = new Set<Promise<unknown>>();
    let failure: unknown;
    for (;;) {
      const work = [...new Set<Promise<unknown>>([...(pending?.values() ?? []), ...(this.pendingPulse ? [this.pendingPulse] : []),
        ...this.deliveryChecks.values(), ...this.proofPublications.values(), ...this.proofDeliveryChecks, ...this.planSynchronizations,
        ...this.leadDeliveries, ...[...this.preparingTaskTypes.values()].map(pending => pending.settled),
        ...(this.preparingStatements ? [this.preparingStatements] : []), this.integrationQueue])]
        .filter(item => !drained.has(item));
      if (!work.length) break;
      work.forEach(item => drained.add(item));
      const checks = await Promise.allSettled(work);
      const failed = checks.find(result => result.status === 'rejected');
      if (failed?.status === 'rejected') failure ??= failed.reason;
      await Promise.resolve();
    }
    if (failure && !this.input.signal.aborted) throw failure;
    await Promise.allSettled([...this.notifications]);
    this.syncPlanNotes();
    if (!this.input.signal.aborted) this.archive.canonicalCommit = this.seed(this.lead, this.archive.canonicalCommit!);
    this.input.save();
  }
  async pulse(workerId?: string): Promise<void> {
    if (workerId) await this.deliveryChecks.get(workerId);
    const pending = await this.inputs();
    const checks = await Promise.allSettled(workerId ? [pending.get(workerId)] : [...pending.values()]);
    const failed = checks.find(result => result.status === 'rejected');
    if (failed?.status === 'rejected') throw failed.reason;
  }
  async restore() {
    for (const [kind, receipt] of [['capacity', this.archive.lastCapacityRefill], ['stagnation', this.archive.lastStagnationRecovery]] as const)
      if (reopenLegacyLeadAssessment(receipt)) this.input.emit('lead_assessment_reopened', {
        kind, requestId: receipt!.requestId, reason: 'legacy-publication-without-executable-work' });
    if (this.refreshFeasibilityAssignments()) this.changed();
    for (const node of this.archive.tasks) if (['pending', 'running'].includes(node.status)) this.restoreTaskSourceRepair(node);
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
    const publication = this.archive.planPublication ?? this.archive.initialPlanPublication;
    if (!(publication && !publication.finalized) &&
        !this.acknowledgedAssessmentDraft() &&
        !this.archive.frontierRecoveries?.some(record => record.status !== 'planned') &&
        fs.existsSync(path.join(this.lead.worktree, 'RESEARCH.md'))) {
      try {
        const rejection = this.archive.planRejection;
        if (!rejection?.stalled || rejection.proposalDigest !== this.proposedPlanDigest() ||
            rejection.inputDigest !== this.planningInputDigest()) {
          const plan = readCooperationPlan(this.input.state.problem, this.lead.worktree);
          this.preserveAdvisoryBacklogs(plan);
          const initial = !this.archive.tasks.length;
          await this.acceptPlan(plan);
          if (initial) this.needsLead = false;
        }
      } catch (error) {
        if (this.archive.lastCapacityRefill?.status === 'requested') {
          // Restoring an interrupted draft is not another completed planning decision.
          this.preserveLeadDraft(commitSolverSources(this.input.state.problem, this.lead.worktree), this.archive.leadSeedCommit,
            error instanceof Error ? error.message : 'math_plan_incomplete');
        } else this.rejectPlan(error);
      }
    }
    if (!solverSourceFeedback(this.input.state.problem, this.lead.worktree)) {
      await this.restoreLeadSources();
      const integrated = this.archive.tasks.filter(node => node.status === 'integrated');
      this.markPendingValidation(integrated, new Set(integrated.map(node => node.task.id)));
      if (integrated.length || this.archive.edits?.some(edit => edit.pendingSync)) await this.schedulePlanSynchronization();
      await this.input.exclusiveCheck(() => this.recheckConditional());
    } else {
      for (const node of this.archive.tasks.filter(node => node.status === 'integrated')) {
        node.status = 'blocked'; node.feedback = 'math_canonical_source_invalid';
      }
      this.needsLead = true;
    }
    for (const node of this.archive.tasks) if (node.status === 'running') node.status = 'pending';
    for (const node of this.archive.tasks.filter(node => node.status === 'delivered')) await this.integrate(node);
    await this.integrateReady();
    const statements = this.prepareStatementContexts(); if (statements) await statements;
    this.syncStatementReviews();
    if (publication && !publication.finalized) {
      // Preserve the draft in restoreLeadSources, then seed future decisions from the accepted graph.
      this.archive.planEdited = true; this.syncPlanNotes();
    }
    this.changed();
  }
  private dispatchBudgetExhausted(budget: DispatchBudget, modelAllowed: boolean) {
    return this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0 || !modelAllowed;
  }
  private async exhaustedDispatch(budget: DispatchBudget, modelAllowed: boolean, running = false): Promise<DispatchResult> {
    const refund = modelAllowed && budget.remainingMs > 0 && this.waitForTurn(budget.maxTurns);
    if (refund) { await refund; return RETRY_DISPATCH; }
    if (running) return this.waitForDispatch();
  }
  protected canAssemble(commit: string) {
    if (commit !== this.archive.canonicalCommit || this.candidateSynchronizationBlocked()) return false;
    const goals = this.archive.tasks.filter(node => node.task.kind === 'goal');
    return this.reviewed() || goals.length > 0 && goals.every(node => node.status === 'integrated');
  }
  async next(worker: ResearchWorker, budget: DispatchBudget): Promise<CooperativeAction | undefined> {
    for (;;) {
      if (this.stopping) return;
      this.input.signal.throwIfAborted();
      if (this.failure) throw this.failure;
      if (this.refreshCapacityExplorations()) this.changed();
      if (this.refreshFeasibilityAssignments()) this.changed();
      this.refreshResearchCheckpoints();
      if (this.refreshFailedTaskInputs()) this.changed();
      if (this.refreshInvalidTaskTypes()) this.changed();
      if (this.archive.frontierWaiting && this.archive.frontierWaiting.inputDigest !== this.planningInputDigest()) {
        this.archive.frontierWaiting = undefined; this.changed();
      }
      if (!this.liveWorkers.has(this.lead.id)) {
        this.recordDispatchWait(worker, { stage: 'lead-unavailable', candidates: [], candidateCount: 0, omittedCandidates: 0 });
        return;
      }
      const modelAllowed = this.input.modelDispatchAllowed?.() !== false;
      const result = await (worker.id === this.lead.id
        ? this.nextLead(worker, budget, modelAllowed) : this.nextPeer(worker, budget, modelAllowed));
      if (result !== RETRY_DISPATCH) return result;
    }
  }
  private async nextLead(worker: ResearchWorker, budget: DispatchBudget, modelAllowed: boolean): Promise<DispatchResult> {
    if (this.synchronizationPending()) return this.waitForDispatch();
    if (this.pendingFixedStatementReviews()) {
      if (!this.livePeers.length || budget.remainingMs <= 0 ||
          this.input.state.turns >= budget.maxTurns && !this.reservedTurns.size || !modelAllowed && !this.active.size) return;
      return this.waitForDispatch();
    }
    const head = this.archive.canonicalCommit!;
    if (this.canAssemble(head) && this.lastAssembly !== head) {
      this.syncPlanNotes();
      const seed = this.seed(worker, head); this.archive.canonicalCommit = seed;
      this.cancelStaleTaskTypes();
      this.lastAssembly = seed; return { kind: 'assemble', seedCommit: seed };
    }
    const running = this.preparingTaskTypes.size > 0 || this.active.size > 0 || this.archive.tasks.some(node => ['running', 'delivered'].includes(node.status) ||
      (node.status === 'conditional' && taskDependenciesReady(node.task, this.archive.tasks))) || this.archive.review?.status === 'running' ||
      this.archive.statementReviews?.some(review => ['translating', 'reviewing'].includes(review.status) ||
        (modelAllowed && this.input.state.turns < budget.maxTurns && budget.remainingMs > 0 &&
          ['pending', 'translated'].includes(review.status) && this.livePeers.length > 0 &&
          this.statementReviewAllowed(this.node(review.taskId).task, true)));
    if (this.dispatchBudgetExhausted(budget, modelAllowed)) return this.exhaustedDispatch(budget, modelAllowed, running);
    if (!running && !this.livePeers.length) return;
    if (this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) return this.waitForDispatch();
    const stagnation = this.stagnationRecovery();
    if (stagnation) this.needsLead = true;
    const rejection = this.archive.planRejection;
    if (rejection?.stalled && !stagnation) {
      if (rejection.inputDigest === this.planningInputDigest() && rejection.proposalDigest === this.proposedPlanDigest()) {
        this.needsLead = false;
        if (!running && !this.canAdvance()) {
          if (this.input.continuousResearch) return this.idleFrontier(this.activeGoalFrontier(), rejection.inputDigest, false);
          this.input.emit('plan_stalled', { ...rejection }); return;
        }
        return this.waitForDispatch();
      }
      this.needsLead = true;
    }
    const pendingHandoffs = selectResearchHandoffBatch(this.archive);
    if (pendingHandoffs.length || pendingResearchChallenges(this.archive).length) this.needsLead = true;
    if (!this.needsLead && this.archive.tasks.length) {
      const support = originalGoalTaskFocus(this.archive.tasks, this.archive.groups).support;
      const supportingWork = this.archive.tasks.some(node => support.has(node.task.id) &&
        (this.preparingTaskTypes.has(node) || ['running', 'delivered'].includes(node.status) ||
          node.status === 'conditional' && taskDependenciesReady(node.task, this.archive.tasks))) ||
        this.archive.statementReviews?.some(review => support.has(review.taskId) &&
          ['pending', 'translating', 'translated', 'reviewing'].includes(review.status));
      // Independent work must not defer reconsidering a stalled original argument.
      if (!supportingWork && !this.hasAssignableTask(support) && !this.canAdvance(support)) {
        const frontier = this.activeGoalFrontier();
        if (frontier.some(item => item.status === 'blocked' && item.attempts > 0)) {
          const recovery = this.requestFrontierRecovery(frontier);
          if (recovery) return recovery;
          if (await this.investigateFrontierRecovery(frontier)) return RETRY_DISPATCH;
        }
      }
    }
    const refill = budget.maxTurns === Infinity && budget.remainingMs === Infinity ? this.capacityRefill() : undefined;
    if (refill) this.needsLead = true;
    if (!running && !this.needsLead && this.archive.tasks.length && (!this.archive.review || this.archive.review.status === 'changes_requested') &&
        !this.canAdvance()) {
      // Parking prevents repeating an inference, not reconsidering its unfinished original goal.
      const frontier = this.activeGoalFrontier();
      const inputDigest = this.planningInputDigest();
      if (!frontier.length || inputDigest === this.archive.lastLeadInputDigest) return this.idleFrontier(frontier, inputDigest);
      this.needsLead = true;
      this.input.emit('blocked_tasks_reconsidered', { taskIds: frontier.map(item => item.taskId),
        goalIds: [...new Set(frontier.flatMap(item => item.goalIds))], inputDigest });
    }
    if (this.needsLead || (!running && (!this.livePeers.length || !this.hasAssignableTask()))) {
      this.needsLead = false;
      const inputDigest = this.planningInputDigest();
      if (!refill && !stagnation && inputDigest === this.archive.lastLeadInputDigest && !this.archive.error && !pendingHandoffs.length &&
          !pendingResearchChallenges(this.archive).length) {
        return !running && !this.hasAssignableTask() ? this.idleFrontier(this.activeGoalFrontier(), inputDigest) : RETRY_DISPATCH;
      }
      if (this.archive.frontierRecoveries?.some(record => record.status === 'requested')) {
        const recovery = this.requestFrontierRecovery(this.activeGoalFrontier());
        if (recovery) return recovery;
      }
      this.syncPlanNotes();
      const planVersion = this.archive.planVersion ??= this.planVersion();
      const coordination = this.archive.tasks.length > 0 &&
        Boolean(pendingHandoffs.length || pendingResearchChallenges(this.archive).length || refill || stagnation);
      const limits = coordination ? { maxItems: 2, maxBytes: 12 * 1024,
        maxFindingBytes: COORDINATION_INLINE_FINDING_BYTES } : undefined;
      const action: CooperativeAction = { kind: 'lead', seedCommit: this.seed(worker, head), planVersion,
        planningInputDigest: inputDigest, responsibilityDigest: this.leadResponsibilityDigest(),
        ...this.handoffDispatch(coordination ? selectResearchHandoffBatch(this.archive, limits) : pendingHandoffs, limits),
        ...(coordination ? { coordination: true as const } : {}),
        ...(!this.archive.tasks.length && !this.archive.initialPlanPublication ? { initialPlanNonce: crypto.randomUUID() } : {}),
        ...(this.archive.tasks.length ? { planNonce: crypto.randomUUID() } : {}) };
      this.leadEvidence.set(action, this.planningEvidenceDigest());
      this.leadExecutableWork.set(action, new Set(this.executableWork().filter(node => !advisory(node.task))
        .map(node => taskProofContractVersion(node.task))));
      if (stagnation) {
        const { receipt, created } = prepareLeadAssessment('stagnation', this.archive.lastStagnationRecovery, { inputDigest: stagnation.inputDigest,
          taskIds: [...stagnation.taskIds], workerIds: [...stagnation.workerIds], reason: stagnation.reason,
          requestedAt: Date.now(), status: 'requested' as const, evidenceDigest: stagnation.evidenceDigest }, action.planNonce ?? action.initialPlanNonce!);
        action.stagnationRecovery = Object.freeze({ requestId: receipt.requestId, inputDigest: receipt.inputDigest,
          taskIds: Object.freeze([...receipt.taskIds]), workerIds: Object.freeze([...receipt.workerIds]),
          requestedAt: receipt.requestedAt, reason: receipt.reason });
        this.archive.lastStagnationRecovery = receipt;
        this.input.emit(created ? 'stagnation_recovery_requested' : 'stagnation_recovery_resumed', { ...receipt, evidenceStatus: 'advisory',
          request: 'Identify independent closed typed sub-obligations with an exact consumer derivation, or retain the precise unresolved gap. Do not repeat the same exploration or count scheduling inactivity as proof failure.' });
        this.changed();
      }
      if (refill) {
        const { receipt, created } = prepareLeadAssessment('capacity', this.archive.lastCapacityRefill, { inputDigest: refill.inputDigest,
          workerIds: [...refill.workerIds], requestedAt: Date.now(), status: 'requested' as const, evidenceDigest: refill.evidenceDigest },
          action.planNonce ?? action.initialPlanNonce!);
        action.capacityRefill = Object.freeze({ requestId: receipt.requestId, inputDigest: receipt.inputDigest,
          workerIds: Object.freeze([...receipt.workerIds]), requestedAt: receipt.requestedAt,
          ...(refill.ownershipCandidates ? { ownershipCandidates: Object.freeze(refill.ownershipCandidates.map(candidate =>
            Object.freeze({ ...candidate, eligibleWorkerIds: Object.freeze([...candidate.eligibleWorkerIds]) }))) } : {}) });
        this.archive.lastCapacityRefill = receipt;
        this.input.emit(created ? 'capacity_refill_requested' : 'capacity_refill_resumed', { ...receipt, planVersion });
        this.changed();
      }
      return action;
    }
    return this.waitForDispatch();
  }
  private taskDispatchBlock(node: TaskRecord): 'preparing-type' | 'synchronizing' | 'capacity-expired' | undefined {
    if (this.preparingTaskTypes.has(node)) return 'preparing-type';
    if (this.synchronizationBlocked(node.task)) return 'synchronizing';
    if (node.capacityExploration && !currentCapacityExploration(node, this.archive.tasks, this.explorationIdentity))
      return 'capacity-expired';
  }
  private recordTaskWait(worker: ResearchWorker, ranked: readonly TaskRecord[], ready: readonly TaskRecord[]) {
    const candidates: DispatchWaitObservation['candidates'] = ranked.slice(0, 16).map(node => {
      const hostBlock = this.taskDispatchBlock(node);
      const assessment = assessTaskResponsibility(node, worker, this.archive);
      return { taskId: node.task.id, taskDigest: digest(node.task),
        reason: hostBlock ?? (assessment.kind === 'blocked' ? assessment.reason : 'policy-no-selection') };
    });
    this.recordDispatchWait(worker, { stage: !ranked.length ? 'm3-no-ready' : !ready.length ? 'host-filtered' : 'm5-no-selection',
      candidateCount: ranked.length, omittedCandidates: ranked.length - candidates.length, candidates });
  }
  private async nextPeer(worker: ResearchWorker, budget: DispatchBudget, modelAllowed: boolean): Promise<DispatchResult> {
    if (budget.remainingMs <= 0 || !modelAllowed || this.input.state.turns >= budget.maxTurns) {
      this.recordDispatchWait(worker, { stage: 'budget-gated',
        gate: budget.remainingMs <= 0 ? 'time-limit' : !modelAllowed ? 'model-disabled' : 'turn-limit',
        candidates: [], candidateCount: 0, omittedCandidates: 0 });
      return budget.remainingMs <= 0 || !modelAllowed ? undefined : this.exhaustedDispatch(budget, modelAllowed);
    }
    const review = this.archive.review;
    const reviewer = this.reviewer();
    const statement = reviewer?.id === worker.id && this.archive.statementReviews?.find(item =>
      ['pending', 'translated'].includes(item.status) && this.statementReviewAllowed(this.node(item.taskId).task, true) &&
      ![...this.active.values()].some(active => isStatementAction(active.action) && active.action.reviewId === item.id));
    if (statement) {
      this.clearDispatchWait(worker, 'selected');
      const kind = statement.status === 'pending' ? 'backtranslate' : 'statement-review';
      fs.rmSync(path.join(statement.workspace, 'RESEARCH.md'), { force: true });
      statement.status = kind === 'backtranslate' ? 'translating' : 'reviewing'; statement.workerId = worker.id;
      statement.assignmentId = crypto.randomUUID();
      this.input.emit('statement_review_assigned', { workerId: worker.id, taskId: statement.taskId, reviewId: statement.id, kind, role: 'reviewer' });
      this.changed(); return { kind, reviewId: statement.id, taskId: statement.taskId, taskDigest: statement.taskDigest,
        snapshotDigest: statement.snapshotDigest, seedCommit: statement.commit, workspace: statement.workspace,
        assignmentId: statement.assignmentId };
    }
    if (review?.status === 'pending' && reviewer?.id === worker.id && !this.candidateSynchronizationBlocked()) {
      this.clearDispatchWait(worker, 'selected');
      this.seed(worker, review.commit);
      const notes = path.join(worker.worktree, 'RESEARCH.md');
      if (fs.existsSync(notes)) fs.writeFileSync(notes, fs.readFileSync(notes, 'utf8').replace(/```(?:math|math-review)\s*\n[\s\S]*?\n```/gu, ''));
      review.workerId = worker.id; review.status = 'running'; review.assignmentId = crypto.randomUUID();
      this.input.emit('review_assigned', { workerId: worker.id, commit: review.commit, role: 'reviewer' });
      this.changed(); return { kind: 'review', seedCommit: review.commit, sourceDigest: review.sourceDigest,
        assignmentId: review.assignmentId };
    }
    const ranked = this.input.modules.M3.ready(this.archive.tasks, this.archive.groups);
    const ready = ranked.filter(node => !this.taskDispatchBlock(node));
    const node = this.input.modules.M5.assign(ready, worker,
      this.allocationPeers, this.archive.groups, this.archive.tasks);
    if (!node) {
      this.recordTaskWait(worker, ranked, ready);
      if (await this.requestCapacityExploration(worker, budget, ready)) return RETRY_DISPATCH;
      return this.liveWorkers.has(worker.id) ? this.waitForDispatch() : undefined;
    }
    if (!ready.includes(node) || !this.archive.tasks.includes(node) || node.status !== 'pending' ||
        !taskCanStart(node.task, this.archive.tasks, this.archive.groups) ||
        !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
        assessTaskResponsibility(node, worker, this.archive).kind !== 'matches') throw new Error('math_task_assignment_invalid');
    this.clearDispatchWait(worker, 'selected');
    const selectedRoute = selectedTaskRoute(node, this.archive.tasks);
    if (node.assignment && node.alternativeRoutes?.length && node.assignment.routeId !== selectedRoute?.id)
      node.assignment = undefined;
    let resuming = node.assignment?.workerId === worker.id;
    if (resuming && advisory(node.task) &&
        (this.archive.researchDrafts?.[node.task.id]?.suspended || this.researchWorkspaceChanged(worker, node))) {
      const previousAssignment = node.assignment;
      const restored = await this.restoreResearchDraft(worker, node);
      if (this.synchronizationBlocked(node.task) || !this.archive.tasks.includes(node) || node.status !== 'pending' ||
          !restored && node.assignment !== previousAssignment ||
          assessTaskResponsibility(node, worker, this.archive).kind !== 'matches' ||
          !taskCanStart(node.task, this.archive.tasks, this.archive.groups) || !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups)) return RETRY_DISPATCH;
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
    const scopedSeed = resuming ? seed : this.seed(worker, seed, node.task);
    if (node.task.kind === 'lemma') {
      const task = node.task, taskDigest = digest(task), environment = this.input.state.environmentDigest;
      const dependencies = this.typePreflightDependencies(task), head = git(worker.worktree, ['rev-parse', 'HEAD']);
      const project = path.join(worker.worktree, this.input.state.problem.projectRelative), started = Date.now();
      const routeDigest = canonicalMathJson(selectedRoute ?? null);
      const assignment = node.assignment, workerAccess = this.input.access.get(worker.id);
      const controller = new AbortController(), signal = AbortSignal.any([this.input.signal, controller.signal]);
      const current = () => !signal.aborted && !this.stopping && !this.failure && this.liveWorkers.has(this.lead.id) &&
        this.archive.canonicalCommit === seed && this.archive.tasks.includes(node) && digest(node.task) === taskDigest &&
        this.typePreflightDependencies(task) === dependencies && this.input.access.get(worker.id) === workerAccess &&
        this.input.state.environmentDigest === environment && node.status === 'pending' && node.assignment === assignment &&
        !this.synchronizationBlocked(node.task) && taskCanStart(node.task, this.archive.tasks, this.archive.groups) &&
        routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) && this.liveWorkers.has(worker.id) &&
        assessTaskResponsibility(node, worker, this.archive).kind === 'matches' &&
        canonicalMathJson(selectedTaskRoute(node, this.archive.tasks) ?? null) === routeDigest &&
        this.input.modelDispatchAllowed?.() !== false &&
        !this.dispatchBudgetExhausted(budget, true) && Date.now() - started < budget.remainingMs;
      // Cancellation keeps the worker occupied until the Lean check has cleaned up.
      let finishPreparation!: () => void;
      const settled = new Promise<void>(resolve => { finishPreparation = resolve; });
      this.preparingTaskTypes.set(node, { workerId: worker.id, controller, current, settled });
      this.changed();
      try {
        const checked: { result: TaskTypePreflight; current: () => boolean } = workerAccess ? await this.taskTypePreflight.check({ problem: this.input.state.problem, task,
          projectRoot: project,
          dependencies: this.dependencies(task).map(item => item.task), environmentDigest: environment,
          env: workerAccess.environment, signal,
          timeoutMs: this.input.timeoutMs ?? Infinity }) : {
            result: { status: 'unavailable', inputDigest: mathDigest(canonicalMathJson([taskDigest, environment, 'worker-environment-unavailable'])),
              taskDigest, reason: 'worker-environment-unavailable', evidence: 'advisory-type-elaboration', proofAcceptance: 'not-assessed' },
            current: () => !this.input.signal.aborted,
          };
        if (!current() || !checked.current() || git(worker.worktree, ['rev-parse', 'HEAD']) !== head ||
            this.input.modules.M5.assign([node], worker, this.allocationPeers, this.archive.groups, this.archive.tasks) !== node)
          return RETRY_DISPATCH;
        node.typePreflight = checked.result;
        this.input.emit('task_type_preflight', { taskId: node.task.id, workerId: worker.id, ...checked.result });
        if (checked.result.status === 'invalid') {
          this.invalidTaskTypes.set(node, { canonical: seed, environment, taskDigest, dependencies, project, workerId: worker.id,
            environmentIdentity: taskTypePreflightEnvironmentIdentity(project, workerAccess!.environment) });
          node.status = 'blocked';
          node.feedback = 'math_task_type_invalid\n' + bounded(checked.result.reason, 2000) +
            (checked.result.artifact ? `\nAdvisory type diagnostics: ${checked.result.artifact.path} (${checked.result.artifact.digest})` : '') +
            '\nRevise the closed helper type or its context before proving it. This is not proof acceptance or a mathematical refutation.';
          this.needsLead = true; this.changed(); return RETRY_DISPATCH;
        }
      } finally {
        this.preparingTaskTypes.delete(node); finishPreparation(); this.changed();
      }
    }
    node.assignment ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id,
      seedCommit: scopedSeed, assignmentId: crypto.randomUUID(), canonicalCommit: seed, groupId: taskGroup(node.task),
      routeId: selectedRoute?.id,
      dependencies: this.dependencies(node.task).map(item => ({ taskId: item.task.id, taskDigest: digest(item.task) })) };
    if (!node.assignment.connectionCheck && automaticTaskConnection(node.task, this.archive.tasks, this.archive.groups)) {
      // Upgrading an idle historical assignment keeps its saved draft but supersedes late publications.
      if (resuming) node.assignment = { ...node.assignment, assignmentId: crypto.randomUUID() };
      node.assignment.connectionCheck = createTaskConnectionCheck(node.task, node.assignment, this.archive.tasks,
        { environmentDigest: this.input.state.environmentDigest, problemReceiptDigest: this.input.state.problem.receiptDigest },
        dependency => committedSource(worker.worktree, node.assignment!.seedCommit,
          `${this.input.state.problem.projectRelative}/${dependency.proofPath}`));
      this.input.emit('task_connection_check_assigned', { taskId: node.task.id, workerId: worker.id,
        connectionCheck: node.assignment.connectionCheck });
    }
    if (!advisory(node.task) &&
        fs.existsSync(path.join(worker.worktree, this.input.state.problem.projectRelative, '.lake/source-constraints.json'))) {
      const problem = this.input.state.problem;
      // Local diagnostics should reject the same unrelated goal edits as task delivery,
      // before the worker spends time compiling a candidate it cannot submit.
      const declarations = Object.fromEntries(Object.entries(problem.declarations).map(([file, originals]) => {
        const source = committedSource(worker.worktree, node.assignment!.seedCommit, `${problem.projectRelative}/${file}`);
        const regions = inspectLeanDeclarationRegions(source);
        return [file, originals.map(original => {
          if (original.body || file === node.task.proofPath &&
              original.name.split('.').at(-1) === node.task.theoremName?.split('.').at(-1)) return original;
          const region = regions.find(item => item.name === original.name)!;
          return { ...original, body: mathDigest(source.slice(region.bodyOffset, region.endOffset).trim()) };
        })];
      }));
      writeMathJsonDurable(path.join(worker.worktree, problem.projectRelative, '.lake/source-constraints.json'),
        { trustedFiles: problem.trustedFiles, declarations, sourceStructure: problem.sourceStructure,
          sourceImports: problem.sourceImports }, 0o400);
    }
    node.status = 'running';
    const route = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
    this.input.emit('task_assigned', { taskId: node.task.id, workerId: worker.id, kind: node.task.kind,
      taskDigest: node.assignment.taskDigest, assignmentKey: assignmentDeliveryFile(node.assignment),
      planVersion: this.archive.planVersion, groupId: taskGroup(node.task), groupTurns: route?.turns,
      seedCommit: node.assignment.seedCommit });
    this.changed(); return { kind: 'task', assignment: node.assignment, task: node.task };
  }
  private typePreflightDependencies(task: CooperativeTask) {
    return canonicalMathJson(this.dependencies(task).map(item => [item.task.id, digest(item.task)]));
  }
  private refreshInvalidTaskTypes() {
    let changed = false;
    for (const node of this.archive.tasks) {
      if (node.status !== 'blocked' || node.typePreflight?.status !== 'invalid') continue;
      const prior = this.invalidTaskTypes.get(node);
      const access = prior && this.input.access.get(prior.workerId);
      if (prior && access && prior.canonical === this.archive.canonicalCommit && prior.environment === this.input.state.environmentDigest &&
          prior.taskDigest === digest(node.task) && prior.dependencies === this.typePreflightDependencies(node.task) &&
          prior.environmentIdentity === taskTypePreflightEnvironmentIdentity(prior.project, access.environment)) continue;
      node.status = 'pending'; node.typePreflight = undefined;
      if (node.feedback?.startsWith('math_task_type_invalid\n')) node.feedback = undefined;
      this.invalidTaskTypes.delete(node); changed = true;
    }
    return changed;
  }
  private canAdvance(taskIds?: ReadonlySet<string>) {
    return researchCanAdvance(this.archive.tasks, this.archive.groups, this.liveWorkers, node =>
      !this.preparingTaskTypes.has(node) && !this.synchronizationBlocked(node.task) &&
      this.livePeers.some(worker => assessTaskResponsibility(node, worker, this.archive).kind === 'matches' &&
        this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node), taskIds);
  }
  private hasAssignableTask(taskIds?: ReadonlySet<string>) {
    return this.input.modules.M3.ready(this.archive.tasks, this.archive.groups).some(node => !this.preparingTaskTypes.has(node) && !this.synchronizationBlocked(node.task) &&
      (!taskIds || taskIds.has(node.task.id)) && this.archive.tasks.includes(node) &&
      this.livePeers.some(worker => assessTaskResponsibility(node, worker, this.archive).kind === 'matches' &&
        this.input.modules.M5.assign([node], worker, this.livePeers, this.archive.groups, this.archive.tasks) === node));
  }
  reviewed(check?: ProofCheck) {
    const required = this.fixedStatementReviewTasks();
    if (this.fixedReviewScope && !required) return false;
    return !this.candidateSynchronizationBlocked() && this.archive.review?.status === 'accepted' && this.archive.review.commit === this.archive.canonicalCommit &&
      (!check || (check.commit === this.archive.review.commit && check.sourceDigest === this.archive.review.sourceDigest)) &&
      this.archive.tasks.filter(node => node.task.statementReview && (!required || required.has(node.task.id))).every(node => this.archive.statementReviews?.some(review =>
        review.taskId === node.task.id && review.taskDigest === digest(node.task) && review.status === 'accepted'));
  }
  requireReview(check: ProofCheck) {
    if (this.archive.review?.commit !== check.commit || this.archive.review.sourceDigest !== check.sourceDigest) {
      this.archive.review = { commit: check.commit, sourceDigest: check.sourceDigest, status: 'pending' };
      this.input.emit('review_requested', { commit: check.commit });
    }
    const configured = this.archive.tasks.filter(node => node.task.statementReview), used = new Set<string>();
    const problem = this.input.state.problem;
    let complete = hasFreshSolverCheck(check) && proofReceiptsMatch(check.verification, check.commit,
      problem.targets.map(target => ({ proofPath: target.proofPath, theoremName: target.theoremName,
        expectedSourceDeclarationHash: target.declarationHash, statementHash: problem.contract.statementHash,
        leanStatementHash: problem.contract.leanStatementHash, claim: 'statement' })));
    if (complete) for (const target of problem.targets) {
      const receipt = check.verification.results.find(result => result.proofPath === target.proofPath && result.theoremName === target.theoremName);
      const references = receipt?.declarationReferences && captureProofReferences(problem, this.lead.worktree, check.commit,
        { name: target.theoremName, file: target.proofPath }, receipt.declarationReferences, this.input.state.environmentDigest);
      if (!references) { complete = false; break; }
      for (const reference of attributeTaskReferences(references, this.archive.tasks)) used.add(reference.taskId);
    }
    const required = new Map(configured.filter(node => !complete || node.task.kind === 'goal' || used.has(node.task.id))
      .map(node => [node.task.id, digest(node.task)]));
    this.fixedReviewScope = { review: this.archive.review, commit: check.commit, sourceDigest: check.sourceDigest,
      environmentDigest: this.input.state.environmentDigest, tasksDigest: this.statementTaskIdentity(), required };
    for (const active of this.active.values()) if (isStatementAction(active.action) && !this.current(active.action) && !active.cancelled) {
      const reviewId = active.action.reviewId;
      const statement = this.archive.statementReviews?.find(item => item.id === reviewId);
      if (statement) resetStatementReview(statement);
      active.cancelled = true; void active.interrupt().catch(() => {});
    }
    this.input.emit('final_statement_review_scope', { commit: check.commit, sourceDigest: check.sourceDigest,
      referenceCoverage: complete ? 'complete' : 'unknown', requiredTaskIds: [...required.keys()],
      unusedTaskIds: configured.filter(node => !required.has(node.task.id)).map(node => node.task.id) });
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
    const gapViewer = task ?? (ordinaryWorker ? { id: 'idle', groupId: '__idle__' } as CooperativeTask : undefined);
    const visibleIds = new Set(tasks.map(node => node.task.id));
    const visible = (id: string, version: string) => visibleIds.has(id) && versions.get(id)?.version === version;
    const deliveries = this.archive.deliveries?.filter(item => this.deliveryVisible(item, task, versions, gapViewer) &&
      (task || tasks === this.archive.tasks || !item.taskId || versions.get(item.taskId)?.task.sharing !== 'group')) ?? [];
    const hiddenFindings = new Set((this.archive.deliveries ?? []).filter(item =>
      !mathematicalGapVisible(item, this.archive, gapViewer)).flatMap(item => item.findingDigest ? [item.findingDigest] : []));
    const scopedFinding = <T extends { finding?: string }>(node: T): T => node.finding && hiddenFindings.has(mathDigest(node.finding)) ?
      { ...node, finding: undefined } : node;
    const deliveryIds = new Set(deliveries.map(item => item.id));
    const proofRoutes = (this.archive.proofRoutes ?? this.archive.tasks.flatMap(node => node.alternativeRoutes ?? []))
      .filter(route => visibleIds.has(route.targetTaskId) &&
        [route.closingTaskId, ...route.prerequisiteTaskIds].every(id => visibleIds.has(id)));
    const scopedTasks = tasks.map(node => scopedFinding(node.alternativeRoutes?.length ? { ...node,
      alternativeRoutes: proofRoutes.filter(route => route.targetTaskId === node.task.id) } : node));
    return { ...this.archive, tasks: scopedTasks,
      deliveryReceipts: this.archive.deliveryReceipts?.filter(receipt => worker && receipt.workerId === worker.id &&
        receipt.environmentDigest === this.input.state.environmentDigest &&
        (action?.kind === 'task' ? receipt.assignmentKey === assignmentDeliveryFile(action.assignment) :
          visible(receipt.taskId, receipt.taskDigest))),
      proofReadyRecords: this.archive.proofReadyRecords?.filter(receipt =>
        (action?.kind === 'lead' || worker?.id === this.lead.id || worker && receipt.workerId === worker.id &&
          (action?.kind !== 'task' || receipt.assignmentKey === assignmentDeliveryFile(action.assignment))) &&
        receipt.problemReceiptDigest === this.input.state.problem.receiptDigest &&
        receipt.environmentDigest === this.input.state.environmentDigest),
      lastStagnationRecovery: action?.kind === 'lead' || worker?.id === this.lead.id ? this.archive.lastStagnationRecovery : undefined,
      parallelQuestions: parallelQuestions(this.archive.tasks, task).filter(question => !ordinaryWorker || task ||
        versions.get(question.taskId)?.task.sharing !== 'group'),
      consumerInterfaces: task ? taskConsumerProjection(task, this.archive.tasks, this.archive.proofRoutes) : undefined,
      mathematicalGaps: mathematicalGaps(this.archive, { problemReceiptDigest: this.input.state.problem.receiptDigest,
        environmentDigest: this.input.state.environmentDigest }, gapViewer),
      researchDecisions: this.archive.researchDecisions && (tasks === this.archive.tasks ?
        normalizedResearchHandoffDecisions(this.archive).filter(item => deliveryIds.has(item.deliveryId)) :
        scopeResearchHandoffDecisions(this.archive, { tasks: scopedTasks, deliveries })),
      challengeDecisions: this.archive.challengeDecisions?.filter(item => deliveryIds.has(item.deliveryId)),
      frontierRecoveries: tasks === this.archive.tasks ? this.archive.frontierRecoveries : undefined,
      failedTaskInputs: this.archive.failedTaskInputs?.filter(record => tasks === this.archive.tasks || visible(record.taskId, record.taskDigest)),
      progressSnapshot: tasks === this.archive.tasks ? this.archive.progressSnapshot : undefined,
      progressReceipts: tasks === this.archive.tasks ? this.archive.progressReceipts : undefined,
      blockers: this.archive.blockers?.filter(blocker => tasks === this.archive.tasks ||
        (visibleIds.has(blocker.taskId) && task && blocker.groupId === taskGroup(task))),
      proofRoutes,
      unchangedResearch: this.archive.unchangedResearch && Object.fromEntries(Object.entries(this.archive.unchangedResearch)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      researchCheckpoints: this.archive.researchCheckpoints && Object.fromEntries(Object.entries(this.archive.researchCheckpoints)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      researchDrafts: this.archive.researchDrafts && Object.fromEntries(Object.entries(this.archive.researchDrafts)
        .filter(([id, record]) => visible(id, record.taskDigest))),
      // Public progress can steer another route before its proof is complete; it remains advisory.
      deliveries,
      history: (tasks === this.archive.tasks ? this.archive.history : this.archive.history?.filter(item =>
        visible(item.task.id, digest(item.task))))?.map(scopedFinding),
      statementReviews: this.archive.statementReviews?.filter(item => item.status !== 'superseded' && visible(item.taskId, item.taskDigest)) };
  }
  private async deliverLead(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, commit: string,
    recovering: boolean, recoveryKind: 'checkpoint' | 'request-failure' | 'scheduling-checkpoint'): Promise<{ checkWhole: boolean; savedPlan?: boolean }> {
    const staged = await this.input.exclusiveCheck(async () => {
      if (!this.current(action)) {
        this.input.emit('lead_decision_superseded', { commit }); this.syncPlanNotes(); this.needsLead = true; this.changed();
        return { finished: true as const, checkWhole: false };
      }
      if (action.recovery && recovering) {
        this.interrupted(worker, action);
        return { finished: true as const, checkWhole: false };
      }
      const sourceChanged = ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
        ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
      let recoveryPlan: ReturnType<typeof parseCooperationPlan> | undefined;
      let resolution: ReturnType<CooperationPlanning['validateRecoveryPlan']> | undefined;
      if (action.recovery) {
        const recovery = this.archive.frontierRecoveries?.find(item => item.id === action.recovery!.id);
        try {
          const response = block(worker.worktree, 'math-plan');
          recoveryPlan = parseCooperationPlan(this.input.state.problem, response);
          resolution = this.validateRecoveryPlan(action, recoveryPlan, response.recovery);
        } catch (error) {
          if (!recovery || recovery.status !== 'requested') {
            this.input.emit('lead_decision_superseded', { commit }); this.needsLead = true; this.changed();
            return { finished: true as const, checkWhole: false };
          }
          if (!(error instanceof Error && error.message === 'math_frontier_recovery_no_executable_step')) {
            this.rejectPlan(error);
            if (!this.archive.planRejection?.stalled) { this.changed(); return { finished: true as const, checkWhole: false }; }
          }
          resolution = { recovery, taskIds: [], reason: error instanceof Error ? error.message : 'math_frontier_recovery_invalid' };
        }
        if (!resolution.taskIds.length) {
          if (action.handoffIds?.length || action.challengeIds?.length) {
            try {
              const response = block(worker.worktree, 'math-plan');
              this.recordAdvisoryDecisions(this.resolveAdvisoryDecisions(action, this.archive.tasks.map(node => node.task), response), true, action);
            } catch (error) {
              this.rejectPlan(error); this.changed(); return { finished: true as const, checkWhole: false };
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
          this.changed(); return { finished: true as const, checkWhole: false };
        }
      }
      let accepted = false;
      let assessmentDecision = false;
      const publishedPlan = this.planSnapshot(action);
      const previousPlanVersion = this.planVersion();
      const previousDecisions = canonicalMathJson([this.archive.researchDecisions ?? [], this.archive.challengeDecisions ?? []]);
      try {
        const schedulingDraft = recovering && recoveryKind === 'scheduling-checkpoint' && !action.initialPlanNonce &&
          !publishedPlan && this.archive.tasks.length > 0;
        const notesFile = path.join(worker.worktree, 'RESEARCH.md');
        const savedNotes = (publishedPlan || schedulingDraft) && fs.existsSync(notesFile)
          ? readMathText(notesFile, MAX_RESEARCH_NOTES_BYTES) : '';
        let unchangedCheckpoint = false;
        if (schedulingDraft) {
          try {
            const seedNotes = git(worker.worktree, ['ls-tree', '--name-only', action.seedCommit, '--', 'RESEARCH.md'])
              ? committedSource(worker.worktree, action.seedCommit, 'RESEARCH.md') : '';
            unchangedCheckpoint = this.proposedPlanDigest(seedNotes) === this.proposedPlanDigest(savedNotes);
          } catch { /* Without a readable dispatch baseline, validate the saved response normally. */ }
        }
        const notes = savedNotes.trimStart();
        const hasFinalPlan = this.publishedPlans.get(action)?.responseDigest !== this.proposedPlanDigest() &&
          (notes.startsWith('{') || /```(?:math|json|math-plan)\s*\n/u.test(notes));
        let assessmentResponse: any, assessmentPlanResponse: any;
        if (!unchangedCheckpoint && action.kind === 'lead' && (action.capacityRefill || action.stagnationRecovery)) {
          try {
            const response = block(worker.worktree, 'math-plan');
            if (response.kind === 'assessment') assessmentResponse = response;
            else assessmentPlanResponse = response;
          } catch { /* The ordinary final-plan path owns non-assessment response validation. */ }
        }
        if (unchangedCheckpoint) {
          // Inherited control notes are a draft, not a fresh response to this inbox.
          // Continue below so saved Lean source changes still take the ordinary merge path.
          this.pin(commit); this.needsLead = true;
          this.input.emit('lead_checkpoint_saved', { commit, seedCommit: action.seedCommit,
            reason: 'unchanged-control-response' });
        } else if (assessmentResponse) {
          assessmentDecision = this.acceptLeadAssessment(action, assessmentResponse);
        } else if (publishedPlan && !hasFinalPlan) {
          // A published immutable event remains useful when the continued writer only saves notes.
          accepted = true;
        } else if (action.handoffIds?.length || retainedResearchHandoffs(this.archive).length ||
            action.challengeIds?.length || retainedResearchChallenges(this.archive).length) {
          const response = block(worker.worktree, 'math-plan');
          const plan = recoveryPlan ?? parseCooperationPlan(this.input.state.problem, response);
          const decided = this.resolveAdvisoryDecisions(action, plan.tasks, response, plan);
          const assessments = response.assessments === undefined ? undefined :
            this.validateLeadAssessments(action, response.assessments, decided);
          await this.acceptPlan(plan, undefined, undefined, decided, action);
          if (assessments) { this.completeLeadAssessments(action, assessments); assessmentDecision = true; }
        } else {
          const assessments = assessmentPlanResponse?.assessments === undefined ? undefined :
            this.validateLeadAssessments(action, assessmentPlanResponse.assessments);
          await this.acceptPlan(recoveryPlan);
          if (assessments) { this.completeLeadAssessments(action, assessments); assessmentDecision = true; }
        }
        if (!unchangedCheckpoint) accepted = true;
      } catch (error) {
        if (recovering) {
          // A checkpoint or failed request may leave only a partial graph. Keep it resumable.
          this.archive.planRejection = undefined;
          const reason = error instanceof Error ? error.message : 'math_plan_incomplete';
          this.input.emit('plan_rejected', { proposalDigest: this.proposedPlanDigest(), inputDigest: this.planningInputDigest(),
            error: reason, stalled: false, incomplete: true, recoveryKind });
          this.preserveLeadDraft(commit, action.seedCommit, reason);
        } else this.rejectPlan(error);
        if (!this.archive.tasks.length && !(recovering && recoveryKind === 'request-failure')) {
          try { await this.startInitialTasks(); }
          catch (fallbackError) { this.input.emit('initial_plan_fallback_failed', {
            reason: fallbackError instanceof Error ? fallbackError.message : 'math_initial_plan_failed' }); }
        }
      }
      const decisionProgress = Boolean(publishedPlan) || assessmentDecision || accepted &&
        (previousPlanVersion !== this.planVersion() ||
          previousDecisions !== canonicalMathJson([this.archive.researchDecisions ?? [], this.archive.challengeDecisions ?? []]));
      const savedPlan = recovering && recoveryKind === 'request-failure' && decisionProgress;
      if (accepted && !recovering && action.kind === 'lead') {
        const nonce = action.initialPlanNonce ?? action.planNonce;
        for (const publication of [this.archive.planPublication, this.archive.initialPlanPublication])
          if (nonce && publication?.nonce === nonce) publication.finalized = true;
      }
      if (accepted && resolution) {
        resolution.recovery.status = 'planned'; resolution.recovery.readyTaskIds = resolution.taskIds;
        this.input.emit('frontier_recovery_planned', { recoveryId: resolution.recovery.id,
          taskIds: resolution.recovery.taskIds, readyTaskIds: resolution.taskIds });
        this.changed();
      }
      if (accepted && (!recovering || decisionProgress)) this.rememberLeadDecision(action);
      if (accepted && (!recovering || decisionProgress)) this.markCapacityRefillAssessed(action);
      this.changed();
      if (accepted) this.rememberCoordinationCompletion(action, decisionProgress);
      return { finished: false as const, sourceChanged, savedPlan, planVersion: this.archive.planVersion };
    });
    if (staged.finished) return { checkWhole: false };
    const saved = staged.savedPlan ? { savedPlan: true } : {};
    if (!staged.sourceChanged) return { checkWhole: false, ...saved };
    try {
      for (;;) {
        const snapshot = await this.input.exclusiveCheck(async () => {
          if (this.archive.planVersion !== staged.planVersion) {
            this.preserveLeadDraft(commit, action.seedCommit, 'math_lead_decision_superseded', false); this.changed(); return;
          }
          return { canonical: this.archive.canonicalCommit!, environmentDigest: this.input.state.environmentDigest,
            problemReceiptDigest: this.input.state.problem.receiptDigest };
        });
        if (!snapshot) return { checkWhole: false, ...saved };
        const merged = await this.mergeLeadSources(commit, action.seedCommit, snapshot.canonical);
        const published = await this.input.exclusiveCheck(async () => {
          this.input.signal.throwIfAborted();
          if (this.archive.planVersion !== staged.planVersion) {
            this.preserveLeadDraft(commit, action.seedCommit, 'math_lead_decision_superseded', false); this.changed(); return 'superseded';
          }
          if (this.archive.canonicalCommit !== snapshot.canonical || this.input.state.environmentDigest !== snapshot.environmentDigest ||
              this.input.state.problem.receiptDigest !== snapshot.problemReceiptDigest) return 'retry';
          this.archive.canonicalCommit = merged;
          const integrated = new Set(this.archive.tasks.filter(node => node.status === 'integrated').map(node => node.task.id));
          this.markPendingValidation(this.archive.tasks.filter(node => integrated.has(node.task.id) || node.task.statementReview), integrated);
          this.changed(); return 'published';
        });
        if (published === 'retry') continue;
        if (published === 'superseded') return { checkWhole: false, ...saved };
        await this.schedulePlanSynchronization();
        return await this.input.exclusiveCheck(async () => {
          if (this.archive.planVersion !== staged.planVersion || this.candidateSynchronizationBlocked()) return { checkWhole: false, ...saved };
          const problem = this.input.state.problem;
          const unchangedDraft = git(worker.worktree, ['rev-parse', 'HEAD']) === commit && problem.ownedFiles.every(file => {
            const local = path.join(worker.worktree, problem.projectRelative, file);
            return fs.existsSync(local) && fs.readFileSync(local, 'utf8') === committedSource(worker.worktree, commit, `${problem.projectRelative}/${file}`);
          });
          if (unchangedDraft) this.archive.canonicalCommit = this.seed(worker, this.archive.canonicalCommit!);
          this.changed(); return { checkWhole: unchangedDraft, ...saved };
        });
      }
    } catch (error) {
      this.input.signal.throwIfAborted();
      if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
      await this.input.exclusiveCheck(async () => {
        this.preserveLeadDraft(commit, action.seedCommit, error instanceof Error ? error.message : 'math_lead_integration_failed',
          this.archive.planVersion === staged.planVersion);
        this.changed();
      });
      return { checkWhole: false, ...saved };
    }
  }
  async deliver(worker: ResearchWorker, action: CooperativeAction, commit: string, recovering = false,
    recoveryKind: 'checkpoint' | 'request-failure' | 'scheduling-checkpoint' = 'checkpoint'): Promise<{ check?: ProofCheck; checkWhole: boolean; savedPlan?: boolean }> {
    if (isStatementAction(action)) return this.deliverStatement(worker, action);
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
      const pending = this.deliverLead(worker, action, commit, recovering, recoveryKind);
      this.leadDeliveries.add(pending);
      try { return await pending; } finally { this.leadDeliveries.delete(pending); this.wake(); }
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
          if (recoveryKind === 'checkpoint') this.researchCheckpoint(worker, action, commit);
          else this.interrupted(worker, action);
          return { checkWhole: false };
        }
        taskChanges(this.input.state.problem, worker.worktree, commit, node.task, action.assignment);
        const notesBlob = (version: string) => git(worker.worktree, ['ls-tree', '--format=%(objectname)', version, '--', 'RESEARCH.md']);
        const inherited = notesBlob(action.assignment.seedCommit);
        if (inherited === notesBlob(commit)) {
          unchangedNotesBlob = inherited;
          throw new Error('math_research_delivery_unchanged: Replace inherited RESEARCH.md with findings for the current task.');
        }
        await this.publishResearchFinding(worker, action, commit,
          { kind: 'notes', text: committedSource(worker.worktree, commit, 'RESEARCH.md') }, { artifacts });
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
      if (advisory(node.task)) {
        this.rejectWorkerDelivery(worker, action, committedSource(worker.worktree, commit, 'RESEARCH.md'), error);
        this.input.save();
      }
      if (artifacts?.artifacts.length) this.record(worker, node.task, 'progress', 'advisory',
        'Recoverable supporting code retained after an incomplete or rejected delivery; it still requires typed host checking.',
        { commit, artifacts, remainingObligations: [node.task.id] });
      if (error instanceof ResearchAdmissionError) {
        // A malformed report is corrected by the same writer, not a mathematical route failure.
        this.preserveResearchDraft(worker, action, commit, artifacts);
        this.interrupted(worker, action);
        return { checkWhole: false };
      }
      if (recovering && recoveryKind === 'request-failure' && feedback.startsWith('math_task_repeated_failed_input\n') &&
          this.restoreInterruptedRepair(worker, action, commit)) {
        return { checkWhole: false };
      }
      if (recovering && feedback.startsWith('math_task_missing_declaration\n')) {
        if (this.continueTaskCheckpoint(worker, node, commit)) {
          node.feedback = feedback; this.interrupted(worker, action);
        } else this.rejected(action, feedback, commit);
        return { checkWhole: false };
      }
      if (/^math_task_(?:missing_declaration|repeated_failed_input)\n/u.test(feedback) || isTaskSourceRepairFeedback(feedback))
        this.rejected(action, feedback, commit, recovering);
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
  rejected(action: CooperativeAction, feedback: string, commit?: string, incomplete = false) {
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
      if (incomplete) this.restoreTaskSourceRepair(node);
      else this.settleTaskSourceRepair(node);
      if (isTaskSourceRepairFeedback(feedback)) localRepair = this.retryTaskSourceLocally(node);
      else if (/^math_task_(?:missing_declaration|repeated_failed_input)\n/u.test(feedback)) {
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
    if (this.failure || this.stopping || !this.liveWorkers.has(worker.id) || !this.liveWorkers.has(this.lead.id)) return false;
    if (this.refreshFeasibilityAssignments()) this.changed();
    if (!this.current(action)) return false;
    if (action.kind === 'task' && action.assignment.workerId !== worker.id) throw new Error('math_task_assignment_invalid');
    if (action.kind === 'review' && this.archive.review?.workerId !== worker.id) throw new Error('math_review_assignment_invalid');
    if (isStatementAction(action) && this.archive.statementReviews?.find(item => item.id === action.reviewId)?.workerId !== worker.id)
      throw new Error('math_statement_review_assignment_invalid');
    if (action.kind === 'task' &&
        assessTaskResponsibility(this.node(action.task.id), worker, this.archive).kind !== 'matches') return false;
    const task = action.kind === 'task' ? action.task : isStatementAction(action) ? this.node(action.taskId).task : undefined;
    if (task && this.synchronizationBlocked(task) || (action.kind === 'review' || action.kind === 'assemble') &&
        this.candidateSynchronizationBlocked()) return false;
    const route = task && this.archive.groups?.find(record => record.group.id === taskGroup(task));
    const fixedStatement = isStatementAction(action) && this.fixedStatementReviewTasks()?.get(action.taskId) === action.taskDigest;
    if (route && !fixedStatement && (route.group.status !== 'active' || route.turns >= (route.group.maxTurns ?? Infinity))) return false;
    if (route && !fixedStatement) route.turns++;
    if (action.kind === 'task') {
      const node = this.node(action.task.id);
      const sourceRepair = this.currentTaskSourceRepair(node);
      if (sourceRepair?.pending) { sourceRepair.pending = false; sourceRepair.startedAttempt = node.attempts + 1; }
      for (const record of this.archive.failedTaskInputs ?? []) if (this.pendingTaskRepair(node, record)) {
        record.repair!.pending = false; record.repair!.startedAttempt = node.attempts + 1;
      }
      node.attempts++;
    }
    this.changed(); return true;
  }
  stopped(worker: ResearchWorker, error?: string) {
    this.clearDispatchWait(worker, 'stopped');
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
