import { parseCooperationPlan, isAdvisoryTask as advisory } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { mathGitResult } from '../math/mathGit';
import { commitSolverSources, withSolverWorktree } from './problem';
import { type ResearchWorker } from './modules/organization';
import { taskCanStart } from './modules/search';
import { deliveryDetails, readDeliveryLines } from './deliveries';
import { isStatementAction } from './statementReview';
import { captureDeliveryArtifacts } from './deliveryArtifacts';
import { researchHandoffs, resolveResearchHandoffs, type ResearchHandoffDecision } from './researchHandoffs';
import { preserveResearchChallengeBacklog, resolveResearchChallenges, type ResearchChallengeDecision } from './researchChallenges';
import { bindMathematicalGap } from './mathematicalGaps';
import { assignmentDeliveryFile, leadPlanDeliveryFile, type CooperativeTask, type TaskRecord, type CooperativeAction } from './tasks';
import { digest, directDeliveryRejections, rejectionCode, HumanEditRecord, TaskVersions, bounded } from './cooperationShared';
import { CooperationPlanning } from './cooperationPlanning';
import { composeHandoffPublication } from './handoffPublication';
import { finishLeadAssessment, type LeadAssessmentKind } from './leadAssessment';
import { pendingResearchHandoffs } from './researchHandoffs';
import { pendingResearchChallenges } from './researchChallenges';
import { prepareResearchDelivery, ResearchAdmissionError } from './researchAdmission';

/** Worker delivery intake. */
export abstract class CooperationInputs extends CooperationPlanning {
  /** A scheduling decision does not edit the task graph or grant proof acceptance. */
  protected acceptLeadAssessment(action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>, response: any): void {
    const invalid = (reason: string) => new Error('math_plan_assessment_' + reason);
    const keys = (value: any, allowed: readonly string[]) => value && typeof value === 'object' && !Array.isArray(value) &&
      Object.keys(value).every(key => allowed.includes(key));
    if (action.kind !== 'lead' || action.initialPlanNonce || action.recovery || !action.planNonce ||
        !keys(response, ['kind', 'dispatchNonce', 'baseVersion', 'summary', 'assessments']) || response.kind !== 'assessment' ||
        response.dispatchNonce !== action.planNonce || response.baseVersion !== action.planVersion ||
        response.baseVersion !== this.archive.planVersion || !this.current(action) || !Array.isArray(response.assessments))
      throw invalid('invalid');
    if (action.handoffIds?.length || action.challengeIds?.length || pendingResearchHandoffs(this.archive).length ||
        pendingResearchChallenges(this.archive).length) throw invalid('inbox_unresolved');
    const requests = [['capacity', action.capacityRefill, this.archive.lastCapacityRefill],
      ['stagnation', action.stagnationRecovery, this.archive.lastStagnationRecovery]] as const;
    const expected = requests.filter(([, request]) => request);
    if (!expected.length || response.assessments.length !== expected.length) throw invalid('request_count');
    const seen = new Set<LeadAssessmentKind>();
    for (const item of response.assessments) {
      const entry = expected.find(([kind]) => kind === item?.kind);
      if (!entry || seen.has(item.kind) || !keys(item, ['kind', 'requestId', 'inputDigest', 'outcome', 'reason']) ||
          item.outcome !== 'no-independent-work' || typeof item.reason !== 'string' || !item.reason.trim() ||
          item.reason.length > 12000) throw invalid('invalid');
      const [, request, receipt] = entry;
      if (!request.requestId || item.requestId !== request.requestId || item.inputDigest !== request.inputDigest ||
          receipt?.requestId !== request.requestId || receipt.inputDigest !== request.inputDigest ||
          receipt.dispatchNonce !== action.planNonce || receipt.status === 'assessed' &&
          (receipt.outcome !== 'no-independent-work' || receipt.decisionReason !== item.reason)) throw invalid('superseded');
      seen.add(item.kind);
    }
    // Validate the complete batch before acknowledging any request.
    for (const [kind, request, receipt] of expected) {
      const item = response.assessments.find((item: any) => item.kind === kind);
      if (finishLeadAssessment(receipt, request, action.planNonce,
        { at: Date.now(), outcome: 'no-independent-work', reason: item.reason }))
        this.input.emit(kind === 'capacity' ? 'capacity_refill_assessed' : 'stagnation_recovery_assessed',
          { ...receipt, evidenceStatus: 'advisory' });
    }
    if (action.planningInputDigest) this.archive.lastLeadInputDigest =
      this.leadEvidence.get(action) === this.planningEvidenceDigest() ? this.planningInputDigest() : action.planningInputDigest;
    this.changed();
  }
  protected syncEditChecks(nodes: ReadonlyMap<string, TaskRecord>, versions: TaskVersions) {
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
        const fresh = !node.pendingValidation && proof && proof.taskDigest === result.taskDigest && this.checkedDeliveries.has(proof);
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
  protected inputs() {
    return this.pendingPulse ??= this.readInputs().finally(() => { this.pendingPulse = undefined; });
  }
  /** Serialize input edits while allowing independent proof checks to continue. */
  private async readInputs(): Promise<ReadonlyMap<string, Promise<void>>> {
    if (this.archive.tasks.some(node => node.pendingValidation) || this.archive.edits?.some(edit => edit.status === 'applied' && edit.pendingSync))
      this.schedulePlanSynchronization();
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
          if (record.status === 'applied' && record.pendingSync) {
            this.schedulePlanSynchronization();
            this.input.emit('edit_applied', { id, planVersion: record!.planVersion, affectedTasks: record!.affectedTasks, recheck: record!.recheck });
          }
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
            !/^math_(?:edit_(?:invalid(?:_json|_id)?|version_conflict)$|plan_[a-z_]+(?:$|:))/u.test(reason)) throw error;
        if (record) { record.status = 'rejected'; record.reason = reason; }
        else (this.archive.edits ??= []).push({ id, status: 'rejected', reason, receivedAt: Date.now() });
        this.changed();
        this.input.emit('edit_rejected', { id, reason });
      }
      advance(entry.offset);
    }
    await this.readPlanDelivery(cursors);
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
  private async readPlanDelivery(cursors: Record<string, number>) {
    const action = this.active.get(this.lead.id)?.action;
    if (!action || action.kind !== 'lead') return;
    const file = leadPlanDeliveryFile(action);
    if (!file) return;
    const initial = Boolean(action.initialPlanNonce), nonce = action.initialPlanNonce ?? action.planNonce!;
    const code = (reason: string) => `math_${initial ? 'initial_plan' : 'plan_publication'}_${reason}`;
    const key = `${this.lead.id}/${file}`, discardKey = `${key}/discardingOversized`;
    const batch = readDeliveryLines(path.join(this.lead.worktree, file), cursors[key] ?? 0,
      { discardingOversized: cursors[discardKey] === 1 });
    let advanced = false;
    const reject = (reason: string) => this.input.emit(initial ? 'initial_plan_rejected' : 'plan_publication_rejected',
      { workerId: this.lead.id, file, reason });
    try {
      for (const entry of batch.entries!) {
        this.input.signal.throwIfAborted();
        if (entry.error) reject(entry.error);
        else if (entry.line?.trim()) {
          // Only a complete explicit event is parsed; RESEARCH.md remains an unpublished draft.
          const eventDigest = mathDigest(entry.line);
          let response: any;
          try { response = JSON.parse(entry.line); }
          catch { reject(code('invalid_json')); }
          if (response !== undefined) {
            try {
              if (!response || typeof response !== 'object' || Array.isArray(response) || !['plan', 'handoff', 'assessment'].includes(response.kind) ||
                  typeof response.baseVersion !== 'string' || !initial && response.dispatchNonce !== nonce)
                throw new Error(code('invalid'));
              const details = deliveryDetails(response);
              await this.input.exclusiveCheck(async () => {
                const publication = this.archive.planPublication ?? this.archive.initialPlanPublication;
                if (publication?.nonce === nonce && publication.eventDigest === eventDigest) return;
                if (publication?.nonce === nonce || initial && (this.archive.initialPlanPublication || this.archive.tasks.length) || action.recovery ||
                    this.active.get(this.lead.id)?.action !== action || !this.current(action))
                  throw new Error(code('superseded'));
                if (!action.planVersion || response.baseVersion !== action.planVersion ||
                    response.baseVersion !== this.archive.planVersion) throw new Error(code('version_conflict'));
                if (response.kind === 'assessment') {
                  this.acceptLeadAssessment(action, response);
                  this.input.emit('lead_assessment_published', { workerId: this.lead.id, file, eventDigest,
                    dispatchNonce: nonce, summary: details.summary });
                  return;
                }
                // Compose against the current graph only after acquiring the same CAS lock as full plans and human edits.
                const handoff = response.kind === 'handoff' ? composeHandoffPublication(this.input.state.problem, this.archive, {
                  tasks: this.plannedTasks().map(node => node.task), groups: this.archive.groups?.map(route => route.group),
                  proofRoutes: this.archive.proofRoutes,
                }, action, response) : undefined;
                const plan = handoff?.plan ?? parseCooperationPlan(this.input.state.problem, response);
                const decisions = handoff?.decisions ?? this.resolveAdvisoryDecisions(action, plan.tasks, response, plan);
                if (handoff) this.preserveAdvisoryBacklogs(plan, decisions.handoffs, []);
                await this.acceptPlan(plan, undefined, { action, receipt: { nonce, file,
                  offset: entry.offset, eventDigest, baseVersion: response.baseVersion, acceptedAt: Date.now() } }, decisions);
                this.markCapacityRefillAssessed(action);
                this.changed();
                this.input.emit(initial ? 'initial_plan_published' : 'plan_published', { ...this.archive.planPublication,
                  workerId: this.lead.id, summary: details.summary, taskIds: plan.tasks.map(task => task.id),
                  ...(handoff ? { publicationKind: 'handoff', adoptedTaskIds: handoff.adoptedTaskIds } : {}) });
              });
            } catch (error) {
              this.input.signal.throwIfAborted();
              if (!(error instanceof Error) || !/^math_(?:initial_plan_|plan_|handoff_|challenge_|delivery_invalid)/u.test(error.message)) throw error;
              reject(error.message);
            }
          }
        }
        cursors[key] = entry.offset; cursors[discardKey] = entry.discardingOversized ? 1 : 0; advanced = true;
      }
      if (cursors[key] !== batch.offset || (cursors[discardKey] === 1) !== batch.discardingOversized) advanced = true;
      cursors[key] = batch.offset; cursors[discardKey] = batch.discardingOversized ? 1 : 0;
    } finally { if (advanced) this.input.save(); }
  }
  protected preserveHandoffBacklog(plan: ReturnType<typeof parseCooperationPlan>, decisions: readonly ResearchHandoffDecision[]) {
    const decided = new Map(decisions.map(decision => [decision.id, decision]));
    const remaining = researchHandoffs(this.advisoryArchiveForPlan(plan)).filter(item => {
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
  /** A replacement plan must keep every queued handoff and challenge decidable (handoffs checked first). */
  protected preserveAdvisoryBacklogs(plan: ReturnType<typeof parseCooperationPlan>, handoffs: readonly ResearchHandoffDecision[] = [],
    challenges: readonly ResearchChallengeDecision[] = []) {
    this.includeCapacityExplorations(plan);
    this.preserveHandoffBacklog(plan, handoffs);
    preserveResearchChallengeBacklog(this.advisoryArchiveForPlan(plan), plan.tasks, plan.proofRoutes, challenges);
  }
  /** Resolve a lead response's handoff and challenge decisions, checking both backlogs against a replacement plan. */
  protected resolveAdvisoryDecisions(action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>,
    tasks: readonly CooperativeTask[], response: { handoffDecisions?: unknown; challengeDecisions?: unknown },
    plan?: ReturnType<typeof parseCooperationPlan>) {
    if (plan) { this.includeCapacityExplorations(plan); tasks = plan.tasks; }
    // Explicit decisions apply to the immutable inbox actually shown at dispatch.
    // The candidate retirement view is only for preserving unseen backlogs below.
    const handoffs = resolveResearchHandoffs(this.archive, action.handoffIds ?? [], tasks, response.handoffDecisions, action.handoffActivations);
    const challenges = resolveResearchChallenges(this.archive, action.challengeIds ?? [], action.challengeActivations ?? {},
      tasks, response.challengeDecisions);
    if (plan) this.preserveAdvisoryBacklogs(plan, handoffs, challenges);
    return { handoffs, challenges };
  }
  private async readWorkerDeliveries(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, cursors: Record<string, number>) {
    const invalidInput = new Set([...directDeliveryRejections, 'math_delivery_invalid_commit',
      'math_delivery_requires_fixed_proof', 'math_delivery_unfinished_dependencies', 'math_route_blocker_invalid']);
    let advanced = false;
    const reject = (reason: Error | string, submission: string) => {
      const error = typeof reason === 'string' ? new Error(reason) : reason;
      this.rejectWorkerDelivery(worker, action, submission, error);
      this.input.emit('delivery_rejected', { workerId: worker.id, reason: error.message });
    };
    try {
      for (const log of [assignmentDeliveryFile(action.assignment), 'DELIVERIES.jsonl']) {
        const scoped = log !== 'DELIVERIES.jsonl', key = scoped ? `${worker.id}/${log}` : worker.id;
        const discardKey = `${key}/discardingOversized`;
        const batch = readDeliveryLines(path.join(worker.worktree, log), cursors[key] ?? 0,
          { discardingOversized: cursors[discardKey] === 1 });
        for (const entry of batch.entries!) {
          this.input.signal.throwIfAborted();
          if (entry.error) reject(entry.error, `${key}:${entry.offset}:${entry.error}`);
          else if (entry.line?.trim()) {
            let value: unknown;
            try { value = JSON.parse(entry.line); }
            catch { reject('math_delivery_invalid_json', entry.line); }
            if (value !== undefined) {
              try { await this.receive(worker, action, value, scoped); }
              catch (error) {
                this.input.signal.throwIfAborted();
                if (!(error instanceof Error) || !invalidInput.has(rejectionCode(error))) throw error;
                reject(error, entry.line);
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
    await this.notifyDeliveryReceipts(worker, action);
  }
  private async receive(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, value: any, scoped = false) {
    if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_delivery_invalid');
    const assignmentKey = assignmentDeliveryFile(action.assignment);
    const automaticId = scoped ? mathDigest(canonicalMathJson({ file: assignmentKey, value })) : undefined;
    if (scoped) value = { id: automaticId, kind: 'progress', taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, ...value };
    const details = deliveryDetails(value);
    if (!value || typeof value.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(value.id) ||
        !['progress', 'proof', 'research', 'ready'].includes(value.kind) || value.taskId !== action.task.id || value.taskDigest !== action.assignment.taskDigest) throw new Error('math_delivery_invalid');
    if (value.kind === 'ready') {
      if (!scoped || advisory(action.task) || value.commit !== undefined || value.targets !== undefined)
        throw new Error('math_delivery_invalid');
      this.receiveProofReady(worker, action, value.id);
      return;
    }
    // Legacy automatic ids already bind the assignment; unscoped old ids cannot identify a new seed.
    const duplicate = this.archive.deliveries?.find(record => record.producer === worker.id && record.submissionId === value.id &&
      record.taskId === action.task.id && record.taskDigest === action.assignment.taskDigest &&
      (record.assignmentKey === assignmentKey || record.assignmentKey === undefined && scoped && value.id === automaticId));
    if (duplicate) {
      const replayed = this.node(action.task.id);
      const resumable = replayed?.assignment === action.assignment && duplicate.status !== 'superseded' &&
        this.proofDeliveryCurrent(replayed) &&
        (duplicate.commit === replayed.proof?.commit || duplicate.commit === replayed.integratedCheck?.commit);
      if (value.kind === 'proof' && duplicate.kind === 'proof' && (this.current(action) || resumable)) {
        await this.settleProofDeliveries(annotations => this.queueIntegration(async () => {
          const node = this.node(action.task.id);
          // Resume the accepted submission, never a changed commit in the replayed line.
          if (node?.assignment === action.assignment && duplicate.status !== 'superseded' &&
              (duplicate.commit === node.proof?.commit || duplicate.commit === node.integratedCheck?.commit)) {
            const annotate = await this.publishProofDelivery(node);
            if (annotate) annotations.push(annotate);
          }
          await this.integrateReadyNow(annotations);
        }));
      }
      return;
    }
    if (!this.current(action)) {
      this.record(worker, action.task, value.kind, 'superseded', details.summary, { ...details, submissionId: value.id, assignmentKey,
        taskDigest: action.assignment.taskDigest, premises: action.task.premises ?? [], dependencies: action.assignment.dependencies ?? [],
        remainingObligations: details.remainingObligations ?? [] });
      return;
    }
    const node = this.node(action.task.id);
    if (value.kind === 'research') {
      if (!value.finding || typeof value.finding !== 'object' || Array.isArray(value.finding))
        throw new Error('math_research_delivery_invalid');
      const admission = prepareResearchDelivery({ kind: 'event', value: value.finding }, { source: node.task,
        assignment: action.assignment, tasks: this.archive.tasks, deliveries: this.archive.deliveries,
        identity: { problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest } });
      if (admission.status === 'rejected') throw new ResearchAdmissionError(admission);
      const finding = admission.finding;
      const base = value.commit ?? action.assignment.seedCommit;
      if (typeof base !== 'string' || !/^[a-f0-9]{40,64}$/u.test(base)) throw new Error('math_delivery_invalid_commit');
      const fixed = mathGitResult(worker.worktree, ['merge-base', '--is-ancestor', action.assignment.seedCommit, base], { maxBuffer: 4096 });
      if (fixed.error) throw fixed.error;
      if (fixed.status !== 0) throw new Error('math_delivery_invalid_commit');
      const supportingArtifacts = value.commit ? captureDeliveryArtifacts({ problem: this.input.state.problem,
        worktree: worker.worktree, commit: base, assignment: action.assignment }) : undefined;
      // Freeze the explicit event in a disposable checkout; the worker keeps its live files and Git index.
      await withSolverWorktree(worker.worktree, base, async checkout => {
        fs.writeFileSync(path.join(checkout, 'RESEARCH.md'), JSON.stringify(finding));
        const commit = commitSolverSources(this.input.state.problem, checkout);
        if (!this.current(action)) return;
        await this.publishResearchFinding({ ...worker, worktree: checkout }, action, commit, finding, false,
          { submissionId: value.id, assignmentKey, ...(supportingArtifacts ? { artifacts: supportingArtifacts } : {}) });
      });
      return;
    }
    if (value.kind === 'progress') {
      if (details.mathematicalGap) bindMathematicalGap(details.mathematicalGap, node.task, this.archive,
        { problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest });
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
}
