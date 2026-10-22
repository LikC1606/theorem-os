import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { committedSource, commitSolverSources, withSolverWorktree } from './problem';
import { solverProofFeedback } from './feedback';
import { taskDependenciesReady } from './modules/search';
import { applyTaskChanges, checkTaskProof, checkTaskProofs, createTaskSourceProjector, isAttributedTaskProof, type TaskProof } from './cooperativeProof';
import { hasDeterministicLeanFailure } from './proofReuse';
import { proofReferencesUnchanged } from './proofReferences';
import { attributeTaskReferences } from './taskReferenceAttribution';
import { hasTaskConnectionCheck } from './taskConnections';
import { taskGroup, taskReferenceDependencies, hasTaskAcceptance, assignmentDeliveryFile, type CooperativeTask, type TaskAssignment, type TaskRecord } from './tasks';
import { digest, taskSourceRejections, integrationRejections, rejectionCode, bounded } from './cooperationShared';
import { CooperationTaskProofs } from './cooperationTaskProofs';

const recheckBatchFallbacks = new Set([...taskSourceRejections, 'math_task_batch_projection_mismatch', 'math_task_missing_declaration']);
const integrationBatchFallbacks = new Set([...taskSourceRejections, 'math_task_integration_conflict', 'math_task_integration_missing_context',
  'math_task_integration_missing_declaration', 'math_task_batch_projection_mismatch']);
/** A changed check identity leaves no usable verifier result; aborts and unlisted failures propagate. */
function expectedRejection(error: unknown, expected: ReadonlySet<string>): Error {
  if (error instanceof Error && rejectionCode(error) === 'math_task_check_identity_changed')
    throw new Error('math_verifier_unavailable', { cause: error });
  if (!(error instanceof Error) || error.name === 'AbortError' || !expected.has(rejectionCode(error))) throw error;
  return error;
}

/** Integration of checked task proofs into the canonical commit and their rechecks. */
export abstract class CooperationIntegration extends CooperationTaskProofs {
  protected queueIntegration<T>(operation: () => Promise<T>): Promise<T> {
    const queuedAt = Date.now();
    const pending = this.integrationQueue.then(() => {
      this.input.signal.throwIfAborted();
      this.input.emit('integration_queue_started', { waitedMs: Date.now() - queuedAt });
      return operation();
    });
    this.integrationQueue = pending.then(() => {}, () => {});
    return pending;
  }
  protected integrateReady() { return this.queueIntegration(() => this.integrateReadyNow()); }
  protected async integrateReadyNow() {
    const publish = (node: TaskRecord) => {
      const producer = this.input.workers.find(worker => worker.id === node.assignment!.workerId) ?? this.lead;
      this.record(producer, node.task, 'proof', node.status === 'integrated' ? 'verified' : 'failed',
        node.feedback ?? 'Checked proof integrated with freshly validated dependencies.',
        { assignmentKey: assignmentDeliveryFile(node.assignment!),
          commit: node.integratedCheck?.commit ?? node.proof!.commit, sourceDigest: node.integratedCheck?.sourceDigest,
          evidence: node.integratedCheck ?? node.proof, actualReferences: (node.integratedCheck ?? node.proof)?.references });
    };
    for (;;) {
      // A parent can reach canonical acceptance before a later snapshot or publication fails.
      const unpublished = this.archive.tasks.find(item => !this.synchronizationBlocked(item.task) && item.status === 'integrated' && item.proof && item.assignment &&
        item.integratedCheck?.passed && item.integratedCheck.taskDigest === digest(item.task) && this.checkedDeliveries.has(item.integratedCheck) &&
        !this.archive.deliveries?.some(record => record.taskId === item.task.id && record.taskDigest === digest(item.task) &&
          record.kind === 'proof' && record.status === 'verified' &&
          (record.commit === item.proof!.commit || record.commit === item.integratedCheck!.commit)));
      if (unpublished) {
        const receipt = unpublished.integratedCheck, version = digest(unpublished.task);
        await this.syncPreparedStatements();
        await this.input.exclusiveCheck(async () => {
          if (this.archive.tasks.includes(unpublished) && unpublished.status === 'integrated' &&
              unpublished.integratedCheck === receipt && digest(unpublished.task) === version) publish(unpublished);
        });
        continue;
      }
      const node = this.archive.tasks.find(item => ['delivered', 'conditional'].includes(item.status) && this.integrationAllowed(item) &&
        taskDependenciesReady(item.task, this.archive.tasks));
      if (!node) return;
      const proof = node.proof;
      await this.integrateNow(node);
      await this.input.exclusiveCheck(async () => {
        if (this.archive.tasks.includes(node) && node.proof === proof && ['integrated', 'blocked'].includes(node.status)) publish(node);
      });
    }
  }
  protected synchronizationPending() {
    return Boolean(this.planSynchronization || this.preparingStatements || this.archive.tasks.some(node => node.pendingValidation));
  }
  protected candidateSynchronizationBlocked() {
    const required = this.fixedStatementReviewTasks();
    return this.archive.tasks.some(node => (node.task.kind === 'goal' || required?.has(node.task.id)) &&
      this.synchronizationBlocked(node.task));
  }
  protected markPendingValidation(nodes: readonly TaskRecord[], proofs: ReadonlySet<string> = new Set()) {
    for (const node of nodes) node.pendingValidation = { id: crypto.randomUUID(), taskDigest: digest(node.task),
      canonicalCommit: this.archive.canonicalCommit!, environmentDigest: this.input.state.environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest,
      ...(proofs.has(node.task.id) || node.pendingValidation?.proof ? { proof: true } : {}) };
  }
  protected schedulePlanSynchronization(): Promise<void> {
    if (this.planSynchronization) return this.planSynchronization;
    const pending = this.synchronizePlan();
    this.planSynchronization = pending; this.planSynchronizations.add(pending);
    void pending.catch(error => {
      if (!this.input.signal.aborted) { this.failure = error instanceof Error ? error : new Error(String(error)); this.changed(); }
    }).finally(() => {
      this.planSynchronizations.delete(pending);
      if (this.planSynchronization === pending && !this.failure) this.planSynchronization = undefined;
      if (!this.failure && !this.input.signal.aborted && (this.archive.tasks.some(node => node.pendingValidation) ||
          this.archive.edits?.some(edit => edit.status === 'applied' && edit.pendingSync))) this.schedulePlanSynchronization();
      this.wake();
    }).catch(() => {});
    return pending;
  }
  private async synchronizePlan() {
    for (;;) {
      const snapshot = await this.input.exclusiveCheck(async () => {
        const targets = this.archive.tasks.filter(node => node.pendingValidation).map(node => ({ node, validation: node.pendingValidation! }));
        const edits = (this.archive.edits ?? []).filter(edit => edit.status === 'applied' && edit.pendingSync);
        if (!targets.length && !edits.length) return;
        return { canonical: this.archive.canonicalCommit!, environmentDigest: this.input.state.environmentDigest,
          problemReceiptDigest: this.input.state.problem.receiptDigest,
          environment: { ...this.input.access.get(this.lead.id)!.environment }, targets, edits,
          inputs: new Map(this.archive.tasks.map(node => [node.task.id, { node, taskDigest: digest(node.task),
            status: node.status, proof: node.proof, integratedCheck: node.integratedCheck, pendingValidation: node.pendingValidation }])),
          tasks: this.archive.tasks.map(node => ({ ...node, pendingValidation: undefined })) };
      });
      if (!snapshot) return;
      const ids = new Set(snapshot.targets.filter(item => item.validation.proof).map(item => item.node.task.id));
      const fresh = snapshot.targets.some(item => item.validation.proof && item.node.integratedCheck &&
        !this.checkedDeliveries.has(item.node.integratedCheck));
      const current = () => this.archive.canonicalCommit === snapshot.canonical &&
        this.input.state.environmentDigest === snapshot.environmentDigest &&
        this.input.state.problem.receiptDigest === snapshot.problemReceiptDigest &&
        snapshot.targets.every(({ node, validation }) => this.archive.tasks.includes(node) &&
          node.pendingValidation === validation && digest(node.task) === validation.taskDigest);
      const rechecked = await this.recheckIntegrated(snapshot.canonical, !fresh, { tasks: snapshot.tasks, ids,
        environment: snapshot.environment, environmentDigest: snapshot.environmentDigest, current });
      if (rechecked && current()) {
        const statements = this.prepareStatementContexts(snapshot.tasks, snapshot.canonical,
          { environment: snapshot.environment, digest: snapshot.environmentDigest, current }); if (statements) await statements;
      }
      await this.input.exclusiveCheck(async () => {
        this.input.signal.throwIfAborted();
        if (this.archive.canonicalCommit !== snapshot.canonical || this.input.state.environmentDigest !== snapshot.environmentDigest ||
            this.input.state.problem.receiptDigest !== snapshot.problemReceiptDigest) {
          const current = snapshot.targets.filter(({ node, validation }) => this.archive.tasks.includes(node) && node.pendingValidation === validation);
          this.markPendingValidation(current.map(item => item.node), ids);
          this.input.emit('plan_recheck_rebased', { from: snapshot.canonical, to: this.archive.canonicalCommit,
            taskIds: current.map(item => item.node.task.id) });
          this.changed(); return;
        }
        // An obsolete snapshot may still contain old receipts for targets not reached by the recheck.
        if (!rechecked || !current()) return;
        const inputCurrent = (id: string) => {
          const baseline = snapshot.inputs.get(id), current = this.node(id);
          return baseline && current === baseline.node && digest(current.task) === baseline.taskDigest &&
            current.status === baseline.status && current.proof === baseline.proof && current.integratedCheck === baseline.integratedCheck &&
            current.pendingValidation === baseline.pendingValidation;
        };
        const dependencies = new Map(snapshot.targets.map(({ node }) => {
          const checked = snapshot.tasks.find(item => item.task.id === node.task.id)!;
          return [node.task.id, [...new Set([...this.dependencies(checked.task, snapshot.tasks).map(item => item.task.id),
            ...(checked.integratedCheck?.references?.tasks?.map(reference => reference.taskId) ?? [])])]];
        }));
        const publishable = new Set(snapshot.targets.filter(({ node, validation }) => inputCurrent(node.task.id) &&
          node.pendingValidation === validation && digest(node.task) === validation.taskDigest &&
          dependencies.get(node.task.id)!.every(inputCurrent)).map(({ node }) => node.task.id));
        for (;;) {
          const invalid = [...publishable].filter(id => dependencies.get(id)!.some(dependency =>
            snapshot.inputs.get(dependency)?.pendingValidation && !publishable.has(dependency)));
          if (!invalid.length) break;
          for (const id of invalid) publishable.delete(id);
        }
        for (const { node, validation } of snapshot.targets) {
          if (!this.archive.tasks.includes(node) || node.pendingValidation !== validation) continue;
          if (!publishable.has(node.task.id)) { this.markPendingValidation([node], ids); continue; }
          const checked = snapshot.tasks.find(item => item.task.id === node.task.id)!;
          if (ids.has(node.task.id)) {
            node.integratedCheck = checked.integratedCheck; node.status = checked.status; node.feedback = checked.feedback;
            if (node.status === 'blocked') this.needsLead = true;
          }
          delete node.pendingValidation;
        }
        this.syncStatementReviews();
        for (const edit of snapshot.edits) if (!edit.recheck?.tasks.some(result => {
          const current = this.node(result.taskId);
          return current?.pendingValidation && digest(current.task) === result.taskDigest;
        })) edit.pendingSync = undefined;
        this.input.emit('task_contract_sources_revalidated', { taskIds: [...ids].filter(id => !this.node(id)?.pendingValidation) });
        this.changed();
      });
      await this.integrateReady();
    }
  }
  private async recheckIntegrated(canonical: string, changedOnly = false, snapshot?: { tasks: TaskRecord[]; ids: ReadonlySet<string>;
    environment: NodeJS.ProcessEnv; environmentDigest: string; current: () => boolean }) {
    // Persisted receipts and receipts for different sources cannot authorize dependent dispatch.
    const tasks = snapshot?.tasks ?? this.archive.tasks;
    const pending = tasks.filter(node => node.status === 'integrated' && (!snapshot || snapshot.ids.has(node.task.id)));
    const selected = new Set(pending.map(node => node.task.id));
    const checked = new Set<string>();
    const batched = new Map<TaskRecord, { proof: TaskProof; source: string; retainedGoals: string }>();
    const batchAttempted = new Set<TaskRecord>();
    const request = (node: TaskRecord) => ({ task: node.task,
      assignment: { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical },
      retainedGoals: this.dependencies(node.task, tasks).filter(item => item.task.kind === 'goal' && item.status === 'integrated')
        .map(item => item.task.theoremName!) });
    let projector: ReturnType<typeof createTaskSourceProjector> | undefined;
    const projections = new Map<string, string | Error>();
    const projection = (node: TaskRecord) => {
      const retainedGoals = request(node).retainedGoals;
      const key = canonicalMathJson({ taskDigest: digest(node.task), retainedGoals });
      let value = projections.get(key);
      if (value === undefined) {
        try {
          projector ??= createTaskSourceProjector(this.input.state.problem, this.lead.worktree, canonical);
          value = mathDigest(canonicalMathJson([...projector(node.task, retainedGoals)]));
        } catch (error) { value = error instanceof Error ? error : new Error(String(error)); }
        projections.set(key, value);
      }
      if (value instanceof Error) throw value;
      return value;
    };
    const checkedProjections = new Map<string, string>();
    const reusable = (node: TaskRecord) => {
      const receipt = node.integratedCheck, references = receipt?.references;
      if (!(changedOnly || snapshot) || !receipt?.passed || receipt.conditions?.length ||
          receipt.taskDigest !== digest(node.task) || !this.checkedDeliveries.has(receipt) || !hasTaskAcceptance(receipt) ||
          !references || references.environmentDigest !== (snapshot?.environmentDigest ?? this.input.state.environmentDigest) ||
          !taskDependenciesReady(node.task, tasks)) return false;
      if (taskReferenceDependencies(node) && proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, canonical, references,
          snapshot?.environmentDigest ?? this.input.state.environmentDigest)) return true;
      // Generated Lean references conservatively bind the entire module. An unchanged
      // complete task projection still has the exact sources checked by this process.
      const commit = receipt.verification.targetCommit;
      if (!commit) return false;
      let checked = checkedProjections.get(commit);
      if (checked === undefined) {
        checked = mathDigest(canonicalMathJson(this.input.state.problem.ownedFiles.map(file => [file,
          committedSource(this.lead.worktree, commit, `${this.input.state.problem.projectRelative}/${file}`)])));
        checkedProjections.set(commit, checked);
      }
      return projection(node) === checked;
    };
    const progress = { canonicalCommit: canonical, total: pending.length, completed: 0, taskId: undefined as string | undefined };
    const persistProgress = async () => {
      const publish = async () => {
        if (snapshot && !snapshot.current()) return;
        this.archive.recheck = { ...progress }; this.input.save();
      };
      if (snapshot) await this.input.exclusiveCheck(publish);
      else await publish();
    };
    await persistProgress();
    const finish = async (node: TaskRecord) => {
      checked.add(node.task.id); progress.completed++; progress.taskId = undefined;
      this.input.emit('task_recheck_finished', { ...progress, taskId: node.task.id, passed: node.status === 'integrated', ...(snapshot ? { staged: true } : {}) });
      await persistProgress();
    };
    while (pending.length) {
      this.input.signal.throwIfAborted();
      if (snapshot && !snapshot.current()) return false;
      const index = pending.findIndex(node => node.task.dependsOn.every(id => !selected.has(id) || tasks.find(item => item.task.id === id)?.status !== 'integrated' || checked.has(id)));
      if (index < 0) throw new Error('math_plan_dependency_cycle');
      const [node] = pending.splice(index, 1);
      progress.taskId = node.task.id;
      this.input.emit('task_recheck_started', { ...progress }); await persistProgress();
      this.input.signal.throwIfAborted();
      if (snapshot && !snapshot.current()) return false;
      const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical };
      try {
        if (reusable(node)) {
          this.input.emit('task_check_reused', { taskId: node.task.id, commit: node.integratedCheck!.commit, canonicalCommit: canonical });
          await finish(node); continue;
        }
        if (!batchAttempted.has(node) && (this.input.modules.M2.checkTask ?? checkTaskProof) === checkTaskProof) {
          const source = projection(node);
          const group = [node, ...pending.filter(item => {
            if (batchAttempted.has(item)) return false;
            try { return !reusable(item) && projection(item) === source; } catch { return false; }
          })].slice(0, 32);
          if (group.length > 1) {
            group.forEach(item => batchAttempted.add(item));
            this.input.emit('task_recheck_batch_started', { taskIds: group.map(item => item.task.id) });
            try {
              const requests = group.map(request);
              const proofs = await checkTaskProofs(this.input.state.problem, this.lead.worktree, canonical, requests,
                snapshot?.environment ?? this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs,
                snapshot?.environmentDigest ?? this.input.state.environmentDigest, this.taskProofCache);
              this.input.signal.throwIfAborted();
              if (proofs.some(proof => ['unavailable', 'blocked'].includes(proof.verification.status) || !isAttributedTaskProof(proof)))
                throw new Error('math_verifier_unavailable');
              if (snapshot && !snapshot.current()) return false;
              group.forEach((item, index) => {
                const proof = proofs[index];
                if (!proof) throw new Error('math_verifier_unavailable');
                batched.set(item, { proof, source, retainedGoals: canonicalMathJson(requests[index].retainedGoals) });
              });
            } catch (error) {
              this.input.signal.throwIfAborted();
              const rejected = expectedRejection(error, recheckBatchFallbacks);
              if (snapshot && !snapshot.current()) return false;
              this.input.emit('task_recheck_batch_fallback', { taskIds: group.map(item => item.task.id), reason: bounded(rejected.message, 1000) });
            }
          }
        }
        // Earlier batch members can invalidate goals retained by a later member.
        // Recheck its current projection instead of submitting an obsolete receipt.
        const prepared = batched.get(node);
        const checkedProof = prepared && prepared.source === projection(node) &&
          prepared.retainedGoals === canonicalMathJson(request(node).retainedGoals) ? prepared.proof : undefined;
        const receipt = await this.check(node.task, assignment, this.lead.worktree, canonical, [], checkedProof, false, false, tasks,
          snapshot && { environment: snapshot.environment, digest: snapshot.environmentDigest });
        this.input.signal.throwIfAborted();
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        if (snapshot && !snapshot.current()) return false;
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.status = 'blocked'; node.feedback = solverProofFeedback(receipt); if (!snapshot) this.needsLead = true; }
        else if (!taskDependenciesReady(node.task, tasks)) {
          node.status = 'blocked'; node.feedback = 'math_task_dependency_invalidated'; if (!snapshot) this.needsLead = true;
        }
      } catch (error) {
        this.input.signal.throwIfAborted();
        const rejected = expectedRejection(error, integrationRejections);
        if (snapshot && !snapshot.current()) return false;
        node.status = 'blocked'; node.feedback = rejected.message; if (!snapshot) this.needsLead = true;
      }
      await finish(node);
    }
    this.input.signal.throwIfAborted();
    if (snapshot && !snapshot.current()) return false;
    // Fresh receipts can reveal inputs absent from the planned graph, including
    // restored receipts that could not authorize an earlier dependency order.
    for (const node of tasks) if (selected.has(node.task.id) && node.status === 'integrated' &&
        !taskDependenciesReady(node.task, tasks)) {
      node.status = 'blocked'; node.feedback = 'math_task_dependency_invalidated';
      if (!snapshot) this.needsLead = true;
      this.input.emit('task_recheck_dependency_invalidated', { ...progress, taskId: node.task.id, ...(snapshot ? { staged: true } : {}) });
    }
    return !snapshot || snapshot.current();
  }
  protected async recheckConditional() {
    for (const node of this.archive.tasks.filter(node => node.status === 'conditional')) {
      const group = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
      if ((node.task.status ?? 'active') !== 'active' || group && group.group.status !== 'active') continue;
      const saved = node.proof;
      this.input.emit('task_conditional_recheck_started', { taskId: node.task.id });
      try {
        if (!(node.task.conditional || node.assignment && hasTaskConnectionCheck(node.task, node.assignment)) ||
            !saved?.passed || saved.taskDigest !== digest(node.task) ||
            !saved.conditions?.length || !node.assignment) throw new Error('math_task_condition_version_invalid');
        const conditions = saved.conditions.map(condition => {
          const input = this.node(condition.taskId);
          if (!input || input.task.kind !== 'lemma' || !input.task.type || digest(input.task) !== condition.taskDigest)
            throw new Error('math_task_condition_version_invalid');
          return input.task;
        });
        const proof = await withSolverWorktree(this.lead.worktree, saved.commit, checkout =>
          this.check(node.task, node.assignment!, checkout, saved.commit, conditions));
        if (['unavailable', 'blocked'].includes(proof.verification.status)) throw new Error('math_verifier_unavailable');
        node.proof = proof;
        if (!proof.passed) {
          node.status = 'blocked'; node.feedback = solverProofFeedback(proof); this.needsLead = true;
        }
      } catch (error) {
        this.input.signal.throwIfAborted();
        node.feedback = expectedRejection(error, integrationRejections).message; node.status = 'blocked'; this.needsLead = true;
      }
      this.input.emit('task_conditional_recheck_finished', { taskId: node.task.id, passed: node.status === 'conditional' });
      this.changed();
    }
  }
  protected integrate(node: TaskRecord) { return this.queueIntegration(() => this.integrateNow(node)); }
  private integrationAllowed(node: TaskRecord) {
    const group = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
    return !this.synchronizationBlocked(node.task) && !(node.proof?.references?.tasks ?? []).some(reference => {
      const dependency = this.node(reference.taskId);
      return !dependency || dependency.pendingValidation || this.preparingStatementTasks.has(reference.taskId);
    }) && (node.task.status ?? 'active') === 'active' && (!this.archive.groups || group?.group.status === 'active');
  }
  private integrationSnapshot(node: TaskRecord) {
    if (!this.archive.tasks.includes(node) || !['delivered', 'conditional'].includes(node.status) ||
        !node.assignment || !node.proof || !this.integrationAllowed(node)) return;
    const tasks = this.archive.tasks.map(item => ({ ...item }));
    const dependencies = this.dependencies(node.task, tasks);
    const group = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
    return { node, task: node.task, taskDigest: digest(node.task), assignment: node.assignment, proof: node.proof, status: node.status,
      canonical: this.archive.canonicalCommit!, environmentDigest: this.input.state.environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest, groupDigest: canonicalMathJson(group?.group ?? null),
      routesDigest: canonicalMathJson({ alternatives: node.alternativeRoutes ?? [], routes: this.archive.proofRoutes ?? [] }), tasks,
      dependencies: dependencies.map(item => ({ id: item.task.id, taskDigest: digest(item.task), status: item.status,
        proof: item.proof, integratedCheck: item.integratedCheck })),
      retainedGoals: dependencies.filter(item => item.task.kind === 'goal' && item.status === 'integrated').map(item => item.task.theoremName!) };
  }
  private integrationTaskCurrent(snapshot: NonNullable<ReturnType<CooperationIntegration['integrationSnapshot']>>) {
    const { node } = snapshot;
    return this.archive.tasks.includes(node) && node.status === snapshot.status && node.assignment === snapshot.assignment &&
      node.proof === snapshot.proof && digest(node.task) === snapshot.taskDigest && this.integrationAllowed(node) &&
      this.input.state.environmentDigest === snapshot.environmentDigest && this.input.state.problem.receiptDigest === snapshot.problemReceiptDigest &&
      canonicalMathJson({ alternatives: node.alternativeRoutes ?? [], routes: this.archive.proofRoutes ?? [] }) === snapshot.routesDigest &&
      snapshot.dependencies.every(dependency => {
        const current = this.node(dependency.id);
        return current && digest(current.task) === dependency.taskDigest;
      });
  }
  private integrationInputsCurrent(snapshot: NonNullable<ReturnType<CooperationIntegration['integrationSnapshot']>>) {
    const group = this.archive.groups?.find(record => record.group.id === taskGroup(snapshot.task));
    return canonicalMathJson(group?.group ?? null) === snapshot.groupDigest && snapshot.dependencies.every(dependency => {
      const current = this.node(dependency.id);
      return current?.status === dependency.status && current.proof === dependency.proof && current.integratedCheck === dependency.integratedCheck;
    });
  }
  /** Batch only work that is ready now; every target must check the same complete union projection. */
  private async integrateBatch(node: TaskRecord): Promise<'fallback' | 'retry' | 'integrated'> {
    if ((this.input.modules.M2.checkTask ?? checkTaskProof) !== checkTaskProof) return 'fallback';
    const batch = await this.input.exclusiveCheck(async () => {
      const eligible = (item: TaskRecord) => item.task.kind === 'lemma' && item.proof?.passed &&
        this.checkedDeliveries.has(item.proof) && !item.proof.conditions?.length && taskDependenciesReady(item.task, this.archive.tasks);
      const first = eligible(node) && this.integrationSnapshot(node);
      if (!first) return;
      const snapshots = [first], declarations = new Set(first.proof.changes.map(change => `${change.file}\0${change.name}`));
      const uses = (item: typeof first) => new Set([...item.task.dependsOn, ...item.dependencies.map(input => input.id),
        ...(item.proof.references?.tasks ?? []).map(input => input.taskId)]);
      for (const candidate of this.archive.tasks) {
        if (snapshots.length === 32) break;
        if (candidate === node || taskGroup(candidate.task) !== taskGroup(first.task) || !eligible(candidate)) continue;
        const snapshot = this.integrationSnapshot(candidate);
        if (!snapshot || snapshot.proof.changes.some(change => declarations.has(`${change.file}\0${change.name}`)) ||
            snapshots.some(item => uses(item).has(snapshot.task.id) || uses(snapshot).has(item.task.id))) continue;
        snapshots.push({ ...snapshot, tasks: first.tasks });
        snapshot.proof.changes.forEach(change => declarations.add(`${change.file}\0${change.name}`));
      }
      if (snapshots.length < 2) return;
      const graph = canonicalMathJson(this.archive.tasks.map(item => [item.task.id, digest(item.task)]));
      const environment = { ...this.input.access.get(this.lead.id)!.environment };
      const key = mathDigest(canonicalMathJson({ canonical: first.canonical, environment, environmentDigest: first.environmentDigest,
        problemReceiptDigest: first.problemReceiptDigest, graph, group: first.groupDigest,
        inputs: snapshots.map(item => ({ task: item.taskDigest, assignment: item.assignment, proof: item.proof,
          routes: item.routesDigest, dependencies: item.dependencies })) }));
      if (this.rejectedIntegrationBatches.has(key)) return;
      return { snapshots, graph, environment, key };
    });
    if (!batch) return 'fallback';
    const { snapshots, environment } = batch, first = snapshots[0], problem = this.input.state.problem;
    let merged: string | undefined, receipts: TaskProof[] | undefined, fallback: string | undefined;
    try {
      await withSolverWorktree(this.lead.worktree, first.canonical, async checkout => {
        for (const snapshot of snapshots) applyTaskChanges(problem, checkout, snapshot.proof.changes, snapshot.proof.imports);
        merged = commitSolverSources(problem, checkout);
        const projector = createTaskSourceProjector(problem, checkout, merged);
        const projections = snapshots.map(snapshot => canonicalMathJson([...projector(snapshot.task, snapshot.retainedGoals)]));
        if (projections.some(projection => projection !== projections[0])) {
          fallback = 'math_task_batch_projection_mismatch'; return;
        }
        this.input.emit('task_integration_batch_started', { taskIds: snapshots.map(snapshot => snapshot.task.id), commit: merged });
        const requests = snapshots.map(snapshot => ({ task: snapshot.task, retainedGoals: snapshot.retainedGoals,
          assignment: { taskId: snapshot.task.id, taskDigest: snapshot.taskDigest, workerId: this.lead.id, seedCommit: merged! } }));
        const proofs = await checkTaskProofs(problem, checkout, merged, requests, environment, this.input.signal,
          this.input.timeoutMs, first.environmentDigest, this.taskProofCache);
        this.input.signal.throwIfAborted();
        if (proofs.some(proof => ['unavailable', 'blocked'].includes(proof.verification.status)))
          throw new Error('math_verifier_unavailable');
        const deterministic = proofs.every(proof => proof.passed || isAttributedTaskProof(proof) && hasDeterministicLeanFailure(proof.verification));
        receipts = [];
        for (const [index, snapshot] of snapshots.entries()) receipts.push(await this.check(snapshot.task, requests[index].assignment,
          checkout, merged, [], proofs[index], false, false, first.tasks,
          { environment, digest: first.environmentDigest }));
        if (receipts.some(receipt => !receipt.passed)) {
          if (!deterministic) throw new Error('math_verifier_unavailable');
          fallback = 'math_task_merged_proof_failed';
        } else if (receipts.some(receipt => receipt.references?.tasks?.some(reference =>
          snapshots.some(snapshot => snapshot.task.id === reference.taskId)))) fallback = 'math_task_batch_dependency_changed';
      });
    } catch (error) {
      this.input.signal.throwIfAborted();
      fallback = rejectionCode(expectedRejection(error, integrationBatchFallbacks));
    }
    const result = await this.input.exclusiveCheck(async () => {
      this.input.signal.throwIfAborted();
      if (this.archive.canonicalCommit !== first.canonical || snapshots.some(snapshot =>
        !this.integrationTaskCurrent(snapshot) || !this.integrationInputsCurrent(snapshot)) ||
        canonicalMathJson(this.archive.tasks.map(item => [item.task.id, digest(item.task)])) !== batch.graph) {
        this.input.emit('task_integration_batch_superseded', { taskIds: snapshots.map(snapshot => snapshot.task.id) });
        return 'retry' as const;
      }
      if (fallback) {
        if (this.rejectedIntegrationBatches.size >= 64) this.rejectedIntegrationBatches.delete(this.rejectedIntegrationBatches.values().next().value!);
        this.rejectedIntegrationBatches.add(batch.key);
        this.input.emit('task_integration_batch_fallback', { taskIds: snapshots.map(snapshot => snapshot.task.id), reason: fallback });
        return 'fallback' as const;
      }
      if (!merged || receipts?.length !== snapshots.length) throw new Error('math_task_integration_missing_receipt');
      if (receipts.some(receipt => receipt.references && canonicalMathJson(receipt.references.tasks) !==
          canonicalMathJson(attributeTaskReferences(receipt.references, this.archive.tasks)))) return 'retry' as const;
      this.archive.canonicalCommit = merged;
      snapshots.forEach((snapshot, index) => { snapshot.node.integratedCheck = receipts[index]; snapshot.node.status = 'integrated'; });
      snapshots.forEach(snapshot => this.input.emit('task_integrated', { taskId: snapshot.task.id,
        groupId: taskGroup(snapshot.task), sharing: snapshot.task.sharing ?? 'problem', commit: merged, batchSize: snapshots.length }));
      this.changed();
      return 'integrated' as const;
    });
    if (result === 'integrated') await this.syncPreparedStatements();
    return result;
  }
  protected async integrateNow(node: TaskRecord) {
    const problem = this.input.state.problem;
    for (;;) {
      const batch = await this.integrateBatch(node);
      if (batch === 'integrated') return;
      if (batch === 'retry') continue;
      const snapshot = await this.input.exclusiveCheck(async () => this.integrationSnapshot(node));
      if (!snapshot) return;
      let submitted = snapshot.proof, receipt: TaskProof | undefined, merged: string | undefined, failure: unknown;
      try {
        await withSolverWorktree(this.lead.worktree, snapshot.canonical, async checkout => {
          const checker = this.input.modules.M2.checkTask ?? checkTaskProof;
          const environment = this.input.access.get(this.lead.id)!.environment;
          const check = async (commit: string, assignment: TaskAssignment, conditions: readonly CooperativeTask[]) => {
            const raw = await checker(problem, checkout, commit, snapshot.task, assignment, snapshot.retainedGoals,
              environment, this.input.signal, this.input.timeoutMs, conditions, snapshot.environmentDigest,
              ...(checker === checkTaskProof ? [this.taskProofCache] : []));
            return this.check(snapshot.task, assignment, checkout, commit, conditions, raw, false, false, snapshot.tasks);
          };
          // Restored JSON needs fresh delivery evidence before its changes can enter a merge.
          if (!this.checkedDeliveries.has(submitted)) {
            const conditions = (submitted.conditions ?? []).map(condition => {
              const dependency = snapshot.tasks.find(item => item.task.id === condition.taskId);
              if (!dependency || digest(dependency.task) !== condition.taskDigest) throw new Error('math_task_condition_version_invalid');
              return dependency.task;
            });
            submitted = await check(submitted.commit, snapshot.assignment, conditions);
          }
          this.input.signal.throwIfAborted();
          if (['unavailable', 'blocked'].includes(submitted.verification.status)) throw new Error('math_verifier_unavailable');
          if (!submitted.passed) throw new Error('math_task_delivery_no_longer_checks');
          if (!taskDependenciesReady(snapshot.task, snapshot.tasks)) throw new Error('math_task_dependency_invalidated');
          const resolvedConditions = (submitted.conditions ?? []).map(condition => {
            const input = snapshot.tasks.find(item => item.task.id === condition.taskId);
            if (!input || input.task.kind !== 'lemma' || !input.task.type || input.status !== 'integrated' ||
                digest(input.task) !== condition.taskDigest) throw new Error('math_task_condition_version_invalid');
            return input.task;
          });
          applyTaskChanges(problem, checkout, submitted.changes, submitted.imports, resolvedConditions);
          merged = commitSolverSources(problem, checkout);
          receipt = await check(merged, { taskId: snapshot.task.id, taskDigest: snapshot.taskDigest,
            workerId: this.lead.id, seedCommit: merged }, []);
          this.input.signal.throwIfAborted();
          if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        });
      } catch (error) { failure = error; }
      const result = await this.input.exclusiveCheck(async () => {
        this.input.signal.throwIfAborted();
        if (!this.integrationTaskCurrent(snapshot)) {
          this.input.emit('task_integration_superseded', { taskId: snapshot.task.id, commit: snapshot.proof.commit });
          this.changed(); return 'superseded';
        }
        if (this.archive.canonicalCommit !== snapshot.canonical || !this.integrationInputsCurrent(snapshot)) {
          this.input.emit('task_integration_rebased', { taskId: snapshot.task.id, from: snapshot.canonical,
            to: this.archive.canonicalCommit });
          this.changed(); return 'retry';
        }
        if (submitted.passed) node.proof = submitted;
        if (!failure && receipt && !receipt.passed) {
          node.integratedCheck = receipt; node.feedback = solverProofFeedback(receipt);
          failure = new Error('math_task_merged_proof_failed');
        }
        if (failure) {
          this.changed();
          node.feedback = `${expectedRejection(failure, integrationRejections).message}\n${node.feedback ?? ''}`; node.status = 'blocked';
          this.needsLead = true; this.changed(); return 'blocked';
        }
        if (!receipt || !merged) throw new Error('math_task_integration_missing_receipt');
        if (receipt.references?.tasks?.some(reference => {
          const current = this.node(reference.taskId);
          return !current || digest(current.task) !== reference.taskDigest;
        })) {
          this.input.emit('task_integration_superseded', { taskId: snapshot.task.id, reason: 'actual-reference-changed' });
          this.changed(); return 'superseded';
        }
        node.integratedCheck = receipt; this.archive.canonicalCommit = merged; node.status = 'integrated';
        this.input.emit('task_integrated', { taskId: node.task.id, groupId: taskGroup(node.task), sharing: node.task.sharing ?? 'problem', commit: merged });
        this.changed(); return 'integrated';
      });
      if (result === 'retry') continue;
      if (result === 'integrated') await this.syncPreparedStatements();
      return;
    }
  }
}
