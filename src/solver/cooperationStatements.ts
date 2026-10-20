import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { type ResearchWorker } from './modules/organization';
import type { ContextBundle } from './modules/context';
import { routeAllowsTask } from './modules/search';
import { deliveryDetails, reviewVerdict, readMathResponse as block } from './deliveries';
import { assertStatementSnapshot, captureStatementContexts, createStatementSnapshotter, isStatementAction, readBacktranslation, resetStatementReview,
  writeStatementSnapshot, type StatementAction, type StatementReview } from './statementReview';
import { captureProofReferences, proofReferencesUnchanged } from './proofReferences';
import { taskGroup, hasTaskReferences, type CooperativeTask, type TaskRecord } from './tasks';
import { digest } from './cooperationShared';
import { CooperationCore } from './cooperationCore';

/** Statement translation reviews and their fixed-snapshot contexts. */
export abstract class CooperationStatements extends CooperationCore {
  protected statementTaskIdentity() {
    return mathDigest(canonicalMathJson(this.archive.tasks.map(node => ({ taskId: node.task.id,
      taskDigest: digest(node.task), statementReview: node.task.statementReview === true }))));
  }
  protected fixedStatementReviewTasks(): ReadonlyMap<string, string> | undefined {
    const scope = this.fixedReviewScope, review = this.archive.review;
    return scope && review === scope.review && review.commit === scope.commit && review.sourceDigest === scope.sourceDigest &&
      this.archive.canonicalCommit === scope.commit && this.input.state.environmentDigest === scope.environmentDigest &&
      this.statementTaskIdentity() === scope.tasksDigest ? scope.required : undefined;
  }
  protected statementReviewAllowed(task: CooperativeTask, dispatch = false) {
    if (this.synchronizationBlocked(task)) return false;
    const required = this.fixedStatementReviewTasks();
    if (required) return required.get(task.id) === digest(task);
    return dispatch ? routeAllowsTask(task, this.archive.tasks, this.archive.groups) :
      (task.status ?? 'active') === 'active' &&
      this.archive.groups?.find(route => route.group.id === taskGroup(task))?.group.status === 'active';
  }
  protected pendingFixedStatementReviews() {
    const required = this.fixedStatementReviewTasks();
    return required && this.archive.statementReviews?.some(review => required.get(review.taskId) === review.taskDigest &&
      ['pending', 'translating', 'translated', 'reviewing'].includes(review.status));
  }
  protected async syncPreparedStatements() {
    for (;;) {
      const canonical = this.archive.canonicalCommit, planVersion = this.archive.planVersion;
      const statements = this.prepareStatementContexts(); if (statements) await statements;
      const synchronized = await this.input.exclusiveCheck(async () => {
        if (canonical !== this.archive.canonicalCommit || planVersion !== this.archive.planVersion) return false;
        this.syncStatementReviews(); this.changed(); return true;
      });
      if (synchronized) return;
    }
  }
  protected supersedeStatementReview(review: StatementReview) {
    review.status = 'superseded';
    for (const record of this.archive.deliveries ?? []) if (record.statementReviewId === review.id) record.status = 'superseded';
  }
  protected prepareStatementContexts(nodes: readonly TaskRecord[] = this.archive.tasks,
    canonical = this.archive.canonicalCommit!,
    checkEnvironment?: { environment: NodeJS.ProcessEnv; digest: string; current?: () => boolean }): Promise<void> | undefined {
    if (checkEnvironment?.current && !checkEnvironment.current()) return;
    if (this.preparingStatements) return this.preparingStatements.then(() => this.prepareStatementContexts(nodes, canonical, checkEnvironment));
    const environmentDigest = checkEnvironment?.digest ?? this.input.state.environmentDigest;
    const tasks = nodes.filter(node => node.task.statementReview).map(node => node.task);
    const snapshot = createStatementSnapshotter(this.input.state.problem, this.lead.worktree, canonical, environmentDigest);
    const keys = new Map(tasks.map(task => [task.id, snapshot(task, this.dependencies(task, nodes).map(dependency =>
        ({ task: dependency.task, taskDigest: digest(dependency.task) }))).snapshotDigest]));
    const missing = tasks.filter(task => !this.statementContexts.has(keys.get(task.id)!));
    if (!missing.length) return;
    for (const task of missing) this.preparingStatementTasks.add(task.id);
    const pending = captureStatementContexts(this.input.state.problem, missing, this.lead.worktree,
      canonical, checkEnvironment?.environment ?? this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs)
      .then(contexts => { for (const task of missing) this.statementContexts.set(keys.get(task.id)!, contexts.get(task.id)!); })
      .finally(() => {
        for (const task of missing) this.preparingStatementTasks.delete(task.id);
        if (this.preparingStatements === pending) this.preparingStatements = undefined;
        this.wake();
      });
    this.preparingStatements = pending;
    return pending;
  }
  protected syncStatementReviews(invalidated = new Set<string>()) {
    if (!this.archive.statementReviews?.length && !this.archive.tasks.some(node => node.task.statementReview)) return;
    const reviews = this.archive.statementReviews ??= [];
    const tasks = this.archive.tasks.filter(node => node.task.statementReview).map(node => node.task);
    const snapshot = createStatementSnapshotter(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!,
      this.input.state.environmentDigest);
    const snapshots = new Map(tasks.map(task => [task.id,
      snapshot(task, this.dependencies(task).map(dependency =>
          ({ task: dependency.task, taskDigest: digest(dependency.task) }))) ]));
    for (const task of tasks) snapshots.set(task.id, snapshot(task, this.dependencies(task).map(dependency =>
        ({ task: dependency.task, taskDigest: digest(dependency.task) })), this.statementContexts.get(snapshots.get(task.id)!.snapshotDigest)));
    for (const review of reviews.filter(item => item.status !== 'superseded')) {
      const node = this.node(review.taskId), snapshot = snapshots.get(review.taskId);
      const reuse = review.status === 'accepted' && node && snapshot?.snapshotDigest === review.snapshotDigest &&
          review.environmentDigest === this.input.state.environmentDigest &&
          review.intendedStatement === node.task.informalStatement &&
          canonicalMathJson(review.premises) === canonicalMathJson(node.task.premises ?? this.input.state.problem.contract.assumptions);
      if (reuse) {
        if (invalidated.has(review.taskId) || review.taskDigest !== digest(node.task) || !this.archive.deliveries?.some(delivery =>
            delivery.statementReviewId === review.id && delivery.kind === 'statement-review' && delivery.status === 'accepted' &&
            delivery.taskDigest === digest(node.task))) {
          review.taskDigest = digest(node.task);
          review.dependencies = snapshot.input.dependencies.map(({ taskId, taskDigest }) => ({ taskId, taskDigest }));
          for (const delivery of this.archive.deliveries ?? []) if (delivery.statementReviewId === review.id &&
              delivery.taskDigest !== review.taskDigest) delivery.status = 'superseded';
          this.record(this.lead, node.task, 'statement-review', 'accepted', review.summary ?? 'Unchanged formal statement review reused.',
            { statementReviewId: review.id, taskDigest: review.taskDigest, statement: review.leanStatement,
              premises: review.premises, dependencies: review.dependencies, remainingObligations: [], commit: review.commit, sourceDigest: review.snapshotDigest });
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
}
