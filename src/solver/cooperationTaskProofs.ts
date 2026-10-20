import { isAdvisoryTask as advisory } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions } from '../math/leanSource';
import { commitSolverSources, committedSource, git, withSolverWorktree } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import { independentFeasibilityWorker, type ResearchWorker } from './modules/organization';
import { proofReceiptsMatch, type ProofCheck } from './modules/evidence';
import { routeAllowsTask, taskCanStart, selectedTaskRoute } from './modules/search';
import { deliveryDetails, parseMathResponse, type DeliveryRecord } from './deliveries';
import { checkTaskProof, createTaskSourceProjector, isAttributedTaskProof, ownedSourceDigest, trustedTaskProjectionReuse, type TaskProof } from './cooperativeProof';
import { proofReferencesUnchanged, type ProofReferences } from './proofReferences';
import { captureDeliveryArtifacts, diagnoseUnbackedLeanClaims, validateDeliveryArtifactClaims, type DeliveryArtifactManifest } from './deliveryArtifacts';
import { validateLemmaRequests } from './taskProposals';
import { routeBlockerBasis, type BlockerBasis } from './routeControl';
import { attributeTaskReferences } from './taskReferenceAttribution';
import { captureObligationSnapshot } from './obligationProgress';
import { checkpointCandidate } from './researchEvidence';
import { inspectKnowledgeUses } from './knowledgeUsage';
import { checkKnowledgeApplications } from './knowledgeApplications';
import { bindMathematicalGap } from './mathematicalGaps';
import { hasTaskConnectionCheck, taskConnectionCheckCurrent } from './taskConnections';
import { taskReferenceDependencies, assignmentDeliveryFile, markTaskReferences, markTaskAcceptance, hasTaskAcceptance, type CooperativeTask,
  type TaskAssignment, type TaskRecord, type CooperativeAction } from './tasks';
import { digest, FailedTaskInput, bounded, deliveryInputFields } from './cooperationShared';
import { CooperationStatements } from './cooperationStatements';

/** Task proof checks, failed-input memory and research checkpoints. */
export abstract class CooperationTaskProofs extends CooperationStatements {
  // Implemented by later layers; listed here because this layer calls them.
  protected abstract queueIntegration<T>(operation: () => Promise<T>): Promise<T>;
  protected abstract integrateReadyNow(): Promise<void>;
  protected abstract integrateNow(node: TaskRecord): Promise<void>;
  abstract interrupted(worker: ResearchWorker, action: CooperativeAction): void;
  abstract rejected(action: CooperativeAction, feedback: string, commit?: string): void;
  private checkpointInputDigest(task: CooperativeTask, workerId: string) {
    const versions = this.taskVersions();
    const deliveries = [...new Set((this.archive.deliveries ?? []).filter(record => record.producer !== workerId &&
      this.deliveryVisible(record, task, versions)).map(record => canonicalMathJson(deliveryInputFields(record))))].sort();
    return mathDigest(canonicalMathJson({ taskDigest: digest(task), environmentDigest: this.input.state.environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest,
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      dependencies: captureObligationSnapshot(this.dependencies(task), { environmentDigest: this.input.state.environmentDigest }).digest,
      deliveries }));
  }
  private checkpointLocalInputDigest(task: CooperativeTask, workerId: string) {
    const dependencies = this.dependencies(task), relevant = new Set([task.id, ...dependencies.map(node => node.task.id)]);
    const versions = this.taskVersions();
    const deliveries = [...new Set((this.archive.deliveries ?? []).filter(record => record.producer !== workerId &&
      this.deliveryVisible(record, task, versions) && (relevant.has(record.taskId ?? '') ||
        record.dependencies.some(reference => reference.taskId === task.id))).map(record => canonicalMathJson({
      ...deliveryInputFields(record), findingDigest: record.findingDigest,
    })))].sort();
    return mathDigest(canonicalMathJson({ taskDigest: digest(task),
      basis: routeBlockerBasis(task, this.archive.tasks, this.input.state.environmentDigest, this.input.state.problem.receiptDigest),
      dependencies: captureObligationSnapshot(dependencies, { environmentDigest: this.input.state.environmentDigest }).digest,
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
  private taskSourceDigest(task: CooperativeTask, worktree: string, commit: string, local = false) {
    const source = committedSource(worktree, commit, `${this.input.state.problem.projectRelative}/${task.proofPath}`);
    const targets = inspectLeanDeclarationRegions(source).filter(region =>
      region.name.split('.').at(-1) === task.theoremName?.split('.').at(-1));
    if (targets.length !== 1) return `declaration-count:${targets.length}`;
    // Selecting a different saved proof is new input; renaming the same declaration is not.
    const target = source.slice(targets[0].startOffset, targets[0].endOffset)
      .replace(/^(theorem|lemma)(\s+)[^\s([{:\n]+/u, '$1$2__task_target');
    return mathDigest(canonicalMathJson({ ...(local ? {} : { file: task.proofPath, offset: targets[0].startOffset }), source: target }));
  }
  private failedTaskBasis(task: CooperativeTask, conditions?: readonly CooperativeTask[],
    assignment = this.node(task.id)?.assignment): { basis: BlockerBasis; inputDigest: string } {
    const normalized = task.kind === 'lemma' ? { ...task, theoremName: undefined, proofPath: undefined } : task;
    conditions ??= task.conditional || assignment && hasTaskConnectionCheck(task, assignment)
      ? this.dependencies(task).filter(node => node.task.kind === 'lemma' && node.status !== 'integrated')
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
  protected failedTaskInput(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string, conditions?: readonly CooperativeTask[]) {
    const { basis, inputDigest } = this.failedTaskBasis(task, conditions, assignment), sourceDigest = this.leanSourceDigest(worktree, commit);
    const targetDigest = this.taskSourceDigest(task, worktree, commit);
    const localTargetDigest = this.taskSourceDigest(task, worktree, commit, true);
    return { id: mathDigest(canonicalMathJson({ inputDigest, sourceDigest, targetDigest })), taskId: task.id, taskDigest: digest(task),
      ...(!localTargetDigest.startsWith('declaration-count:') ? {
        attemptFingerprint: mathDigest(canonicalMathJson({ inputDigest, target: localTargetDigest })),
      } : {}),
      inputDigest, basis, sourceDigest, targetDigest, seedSourceDigest: this.leanSourceDigest(worktree, assignment.seedCommit),
      seedTargetDigest: this.taskSourceDigest(task, worktree, assignment.seedCommit),
      canonicalSourceDigest: this.leanSourceDigest(this.lead.worktree, this.archive.canonicalCommit!),
      canonicalTargetDigest: this.taskSourceDigest(task, this.lead.worktree, this.archive.canonicalCommit!) };
  }
  protected rememberTaskFailure(candidate: Omit<FailedTaskInput, 'feedback' | 'repair'>, feedback: string, repair?: FailedTaskInput['repair']) {
    const records = this.archive.failedTaskInputs ??= [];
    const previous = records.find(record => record.id === candidate.id);
    if (previous) return previous;
    const related = candidate.attemptFingerprint && records.findLast(record => record.attemptFingerprint === candidate.attemptFingerprint);
    const relatedFailureIds = related ? [related.id] : [];
    const record: FailedTaskInput = { ...candidate, feedback: bounded(feedback, 8000),
      ...(relatedFailureIds.length ? { relatedFailureIds } : {}), ...(repair ? { repair } : {}) };
    records.push(record);
    if (relatedFailureIds.length) {
      this.needsLead = true;
      this.input.emit('task_attempt_repeated_advisory', { taskId: record.taskId, failureId: record.id,
        attemptFingerprint: record.attemptFingerprint, relatedFailureIds, evidence: 'same-target-and-local-inputs-not-equivalence' });
    }
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
  protected pendingTaskRepair(node: TaskRecord, record: FailedTaskInput) {
    const repair = record.repair;
    return Boolean(repair?.pending && repair.taskId === node.task.id && repair.taskDigest === digest(node.task) &&
      node.assignment?.workerId === repair.workerId && node.assignment.taskDigest === repair.taskDigest);
  }
  private repeatedTaskFeedback(record: FailedTaskInput) {
    return 'math_task_repeated_failed_input\nThe same Lean source and mathematical inputs already failed. ' +
      'Save a changed proof or supply new premises, checked dependency evidence, or verifier inputs before retrying.\n' + record.feedback;
  }
  protected refreshFailedTaskInputs() {
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
  protected refreshResearchCheckpoints() {
    for (const [taskId, checkpoint] of Object.entries(this.archive.researchCheckpoints ?? {})) {
      if (!checkpoint.paused) continue;
      const node = this.node(taskId), worker = this.input.workers.find(worker => worker.id === node?.assignment?.workerId);
      if (!node || digest(node.task) !== checkpoint.taskDigest) { delete this.archive.researchCheckpoints![taskId]; continue; }
      if (!worker || node.status !== 'blocked' || !node.feedback?.startsWith('math_research_checkpoint_unchanged')) continue;
      const inputChanged = checkpoint.localInputDigest
        ? this.checkpointLocalInputDigest(node.task, worker.id) !== checkpoint.localInputDigest
        : this.checkpointInputDigest(node.task, worker.id) !== checkpoint.inputDigest;
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
  protected preserveResearchDraft(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, artifacts: DeliveryArtifactManifest) {
    (this.archive.researchDrafts ??= {})[action.task.id] = { taskDigest: action.assignment.taskDigest,
      workerId: worker.id, assignmentId: action.assignment.assignmentId,
      seedCommit: action.assignment.seedCommit, canonicalCommit: action.assignment.canonicalCommit,
      commit, outputDigest: this.checkpointOutputDigest(worker.worktree, commit), artifacts };
    this.pin(commit);
  }
  protected suspendResearchDrafts(worker: ResearchWorker, taskId?: string) {
    let changed = false;
    for (const [id, draft] of Object.entries(this.archive.researchDrafts ?? {}))
      if (draft.workerId === worker.id && id !== taskId && !draft.suspended) { draft.suspended = true; changed = true; }
    // Persist ownership before a different responsibility overwrites the worktree.
    if (changed) this.input.save();
  }
  protected researchWorkspaceChanged(worker: ResearchWorker, node: TaskRecord) {
    const session = this.input.state.workers?.find(record => record.id === worker.id);
    if (session?.sessionTaskId) return session.sessionTaskId !== node.task.id ||
      Boolean(session.sessionTaskVersion && session.sessionTaskVersion !== digest(node.task));
    if (session?.sessionStatementReview || session?.sessionRole && session.sessionRole !== 'researcher') return true;
    const checkpoint = this.archive.researchCheckpoints?.[node.task.id];
    return Boolean(checkpoint && checkpoint.outputDigest !==
      this.checkpointOutputDigest(worker.worktree, git(worker.worktree, ['rev-parse', 'HEAD'])));
  }
  protected async restoreResearchDraft(worker: ResearchWorker, node: TaskRecord): Promise<boolean> {
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
          !taskCanStart(node.task, this.archive.tasks, this.archive.groups) || !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups)) return false;
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
  protected researchCheckpoint(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string) {
    const node = this.node(action.task.id), taskDigest = digest(node.task);
    const inputDigest = this.checkpointInputDigest(node.task, worker.id), outputDigest = this.checkpointOutputDigest(worker.worktree, commit);
    const localInputDigest = this.checkpointLocalInputDigest(node.task, worker.id);
    const notesBlob = git(worker.worktree, ['ls-tree', '--format=%(objectname)', commit, '--', 'RESEARCH.md']);
    const candidate = checkpointCandidate(notesBlob ? committedSource(worker.worktree, commit, 'RESEARCH.md') : '',
      this.archive.researchDrafts?.[node.task.id]?.artifacts);
    const previous = this.archive.researchCheckpoints?.[node.task.id];
    const sameInput = previous?.taskDigest === taskDigest && (previous.localInputDigest
      ? previous.localInputDigest === localInputDigest : previous.inputDigest === inputDigest);
    const count = sameInput && previous.outputDigest === outputDigest
      ? previous.count + 1 : 1;
    const unchangedEvidenceCount = sameInput && previous.candidateOutputDigest === candidate.digest
      ? (previous.unchangedEvidenceCount ?? 1) + 1 : 1;
    const checkpoint = (this.archive.researchCheckpoints ??= {})[node.task.id] = { taskDigest, inputDigest, outputDigest,
      localInputDigest, candidateOutputDigest: candidate.digest, candidateStatus: candidate.status, unchangedEvidenceCount, count, paused: count >= 2 };
    this.input.emit('research_checkpoint_recorded', { taskId: node.task.id, ...checkpoint });
    if (checkpoint.paused) {
      const scope = `assigned-local-inference/checkpoint:${mathDigest(canonicalMathJson({ inputDigest, outputDigest }))}`;
      this.reportBlockers(node.task, [{ mechanism: 'unchanged-research-checkpoint', scope }]);
      Object.assign(checkpoint, { blockerId: this.archive.blockers?.find(record => record.taskId === node.task.id && record.scope === scope)?.id });
      this.rejected(action, 'math_research_checkpoint_unchanged: The same checkpoint has no new saved notes, draft, or task input. Wait for new input or revise the investigation.', commit);
    } else this.interrupted(worker, action);
  }
  protected async publishResearchFinding(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string,
    finding: any, complete: boolean, options: Partial<DeliveryRecord> = {}) {
    const node = this.node(action.task.id), details = deliveryDetails(finding);
    if (details.mathematicalGap) bindMathematicalGap(details.mathematicalGap, node.task, this.archive,
      { problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest });
    if (finding.taskId !== node.task.id || !details.summary.trim() || !['supporting', 'refuted', 'inconclusive'].includes(finding.conclusion))
      throw new Error('math_research_delivery_invalid');
    let artifacts = options.artifacts ?? captureDeliveryArtifacts({ problem: this.input.state.problem, worktree: worker.worktree, commit, assignment: action.assignment });
    artifacts = { ...artifacts, reportedChecks: validateDeliveryArtifactClaims(finding, artifacts) };
    const artifactWarning = diagnoseUnbackedLeanClaims(finding, artifacts);
    const lemmaRequests = validateLemmaRequests(this.input.state.problem, this.archive.tasks.map(node => node.task),
      this.archive.groups?.map(route => route.group) ?? [], node.task, finding.lemmaRequests,
      this.archive.deliveries?.filter(delivery => delivery.kind === 'research' && delivery.status !== 'superseded' &&
        delivery.taskId === node.task.id && delivery.taskDigest === digest(node.task)).flatMap(delivery => delivery.lemmaRequests ?? []));
    const knowledgeUses = await this.knowledgeUses(worker, node.task, commit);
    if (!this.current(action)) return;
    if (details.mathematicalGap) bindMathematicalGap(details.mathematicalGap, node.task, this.archive,
      { problemReceiptDigest: this.input.state.problem.receiptDigest, environmentDigest: this.input.state.environmentDigest });
    // A challenge alone is never a repeated-blocker report that parks the proof task.
    this.reportBlockers(node.task, finding.blockers ?? (complete && finding.conclusion === 'refuted' ? [{
      mechanism: 'reported-local-refutation', scope: 'assigned-local-inference', evidenceRefs: details.evidenceRefs,
    }] : undefined));
    const text = JSON.stringify(finding);
    if (complete) {
      node.finding = text; node.status = 'completed'; node.feedback = undefined;
      if (this.archive.unchangedResearch) delete this.archive.unchangedResearch[node.task.id];
      if (this.archive.researchCheckpoints) delete this.archive.researchCheckpoints[node.task.id];
    }
    if (finding.needsDecision === true || finding.conclusion === 'refuted' || lemmaRequests.length || artifactWarning) this.needsLead = true;
    const remaining = [...new Set([...(details.remainingObligations ?? []),
      ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])];
    this.record(worker, node.task, 'research', !remaining.length && node.task.kind !== 'sketch' ? 'advisory' : 'conditional', details.summary,
      { ...details, ...options, remainingObligations: remaining, commit, artifacts, lemmaRequests, finding: text, findingDigest: mathDigest(text),
        knowledgeUses, ...(artifactWarning ? { artifactWarning } : {}) });
    this.input.emit('research_delivered', { taskId: node.task.id, conclusion: finding.conclusion, complete });
  }
  private sourceProjector(worktree: string, commit: string) {
    const identity = mathDigest(canonicalMathJson({ problem: this.input.state.problem, worktree, commit }));
    if (this.preparedSources?.identity !== identity) this.preparedSources = { identity,
      project: createTaskSourceProjector(this.input.state.problem, worktree, commit) };
    return this.preparedSources.project;
  }
  protected async check(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string,
    conditions?: readonly CooperativeTask[], checked?: TaskProof, reuseDeliveryFailure = false, incompleteDelivery = false,
    taskGraph: readonly TaskRecord[] = this.archive.tasks,
    checkEnvironment?: { environment: NodeJS.ProcessEnv; digest: string }): Promise<TaskProof> {
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
    const tasks = taskGraph.map(node => ({ ...node }));
    const dependencies = this.dependencies(task, tasks), taskDigest = digest(task);
    const environmentDigest = checkEnvironment?.digest ?? this.input.state.environmentDigest;
    if (assignment.connectionCheck && !taskConnectionCheckCurrent(task, assignment, tasks,
      { environmentDigest, problemReceiptDigest: this.input.state.problem.receiptDigest }))
      throw new Error('math_task_condition_version_invalid');
    conditions ??= task.conditional || hasTaskConnectionCheck(task, assignment)
      ? dependencies.filter(node => node.task.kind === 'lemma' && node.status !== 'integrated').map(node => node.task) : [];
    const retainedGoals = dependencies.filter(node => node.task.kind === 'goal' && node.status === 'integrated').map(node => node.task.theoremName!);
    const checker = this.input.modules.M2.checkTask ?? checkTaskProof;
    const environment = checkEnvironment?.environment ?? this.input.access.get(this.lead.id)!.environment;
    const proof = checked ?? await checker(this.input.state.problem, worktree, commit, task, assignment, retainedGoals,
      environment, this.input.signal, this.input.timeoutMs, conditions, environmentDigest,
      ...(checker === checkTaskProof ? [this.taskProofCache] : []));
    const reuse = trustedTaskProjectionReuse(proof);
    if (proof.projectionReuse && !reuse || checker === checkTaskProof && proof.passed && !isAttributedTaskProof(proof))
      throw new Error('math_task_check_identity_changed');
    if (checker === checkTaskProof && !isAttributedTaskProof(proof)) throw new Error('math_verifier_unavailable');
    const projectionCommit = reuse?.projectionCommit ?? proof.verification.targetCommit;
    if (reuse && (reuse.checkedProjectionCommit !== proof.verification.targetCommit ||
        git(worktree, ['rev-parse', `${reuse.projectionCommit}^{tree}`]) !== reuse.projectionTree ||
        git(worktree, ['rev-parse', `${reuse.checkedProjectionCommit}^{tree}`]) !== reuse.projectionTree))
      throw new Error('math_task_check_identity_changed');
    const declarationHash = proof.passed && proof.verification.targetCommit && hashMathFormalSourceDeclaration(
      committedSource(worktree, proof.verification.targetCommit, `${this.input.state.problem.projectRelative}/${task.proofPath}`), task.theoremName!);
    const projected = (proof.passed || reuse) && this.sourceProjector(worktree, commit)(task, retainedGoals, conditions);
    const allowed = new Set(this.input.state.problem.ownedFiles.map(file => `${this.input.state.problem.projectRelative}/${file}`));
    allowed.add('RESEARCH.md');
    const projectionMatches = projected && projectionCommit &&
      [...projected].every(([file, source]) => source === committedSource(worktree, projectionCommit,
        `${this.input.state.problem.projectRelative}/${file}`)) &&
      git(worktree, ['diff', '--no-renames', '--name-only', '-z', commit, projectionCommit, '--'])
        .split('\0').filter(Boolean).every(file => allowed.has(file));
    if (proof.commit !== commit || proof.taskDigest !== taskDigest || proof.seedCommit !== assignment.seedCommit ||
        proof.sourceDigest !== ownedSourceDigest(this.input.state.problem, worktree, commit) ||
        canonicalMathJson(proof.conditions ?? []) !== canonicalMathJson(conditions.map(task => ({ taskId: task.id, taskDigest: digest(task) }))) ||
        (reuse && !projectionMatches) ||
        (proof.passed && (!projectionMatches || !declarationHash || !proofReceiptsMatch(proof.verification, proof.verification.targetCommit,
          [{ proofPath: task.proofPath!, theoremName: task.theoremName!, expectedSourceDeclarationHash: declarationHash,
            statementHash: taskDigest, leanStatementHash: taskDigest, claim: 'statement' }]))))
      throw new Error('math_task_check_identity_changed');
    if (proof.passed && conditions.length && projected) proof.projection = {
      environmentDigest,
      problemReceiptDigest: this.input.state.problem.receiptDigest,
      sourceDigest: mathDigest(canonicalMathJson([...projected])),
    };
    else delete proof.projection;
    if (proof.references) {
      const references = proof.references;
      references.tasks = attributeTaskReferences(references, tasks);
      markTaskReferences(proof);
    }
    this.pin(proof.commit); this.pin(projectionCommit); this.pin(proof.verification.targetCommit);
    this.checkedDeliveries.add(proof); markTaskAcceptance(proof);
    return proof;
  }
  /** Check isolated sources concurrently; only publishing and canonical integration are serialized. */
  protected async publishTaskProof(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, summary: string, options: Partial<DeliveryRecord> = {}, recovering = false) {
    const key = canonicalMathJson([worker.id, assignmentDeliveryFile(action.assignment), commit]);
    const previous = this.proofPublications.get(key);
    if (previous) return previous;
    const pending = this.publishCheckedTaskProof(worker, action, commit, summary, options, recovering);
    this.proofPublications.set(key, pending);
    try { return await pending; }
    finally { if (this.proofPublications.get(key) === pending) this.proofPublications.delete(key); }
  }
  private async publishCheckedTaskProof(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>,
    commit: string, summary: string, options: Partial<DeliveryRecord>, recovering: boolean): Promise<TaskProof | undefined> {
    const previous = this.node(action.task.id);
    // Notes-only completion cannot renew obsolete conditional inputs after unconditional integration.
    const notesOnly = previous?.status === 'integrated' && previous.proof && taskReferenceDependencies(previous) &&
      proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!,
        previous.integratedCheck!.references!, this.input.state.environmentDigest) &&
      git(worker.worktree, ['diff', '--no-renames', '--name-only', '-z', previous.proof.commit, commit, '--'])
        .split('\0').filter(Boolean).every(file => file === 'RESEARCH.md');
    const proof = previous?.proof && (previous.proof.commit === commit || notesOnly) &&
      ['delivered', 'conditional', 'integrated'].includes(previous.status) && this.checkedDeliveries.has(previous.proof) ? previous.proof :
      await this.check(action.task, action.assignment, worker.worktree, commit, undefined, undefined, true, recovering);
    const staged = await this.input.exclusiveCheck(async () => {
      if (!this.current(action) || !(proof.references?.tasks ?? []).every(reference =>
          this.archive.tasks.some(node => node.task.id === reference.taskId && digest(node.task) === reference.taskDigest))) {
        this.record(worker, action.task, 'proof', 'superseded', 'Assignment changed while its proof was being checked.',
          { ...options, commit, taskDigest: action.assignment.taskDigest, dependencies: action.assignment.dependencies ?? [] });
        this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
        return;
      }
      const node = this.node(action.task.id);
      if (['conditional', 'integrated'].includes(node.status)) {
        return { node, proof: node.proof?.commit === commit ? node.proof : undefined };
      }
      if (recovering && !proof.passed && proof.verification.status === 'failed') {
        node.feedback = solverProofFeedback(proof);
        if (this.deterministicTaskFailure(proof)) this.continueTaskCheckpoint(worker, node, commit);
        this.interrupted(worker, action);
        return { node: undefined, proof };
      }
      this.deliverProof(node, proof);
      return { node, proof };
    });
    if (!staged?.node) return staged?.proof;
    return this.queueIntegration(async () => {
      const node = staged.node, submitted = staged.proof;
      if (submitted && this.current(action) && node.proof === submitted) {
        if (node.status === 'delivered') await this.integrateNow(node);
        else if (node.status === 'integrated') await this.syncPreparedStatements();
        await this.input.exclusiveCheck(async () => {
          if (this.current(action) && node.proof === submitted)
            await this.finishProofDelivery(worker, node, submitted, summary, options);
          else {
            this.record(worker, action.task, 'proof', 'superseded', 'Assignment changed during canonical integration.',
              { ...options, commit, taskDigest: action.assignment.taskDigest, dependencies: action.assignment.dependencies ?? [] });
          }
        });
      }
      await this.integrateReadyNow();
      return submitted;
    });
  }
  protected retryTaskLocally(node: TaskRecord, commit?: string): boolean {
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
  protected restoreInterruptedRepair(worker: ResearchWorker, action: Extract<CooperativeAction, { kind: 'task' }>, commit: string) {
    const node = this.node(action.task.id), candidate = this.failedTaskInput(action.task, action.assignment, worker.worktree, commit);
    const failed = this.archive.failedTaskInputs?.find(record => record.id === candidate.id), repair = failed?.repair;
    if (!repair || repair.pending || repair.taskId !== node.task.id || repair.taskDigest !== digest(node.task) ||
        repair.workerId !== worker.id || repair.startedAttempt !== node.attempts) return false;
    repair.pending = true; delete repair.startedAttempt;
    node.feedback = failed!.feedback; node.status = 'pending';
    this.input.emit('task_repair_interrupted', { taskId: node.task.id, workerId: worker.id, failureId: failed!.id });
    this.changed(); return true;
  }
  protected continueTaskCheckpoint(worker: ResearchWorker, node: TaskRecord, commit: string) {
    const candidate = this.failedTaskInput(node.task, node.assignment!, worker.worktree, commit);
    const failed = this.archive.failedTaskInputs?.find(record => record.id === candidate.id);
    if (!failed) return;
    this.settleTaskRepair(node);
    failed.repair ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id, pending: true };
    this.input.emit('task_checkpoint_continuation_requested', { taskId: node.task.id, workerId: worker.id, failureId: failed.id });
  }
  protected settleTaskRepair(node: TaskRecord) {
    for (const { repair } of this.archive.failedTaskInputs ?? []) if (repair && !repair.pending &&
        repair.taskId === node.task.id && repair.taskDigest === digest(node.task) &&
        repair.workerId === node.assignment?.workerId && repair.startedAttempt === node.attempts) delete repair.startedAttempt;
  }
  private deliverProof(node: TaskRecord, proof: TaskProof) {
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
    this.changed();
  }
  private async finishProofDelivery(worker: ResearchWorker, node: TaskRecord, proof: TaskProof, summary: string, options: Partial<DeliveryRecord>) {
    const task = node.task, taskDigest = digest(task), assignment = node.assignment;
    const submittedProof = node.proof, integratedProof = node.integratedCheck;
    const environmentDigest = this.input.state.environmentDigest;
    const status = this.node(node.task.id).status;
    const verdict = status === 'integrated' ? 'verified' : status === 'conditional' ? 'conditional' :
      !proof.passed || status === 'blocked' ? 'failed' : undefined;
    if (!verdict) return;
    const assignmentKey = options.assignmentKey ?? assignmentDeliveryFile(node.assignment!);
    const duplicate = () => this.archive.deliveries?.some(record => record.producer === worker.id && record.kind === 'proof' && record.status === verdict &&
      record.taskId === task.id && record.taskDigest === taskDigest && record.assignmentKey === assignmentKey &&
      (record.commit === proof.commit || verdict === 'verified' && record.commit === node.integratedCheck?.commit));
    if (duplicate()) return;
    const knowledgeUses = await this.knowledgeUses(worker, task, proof.commit, proof);
    if (this.node(task.id) !== node || digest(node.task) !== taskDigest || node.status !== status ||
        node.assignment !== assignment || node.proof !== submittedProof || node.integratedCheck !== integratedProof ||
        this.input.state.environmentDigest !== environmentDigest || duplicate()) return;
    this.record(worker, task, 'proof', verdict, node.feedback ?? summary,
      { ...options, assignmentKey, commit: proof.commit, sourceDigest: proof.sourceDigest, evidence: proof, actualReferences: proof.references, knowledgeUses });
  }
  private async knowledgeUses(worker: ResearchWorker, task: CooperativeTask, commit: string, proof?: ProofCheck & { references?: ProofReferences }) {
    let value: unknown;
    try { value = parseMathResponse(committedSource(worker.worktree, commit, 'RESEARCH.md'), 'math-result', {}, 'summary').knowledgeUses; }
    catch { return []; }
    const { uses, rejected } = inspectKnowledgeUses(value, this.input.access.get(worker.id)?.knowledgeSnapshot, task, proof);
    const observed = await checkKnowledgeApplications(uses, { task, projectRoot: path.join(worker.worktree, this.input.state.problem.projectRelative),
      env: this.input.access.get(worker.id)?.environment ?? {}, environmentDigest: this.input.state.environmentDigest,
      commit, signal: this.input.signal, timeoutMs: this.input.timeoutMs,
      originalContexts: this.input.state.problem.targets,
      sourceAtCommit: file => committedSource(worker.worktree, commit, path.posix.join(this.input.state.problem.projectRelative, file)),
      previous: this.archive.deliveries?.flatMap(delivery => delivery.knowledgeUses ?? []) });
    if (rejected) this.input.emit('knowledge_use_rejected', { taskId: task.id, commit, rejected });
    for (const use of observed) this.input.emit('knowledge_use_observed', { ...use, taskId: task.id, commit });
    return observed;
  }
}
