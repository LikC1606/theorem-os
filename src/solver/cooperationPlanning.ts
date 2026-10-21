import { parseCooperationPlan, isAdvisoryTask as advisory } from './tasks';
import fs from 'node:fs';
import path from 'node:path';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';
import { commitSolverSources, committedSource, git, solverProofImports, withSolverWorktree } from './problem';
import { originalGoalTaskFocus, routeAllowsTask, taskCanStart, plannedTaskDependencyIds } from './modules/search';
import { readMathResponse as block, MAX_RESEARCH_NOTES_BYTES } from './deliveries';
import { applyTaskChanges, ownedSourceDigest, taskChanges } from './cooperativeProof';
import { statementSnapshot } from './statementReview';
import { proofReferencesUnchanged } from './proofReferences';
import { refreshRouteBlockers, routeBlockerBasis } from './routeControl';
import { pendingResearchHandoffs } from './researchHandoffs';
import { pendingResearchChallenges } from './researchChallenges';
import { captureObligationSnapshot } from './obligationProgress';
import { taskConnectionCheckCurrent } from './taskConnections';
import { taskGroup, taskVersion, taskProofContractVersion, taskReferenceDependencies, invalidatedTaskIds, type CooperativeTask, type TaskRecord,
  type CooperativeAction } from './tasks';
import { digest, HumanEditRecord, InitialPlanPublication, RETRY_DISPATCH, DispatchResult, bounded, deliveryInputFields, readCooperationPlan } from './cooperationShared';
import { CooperationIntegration } from './cooperationIntegration';

/** Lead plan acceptance, plan identity and original-goal frontier recovery. */
export abstract class CooperationPlanning extends CooperationIntegration {
  protected syncPlanNotes() {
    if (!this.archive.planEdited) return;
    const file = path.join(this.lead.worktree, 'RESEARCH.md');
    const source = fs.existsSync(file) ? readMathText(file, MAX_RESEARCH_NOTES_BYTES) : '';
    const plan = '```math\n' + JSON.stringify({ tasks: this.archive.tasks.map(node => node.task), groups: this.archive.groups?.map(route => route.group),
      ...(this.archive.proofRoutes?.length ? { proofRoutes: this.archive.proofRoutes } : {}) }) + '\n```';
    fs.writeFileSync(file, /```(?:math|math-plan)\s*\n[\s\S]*?\n```/u.test(source)
      ? source.replace(/```(?:math|math-plan)\s*\n[\s\S]*?\n```/u, () => plan) : plan + '\n' + bounded(source, 8000));
    this.archive.planEdited = false;
  }
  protected planningInputDigest() {
    const versions = new Map(this.archive.tasks.map(node => [node.task.id, digest(node.task)]));
    const deliveries = [...new Set((this.archive.deliveries ?? []).filter(record => record.status !== 'superseded' &&
      (!record.taskId || versions.get(record.taskId) === record.taskDigest))
      .map(record => canonicalMathJson(deliveryInputFields(record))))].sort();
    return mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      environmentDigest: this.input.state.environmentDigest, planVersion: this.archive.planVersion,
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      liveWorkers: this.input.workers.filter(worker => this.liveWorkers.has(worker.id)).map(({ id, role }) => ({ id, role })),
      progress: captureObligationSnapshot(this.archive.tasks, { groups: this.archive.groups,
        environmentDigest: this.input.state.environmentDigest, proofRoutes: this.archive.proofRoutes, blockers: this.archive.blockers }).digest,
      tasks: this.archive.tasks.map(node => ({ id: node.task.id, status: node.status, feedback: node.feedback })),
      researchDecisions: this.archive.researchDecisions,
      challengeDecisions: this.archive.challengeDecisions,
      pendingChallengeActivations: pendingResearchChallenges(this.archive).map(item => [item.id, item.activationDigest]),
      pendingHandoffActivations: pendingResearchHandoffs(this.archive).map(item => [item.id, item.activationDigest]), deliveries }));
  }
  protected planningEvidenceDigest() {
    // Plan invalidation can supersede old deliveries, so compare their immutable content.
    return mathDigest(canonicalMathJson({ problemReceiptDigest: this.input.state.problem.receiptDigest,
      environmentDigest: this.input.state.environmentDigest,
      liveWorkers: this.input.workers.filter(worker => this.liveWorkers.has(worker.id)).map(({ id, role }) => ({ id, role })),
      sourceDigest: ownedSourceDigest(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!),
      deliveries: (this.archive.deliveries ?? []).filter(record => record.producer !== this.lead.id)
        .map(({ status: _status, evidence: _evidence, ...record }) => record) }));
  }
  protected activeGoalFrontier() {
    const focus = originalGoalTaskFocus(this.archive.tasks, this.archive.groups, this.input.state.environmentDigest, { includeParkedTasks: true });
    return [...focus.frontier].map(taskId => {
      const node = this.node(taskId);
      return { taskId, status: node.status, attempts: node.attempts, goalIds: [...focus.frontierGoals.get(taskId)!], parkedBy: node.routeParking ?? [] };
    });
  }
  private resumeUnattemptedFrontier(frontier: ReturnType<CooperationPlanning['activeGoalFrontier']>) {
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
      node.typePreflight?.status !== 'invalid' &&
      !node.feedback?.startsWith('math_task_repeated_failed_input\n') &&
      !this.archive.blockers?.some(blocker => blocker.taskId === node.task.id && blocker.status === 'parked') &&
      routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) && taskCanStart(node.task, this.archive.tasks, this.archive.groups) &&
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
  protected requestFrontierRecovery(frontier: ReturnType<CooperationPlanning['activeGoalFrontier']>): CooperativeAction | undefined {
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
  protected async investigateFrontierRecovery(frontier: ReturnType<CooperationPlanning['activeGoalFrontier']>) {
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
  private async waitForFrontierInput(frontier: ReturnType<CooperationPlanning['activeGoalFrontier']>, inputDigest: string) {
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
  protected validateRecoveryPlan(action: Extract<CooperativeAction, { kind: 'lead' | 'assemble' }>,
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
  protected proposedPlanDigest() {
    try {
      const { tasks, groups, proofRoutes, recovery, handoffDecisions, challengeDecisions } = block(this.lead.worktree, 'math-plan');
      return mathDigest(canonicalMathJson({ tasks, groups, proofRoutes, recovery, handoffDecisions, challengeDecisions }));
    } catch {
      // A notes-only commit must not make an identical malformed response new input.
      const file = path.join(this.lead.worktree, 'RESEARCH.md');
      return fs.existsSync(file) ? git(this.lead.worktree, ['hash-object', '--', file]) : 'missing';
    }
  }
  protected rejectPlan(error: unknown) {
    const reason = error instanceof Error ? error.message : 'math_plan_invalid';
    const proposalDigest = this.proposedPlanDigest(), inputDigest = this.planningInputDigest();
    const previous = this.archive.planRejection;
    const stalled = previous?.proposalDigest === proposalDigest && previous.inputDigest === inputDigest && previous.error === reason;
    this.archive.error = reason;
    this.archive.planRejection = { proposalDigest, inputDigest, error: reason, stalled };
    this.needsLead = !stalled;
    this.input.emit('plan_rejected', { ...this.archive.planRejection });
  }
  protected async mergeLeadSources(commit: string, seedCommit: string, canonical = this.archive.canonicalCommit!) {
    const problem = this.input.state.problem;
    git(this.lead.worktree, ['merge-base', '--is-ancestor', seedCommit, commit]);
    const changes = taskChanges(problem, this.lead.worktree, commit, undefined, { seedCommit });
    const imports = problem.ownedFiles.filter(file => file.endsWith('.lean')).flatMap(file => {
      const before = solverProofImports(problem, committedSource(this.lead.worktree, seedCommit, `${problem.projectRelative}/${file}`));
      return solverProofImports(problem, committedSource(this.lead.worktree, commit, `${problem.projectRelative}/${file}`))
        .filter(module => !before.includes(module)).map(module => ({ file, module }));
    });
    return withSolverWorktree(this.lead.worktree, canonical, async checkout => {
      applyTaskChanges(problem, checkout, changes, imports);
      const merged = commitSolverSources(problem, checkout);
      this.pin(merged);
      return merged;
    });
  }
  protected preserveLeadDraft(commit: string, seedCommit: string | undefined, reason: string, requestDecision = true) {
    const summary = `Saved Lead draft pending integration: ${reason}. ` +
      `Inspect git show ${commit}:PROJECT_RELATIVE_PATH and reapply the useful declarations against the current canonical sources. ` +
      'This draft has no proof acceptance.';
    if (!this.archive.deliveries?.some(record => record.producer === this.lead.id && record.kind === 'progress' &&
        record.commit === commit && record.summary.startsWith('Saved Lead draft pending integration:'))) {
      this.record(this.lead, undefined, 'progress', 'advisory', summary, { commit });
    }
    if (requestDecision) { this.archive.error = reason; this.needsLead = true; }
    this.input.emit('lead_draft_preserved', { commit, seedCommit, canonicalCommit: this.archive.canonicalCommit, reason });
  }
  protected async restoreLeadSources() {
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
  protected planInvalidation({ tasks, groups, proofRoutes }: ReturnType<typeof parseCooperationPlan>, proofContracts = false) {
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
    const proposed = tasks.map(task => ({ task, status: 'pending' as const, attempts: 0,
      alternativeRoutes: proofRoutes?.filter(route => route.targetTaskId === task.id) }));
    const routeChanges = new Set(this.archive.tasks.filter(node => node.status !== 'integrated' &&
      (canonicalMathJson(node.alternativeRoutes ?? []) !== canonicalMathJson(proofRoutes?.filter(route => route.targetTaskId === node.task.id) ?? []) ||
        node.assignment?.connectionCheck && !taskConnectionCheckCurrent(node.task, node.assignment, proposed)))
      .map(node => node.task.id));
    return invalidatedTaskIds(this.archive.tasks, tasks, changedGroups, dependencies, routeChanges,
      proofContracts ? taskProofContractVersion : taskVersion);
  }
  protected async acceptPlan(plan = readCooperationPlan(this.input.state.problem, this.lead.worktree), edit?: HumanEditRecord,
    publication?: { action: CooperativeAction; receipt: Omit<InitialPlanPublication, 'planVersion'> }) {
    const { tasks, groups, proofRoutes } = plan;
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
    const proofChanges = this.planInvalidation(plan, true);
    const revalidate = new Set([...invalidated].filter(id => !proofChanges.has(id) && current.get(id)?.status === 'integrated'));
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
      if (previous && (!invalidated.has(task.id) || revalidate.has(task.id))) {
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
    if (publication) {
      // Publish the graph, receipt and dispatch continuation together before waking any peer.
      this.archive.initialPlanPublication = { ...publication.receipt, planVersion: this.archive.planVersion };
      this.initialPlans.set(publication.action, { plan, version: this.archive.planVersion });
    }
    // Restored reviews include elaboration; compare them only after rebuilding that context.
    const missingStatementContext = (node: TaskRecord) => !this.statementContexts.has(statementSnapshot(
      this.input.state.problem, node.task, this.lead.worktree, this.archive.canonicalCommit!, this.input.state.environmentDigest,
      this.dependencies(node.task).map(dependency => ({ task: dependency.task, taskDigest: digest(dependency.task) }))).snapshotDigest);
    const synchronize = this.archive.tasks.filter(node => revalidate.has(node.task.id) || node.task.statementReview &&
      (invalidated.has(node.task.id) || !current.has(node.task.id) || !this.archive.statementReviews?.some(review =>
        review.taskId === node.task.id && review.taskDigest === digest(node.task) && review.status !== 'superseded') ||
        missingStatementContext(node)));
    this.markPendingValidation(synchronize, revalidate);
    this.changed(edit);
    this.input.emit('plan_updated', { groups: this.archive.groups, tasks: tasks.map(task =>
      ({ id: task.id, kind: task.kind, dependsOn: task.dependsOn, groupId: taskGroup(task), sharing: task.sharing ?? 'problem' })), invalidated: [...invalidated] });
    if (this.archive.tasks.some(node => node.pendingValidation)) this.schedulePlanSynchronization();
    else {
      this.syncStatementReviews(invalidated);
      if (edit) edit.pendingSync = undefined;
    }
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
  protected planVersion() {
    return mathDigest(canonicalMathJson({ tasks: this.archive.tasks.map(node => node.task),
      groups: this.archive.groups?.map(route => route.group),
      ...(this.archive.proofRoutes?.length ? { proofRoutes: this.archive.proofRoutes } : {}) }));
  }
  protected async idleFrontier(frontier: ReturnType<CooperationPlanning['activeGoalFrontier']>, inputDigest: string): Promise<DispatchResult> {
    if (this.preparingTaskTypes.size) return this.waitForDispatch();
    if (this.resumeUnattemptedFrontier(frontier)) return RETRY_DISPATCH;
    const recovery = this.requestFrontierRecovery(frontier);
    if (recovery) return recovery;
    if (await this.investigateFrontierRecovery(frontier)) return RETRY_DISPATCH;
    if (await this.waitForFrontierInput(frontier, inputDigest)) return RETRY_DISPATCH;
    this.input.emit('routes_idle', { groups: this.archive.groups,
      goalIds: [...new Set(frontier.flatMap(item => item.goalIds))], frontier,
      reason: frontier.length ? 'unchanged-mathematical-input' : 'no-active-goal-frontier', inputDigest });
  }
}
