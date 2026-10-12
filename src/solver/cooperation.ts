import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { canonicalMathJson, mathDigest, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration } from '../math/verifier';
import { commitSolverSources, committedSource, git, withSolverWorktree, type SolverProblem } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import type { SolverRunState } from './archive';
import type { ResearchWorker } from './modules/organization';
import type { ContextBundle } from './modules/context';
import type { ProofCheck } from './modules/evidence';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { routeAllowsTask, taskCanStart, taskDependenciesReady } from './modules/search';
import { deliveryDetails, readDeliveryLines, readMathResponse as block, type DeliveryRecord } from './deliveries';
import { applyTaskChanges, checkTaskProof, omitTaskHelpers, ownedSourceDigest, projectTaskSources, taskChanges, type TaskProof } from './cooperativeProof';
import { assertStatementSnapshot, isStatementAction, readBacktranslation, statementSnapshot, writeStatementSnapshot,
  type StatementAction, type StatementReview } from './statementReview';
import { captureProofReferences, proofReferencesUnchanged, type ProofReferences } from './proofReferences';

import { taskGroup, taskVersion, taskReferenceDependencies, assignmentDeliveryFile, markTaskReferences, hasTaskReferences,
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
  planVersion?: string; planEdited?: boolean; statementReviews?: StatementReview[] };
const advisory = (task: CooperativeTask) => ['research', 'sketch'].includes(task.kind);
const bounded = (text: string, bytes: number) => Buffer.from(text).subarray(0, bytes).toString('utf8').replace(/\uFFFD$/u, '');
/** Model proposes tasks; the host validates coverage, exact targets and an acyclic dependency graph. */
export function readCooperationPlan(problem: SolverProblem, worktree: string): { tasks: CooperativeTask[]; groups: RouteGroup[] } {
  return parseCooperationPlan(problem, block(worktree, 'math-plan'));
}
export function parseCooperationPlan(problem: SolverProblem, value: any): { tasks: CooperativeTask[]; groups: RouteGroup[] } {
  if (!value || !Array.isArray(value.tasks) || value.tasks.length < 1 || value.tasks.length > 32)
    throw new Error('math_plan_invalid');
  const rawGroups = value.groups ?? [{ id: 'main', objective: 'Prove the original problem' }];
  if (!Array.isArray(rawGroups) || !rawGroups.length || rawGroups.length > 16) throw new Error('math_plan_invalid_groups');
  const groups: RouteGroup[] = rawGroups.map((group: any) => {
    if (!group || typeof group.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(group.id) ||
        typeof group.objective !== 'string' || !group.objective.trim() || group.objective.length > 2000 ||
        !['active', 'paused', 'stopped'].includes(group.status ?? 'active') ||
        !Number.isSafeInteger(group.revision ?? 0) || (group.revision ?? 0) < 0 ||
        (group.engineerId !== undefined && (typeof group.engineerId !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(group.engineerId))) ||
        (group.maxTurns !== undefined && (!Number.isSafeInteger(group.maxTurns) || group.maxTurns < 0)) ||
        (group.maxConcurrent !== undefined && (!Number.isSafeInteger(group.maxConcurrent) || group.maxConcurrent < 1 || group.maxConcurrent > 3)))
      throw new Error('math_plan_invalid_group');
    return { id: group.id, objective: group.objective, status: group.status ?? 'active', revision: group.revision ?? 0,
      ...(group.engineerId === undefined ? {} : { engineerId: group.engineerId }),
      ...(group.maxTurns === undefined ? {} : { maxTurns: group.maxTurns }),
      ...(group.maxConcurrent === undefined ? {} : { maxConcurrent: group.maxConcurrent }) };
  });
  if (new Set(groups.map(group => group.id)).size !== groups.length) throw new Error('math_plan_duplicate_group');
  const tasks: CooperativeTask[] = value.tasks.map((value: any) => {
    const task = value && { ...value, dependsOn: value.dependsOn ?? [], proofPath: value.proofPath ??
      (value.kind === 'goal' ? problem.targets.find(target => target.theoremName === value.theoremName)?.proofPath :
        problem.ownedFiles.filter(file => file.endsWith('.lean')).length === 1 ? problem.ownedFiles.find(file => file.endsWith('.lean')) : undefined) };
    if (!task || typeof task.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(task.id) ||
        !['research', 'sketch', 'lemma', 'goal'].includes(task.kind) || typeof task.objective !== 'string' ||
        !task.objective.trim() || task.objective.length > 2000 || !Array.isArray(task.dependsOn) ||
        task.dependsOn.some((id: unknown) => typeof id !== 'string') ||
        !Number.isSafeInteger(task.revision ?? 0) || (task.revision ?? 0) < 0)
      throw new Error('math_plan_invalid_task');
    if ((task.status !== undefined && !['active', 'paused', 'stopped'].includes(task.status)) ||
        (task.conditional !== undefined && (typeof task.conditional !== 'boolean' || advisory(task))) ||
        (task.statementReview !== undefined && (typeof task.statementReview !== 'boolean' || advisory(task))) ||
        (task.informalStatement !== undefined && (typeof task.informalStatement !== 'string' || !task.informalStatement.trim() || task.informalStatement.length > 8000)) ||
        (task.statementReview === true && !task.informalStatement) ||
        (task.ownerId !== undefined && (typeof task.ownerId !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(task.ownerId))) ||
        (task.premises !== undefined && (!Array.isArray(task.premises) || task.premises.length > 32 ||
          task.premises.some((premise: unknown) => typeof premise !== 'string' || premise.length > 2000)))) throw new Error('math_plan_invalid_task');
    if (!groups.some(group => group.id === (task.groupId ?? 'main')) ||
        (task.sharing !== undefined && !['group', 'problem'].includes(task.sharing))) throw new Error('math_plan_invalid_task_group');
    if (!advisory(task) && (!problem.ownedFiles.includes(task.proofPath) ||
        typeof task.theoremName !== 'string' || !/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(task.theoremName)))
      throw new Error('math_plan_invalid_proof_target');
    if (task.kind === 'goal' && !problem.targets.some(target => target.proofPath === task.proofPath && target.theoremName === task.theoremName))
      throw new Error('math_plan_changed_original_target');
    if (task.kind === 'lemma' && (typeof task.type !== 'string' || !task.type.trim() || task.type.length > 8000 ||
        Object.values(problem.declarations).some(items => items.some(item => item.name.split('.').at(-1) === task.theoremName.split('.').at(-1)))))
      throw new Error('math_plan_invalid_helper_type');
    return { id: task.id, kind: task.kind, objective: task.objective, dependsOn: [...new Set<string>(task.dependsOn)],
      revision: task.revision ?? 0, ...(advisory(task) ? {} : { proofPath: task.proofPath, theoremName: task.theoremName }),
      ...(task.kind === 'lemma' ? { type: task.type } : {}),
      ...(task.conditional === undefined ? {} : { conditional: task.conditional }),
      ...(task.statementReview === undefined ? {} : { statementReview: task.statementReview }),
      ...(task.informalStatement === undefined ? {} : { informalStatement: task.informalStatement }),
      ...(task.status === undefined ? {} : { status: task.status }),
      ...(task.ownerId === undefined ? {} : { ownerId: task.ownerId }),
      ...(task.premises === undefined ? {} : { premises: task.premises }),
      ...(task.groupId === undefined ? {} : { groupId: task.groupId }),
      ...(task.sharing === undefined ? groups.length > 1 ? { sharing: 'group' } : {} : { sharing: task.sharing }) };
  });
  if (new Set(tasks.map(task => task.id)).size !== tasks.length ||
      new Set(tasks.filter(task => !advisory(task)).map(task => task.theoremName!.split('.').at(-1))).size !== tasks.filter(task => !advisory(task)).length)
    throw new Error('math_plan_duplicate_task');
  if (problem.targets.some(target => tasks.filter(task => task.kind === 'goal' && task.proofPath === target.proofPath && task.theoremName === target.theoremName).length !== 1))
    throw new Error('math_plan_incomplete_original_coverage');
  const byId = new Map(tasks.map(task => [task.id, task]));
  const visiting = new Set<string>(), visited = new Set<string>();
  const visit = (id: string) => {
    if (visiting.has(id)) throw new Error('math_plan_dependency_cycle');
    if (visited.has(id)) return;
    const task = byId.get(id);
    if (!task) throw new Error('math_plan_missing_dependency');
    visiting.add(id); task.dependsOn.forEach(visit); visiting.delete(id); visited.add(id);
  };
  tasks.forEach(task => visit(task.id));
  for (const task of tasks) for (const id of task.dependsOn) {
    const dependency = byId.get(id)!;
    if (taskGroup(task) !== taskGroup(dependency) && dependency.sharing === 'group') throw new Error('math_plan_dependency_not_shared');
  }
  return { tasks, groups };
}

export function readCooperativePlan(problem: SolverProblem, worktree: string): CooperativeTask[] {
  return readCooperationPlan(problem, worktree).tasks;
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
  private leadStopped = false;
  private checkedDeliveries = new WeakSet<TaskProof>();
  private checkedStatementReferences = new WeakSet<ProofReferences>();
  private active = new Map<string, { action: CooperativeAction; interrupt: () => Promise<void>; notify: (message: string) => Promise<void>; cancelled?: boolean }>();
  private notifications = new Set<Promise<void>>();
  private pendingPulse?: Promise<void>;
  private timer?: NodeJS.Timeout;
  private failure?: Error;
  private pinned = new Set<string>();
  constructor(private readonly input: { state: SolverRunState; workers: readonly ResearchWorker[];
    access: ReadonlyMap<string, WorkerAccess>; signal: AbortSignal; timeoutMs?: number;
    save: () => void; emit: (event: string, details?: Record<string, unknown>) => void;
    modules: SolverModules; exclusiveCheck: <T>(check: () => Promise<T>) => Promise<T> }) {
    this.lead = input.workers[0];
    this.archive = input.state.cooperation ??= { tasks: [] };
    this.archive.canonicalCommit ??= git(this.lead.worktree, ['rev-parse', 'HEAD']);
    this.liveWorkers = new Set(input.workers.slice(1).map(worker => worker.id));
    this.needsLead = !this.archive.tasks.length || Boolean(this.archive.error) || this.archive.tasks.some(node => node.status === 'blocked');
  }
  private syncEditChecks() {
    for (const edit of this.archive.edits ?? []) {
      if (edit.status !== 'applied' || !edit.recheck) continue;
      const before = canonicalMathJson(edit.recheck);
      for (const result of edit.recheck.tasks) {
        if (['removed', 'superseded'].includes(result.status)) continue;
        const node = this.node(result.taskId);
        if (!node || digest(node.task) !== result.taskDigest) {
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
    for (const route of this.archive.groups ?? []) {
      const owners = new Set(this.archive.tasks.filter(node => node.status === 'running' && taskGroup(node.task) === route.group.id)
        .map(node => node.assignment?.workerId));
      for (const [id, active] of this.active) if (active.action.kind === 'task' && taskGroup(active.action.task) === route.group.id) owners.add(id);
      for (const review of this.archive.statementReviews ?? []) if (['translating', 'reviewing'].includes(review.status) &&
          this.node(review.taskId) && taskGroup(this.node(review.taskId).task) === route.group.id) owners.add(review.workerId);
      route.busy = owners.size;
    }
    this.archive.planVersion = mathDigest(canonicalMathJson({ tasks: this.archive.tasks.map(node => node.task), groups: this.archive.groups?.map(route => route.group) }));
    if (edit?.status === 'applied') edit.planVersion = this.archive.planVersion;
    this.syncEditChecks();
    this.input.save();
    for (const worker of this.input.workers) {
      const action = this.active.get(worker.id)?.action;
      const scoped = this.contextState(action, worker);
      const visible = scoped.tasks;
      const deliveries = (scoped.deliveries ?? []).slice(-16);
      writeMathJsonDurable(path.join(worker.worktree, 'COOPERATION.json'), {
        planVersion: this.archive.planVersion,
        edits: (this.archive.edits ?? []).slice(-16),
        agents: this.input.workers.map(peer => {
          const work = this.active.get(peer.id)?.action;
          return { id: peer.id, role: work && (work.kind === 'review' || isStatementAction(work)) ? 'reviewer' : peer.role,
            status: work ? 'working' : peer.id === this.lead.id || this.liveWorkers.has(peer.id) ? 'idle' : 'stopped',
            work: work && { kind: work.kind, taskId: work.kind === 'task' ? work.task.id : undefined,
              version: work.kind === 'task' ? work.assignment.taskDigest : work.seedCommit } };
        }),
        peers: this.archive.tasks.map(node => ({ id: node.task.id, groupId: taskGroup(node.task), kind: node.task.kind,
          status: node.status, owner: node.assignment?.workerId ?? node.task.ownerId, dependsOn: node.task.dependsOn,
          ...(visible.includes(node) ? { objective: node.task.objective, feedback: node.feedback,
            actualReferences: (node.integratedCheck ?? node.proof)?.references } : {}) })),
        deliveries: deliveries.map(({ evidence: _evidence, ...record }) => record),
        statements: (scoped.statementReviews ?? []).map(review => ({
          id: review.id, taskId: review.taskId, taskDigest: review.taskDigest, status: review.status,
          leanStatement: review.leanStatement, intendedStatement: review.intendedStatement, translation: review.translation,
          summary: review.summary, snapshotDigest: review.snapshotDigest, environmentDigest: review.environmentDigest, actualReferences: review.references })),
      });
    }
    for (const wake of this.waiters) wake(); this.waiters.clear();
  }
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
  private visibleDeliveries(task?: CooperativeTask) {
    return (this.archive.deliveries ?? []).filter(record => {
      if (record.status === 'superseded') return false;
      if (!record.taskId) return !task;
      const node = this.archive.tasks.find(item => item.task.id === record.taskId && digest(item.task) === record.taskDigest);
      return node && record.dependencies.every(dependency => this.archive.tasks.some(item =>
        item.task.id === dependency.taskId && digest(item.task) === dependency.taskDigest)) &&
        (!task || taskGroup(node.task) === taskGroup(task) || node.task.sharing !== 'group');
    });
  }
  private inform(record: DeliveryRecord) {
    for (const [id, active] of this.active) {
      if (id === record.producer) continue;
      if (isStatementAction(active.action)) continue;
      const task = active.action.kind === 'task' ? active.action.task : undefined;
      if (task && record.taskId && !this.visibleDeliveries(task).includes(record)) continue;
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
    if (record.evidence) record.evidence = { passed: record.evidence.passed, verification: record.evidence.verification };
    this.pin(record.commit); this.pin(record.evidence?.verification.targetCommit);
    (this.archive.deliveries ??= []).push(record); this.changed();
    if (status !== 'superseded') this.inform(record);
    return record;
  }
  start() {
    this.timer = setInterval(() => { void this.pulse().catch(error => {
      this.input.emit('cooperation_poll_failed', { reason: error instanceof Error ? error.message : 'unknown' });
      if (error instanceof Error && error.message === 'math_verifier_unavailable') { this.failure = error; this.changed(); }
    }); }, 200);
    this.timer.unref();
  }
  private syncPlanNotes() {
    if (!this.archive.planEdited) return;
    const file = path.join(this.lead.worktree, 'RESEARCH.md');
    const source = fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '';
    const plan = '```math\n' + JSON.stringify({ tasks: this.archive.tasks.map(node => node.task), groups: this.archive.groups?.map(route => route.group) }) + '\n```';
    fs.writeFileSync(file, /```(?:math|math-plan)\s*\n[\s\S]*?\n```/u.test(source)
      ? source.replace(/```(?:math|math-plan)\s*\n[\s\S]*?\n```/u, plan) : plan + '\n' + bounded(source, 8000));
    this.archive.planEdited = false;
  }
  async stop() {
    clearInterval(this.timer);
    try { await this.pendingPulse; } catch (error) { if (!this.input.signal.aborted) throw error; }
    await Promise.allSettled([...this.notifications]);
    this.syncPlanNotes();
    if (!this.input.signal.aborted) this.archive.canonicalCommit = this.seed(this.lead, this.archive.canonicalCommit!);
    this.input.save();
  }
  pulse(): Promise<void> {
    if (this.pendingPulse) return this.pendingPulse;
    const pending = this.input.exclusiveCheck(async () => {
      const cursors = this.archive.cursors ??= {};
      let consumed = false;
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
          this.acceptPlan(parseCooperationPlan(this.input.state.problem, edit), record);
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
        const active = this.active.get(worker.id);
        if (active?.action.kind !== 'task') continue;
        for (const log of [assignmentDeliveryFile(active.action.assignment), 'DELIVERIES.jsonl']) {
          const scoped = log !== 'DELIVERIES.jsonl', key = scoped ? `${worker.id}/${log}` : worker.id;
          const batch = readDeliveryLines(path.join(worker.worktree, log), cursors[key] ?? 0);
          consumed ||= batch.lines.length > 0;
          for (const line of batch.lines) {
            try { await this.receive(worker, active.action, JSON.parse(line), scoped); }
            catch (error) {
              if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
              this.input.emit('delivery_rejected', { workerId: worker.id,
                reason: error instanceof Error ? error.message : 'math_delivery_invalid' }); }
          }
          cursors[key] = batch.offset;
        }
      }
      if (edits.lines.length) this.changed(); else if (consumed) this.input.save();
    });
    this.pendingPulse = pending;
    void pending.finally(() => { if (this.pendingPulse === pending) this.pendingPulse = undefined; }).catch(() => {});
    return pending;
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
      const remaining = [...new Set([...(value.remainingObligations ?? []),
        ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])] as string[];
      this.record(worker, node.task, 'progress', remaining.length || node.task.kind === 'sketch' ? 'conditional' : 'advisory', value.summary,
        { ...details, submissionId: value.id, remainingObligations: remaining });
      if (value.needsDecision === true) { this.needsLead = true; this.changed(); }
      return;
    }
    if (advisory(node.task) || typeof value.commit !== 'string' || !/^[a-f0-9]{40,64}$/u.test(value.commit)) throw new Error('math_delivery_requires_fixed_proof');
    if (!taskCanStart(node.task, this.archive.tasks)) throw new Error('math_delivery_unfinished_dependencies');
    if (['conditional', 'integrated'].includes(node.status)) return;
    const proof = await this.check(node.task, action.assignment, worker.worktree, value.commit);
    await this.deliverProof(worker, node, proof, value.summary, { submissionId: value.id, evidenceRefs: value.evidenceRefs });
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
    const found = new Set<string>();
    const ids = (node: TaskRecord) => taskReferenceDependencies(node)?.map(reference => reference.taskId) ?? node.task.dependsOn;
    const visit = (id: string) => { if (found.has(id)) return; found.add(id); ids(this.node(id)).forEach(visit); };
    const node = this.node(task.id);
    (node?.task === task ? ids(node) : task.dependsOn).forEach(visit);
    return [...found].map(id => this.node(id));
  }
  private ready(node: TaskRecord) {
    return this.input.modules.M3.ready(this.archive.tasks, this.archive.groups).includes(node);
  }
  private retainedGoals(task: CooperativeTask) {
    return this.dependencies(task).filter(node => node.task.kind === 'goal' && node.status === 'integrated').map(node => node.task.theoremName!);
  }
  private async check(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string,
    conditions = task.conditional ? this.dependencies(task).filter(node => node.task.kind === 'lemma' && node.status !== 'integrated').map(node => node.task) : []) {
    const required = new Set([task.id, ...this.dependencies(task).map(node => node.task.id)]);
    const excluded = this.archive.tasks.filter(node => node.task.kind === 'lemma' && !required.has(node.task.id)).map(node => node.task.theoremName!);
    const proof = await (this.input.modules.M2.checkTask ?? checkTaskProof)(this.input.state.problem, worktree, commit, task, assignment, this.retainedGoals(task),
      this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs, excluded, conditions, this.input.state.environmentDigest);
    const declarationHash = proof.passed && proof.verification.targetCommit && hashMathFormalSourceDeclaration(
      committedSource(worktree, proof.verification.targetCommit, `${this.input.state.problem.projectRelative}/${task.proofPath}`), task.theoremName!);
    const projected = proof.passed && projectTaskSources(this.input.state.problem, worktree, commit, task,
      this.retainedGoals(task), excluded, conditions);
    const allowed = new Set(this.input.state.problem.ownedFiles.map(file => `${this.input.state.problem.projectRelative}/${file}`));
    allowed.add('RESEARCH.md');
    const projectionMatches = projected && proof.verification.targetCommit &&
      [...projected].every(([file, source]) => source === committedSource(worktree, proof.verification.targetCommit!,
        `${this.input.state.problem.projectRelative}/${file}`)) &&
      git(worktree, ['diff', '--no-renames', '--name-only', '-z', commit, proof.verification.targetCommit, '--'])
        .split('\0').filter(Boolean).every(file => allowed.has(file));
    if (proof.commit !== commit || proof.taskDigest !== digest(task) || proof.seedCommit !== assignment.seedCommit ||
        proof.sourceDigest !== ownedSourceDigest(this.input.state.problem, worktree, commit) ||
        canonicalMathJson(proof.conditions ?? []) !== canonicalMathJson(conditions.map(task => ({ taskId: task.id, taskDigest: digest(task) }))) ||
        (proof.passed && (!projectionMatches || !declarationHash || proof.verification.status !== 'kernel_verified' || proof.verification.results.length !== 1 ||
          proof.verification.results.some(result => result.status !== 'kernel_verified' || result.targetCommit !== proof.verification.targetCommit ||
            result.theoremName !== task.theoremName || result.proofPath !== task.proofPath ||
            result.statementHash !== digest(task) || result.leanStatementHash !== digest(task) ||
            result.sourceDeclarationHash !== declarationHash || result.claim !== 'statement'))))
      throw new Error('math_task_check_identity_changed');
    if (proof.references) {
      const references = proof.references;
      references.tasks = this.archive.tasks.filter(node => node.task.id !== task.id && this.referencesTask(references, node))
        .map(node => ({ taskId: node.task.id, taskDigest: digest(node.task) }));
      markTaskReferences(proof);
    }
    this.checkedDeliveries.add(proof);
    return proof;
  }
  private referencesTask(references: ProofReferences, node: TaskRecord) {
    return references.inputs.some(input => input.file === node.task.proofPath &&
      input.name && [node.task.theoremName, ...(node.proof?.changes.map(change => change.name) ?? [])]
        .some(name => name && name.split('.').at(-1) === input.name!.split('.').at(-1)));
  }
  private async deliverProof(worker: ResearchWorker, node: TaskRecord, proof: TaskProof, summary: string, options: Partial<DeliveryRecord> = {}) {
    node.proof = proof;
    if (['unavailable', 'blocked'].includes(proof.verification.status)) throw new Error('math_verifier_unavailable');
    node.status = proof.passed ? proof.conditions?.length ? 'conditional' : 'delivered' : 'blocked';
    if (!proof.passed) { node.feedback = solverProofFeedback(proof); this.needsLead = true; }
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
    while (pending.length) {
      const index = pending.findIndex(node => node.task.dependsOn.every(id => this.node(id).status !== 'integrated' || checked.has(id)));
      if (index < 0) throw new Error('math_plan_dependency_cycle');
      const [node] = pending.splice(index, 1);
      if (changedOnly && taskReferenceDependencies(node) && taskDependenciesReady(node.task, this.archive.tasks) && node.integratedCheck?.references &&
          proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, canonical, node.integratedCheck.references, this.input.state.environmentDigest)) {
        this.input.emit('task_check_reused', { taskId: node.task.id, commit: node.integratedCheck.commit, canonicalCommit: canonical });
        checked.add(node.task.id); continue;
      }
      const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical };
      try {
        const receipt = await this.check(node.task, assignment, this.lead.worktree, canonical, []);
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.status = 'blocked'; node.feedback = solverProofFeedback(receipt); this.needsLead = true; }
        else if (!taskDependenciesReady(node.task, this.archive.tasks)) {
          node.status = 'blocked'; node.feedback = 'math_task_dependency_invalidated'; this.needsLead = true;
        }
      } catch (error) {
        if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
        node.status = 'blocked'; node.feedback = error instanceof Error ? error.message : 'math_task_recheck_failed'; this.needsLead = true;
      }
      checked.add(node.task.id);
    }
  }
  private supersedeStatementReview(review: StatementReview) {
    review.status = 'superseded';
    for (const record of this.archive.deliveries ?? []) if (record.statementReviewId === review.id) record.status = 'superseded';
  }
  private syncStatementReviews(invalidated = new Set<string>()) {
    if (!this.archive.statementReviews?.length && !this.archive.tasks.some(node => node.task.statementReview)) return;
    const reviews = this.archive.statementReviews ??= [];
    const snapshots = new Map(this.archive.tasks.filter(node => node.task.statementReview).map(node => [node.task.id,
      statementSnapshot(this.input.state.problem, node.task, this.lead.worktree, this.archive.canonicalCommit!,
        this.input.state.environmentDigest, this.dependencies(node.task).map(dependency =>
          ({ task: dependency.task, taskDigest: digest(dependency.task) }))) ]));
    for (const review of reviews.filter(item => item.status !== 'superseded')) {
      const node = this.node(review.taskId), snapshot = snapshots.get(review.taskId);
      if (invalidated.has(review.taskId) || !snapshot || !node || digest(node.task) !== review.taskDigest ||
          (snapshot.snapshotDigest !== review.snapshotDigest && (!review.references || !this.checkedStatementReferences.has(review.references) ||
            !proofReferencesUnchanged(this.input.state.problem, this.lead.worktree, this.archive.canonicalCommit!, review.references, this.input.state.environmentDigest)))) {
        this.supersedeStatementReview(review);
      }
      if (review.status !== 'superseded' && (!review.references || !this.checkedStatementReferences.has(review.references)) && snapshot?.snapshotDigest === review.snapshotDigest) {
        const proof = node?.integratedCheck;
        if (proof?.references && hasTaskReferences(proof)) review.references = captureProofReferences(this.input.state.problem,
          this.lead.worktree, this.archive.canonicalCommit!, proof.references.root,
          { statement: proof.references.statement, proof: [] }, this.input.state.environmentDigest, 'statement');
        if (review.references) this.checkedStatementReferences.add(review.references);
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
        dependencies: this.dependencies(task).map(node => ({ taskId: node.task.id, taskDigest: digest(node.task) })),
        workspace, files: writeStatementSnapshot(workspace, snapshot), status: 'pending' });
      this.input.emit('statement_review_requested', { taskId, reviewId: id, snapshotDigest: snapshot.snapshotDigest });
    }
    for (const active of this.active.values()) if (isStatementAction(active.action) && !this.current(active.action) && !active.cancelled) {
      const reviewId = active.action.reviewId;
      const review = reviews.find(item => item.id === reviewId);
      if (review && ['translating', 'reviewing'].includes(review.status)) {
        review.status = review.status === 'translating' ? 'pending' : 'translated'; review.workerId = undefined;
      }
      active.cancelled = true; void active.interrupt().catch(() => {});
    }
  }
  async restore() {
    this.syncPlanNotes();
    for (const review of this.archive.statementReviews ?? []) if (review.status !== 'superseded') {
      try { assertStatementSnapshot(review); }
      catch { this.supersedeStatementReview(review); continue; }
      if (review.status === 'translating') review.status = 'pending';
      if (review.status === 'reviewing') review.status = 'translated';
      review.workerId = undefined;
    }
    // A resumed review must inspect the fixed version again.
    if (this.archive.review) this.archive.review.status = 'pending';
    if (this.archive.tasks.length && fs.existsSync(path.join(this.lead.worktree, 'RESEARCH.md'))) {
      try { this.acceptPlan(); } catch (error) { this.archive.error = error instanceof Error ? error.message : 'math_plan_invalid'; this.needsLead = true; }
    }
    if (!solverSourceFeedback(this.input.state.problem, this.lead.worktree)) {
      if (this.archive.canonicalCommit !== git(this.lead.worktree, ['rev-parse', 'HEAD']) &&
          !git(this.lead.worktree, ['diff', 'HEAD', '--name-only', '--', ...this.input.state.problem.ownedFiles.map(file => path.join(this.input.state.problem.projectRelative, file))])) {
        this.seed(this.lead, this.archive.canonicalCommit!);
      }
      this.archive.canonicalCommit = commitSolverSources(this.input.state.problem, this.lead.worktree);
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
    this.syncStatementReviews();
    this.changed();
  }
  private acceptPlan(plan = readCooperationPlan(this.input.state.problem, this.lead.worktree), edit?: HumanEditRecord) {
    const { tasks, groups } = plan;
    for (const task of tasks) if (task.ownerId) {
      const owner = this.input.workers.find(worker => worker.id === task.ownerId);
      if (!owner || owner.role === 'lead' || (task.kind === 'goal' ? owner.role !== 'engineer' : owner.role !== 'researcher'))
        throw new Error('math_plan_task_owner_unavailable');
    }
    const previousGroups = new Map(this.archive.groups?.map(record => [record.group.id, record]));
    const engineer = this.input.workers.find(worker => worker.role === 'engineer');
    const configuredGroups = groups.map(group => {
      const engineerId = group.engineerId ?? engineer?.id;
      if (engineerId && !this.input.workers.some(worker => worker.id === engineerId && worker.role === 'engineer'))
        throw new Error('math_plan_group_engineer_unavailable');
      return { ...group, ...(engineerId ? { engineerId } : {}) };
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
        : [...node.task.dependsOn, ...(node.assignment?.dependencies?.map(dependency => dependency.taskId) ?? [])]];
    }));
    const invalidated = new Set(this.archive.tasks.filter(node => changedGroups.has(taskGroup(node.task)) ||
      !tasks.some(task => task.id === node.task.id && digest(task) === digest(node.task)))
      .map(node => node.task.id));
    for (let changed = true; changed;) {
      changed = false;
      for (const task of tasks) if (!invalidated.has(task.id) && (dependencies.get(task.id) ?? task.dependsOn).some(id => invalidated.has(id))) {
        invalidated.add(task.id); changed = true;
      }
    }
    for (const previousEdit of this.archive.edits ?? []) for (const result of previousEdit.recheck?.tasks ?? [])
      if (invalidated.has(result.taskId) && result.status !== 'removed') result.status = 'superseded';
    for (const record of this.archive.deliveries ?? []) if (record.taskId && invalidated.has(record.taskId)) record.status = 'superseded';
    for (const id of invalidated) {
      const previous = current.get(id);
      if (previous) this.archive.history = [...(this.archive.history ?? []),
        { task: previous.task, producer: previous.assignment?.workerId, proof: previous.proof, integratedCheck: previous.integratedCheck, finding: previous.finding }];
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
    this.input.emit('plan_updated', { groups: this.archive.groups, tasks: tasks.map(task =>
      ({ id: task.id, kind: task.kind, dependsOn: task.dependsOn, groupId: taskGroup(task), sharing: task.sharing ?? 'problem' })), invalidated: [...invalidated] });
    this.changed(edit);
  }
  private canAdvance(node: TaskRecord): boolean {
    if (node.status === 'blocked') return false;
    if (node.status === 'conditional') return node.task.dependsOn.every(id => this.canAdvance(this.node(id)));
    if (['integrated', 'completed', 'delivered', 'running'].includes(node.status)) return true;
    if ((node.task.ownerId && !this.liveWorkers.has(node.task.ownerId)) ||
        (node.assignment && !this.liveWorkers.has(node.assignment.workerId))) return false;
    return routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) && node.task.dependsOn.every(id => this.canAdvance(this.node(id)));
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
        applyTaskChanges(problem, checkout, submitted.changes);
        const merged = commitSolverSources(problem, checkout);
        const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: merged };
        const receipt = await this.check(node.task, assignment, checkout, merged);
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.feedback = solverProofFeedback(receipt); throw new Error('math_task_merged_proof_failed'); }
        this.archive.canonicalCommit = merged;
        node.status = 'integrated';
        this.pin(receipt.commit); this.pin(receipt.verification.targetCommit);
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
      if (this.leadStopped) return;
      if (worker.id === this.lead.id) {
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
            (['pending', 'translated'].includes(review.status) && this.liveWorkers.size > 0 &&
              routeAllowsTask(this.node(review.taskId).task, this.archive.tasks, this.archive.groups)));
        if (this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0) {
          if (running) { await this.wait(); continue; }
          return;
        }
        if (!running && !this.liveWorkers.size) return;
        if (this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) { await this.wait(); continue; }
        if (!running && !this.needsLead && this.archive.tasks.length && (!this.archive.review || this.archive.review.status === 'changes_requested') &&
            !this.archive.tasks.some(node => ['pending', 'blocked'].includes(node.status) && this.canAdvance(node))) {
          this.input.emit('routes_idle', { groups: this.archive.groups }); return;
        }
        if (this.needsLead || (!running && !this.archive.tasks.some(node => this.ready(node) && this.liveWorkers.size))) {
          this.needsLead = false;
          this.syncPlanNotes();
          return { kind: 'lead', seedCommit: this.seed(worker, head), planVersion: this.archive.planVersion };
        }
      } else {
        if (budget.remainingMs <= 0) return;
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
          this.input.workers.filter(item => this.liveWorkers.has(item.id)), this.archive.groups);
        if (node) {
          const engineerId = node.task.kind === 'goal' && this.archive.groups?.find(route => route.group.id === taskGroup(node.task))?.group.engineerId;
          if (!ready.includes(node) || !this.archive.tasks.includes(node) || node.status !== 'pending' ||
              !taskCanStart(node.task, this.archive.tasks) ||
              !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
              (node.task.ownerId && node.task.ownerId !== worker.id) || (engineerId && engineerId !== worker.id) ||
              (node.assignment && node.assignment.workerId !== worker.id)) throw new Error('math_task_assignment_invalid');
          const seed = this.archive.canonicalCommit!;
          const resuming = node.assignment?.workerId === worker.id;
          let scopedSeed = seed;
          if (!resuming) {
            scopedSeed = this.seed(worker, seed, node.task);
          }
          node.assignment ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id,
            seedCommit: scopedSeed, canonicalCommit: seed, groupId: taskGroup(node.task),
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
    return this.archive.tasks.filter(node => taskGroup(node.task) === taskGroup(task) ||
      (node.task.sharing !== 'group' && ['integrated', 'completed'].includes(node.status)));
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
  reviewed() {
    return this.archive.review?.status === 'accepted' && this.archive.review.commit === this.archive.canonicalCommit &&
      this.archive.tasks.filter(node => node.task.statementReview).every(node => this.archive.statementReviews?.some(review =>
        review.taskId === node.task.id && review.taskDigest === digest(node.task) && review.status === 'accepted'));
  }
  requireReview(check: ProofCheck) {
    if (this.archive.review?.commit !== check.commit) {
      this.archive.review = { commit: check.commit, sourceDigest: check.sourceDigest, status: 'pending' };
      this.input.emit('review_requested', { commit: check.commit });
    }
    this.changed();
  }
  contextState(action?: CooperativeAction, worker?: ResearchWorker): CooperationState {
    const record = worker && this.input.state.workers?.find(item => item.id === worker.id);
    const ordinaryWorker = !action && worker && worker.id !== this.lead.id;
    const task = action?.kind === 'task' ? action.task : ordinaryWorker ?
      this.archive.tasks.find(node => node.status === 'running' && node.assignment?.workerId === worker.id)?.task ??
      this.archive.tasks.find(node => node.task.id === record?.sessionTaskId)?.task : undefined;
    const tasks = task ? this.visible(task) : ordinaryWorker ?
      this.archive.tasks.filter(node => node.task.sharing !== 'group' && ['integrated', 'completed'].includes(node.status)) : this.archive.tasks;
    const visible = (id: string, version: string) => tasks.some(node => node.task.id === id && digest(node.task) === version);
    return { ...this.archive, tasks,
      // Public progress can steer another route before its proof is complete; it remains advisory.
      deliveries: this.visibleDeliveries(task).filter(item => task || tasks === this.archive.tasks ||
        !item.taskId || this.node(item.taskId).task.sharing !== 'group'),
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
        { reviewId: review.id, snapshotDigest: review.snapshotDigest });
      if (result?.reviewId !== review.id || result.snapshotDigest !== review.snapshotDigest) throw new Error('math_statement_review_identity_changed');
      if (action.kind === 'backtranslate') {
        review.translation = readBacktranslation(result); review.status = 'translated';
        review.summary = 'Independent backtranslation saved; mathematical comparison remains pending.';
        evidenceRefs = review.translation.evidenceRefs;
      } else {
        const details = deliveryDetails(result);
        if (!review.translation || !['accepted', 'changes_requested'].includes(result.verdict)) throw new Error('math_statement_review_invalid');
        review.status = result.verdict; review.summary = details.summary; evidenceRefs = details.evidenceRefs;
      }
    } catch (error) {
      review.status = 'changes_requested'; review.summary = error instanceof Error ? error.message : 'math_statement_review_failed';
    }
    review.workerId = undefined;
    if (review.status === 'accepted') this.lastAssembly = undefined;
    if (review.status === 'changes_requested') { this.archive.error = review.summary; this.needsLead = true; }
    this.record(worker, this.node(review.taskId).task, kind, review.status === 'translated' ? 'advisory' :
      review.status === 'accepted' ? 'accepted' : 'changes_requested', review.summary ?? '', { ...options, evidenceRefs });
    this.input.emit('statement_review_completed', { workerId: worker.id, taskId: review.taskId, reviewId: review.id, kind, status: review.status });
    return { checkWhole: false };
  }
  async deliver(worker: ResearchWorker, action: CooperativeAction, commit: string): Promise<{ check?: ProofCheck; checkWhole: boolean }> {
    if (isStatementAction(action)) return this.deliverStatement(worker, action);
    if (action.kind === 'review') {
      const review = this.archive.review;
      if (!review || review.commit !== action.seedCommit || review.workerId !== worker.id || review.status !== 'running') {
        this.record(worker, undefined, 'review', 'superseded', 'The reviewed version is no longer current.', { commit: action.seedCommit });
        return { checkWhole: false };
      }
      let evidenceRefs: string[] = [];
      try {
        if (ownedSourceDigest(this.input.state.problem, worker.worktree, commit) !== action.sourceDigest)
          throw new Error('math_review_source_changed');
        const result = block(worker.worktree, 'math-review', { commit: action.seedCommit, evidenceRefs: [] });
        if (result?.commit !== action.seedCommit || !['accepted', 'changes_requested'].includes(result.verdict) ||
            typeof result.summary !== 'string' || result.summary.length > 3000 || !Array.isArray(result.evidenceRefs) ||
            result.evidenceRefs.length > 16 || result.evidenceRefs.some((ref: unknown) => typeof ref !== 'string' || ref.length > 1000))
          throw new Error('math_review_delivery_invalid');
        review.status = result.verdict; review.summary = bounded(JSON.stringify(result), 5000);
        evidenceRefs = result.evidenceRefs;
        this.input.emit('review_completed', { commit: review.commit, verdict: review.status, workerId: worker.id });
      } catch (error) {
        review.status = 'changes_requested'; review.summary = error instanceof Error ? error.message : 'math_review_failed';
      }
      if (review.status === 'accepted') this.lastAssembly = undefined;
      else { this.archive.error = review.summary; this.needsLead = true; }
      this.record(worker, undefined, 'review', review.status === 'accepted' ? 'accepted' : 'changes_requested', review.summary ?? '', { commit: review.commit, sourceDigest: review.sourceDigest, evidenceRefs });
      this.changed(); return { checkWhole: false };
    }
    if (action.kind !== 'task') {
      if (action.kind === 'lead') {
        if (action.planVersion !== undefined && action.planVersion !== this.archive.planVersion) {
          this.input.emit('lead_decision_superseded', { commit }); this.syncPlanNotes(); this.needsLead = true; this.changed();
          return { checkWhole: false };
        }
        const sourceChanged = ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
          ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
        try { this.acceptPlan(); } catch (error) { this.archive.error = error instanceof Error ? error.message : 'math_plan_invalid'; this.needsLead = true; }
        if (sourceChanged) {
          try {
            await withSolverWorktree(worker.worktree, this.archive.canonicalCommit!, async checkout => {
              applyTaskChanges(this.input.state.problem, checkout, taskChanges(this.input.state.problem, worker.worktree, commit, undefined, action));
              this.archive.canonicalCommit = commitSolverSources(this.input.state.problem, checkout);
              await this.recheckIntegrated(this.archive.canonicalCommit, true);
              this.archive.canonicalCommit = this.seed(worker, this.archive.canonicalCommit);
              this.syncStatementReviews();
            });
          } catch (error) {
            this.archive.error = error instanceof Error ? error.message : 'math_lead_integration_failed'; this.needsLead = true;
            this.changed(); return { checkWhole: false };
          }
        }
        this.changed(); return { checkWhole: sourceChanged };
      }
      this.changed();
      return { checkWhole: action.kind === 'assemble' || ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
        ownedSourceDigest(this.input.state.problem, worker.worktree, commit) };
    }
    const node = this.node(action.task.id);
    if (!this.current(action)) {
      this.record(worker, action.task, advisory(action.task) ? 'research' : 'proof', 'superseded', 'Delivery belongs to a superseded assignment.',
        { taskDigest: action.assignment.taskDigest, premises: action.task.premises ?? [], dependencies: action.assignment.dependencies ?? [], commit });
      this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
      return { checkWhole: false };
    }
    if (['conditional', 'integrated'].includes(node.status)) return { checkWhole: false };
    try {
      if (advisory(node.task)) {
        taskChanges(this.input.state.problem, worker.worktree, commit, node.task, action.assignment);
        const finding = block(worker.worktree, 'math-result', { taskId: node.task.id, conclusion: 'inconclusive' });
        const details = deliveryDetails(finding);
        if (finding?.taskId !== node.task.id || !['supporting', 'refuted', 'inconclusive'].includes(finding.conclusion))
          throw new Error('math_research_delivery_invalid');
        node.finding = bounded(JSON.stringify(finding), 5000); node.status = 'completed';
        if (finding.needsDecision === true || finding.conclusion === 'refuted') this.needsLead = true;
        const remaining = [...new Set([...(details.remainingObligations ?? []),
          ...this.dependencies(node.task).filter(dependency => !['integrated', 'completed'].includes(dependency.status)).map(dependency => dependency.task.id)])];
        this.record(worker, node.task, 'research', !remaining.length && node.task.kind !== 'sketch' ? 'advisory' : 'conditional', finding.summary,
          { ...details, remainingObligations: remaining, commit });
        this.input.emit('research_delivered', { taskId: node.task.id, conclusion: finding.conclusion });
      } else {
        const proof = await this.check(node.task, action.assignment, worker.worktree, commit);
        await this.deliverProof(worker, node, proof, 'Fixed declaration checked; unresolved lemma assumptions remain obligations.');
        return { check: proof, checkWhole: false };
      }
    } catch (error) {
      node.status = 'blocked'; node.feedback = error instanceof Error ? error.message : 'math_task_delivery_failed'; this.needsLead = true;
      this.record(worker, node.task, 'failure', 'failed', node.feedback, { commit });
      if (node.feedback === 'math_verifier_unavailable') throw error;
    } finally { this.changed(); }
    return { checkWhole: false };
  }
  interrupted(worker: ResearchWorker, action: CooperativeAction) {
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      if (review && this.current(action) && review.workerId === worker.id) {
        review.status = action.kind === 'backtranslate' ? 'pending' : 'translated'; review.workerId = undefined;
      }
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
  rejected(action: CooperativeAction, feedback: string) {
    if (isStatementAction(action)) {
      const review = this.archive.statementReviews?.find(item => item.id === action.reviewId);
      if (!review || !this.current(action)) return;
      review.status = 'changes_requested'; review.summary = feedback;
      const worker = this.input.workers.find(item => item.id === review.workerId);
      review.workerId = undefined;
      if (worker) this.record(worker, this.node(review.taskId).task, 'failure', 'failed', feedback,
        { sourceDigest: review.snapshotDigest, commit: review.commit });
      this.archive.error = feedback; this.needsLead = true; this.changed(); return;
    } else if (action.kind === 'task') {
      const node = this.node(action.task.id); node.status = 'blocked'; node.feedback = feedback;
    } else if (action.kind === 'review') {
      this.archive.review!.status = 'changes_requested'; this.archive.review!.summary = feedback;
    } else this.archive.error = feedback;
    const worker = action.kind === 'task' ? this.input.workers.find(item => item.id === action.assignment.workerId) : this.lead;
    if (worker) this.record(worker, action.kind === 'task' ? action.task : undefined, 'failure', 'failed', feedback);
    this.needsLead = true; this.changed();
  }
  assemblyFailed(check: ProofCheck) { this.archive.error = solverProofFeedback(check); this.needsLead = true; this.changed(); }
  /** A reserved turn may still be refunded; the caller rechecks synchronously after waking. */
  waitForTurn(maxTurns: number): Promise<void> | undefined {
    return this.input.state.turns >= maxTurns && this.reservedTurns.size ? this.wait() : undefined;
  }
  reserveTurn(worker: ResearchWorker) { this.reservedTurns.add(worker.id); }
  settleTurn(worker: ResearchWorker) { if (this.reservedTurns.delete(worker.id)) this.changed(); }
  release(worker: ResearchWorker, action: CooperativeAction) {
    if (action.kind === 'task' && this.current(action)) {
      const node = this.node(action.task.id);
      if (!node.attempts) node.assignment = undefined;
      if (node.status === 'running') node.status = 'pending';
      this.changed();
    } else this.interrupted(worker, action);
  }
  private reviewer(): ResearchWorker | undefined {
    const available = this.input.workers.filter(worker => this.liveWorkers.has(worker.id) && !this.active.has(worker.id) &&
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
    if (worker.id === this.lead.id) this.leadStopped = true;
    this.liveWorkers.delete(worker.id);
    if (this.archive.review?.status === 'running' && this.archive.review.workerId === worker.id) this.archive.review.status = 'pending';
    for (const review of this.archive.statementReviews ?? []) if (review.workerId === worker.id && ['translating', 'reviewing'].includes(review.status)) {
      review.status = review.status === 'translating' ? 'pending' : 'translated'; review.workerId = undefined;
    }
    for (const node of this.archive.tasks.filter(node => node.status === 'running' && node.assignment?.workerId === worker.id)) {
      node.status = error ? 'blocked' : 'pending'; node.feedback = error;
      if (error) this.needsLead = true;
    }
    this.changed();
  }
}
