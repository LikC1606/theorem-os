import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { canonicalMathJson, mathDigest } from '../math/mathRuntimeIo';
import { commitSolverSources, git, type SolverProblem } from './problem';
import { solverProofFeedback, solverSourceFeedback } from './feedback';
import type { SolverRunState } from './archive';
import type { ResearchWorker } from './modules/organization';
import type { ContextBundle } from './modules/context';
import type { ProofCheck } from './modules/evidence';
import type { WorkerAccess } from './research';
import type { SolverModules } from './modules';
import { routeAllowsTask } from './modules/search';
import { applyTaskChanges, checkTaskProof, committedSource, omitTaskHelpers, ownedSourceDigest, taskChanges, type TaskProof } from './cooperativeProof';

export type CooperativeTask = Readonly<{ id: string; kind: 'research' | 'lemma' | 'goal'; objective: string;
  dependsOn: readonly string[]; revision: number; proofPath?: string; theoremName?: string; type?: string;
  groupId?: string; sharing?: 'group' | 'problem' }>;
export type RouteGroup = Readonly<{ id: string; objective: string; status: 'active' | 'paused' | 'stopped'; revision: number;
  engineerId?: string; maxTurns?: number; maxConcurrent?: number }>;
export type RouteRecord = { group: RouteGroup; turns: number };
export const taskGroup = (task: CooperativeTask): string => task.groupId ?? 'main';
export type TaskAssignment = { taskId: string; taskDigest: string; workerId: string; seedCommit: string; groupId?: string; canonicalCommit?: string };
export type TaskRecord = { task: CooperativeTask; status: 'pending' | 'running' | 'blocked' | 'delivered' | 'integrated' | 'completed';
  attempts: number; assignment?: TaskAssignment; proof?: TaskProof; integratedCheck?: ProofCheck; feedback?: string; finding?: string };
export type ReviewRecord = { commit: string; sourceDigest: string; status: 'pending' | 'running' | 'accepted' | 'changes_requested';
  workerId?: string; summary?: string };
export type CooperationState = { tasks: TaskRecord[]; groups?: RouteRecord[]; canonicalCommit?: string; review?: ReviewRecord; error?: string;
  history?: { task: CooperativeTask; proof?: TaskProof; integratedCheck?: ProofCheck; finding?: string }[] };
export type CooperativeAction = { kind: 'lead' | 'assemble'; seedCommit: string } |
  { kind: 'review'; seedCommit: string; sourceDigest: string } | { kind: 'task'; assignment: TaskAssignment; task: CooperativeTask };

const digest = (task: CooperativeTask) => mathDigest(canonicalMathJson(task));
const bounded = (text: string, bytes: number) => Buffer.from(text).subarray(0, bytes).toString('utf8').replace(/\uFFFD$/u, '');
const block = (worktree: string, fence: string) => {
  const file = path.join(worktree, 'RESEARCH.md');
  if (!fs.existsSync(file) || fs.statSync(file).size > 64_000) throw new Error(`math_${fence}_missing_or_too_large`);
  const blocks = [...fs.readFileSync(file, 'utf8').matchAll(new RegExp('```' + fence + '\\s*\\n([\\s\\S]*?)\\n```', 'gu'))];
  if (blocks.length !== 1) throw new Error(`math_${fence}_requires_one_block`);
  return JSON.parse(blocks[0][1]);
};

/** Model proposes tasks; the host validates coverage, exact targets and an acyclic dependency graph. */
export function readCooperationPlan(problem: SolverProblem, worktree: string): { tasks: CooperativeTask[]; groups: RouteGroup[] } {
  const value = block(worktree, 'math-plan');
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
  const tasks: CooperativeTask[] = value.tasks.map((task: any) => {
    if (!task || typeof task.id !== 'string' || !/^[a-zA-Z0-9_-]{1,64}$/u.test(task.id) ||
        !['research', 'lemma', 'goal'].includes(task.kind) || typeof task.objective !== 'string' ||
        !task.objective.trim() || task.objective.length > 2000 || !Array.isArray(task.dependsOn) ||
        task.dependsOn.some((id: unknown) => typeof id !== 'string') ||
        !Number.isSafeInteger(task.revision ?? 0) || (task.revision ?? 0) < 0)
      throw new Error('math_plan_invalid_task');
    if (!groups.some(group => group.id === (task.groupId ?? 'main')) ||
        (task.sharing !== undefined && !['group', 'problem'].includes(task.sharing))) throw new Error('math_plan_invalid_task_group');
    if (task.kind !== 'research' && (!problem.ownedFiles.includes(task.proofPath) ||
        typeof task.theoremName !== 'string' || !/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(task.theoremName)))
      throw new Error('math_plan_invalid_proof_target');
    if (task.kind === 'goal' && !problem.targets.some(target => target.proofPath === task.proofPath && target.theoremName === task.theoremName))
      throw new Error('math_plan_changed_original_target');
    if (task.kind === 'lemma' && (typeof task.type !== 'string' || !task.type.trim() || task.type.length > 8000 ||
        Object.values(problem.declarations).some(items => items.some(item => item.name.split('.').at(-1) === task.theoremName.split('.').at(-1)))))
      throw new Error('math_plan_invalid_helper_type');
    return { id: task.id, kind: task.kind, objective: task.objective, dependsOn: [...new Set<string>(task.dependsOn)],
      revision: task.revision ?? 0, ...(task.kind === 'research' ? {} : { proofPath: task.proofPath, theoremName: task.theoremName }),
      ...(task.kind === 'lemma' ? { type: task.type } : {}),
      ...(task.groupId === undefined ? {} : { groupId: task.groupId }),
      ...(task.sharing === undefined ? groups.length > 1 ? { sharing: 'group' } : {} : { sharing: task.sharing }) };
  });
  if (new Set(tasks.map(task => task.id)).size !== tasks.length ||
      new Set(tasks.filter(task => task.kind !== 'research').map(task => task.theoremName!.split('.').at(-1))).size !== tasks.filter(task => task.kind !== 'research').length)
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
  private liveWorkers: Set<string>;
  private leadStopped = false;
  private checkedDeliveries = new WeakSet<TaskProof>();
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
  private changed() { this.input.save(); for (const wake of this.waiters) wake(); this.waiters.clear(); }
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
    const visit = (id: string) => { if (found.has(id)) return; found.add(id); this.node(id).task.dependsOn.forEach(visit); };
    task.dependsOn.forEach(visit);
    return [...found].map(id => this.node(id));
  }
  private ready(node: TaskRecord) {
    return this.input.modules.M3.ready(this.archive.tasks, this.archive.groups).includes(node);
  }
  private retainedGoals(task: CooperativeTask) {
    return this.dependencies(task).filter(node => node.task.kind === 'goal' && node.status === 'integrated').map(node => node.task.theoremName!);
  }
  private async check(task: CooperativeTask, assignment: TaskAssignment, worktree: string, commit: string) {
    const required = new Set([task.id, ...this.dependencies(task).map(node => node.task.id)]);
    const excluded = this.archive.tasks.filter(node => node.task.kind === 'lemma' && !required.has(node.task.id)).map(node => node.task.theoremName!);
    return checkTaskProof(this.input.state.problem, worktree, commit, task, assignment, this.retainedGoals(task),
      this.input.access.get(this.lead.id)!.environment, this.input.signal, this.input.timeoutMs, excluded);
  }
  private async recheckIntegrated(canonical: string) {
    // Persisted receipts and receipts for different sources cannot authorize dependent dispatch.
    const pending = this.archive.tasks.filter(node => node.status === 'integrated');
    const checked = new Set<string>();
    while (pending.length) {
      const index = pending.findIndex(node => node.task.dependsOn.every(id => this.node(id).status !== 'integrated' || checked.has(id)));
      if (index < 0) throw new Error('math_plan_dependency_cycle');
      const [node] = pending.splice(index, 1);
      if (!node.task.dependsOn.every(id => ['integrated', 'completed'].includes(this.node(id).status))) {
        node.status = 'blocked'; node.feedback = 'math_task_dependency_invalidated'; this.needsLead = true;
        checked.add(node.task.id); continue;
      }
      const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: canonical };
      try {
        const receipt = await this.check(node.task, assignment, this.lead.worktree, canonical);
        if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
        node.integratedCheck = receipt;
        if (!receipt.passed) { node.status = 'blocked'; node.feedback = solverProofFeedback(receipt); this.needsLead = true; }
      } catch (error) {
        if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
        node.status = 'blocked'; node.feedback = error instanceof Error ? error.message : 'math_task_recheck_failed'; this.needsLead = true;
      }
      checked.add(node.task.id);
    }
  }
  async restore() {
    // A resumed review must inspect the fixed version again.
    if (this.archive.review) this.archive.review.status = 'pending';
    if (this.archive.tasks.length && fs.existsSync(path.join(this.lead.worktree, 'RESEARCH.md'))) {
      try { this.acceptPlan(); } catch (error) { this.archive.error = error instanceof Error ? error.message : 'math_plan_invalid'; this.needsLead = true; }
    }
    if (!solverSourceFeedback(this.input.state.problem, this.lead.worktree)) {
      this.archive.canonicalCommit = commitSolverSources(this.input.state.problem, this.lead.worktree);
      await this.input.exclusiveCheck(() => this.recheckIntegrated(this.archive.canonicalCommit!));
    } else {
      for (const node of this.archive.tasks.filter(node => node.status === 'integrated')) {
        node.status = 'blocked'; node.feedback = 'math_canonical_source_invalid';
      }
      this.needsLead = true;
    }
    for (const node of this.archive.tasks) if (node.status === 'running') node.status = 'pending';
    this.changed();
  }
  private acceptPlan() {
    const { tasks, groups } = readCooperationPlan(this.input.state.problem, this.lead.worktree);
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
    const invalidated = new Set(this.archive.tasks.filter(node => changedGroups.has(taskGroup(node.task)) ||
      !tasks.some(task => task.id === node.task.id && digest(task) === digest(node.task)))
      .map(node => node.task.id));
    for (let changed = true; changed;) {
      changed = false;
      for (const task of tasks) if (!invalidated.has(task.id) && task.dependsOn.some(id => invalidated.has(id))) {
        invalidated.add(task.id); changed = true;
      }
    }
    for (const id of invalidated) {
      const previous = current.get(id);
      if (previous) this.archive.history = [...(this.archive.history ?? []).slice(-31),
        { task: previous.task, proof: previous.proof, integratedCheck: previous.integratedCheck, finding: previous.finding }];
    }
    this.archive.tasks = tasks.map(task => {
      const previous = current.get(task.id);
      return previous && !invalidated.has(task.id) ? previous : { task, status: 'pending', attempts: previous?.attempts ?? 0 };
    });
    this.archive.groups = configuredGroups.map(group => ({ group, turns: previousGroups.get(group.id)?.turns ?? 0 }));
    if (invalidated.size) this.archive.review = undefined;
    this.archive.error = undefined;
    this.input.emit('plan_updated', { groups: this.archive.groups, tasks: tasks.map(task =>
      ({ id: task.id, kind: task.kind, dependsOn: task.dependsOn, groupId: taskGroup(task), sharing: task.sharing ?? 'problem' })), invalidated: [...invalidated] });
  }
  private canAdvance(node: TaskRecord): boolean {
    if (['integrated', 'completed', 'delivered', 'running'].includes(node.status)) return true;
    return routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) && node.task.dependsOn.every(id => this.canAdvance(this.node(id)));
  }
  private async integrate(node: TaskRecord) {
    const problem = this.input.state.problem;
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-integrate-'));
    const checkout = path.join(directory, 'worktree');
    let added = false;
    try {
      const head = this.archive.canonicalCommit!;
      git(this.lead.worktree, ['worktree', 'add', '--quiet', '--detach', checkout, head]); added = true;
      // Only archived deliveries need a second delivery check; merged sources always get their own check.
      const submitted = this.checkedDeliveries.has(node.proof!) ? node.proof! :
        await this.check(node.task, node.assignment!, checkout, node.proof!.commit);
      if (['unavailable', 'blocked'].includes(submitted.verification.status)) throw new Error('math_verifier_unavailable');
      if (!submitted.passed) throw new Error('math_task_delivery_no_longer_checks');
      if (!node.task.dependsOn.every(id => ['integrated', 'completed'].includes(this.node(id).status)))
        throw new Error('math_task_dependency_invalidated');
      applyTaskChanges(problem, checkout, submitted.changes);
      const merged = commitSolverSources(problem, checkout);
      const assignment = { taskId: node.task.id, taskDigest: digest(node.task), workerId: this.lead.id, seedCommit: merged };
      const receipt = await this.check(node.task, assignment, checkout, merged);
      if (['unavailable', 'blocked'].includes(receipt.verification.status)) throw new Error('math_verifier_unavailable');
      if (!receipt.passed) { node.feedback = solverProofFeedback(receipt); throw new Error('math_task_merged_proof_failed'); }
      git(this.lead.worktree, ['merge', '--ff-only', merged]);
      this.archive.canonicalCommit = merged;
      node.integratedCheck = receipt; node.status = 'integrated';
      this.input.emit('task_integrated', { taskId: node.task.id, groupId: taskGroup(node.task), sharing: node.task.sharing ?? 'problem', commit: merged });
    } catch (error) {
      node.status = 'blocked'; node.feedback = `${error instanceof Error ? error.message : 'math_task_integration_failed'}\n${node.feedback ?? ''}`;
      this.needsLead = true;
      if (error instanceof Error && error.message === 'math_verifier_unavailable') throw error;
    } finally {
      if (added) git(this.lead.worktree, ['worktree', 'remove', '--force', checkout]);
      fs.rmSync(directory, { recursive: true, force: true }); this.changed();
    }
  }
  async next(worker: ResearchWorker, budget: { maxTurns: number; remainingMs: number }): Promise<CooperativeAction | undefined> {
    for (;;) {
      this.input.signal.throwIfAborted();
      if (this.leadStopped) return;
      if (worker.id === this.lead.id) {
        for (;;) {
          const node = this.archive.tasks.find(node => node.status === 'delivered');
          if (!node) break;
          await this.input.exclusiveCheck(() => this.integrate(node));
        }
        const head = this.archive.canonicalCommit!;
        const goals = this.archive.tasks.filter(node => node.task.kind === 'goal');
        if (((goals.length && goals.every(node => node.status === 'integrated')) || this.reviewed()) && this.lastAssembly !== head) {
          this.lastAssembly = head; return { kind: 'assemble', seedCommit: head };
        }
        const running = this.archive.tasks.some(node => node.status === 'running') || this.archive.review?.status === 'running';
        if (this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0) {
          if (running) { await this.wait(); continue; }
          return;
        }
        if (this.archive.review && ['pending', 'running'].includes(this.archive.review.status)) { await this.wait(); continue; }
        if (!running && this.archive.tasks.length && !this.archive.review &&
            !this.archive.tasks.some(node => ['pending', 'blocked'].includes(node.status) && this.canAdvance(node))) {
          this.input.emit('routes_idle', { groups: this.archive.groups }); return;
        }
        if (this.needsLead || (!running && !this.archive.tasks.some(node => this.ready(node) && this.liveWorkers.size))) {
          this.needsLead = false;
          return { kind: 'lead', seedCommit: head };
        }
      } else {
        if (this.input.state.turns >= budget.maxTurns || budget.remainingMs <= 0) return;
        const review = this.archive.review;
        const hasResearcher = this.input.workers.some(item => item.role === 'researcher' && this.liveWorkers.has(item.id));
        if (review?.status === 'pending' && (worker.role === 'researcher' || !hasResearcher)) {
          this.seed(worker, review.commit);
          review.workerId = worker.id; review.status = 'running';
          this.input.emit('review_assigned', { workerId: worker.id, commit: review.commit, role: 'reviewer' });
          this.changed(); return { kind: 'review', seedCommit: review.commit, sourceDigest: review.sourceDigest };
        }
        const node = !this.needsLead && this.input.modules.M5.assign(this.input.modules.M3.ready(this.archive.tasks, this.archive.groups), worker,
          this.input.workers.filter(item => this.liveWorkers.has(item.id)), this.archive.groups);
        if (node) {
          if (!this.archive.tasks.includes(node) || node.status !== 'pending' ||
              !node.task.dependsOn.every(id => ['integrated', 'completed'].includes(this.node(id).status)) ||
              !routeAllowsTask(node.task, this.archive.tasks, this.archive.groups) ||
              (node.assignment && node.assignment.workerId !== worker.id)) throw new Error('math_task_assignment_invalid');
          const seed = this.archive.canonicalCommit!;
          const resuming = node.assignment?.workerId === worker.id;
          let scopedSeed = seed;
          if (!resuming) {
            scopedSeed = this.seed(worker, seed, node.task);
          }
          node.assignment ??= { taskId: node.task.id, taskDigest: digest(node.task), workerId: worker.id,
            seedCommit: scopedSeed, canonicalCommit: seed, groupId: taskGroup(node.task) };
          node.status = 'running'; node.attempts++;
          const route = this.archive.groups?.find(record => record.group.id === taskGroup(node.task));
          if (route) route.turns++;
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
    return this.archive.review?.status === 'accepted' && this.archive.review.commit === this.archive.canonicalCommit;
  }
  requireReview(check: ProofCheck) {
    if (this.archive.review?.commit !== check.commit) {
      this.archive.review = { commit: check.commit, sourceDigest: check.sourceDigest, status: 'pending' };
      this.input.emit('review_requested', { commit: check.commit });
    }
    this.changed();
  }
  decorate(context: ContextBundle, action: CooperativeAction): ContextBundle {
    const records = action.kind === 'task' ? this.visible(action.task) : this.archive.tasks;
    const summary = records.map(node => ({ ...node.task, status: node.status, attempts: node.attempts,
      groupId: taskGroup(node.task), producer: node.assignment?.workerId, sharing: node.task.sharing ?? 'problem',
      feedback: node.feedback && bounded(node.feedback, 2500), finding: node.finding,
      integratedCommit: node.integratedCheck?.commit, checkedSourceDigest: node.integratedCheck?.sourceDigest }));
    const rules = action.kind === 'review'
      ? 'You are the Independent Reviewer. Inspect this fixed canonical version, the original statement, assumptions, task dependencies and Lean evidence. Leave every Lean file unchanged. Review whether it answers the original problem and whether shared lemmas have matching premises. Write exactly one math-review JSON block in RESEARCH.md: {"commit":"ASSIGNED_COMMIT","verdict":"accepted|changes_requested","summary":"...","evidenceRefs":["..."]}. Cite concrete declarations and checks for objections. Your review is separate from Lean evidence and cannot grant proof acceptance. Return one bounded review of this version.\n'
      : action.kind !== 'task'
      ? 'You are the Lead. Decompose the original obligations into independent research questions, ordinary typed helper lemmas and original goal nodes. Preserve exactly one math-plan JSON block in RESEARCH.md: {"tasks":[{"id":"bridge","kind":"lemma","objective":"...","dependsOn":[],"proofPath":"owned.lean","theoremName":"Namespace.bridge","type":"FULL_CLOSED_LEAN_TYPE","revision":0},{"id":"goal","kind":"goal","objective":"...","dependsOn":["bridge"],"proofPath":"owned.lean","theoremName":"Original.target","revision":0}]}. Include exactly one goal node for every original target. A research node needs id, kind="research", objective, dependsOn and revision; it returns advisory findings, not proof evidence. The host dispatches ready nodes and merges checked declarations. Revise a task objective, dependencies or revision to change the route or retry a blocked task. The host invalidates that task and its dependent versions, keeps unrelated work, and ignores superseded deliveries. Existing helpers may be revised only in their own assigned task. Review Lean feedback and adjust the route rather than replaying unchanged work. Keep the plan and concise notes within 64000 bytes. You may also finish the canonical original proof yourself.\n'
      : 'You are a Worker executing one Lead-assigned task. Work only on its specific objective and proofPath. Preserve all other original goal bodies and existing helper declarations from the seeded canonical source; only the assigned goal or helper may be revised. A lemma must have the exact requested full closed type; prove it independently of unfinished original targets. You may add ordinary supporting helpers in the same owned file. A research task must leave Lean source unchanged and return exactly one math-result JSON block in RESEARCH.md: {"taskId":"TASK_ID","summary":"...","conclusion":"supporting|refuted|inconclusive","evidenceRefs":["..."],"nextAction":"..."}. Research findings are advisory. Finish one coherent task delivery and return; the host checks it, combines peer declarations and supplies the checked dependencies for subsequent tasks. Do not attempt an unrelated complete candidate.\n';
    return { ...context, instructions: context.instructions.replace('Keep RESEARCH.md within 6000 bytes', 'Keep RESEARCH.md within 64000 bytes') + '\n' + rules +
      'Plans may include groups: [{id, objective, status: active|paused|stopped, revision, engineerId, maxTurns, maxConcurrent}]. A task may set groupId and sharing: group|problem. With several groups, sharing defaults to group; cross-group dependencies must explicitly be shared with problem. Each group uses its designated Engineer for original proof nodes. Route turn budgets count worker task attempts within the original total budget; final review still counts in the total. Paused, stopped and exhausted groups retain artifacts and receive no new work. Change the group objective or revision only to change its mathematical route; changing limits or pausing preserves checked work. Workers see their group and short summaries of checked shared results, and must record cross-group uses as dependsOn.\n' +
      'Unrelated unfinished original goals may remain drafts. The host checks each formal assignment in an isolated source projection and checks the complete canonical proof separately.\n',
      message: context.message + '\n\nCooperative assignment:\n' + JSON.stringify(action) +
        '\n\nLead task graph and host feedback:\n' + bounded(JSON.stringify(summary), 14000) +
        '\n\nRoute groups and budgets:\n' + bounded(JSON.stringify(this.archive.groups ?? []), 6000) +
        `\nPlan error: ${this.archive.error ?? 'none'}\nReview: ${JSON.stringify(this.archive.review ?? null)}` +
        `\nOriginal targets: ${JSON.stringify(this.input.state.problem.targets)}\nYour role: ${action.kind === 'review' ? 'reviewer' : action.kind === 'task' ? action.task.kind === 'goal' ? 'engineer' : 'researcher' : 'lead'}` };
  }
  async deliver(worker: ResearchWorker, action: CooperativeAction, commit: string): Promise<{ check?: ProofCheck; checkWhole: boolean }> {
    if (action.kind === 'review') {
      const review = this.archive.review!;
      try {
        if (review.commit !== action.seedCommit || review.workerId !== worker.id || review.status !== 'running')
          throw new Error('math_review_identity_changed');
        if (ownedSourceDigest(this.input.state.problem, worker.worktree, commit) !== action.sourceDigest)
          throw new Error('math_review_source_changed');
        const result = block(worker.worktree, 'math-review');
        if (result?.commit !== action.seedCommit || !['accepted', 'changes_requested'].includes(result.verdict) ||
            typeof result.summary !== 'string' || result.summary.length > 3000 || !Array.isArray(result.evidenceRefs) ||
            result.evidenceRefs.length > 16 || result.evidenceRefs.some((ref: unknown) => typeof ref !== 'string' || ref.length > 1000))
          throw new Error('math_review_delivery_invalid');
        review.status = result.verdict; review.summary = bounded(JSON.stringify(result), 5000);
        this.input.emit('review_completed', { commit: review.commit, verdict: review.status, workerId: worker.id });
      } catch (error) {
        review.status = 'changes_requested'; review.summary = error instanceof Error ? error.message : 'math_review_failed';
      }
      if (review.status === 'accepted') this.lastAssembly = undefined;
      else { this.archive.error = review.summary; this.needsLead = true; }
      this.changed(); return { checkWhole: false };
    }
    if (action.kind !== 'task') {
      if (action.kind === 'lead') {
        this.archive.canonicalCommit = commit;
        const sourceChanged = ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
          ownedSourceDigest(this.input.state.problem, worker.worktree, commit);
        if (sourceChanged) await this.recheckIntegrated(commit);
        try { this.acceptPlan(); } catch (error) { this.archive.error = error instanceof Error ? error.message : 'math_plan_invalid'; this.needsLead = true; }
      }
      this.changed();
      return { checkWhole: action.kind === 'assemble' || ownedSourceDigest(this.input.state.problem, worker.worktree, action.seedCommit) !==
        ownedSourceDigest(this.input.state.problem, worker.worktree, commit) };
    }
    const node = this.node(action.task.id);
    if (!node || node.status !== 'running' || node.assignment !== action.assignment || action.assignment.taskDigest !== digest(node.task)) {
      this.input.emit('task_delivery_superseded', { taskId: action.task.id, workerId: worker.id, commit });
      return { checkWhole: false };
    }
    try {
      if (node.task.kind === 'research') {
        taskChanges(this.input.state.problem, worker.worktree, commit, node.task, action.assignment);
        const finding = block(worker.worktree, 'math-result');
        if (finding?.taskId !== node.task.id || typeof finding.summary !== 'string' || finding.summary.length > 3000 ||
            !['supporting', 'refuted', 'inconclusive'].includes(finding.conclusion) || !Array.isArray(finding.evidenceRefs) ||
            finding.evidenceRefs.length > 16 || finding.evidenceRefs.some((ref: unknown) => typeof ref !== 'string' || ref.length > 1000))
          throw new Error('math_research_delivery_invalid');
        node.finding = bounded(JSON.stringify(finding), 5000); node.status = 'completed';
        this.needsLead = true;
        this.input.emit('research_delivered', { taskId: node.task.id, conclusion: finding.conclusion });
      } else {
        const proof = await this.check(node.task, action.assignment, worker.worktree, commit);
        node.proof = proof;
        this.checkedDeliveries.add(proof);
        if (['unavailable', 'blocked'].includes(proof.verification.status)) throw new Error('math_verifier_unavailable');
        node.status = proof.passed ? 'delivered' : 'blocked';
        if (!proof.passed) { node.feedback = solverProofFeedback(proof); this.needsLead = true; }
        this.input.emit('task_checked', { taskId: node.task.id, passed: proof.passed, commit });
        return { check: proof, checkWhole: false };
      }
    } catch (error) {
      node.status = 'blocked'; node.feedback = error instanceof Error ? error.message : 'math_task_delivery_failed'; this.needsLead = true;
      if (node.feedback === 'math_verifier_unavailable') throw error;
    } finally { this.changed(); }
    return { checkWhole: false };
  }
  interrupted(worker: ResearchWorker, action: CooperativeAction) {
    if (action.kind === 'task') this.node(action.task.id).status = 'pending';
    else if (action.kind === 'review') this.archive.review!.status = 'pending';
    else this.needsLead = true;
    this.changed();
  }
  rejected(action: CooperativeAction, feedback: string) {
    if (action.kind === 'task') {
      const node = this.node(action.task.id); node.status = 'blocked'; node.feedback = feedback;
    } else if (action.kind === 'review') {
      this.archive.review!.status = 'changes_requested'; this.archive.review!.summary = feedback;
    } else this.archive.error = feedback;
    this.needsLead = true; this.changed();
  }
  assemblyFailed(check: ProofCheck) { this.archive.error = solverProofFeedback(check); this.needsLead = true; this.changed(); }
  stopped(worker: ResearchWorker, error?: string) {
    if (worker.id === this.lead.id) this.leadStopped = true;
    this.liveWorkers.delete(worker.id);
    if (this.archive.review?.status === 'running' && this.archive.review.workerId === worker.id) this.archive.review.status = 'pending';
    for (const node of this.archive.tasks.filter(node => node.status === 'running' && node.assignment?.workerId === worker.id)) {
      node.status = error ? 'blocked' : 'pending'; node.feedback = error;
      if (error) this.needsLead = true;
    }
    this.changed();
  }
}
