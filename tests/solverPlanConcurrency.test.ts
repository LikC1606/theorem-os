import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import { taskDependenciesReady } from '../src/solver/modules/search';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => 'plan-concurrency-fixture-tools',
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest, passed = true): MathematicsVerifierBatchResult {
  const status = passed ? 'kernel_verified' : 'failed';
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status,
    targetCommit: request.targetCommit!, sessionId: 'plan-concurrency-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map((item, index) => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      checkId: item.id?.trim() || `check-${index + 1}`, sessionId: 'plan-concurrency-fixture', checkedAt: 2,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status, claim: 'statement', ...(!passed ? { error: 'Fixture obsolete recheck failure.' } : {}) })) as MathematicsVerifierBatchResult['results'] };
}
const deferred = <T,>() => {
  let resolve!: (value: T) => void;
  const promise = new Promise<T>(complete => { resolve = complete; });
  return { promise, resolve };
};
type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;

describe('plan synchronization with concurrent host control', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController;
  let lockHeld: boolean, exclusive: <T>(check: () => Promise<T>) => Promise<T>;
  let pending: Promise<unknown>[], releases: (() => void)[];
  let events: { event: string; details?: Record<string, unknown> }[];
  const node = (id: string) => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const track = <T,>(promise: Promise<T>) => { pending.push(promise); void promise.catch(() => {}); return promise; };
  const create = () => new CooperativeResearch({ state, workers,
    access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
    signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }),
    modules: directSolverModules, exclusiveCheck: check => exclusive(check) });
  const source = () => committedSource(workspace, state.cooperation!.canonicalCommit!, `${problem.projectRelative}/Submission.lean`);
  const writeLemma = (worker: ResearchWorker, name: string) => {
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', `lemma ${name} : True := by trivial\ntheorem add_zero`));
    return commitSolverSources(problem, worker.worktree);
  };
  const gateCheck = () => {
    const entered = deferred<MathematicsVerifierBatchRequest>(), result = deferred<MathematicsVerifierBatchResult>();
    let request: MathematicsVerifierBatchRequest | undefined, heldAtEntry: boolean | undefined;
    host.verify.mockImplementationOnce(async (input: MathematicsVerifierBatchRequest) => {
      request = input; heldAtEntry = lockHeld; entered.resolve(input); return result.promise;
    });
    const release = (passed = true) => { if (request) result.resolve(verified(request, passed)); };
    releases.push(release);
    const waitFor = (delivery: Promise<unknown>) => Promise.race([entered.promise, delivery.then(() => {
      throw new Error(`Delivery completed before the expected verifier check: ${JSON.stringify(events.slice(-5))}`);
    })]);
    return { entered: entered.promise, waitFor, release, heldAtEntry: () => heldAtEntry };
  };
  const edit = (id: string, change: (task: CooperativeTask) => CooperativeTask) => {
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id, baseVersion: state.cooperation!.planVersion,
      tasks: state.cooperation!.tasks.map(item => change(item.task)), groups: state.cooperation!.groups!.map(item => item.group) }) + '\n');
    return track(cooperative.pulse(workers[0].id));
  };
  const sync = () => track((cooperative as any).schedulePlanSynchronization() as Promise<void>);
  const integrateA = async () => {
    const current = node('a');
    const action: TaskAction = { kind: 'task', task: current.task, assignment: current.assignment! };
    await cooperative.deliver(workers[1], action, writeLemma(workers[1], 'a'));
    expect(node('a').status).toBe('integrated');
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-plan-concurrency-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace); problem = readSolverProblem(workspace, receipt.activeProblemPath);
    workers = [{ id: 'lead', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles },
      ...['author', 'consumer', 'independent'].map(id => {
        const worktree = path.join(directory, id);
        git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
        return { id, role: 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
      })];
    const lemma = (id: string, ownerId: string, dependsOn: string[] = []): CooperativeTask => ({ id, ownerId, kind: 'lemma',
      objective: `Prove ${id}.`, proofPath: 'Submission.lean', theoremName: `Tutorial.${id}`, type: 'True', dependsOn, revision: 0 });
    const a = lemma('a', 'author');
    state = { schema: 'deepscientist.math.solver.v1', runId: 'plan-concurrency-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [{ task: a, status: 'running', attempts: 1,
          assignment: { taskId: 'a', taskDigest: taskVersion(a), workerId: 'author', seedCommit: problem.baseCommit,
            assignmentId: 'a-dispatch', dependencies: [] } },
        ...[lemma('b', 'consumer', ['a']), lemma('c', 'independent')].map(task => ({ task, status: 'pending' as const, attempts: 0 })),
        ...problem.targets.map((target, index) => ({ task: { id: `goal_${index}`, kind: 'goal' as const,
          objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
          dependsOn: ['b'], revision: 0, status: 'paused' as const }, status: 'pending' as const, attempts: 0 }))] } };
    events = []; pending = []; releases = []; lockHeld = false; controller = new AbortController();
    let queue = Promise.resolve();
    exclusive = async check => {
      const previous = queue;
      let release!: () => void;
      queue = new Promise<void>(resolve => { release = resolve; });
      await previous; lockHeld = true;
      try { return await check(); } finally { lockHeld = false; release(); }
    };
    cooperative = create(); state.cooperation!.planVersion = (cooperative as any).planVersion();
  });
  afterEach(async () => {
    for (const release of releases) release();
    controller.abort(); await Promise.allSettled(pending); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('advances the edit cursor and allows independent work while keeping a revalidated dependency unavailable', async () => {
    await integrateA();
    const gate = gateCheck();
    await edit('describe-a', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Clarify the same theorem.' } : task);
    await gate.entered;
    expect(gate.heldAtEntry()).toBe(false);
    expect(node('a').pendingValidation).toMatchObject({ taskDigest: taskVersion(node('a').task), proof: true });
    expect(state.cooperation!.cursors!.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(directSolverModules.M3.ready(state.cooperation!.tasks, state.cooperation!.groups).map(item => item.task.id)).not.toContain('b');
    const independent = await cooperative.next(workers[3], { maxTurns: 20, remainingMs: Infinity });
    expect(independent).toMatchObject({ kind: 'task', task: { id: 'c' } });
    expect(cooperative.started(workers[3], independent!)).toBe(true);
    const waiting = node('b');
    waiting.assignment = { taskId: 'b', taskDigest: taskVersion(waiting.task), workerId: 'consumer', seedCommit: state.cooperation!.canonicalCommit! };
    expect(cooperative.started(workers[2], { kind: 'task', task: waiting.task, assignment: waiting.assignment })).toBe(false);
    await edit('pause-consumer', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: 'pause-consumer', status: 'applied' }));
    gate.release(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(node('a').integratedCheck?.taskDigest).toBe(taskVersion(node('a').task));
    expect(state.cooperation!.edits!.every(item => !item.pendingSync)).toBe(true);
  });

  it.each([true, false])('discards an obsolete %s recheck after a mathematical revision without publishing a failure', async passed => {
    await integrateA(); const gate = gateCheck();
    await edit('old-description', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await gate.entered;
    await edit('new-mathematics', task => task.id === 'a' ? { ...task, revision: 2, type: 'True ∧ True' } : task);
    const current = node('a'), saved = JSON.parse(JSON.stringify(current));
    gate.release(passed); await sync();
    expect(node('a')).toBe(current); expect(node('a')).toEqual(saved);
    expect(node('a').proof).toBeUndefined(); expect(node('a').integratedCheck).toBeUndefined();
    expect(state.cooperation!.deliveries?.some(item => item.kind === 'failure' || item.status === 'failed')).not.toBe(true);
    expect(events.some(item => item.event === 'delivery_rejected')).toBe(false);
  });

  it('keeps newer progress when an identical task receives a new validation identity', async () => {
    await integrateA();
    const saved: { progress: NonNullable<NonNullable<SolverRunState['cooperation']>['recheck']>; locked: boolean }[] = [];
    vi.spyOn((cooperative as any).input, 'save').mockImplementation(() => {
      const progress = state.cooperation!.recheck;
      if (progress) saved.push({ progress: { ...progress }, locked: lockHeld });
    });
    const gate = gateCheck();
    await edit('describe-for-progress', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await gate.entered;
    expect(state.cooperation!.recheck).toMatchObject({ total: 1, completed: 0, taskId: 'a' });
    const previous = node('a').pendingValidation!;
    const newer = { ...previous, id: 'new-validation-for-identical-mathematics' };
    const newerProgress = { ...state.cooperation!.recheck! };
    await exclusive(async () => {
      node('a').pendingValidation = newer;
      state.cooperation!.recheck = newerProgress;
    });
    expect(newer.taskDigest).toBe(previous.taskDigest);
    const prepared = deferred<void>(), release = deferred<void>();
    releases.push(() => release.resolve());
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockImplementationOnce(() => {
      prepared.resolve(); return release.promise;
    }).mockReturnValue(undefined);
    const savesBeforeCompletion = saved.length;
    gate.release(); await prepared.promise;
    expect(state.cooperation!.recheck).toBe(newerProgress);
    expect(saved).toHaveLength(savesBeforeCompletion);
    expect(node('a').pendingValidation).toBe(newer);
    release.resolve(); await sync();
    expect(state.cooperation!.recheck).toMatchObject({ total: 1, completed: 1 });
    expect(node('a').pendingValidation).toBeUndefined();
    expect(saved.every(item => item.locked)).toBe(true);
    expect(saved.some(item => item.progress.completed === 1)).toBe(true);
  });

  it('rebases validation after an independent proof integrates and retains both declarations', async () => {
    await integrateA(); const gate = gateCheck();
    await edit('describe-before-integration', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    const old = await gate.entered;
    const action = await cooperative.next(workers[3], { maxTurns: 20, remainingMs: Infinity });
    expect(action).toMatchObject({ kind: 'task', task: { id: 'c' } });
    await cooperative.deliver(workers[3], action!, writeLemma(workers[3], 'c'));
    expect(node('c').status).toBe('integrated');
    expect(source()).toContain('lemma c : True := by trivial');
    gate.release(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(node('a').status).toBe('integrated'); expect(node('c').status).toBe('integrated');
    expect(source()).toContain('lemma a : True := by trivial'); expect(source()).toContain('lemma c : True := by trivial');
    expect(events).toContainEqual(expect.objectContaining({ event: 'plan_recheck_rebased' }));
    expect(node('a').integratedCheck!.commit).not.toBe(old.targetCommit);
  });

  it('restores pending validation independently of an already advanced input cursor', async () => {
    await integrateA(); const oldGate = gateCheck();
    await edit('resume-description', task => task.id === 'a' ? { ...task, revision: 1, objective: 'Describe a.' } : task);
    await oldGate.entered;
    const saved = JSON.parse(JSON.stringify(state));
    controller.abort(); oldGate.release(); await Promise.allSettled([(cooperative as any).planSynchronization]); await cooperative.stop();
    state = saved; controller = new AbortController(); cooperative = create();
    const gate = gateCheck(), restoring = track(cooperative.restore());
    await gate.entered;
    expect(gate.heldAtEntry()).toBe(false);
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    expect(state.cooperation!.edits).toHaveLength(1);
    gate.release(); await restoring;
    expect(node('a').pendingValidation).toBeUndefined(); expect(node('a').status).toBe('integrated');
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied' });
    expect(state.cooperation!.edits![0].recheck!.tasks.find(item => item.taskId === 'a')!.status).toBe('passed');
    expect(state.cooperation!.edits![0].pendingSync).toBeUndefined();
    expect(state.cooperation!.history ?? []).toHaveLength(saved.cooperation.history?.length ?? 0);
    expect(state.cooperation!.cursors!.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
  });

  it.each([true, false])('preserves a newer Lead draft after source validation (concurrent control: %s)', async control => {
    await integrateA();
    // Legacy receipts without a reference footprint must be checked after source changes.
    delete node('a').integratedCheck!.references;
    const canonical = state.cooperation!.canonicalCommit!;
    // A Lead journal makes its source seed a distinct commit even within one clock tick.
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Lead journal before canonical source synchronization.\n');
    commitSolverSources(problem, workspace);
    const seed = (cooperative as any).seed(workers[0], canonical) as string;
    expect(seed).not.toBe(canonical);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
      tasks: state.cooperation!.tasks.map(item => item.task), groups: state.cooperation!.groups!.map(item => item.group),
    }) + '\n```\n');
    const commit = writeLemma(workers[0], 'lead_helper');
    const action: CooperativeAction = { kind: 'lead', seedCommit: seed, planVersion: state.cooperation!.planVersion };
    const gate = gateCheck(), delivery = track(cooperative.deliver(workers[0], action, commit));
    await gate.waitFor(delivery);
    expect(gate.heldAtEntry()).toBe(false);
    if (control) await edit('pause-during-lead-check', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    const newerDraft = writeLemma(workers[0], 'newer_draft');
    gate.release(); await delivery; await sync();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(newerDraft);
    expect(fs.readFileSync(path.join(workspace, problem.projectRelative, 'Submission.lean'), 'utf8')).toContain('lemma newer_draft');
    expect(source()).toContain('lemma lead_helper');
    expect(source()).not.toContain('lemma newer_draft');
    if (control) {
      expect(node('b').task.status).toBe('paused');
      expect(state.cooperation!.edits!.find(item => item.id === 'pause-during-lead-check')!.status).toBe('applied');
    }
  });

  it('persists a preparation failure after accepting an edit and retries it on restore without replaying the plan', async () => {
    await integrateA();
    const error = Object.assign(new Error('Statement context storage EIO'), { code: 'EIO' });
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockRejectedValueOnce(error);
    await edit('statement-preparation-retry', task => task.id === 'a' ? { ...task, statementReview: true, informalStatement: 'True.' } : task);
    await expect(sync()).rejects.toBe(error);
    expect(node('a').pendingValidation).toBeDefined();
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied', pendingSync: true });
    const saved = JSON.parse(JSON.stringify(state));
    expect(saved.cooperation.cursors.edits).toBe(fs.statSync(path.join(directory, 'edits.jsonl')).size);
    expect(events.some(item => item.event === 'edit_rejected')).toBe(false);
    controller.abort(); await cooperative.stop();
    state = saved; controller = new AbortController(); cooperative = create();
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockReturnValue(undefined);
    const accept = vi.spyOn(cooperative as any, 'acceptPlan');
    await cooperative.restore(); await cooperative.pulse();
    expect(accept.mock.calls.every(([, appliedEdit]) => appliedEdit === undefined)).toBe(true);
    expect(node('a').pendingValidation).toBeUndefined();
    expect(state.cooperation!.edits).toHaveLength(1);
    expect(state.cooperation!.history ?? []).toHaveLength(saved.cooperation.history?.length ?? 0);
    expect(state.cooperation!.edits![0]).toMatchObject({ status: 'applied' });
    expect(state.cooperation!.edits![0].pendingSync).toBeUndefined();
    expect(state.cooperation!.statementReviews).toContainEqual(expect.objectContaining({ taskId: 'a', status: 'pending' }));
  });

  it('allows independent work and another edit while preparing a fixed statement context', async () => {
    await integrateA();
    const entered = deferred<void>(), release = deferred<void>();
    releases.push(() => release.resolve());
    vi.spyOn(cooperative as any, 'prepareStatementContexts').mockImplementationOnce(() => {
      expect(lockHeld).toBe(false); entered.resolve(); return release.promise;
    }).mockReturnValue(undefined);
    await edit('prepare-statement', task => task.id === 'a' ? { ...task, statementReview: true, informalStatement: 'True.' } : task);
    await entered.promise;
    expect(node('a').pendingValidation).toBeDefined();
    expect(taskDependenciesReady(node('b').task, state.cooperation!.tasks)).toBe(false);
    const independent = await cooperative.next(workers[3], { maxTurns: 20, remainingMs: Infinity });
    expect(independent).toMatchObject({ kind: 'task', task: { id: 'c' } });
    await edit('control-during-statement', task => task.id === 'b' ? { ...task, status: 'paused' } : task);
    expect(state.cooperation!.edits!.find(item => item.id === 'control-during-statement')!.status).toBe('applied');
    release.resolve(); await sync();
    expect(node('a').pendingValidation).toBeUndefined();
    expect(state.cooperation!.statementReviews).toContainEqual(expect.objectContaining({ taskId: 'a', status: 'pending' }));
  });

  it('integrates a previously delivered consumer once its source dependency finishes validation', async () => {
    await integrateA();
    const consumer = await cooperative.next(workers[2], { maxTurns: 20, remainingMs: Infinity });
    expect(consumer).toMatchObject({ kind: 'task', task: { id: 'b' } });
    const consumerCommit = writeLemma(workers[2], 'b');
    const canonical = state.cooperation!.canonicalCommit!;
    const seed = (cooperative as any).seed(workers[0], canonical) as string;
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({
      tasks: state.cooperation!.tasks.map(item => item.task), groups: state.cooperation!.groups!.map(item => item.group),
    }) + '\n```\n');
    delete node('a').integratedCheck!.references;
    const commit = writeLemma(workers[0], 'lead_helper');
    const gate = gateCheck(), delivery = track(cooperative.deliver(workers[0], {
      kind: 'lead', seedCommit: seed, planVersion: state.cooperation!.planVersion,
    }, commit));
    await gate.waitFor(delivery);
    await cooperative.deliver(workers[2], consumer!, consumerCommit);
    expect(node('b').status).toBe('delivered');
    expect(source()).not.toContain('lemma b : True := by trivial');
    gate.release(); await delivery; await sync();
    expect(node('b').status).toBe('integrated'); expect(source()).toContain('lemma b : True := by trivial');
    expect(state.cooperation!.deliveries!.filter(item => item.taskId === 'b' && item.kind === 'proof' && item.status === 'verified')).toHaveLength(1);
  });
});
