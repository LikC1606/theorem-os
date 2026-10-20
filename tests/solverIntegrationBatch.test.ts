import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskAssignment, type TaskRecord } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const deferred = <T,>() => {
  let resolve!: (value: T) => void;
  const promise = new Promise<T>(complete => { resolve = complete; });
  return { promise, resolve };
};

describe('same-layer checked task integration batches', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController;
  let receipts: MathematicsVerifierBatchResult[], sequence: number, releases: (() => void)[], pending: Promise<unknown>[];
  let events: { event: string; details?: Record<string, unknown> }[];

  const node = (id = 'first') => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const canonicalSource = () => committedSource(workspace, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const calls = () => host.verify.mock.calls.map(([request]) => request as MathematicsVerifierBatchRequest);
  const track = <T,>(promise: Promise<T>) => {
    pending.push(promise); void promise.catch(() => {}); return promise;
  };
  const verified = (request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult => {
    const sessionId = `integration-batch-${++sequence}`;
    const batch: MathematicsVerifierBatchResult = {
      schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
      targetCommit: request.targetCommit!, sessionId, events: [], startedAt: sequence * 10,
      checkedAt: sequence * 10 + 2, durationMs: 2,
      results: request.items.map((item, index) => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
        checkId: item.id?.trim() || `check-${index + 1}`, sessionId, checkedAt: sequence * 10 + 2,
        receiptId: `${sessionId}-${item.theoremName}`, targetCommit: request.targetCommit,
        status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'],
    };
    receipts.push(batch); return batch;
  };
  const writeLemma = (worker: ResearchWorker, declarations: string) => {
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', declarations + '\ntheorem add_zero'));
    return commitSolverSources(problem, worker.worktree);
  };
  const changeTask = (id: string, change: Partial<CooperativeTask>) => {
    const record = node(id);
    record.task = { ...record.task, ...change };
    record.assignment = { ...record.assignment!, taskDigest: taskVersion(record.task) };
  };
  const prepare = async (id = 'first', declarations = `lemma batch_${id} : True := by trivial`) => {
    const record = node(id), worker = workers.find(item => item.id === record.assignment!.workerId)!;
    const commit = writeLemma(worker, declarations);
    const proof = await (cooperative as any).check(record.task, record.assignment, worker.worktree, commit);
    expect(proof.passed).toBe(true);
    Object.assign(record, { status: 'delivered', proof });
    return proof;
  };
  const preparePair = async () => {
    const proofs = await Promise.all([prepare('first'), prepare('second')]);
    host.verify.mockClear(); receipts = []; return proofs;
  };
  const integrate = (id = 'first') => track((cooperative as any).integrateNow(node(id)) as Promise<void>);
  const drain = () => track((cooperative as any).integrateReadyNow() as Promise<void>);
  const gateBatch = (resultFor: (request: MathematicsVerifierBatchRequest) => MathematicsVerifierBatchResult = verified) => {
    const entered = deferred<MathematicsVerifierBatchRequest>(), result = deferred<MathematicsVerifierBatchResult>();
    let held: MathematicsVerifierBatchRequest | undefined;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (request.items.length < 2 || held) return verified(request);
      held = request; entered.resolve(request); return result.promise;
    });
    const release = () => { if (held) result.resolve(resultFor(held)); };
    releases.push(release); return { entered: entered.promise, release };
  };
  const expectNoFailure = () => {
    expect(state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(state.cooperation!.blockers ?? []).toEqual([]);
    expect(state.cooperation!.deliveries?.filter(item => item.status === 'failed') ?? []).toEqual([]);
  };

  beforeEach(() => {
    receipts = []; sequence = 0; releases = []; pending = []; events = [];
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-integration-batch-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    workers = [{ id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles },
      ...['first', 'second', 'independent'].map(id => {
        const worktree = path.join(directory, id);
        git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
        return { id, role: 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
      })];
    const tasks: TaskRecord[] = ['first', 'second'].map(id => {
      const task: CooperativeTask = { id, kind: 'lemma', objective: `Prove independent helper ${id}.`,
        theoremName: `Tutorial.batch_${id}`, proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
      const assignment: TaskAssignment = { taskId: id, taskDigest: taskVersion(task), workerId: id,
        seedCommit: problem.baseCommit, assignmentId: `batch-dispatch-${id}`, dependencies: [] };
      return { task, assignment, status: 'running', attempts: 1 };
    });
    state = { schema: 'deepscientist.math.solver.v1', runId: 'integration-batch-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [...tasks, ...problem.targets.map((target, index) => ({
          task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
            theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
          status: 'pending' as const, attempts: 0,
        }))] } };
    controller = new AbortController();
    let queue = Promise.resolve();
    cooperative = new CooperativeResearch({ state, workers,
      access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => {}, emit: (event, details) => events.push({ event, details }), modules: directSolverModules,
      exclusiveCheck: async check => {
        const previous = queue;
        let release!: () => void;
        queue = new Promise<void>(resolve => { release = resolve; });
        await previous;
        try { return await check(); } finally { release(); }
      } });
    state.cooperation!.planVersion = (cooperative as any).planVersion();
  });
  afterEach(async () => {
    for (const release of releases) release();
    controller.abort(); await Promise.allSettled(pending); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('checks a ready pair once and preserves each target\'s original receipt while publishing the union', async () => {
    const proofs = await preparePair();

    await integrate();

    expect(calls()).toHaveLength(1);
    expect(calls()[0]!.items.map(item => item.theoremName).sort()).toEqual(['Tutorial.batch_first', 'Tutorial.batch_second']);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('integrated');
    expect(node().proof).toBe(proofs[0]); expect(node('second').proof).toBe(proofs[1]);
    expect(canonicalSource()).toContain('lemma batch_first : True := by trivial');
    expect(canonicalSource()).toContain('lemma batch_second : True := by trivial');
    for (const record of [node(), node('second')]) {
      const check = record.integratedCheck!, raw = receipts[0]!;
      expect(check.passed).toBe(true);
      expect(check.verification.sessionId).toBe(raw.sessionId);
      expect(check.verification.targetCommit).toBe(raw.targetCommit);
      expect(check.verification.checkedAt).toBe(raw.checkedAt);
      expect(check.verification.results).toEqual([raw.results.find(item => item.theoremName === record.task.theoremName)]);
      expect(check.commit).toBe(state.cooperation!.canonicalCommit);
    }
    await drain(); await drain();
    expect(calls()).toHaveLength(1);
    expect(state.cooperation!.deliveries?.filter(item => item.kind === 'proof' && item.status === 'verified')).toHaveLength(2);
    expect(events.filter(item => item.event === 'task_integrated')).toHaveLength(2);
    expectNoFailure();
  });

  it.each(['different-group', 'paused', 'dependency', 'unchecked'] as const)
  ('excludes a %s candidate from the ready batch', async exclusion => {
    if (exclusion === 'different-group') {
      changeTask('second', { groupId: 'other' });
      state.cooperation!.groups!.push({ group: { id: 'other', objective: 'Other route.', status: 'active', revision: 0 }, turns: 0 });
    } else if (exclusion === 'dependency') {
      changeTask('second', { dependsOn: ['first'] });
      node('second').assignment!.dependencies = [{ taskId: 'first', taskDigest: taskVersion(node().task) }];
    }
    await preparePair();
    if (exclusion === 'paused') changeTask('second', { status: 'paused' });
    if (exclusion === 'unchecked') node('second').proof = structuredClone(node('second').proof);

    await integrate();

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('delivered');
    expect(canonicalSource()).toContain('lemma batch_first'); expect(canonicalSource()).not.toContain('lemma batch_second');
  });

  it('keeps overlapping declaration changes in individual integrations', async () => {
    await prepare('first', 'lemma shared_helper : True := by trivial\nlemma batch_first : True := by trivial');
    await prepare('second', 'lemma shared_helper : True := by trivial\nlemma batch_second : True := by trivial');
    host.verify.mockClear(); receipts = [];

    await integrate();

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('delivered');
    await drain();
    expect(calls()).toHaveLength(2); expect(calls().every(request => request.items.length === 1)).toBe(true);
    expect(node('second').status).toBe('integrated'); expectNoFailure();
  });

  it('checks individual trees when two targets require different complete source projections', async () => {
    // The mock kernel permits this source so the host's projection grouping is exercised independently.
    await prepare('first', 'lemma batch_first : True := by have _ := Tutorial.add_zero; trivial');
    await prepare('second');
    host.verify.mockClear(); receipts = [];

    await integrate();

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('delivered');
    expect(node().integratedCheck!.verification.results).toHaveLength(1);
  });

  it('preserves a custom M2 checker instead of replacing it with the default batch verifier', async () => {
    await preparePair();
    const original = directSolverModules.M2.checkTask;
    const custom = vi.fn((...args: Parameters<typeof original>) => original(...args));
    (cooperative as any).input.modules = { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask: custom } };

    await integrate();

    expect(custom).toHaveBeenCalledTimes(1);
    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('delivered');
  });

  it('falls back to individual fresh trees after a mixed deterministic batch failure', async () => {
    await preparePair();
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      if (request.items.length === 1) return batch;
      batch.status = 'failed';
      batch.results[1] = { ...batch.results[1]!, status: 'failed', error: 'Lean exited with status 1.',
        stdoutPreview: 'Submission.lean:3:1: error: Fixture failure only in the combined projection.' };
      return batch;
    });

    await integrate(); await drain();

    expect(calls().map(request => request.items.length)).toEqual([2, 1, 1]);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('integrated');
    expect(node().integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    expect(node('second').integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    expect(node().integratedCheck!.verification.targetCommit).not.toBe(receipts[0]!.targetCommit);
    expectNoFailure();
  });

  it('isolates a canonical merge conflict and still integrates an independent checked task', async () => {
    await preparePair();
    state.cooperation!.canonicalCommit = writeLemma(workers[3]!, 'lemma batch_first : True := by exact True.intro');

    await integrate(); await drain();

    expect(node().status).toBe('blocked'); expect(node('second').status).toBe('integrated');
    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(canonicalSource()).toContain('lemma batch_first : True := by exact True.intro');
    expect(canonicalSource()).toContain('lemma batch_second : True := by trivial');
  });

  it('does not repeat a failed mathematical batch for the same canonical and checked inputs', async () => {
    await preparePair();
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      batch.status = 'failed';
      batch.results = batch.results.map(item => ({ ...item, status: 'failed', error: 'Lean exited with status 1.',
        stdoutPreview: 'Submission.lean:3:1: error: Fixture deterministic check failure.' }));
      return batch;
    });
    await integrate();
    expect(node().status).toBe('blocked');
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    Object.assign(node(), { status: 'delivered', feedback: undefined, integratedCheck: undefined });

    await integrate();

    expect(calls().map(request => request.items.length)).toEqual([2, 1, 1]);
    expect(node().status).toBe('blocked'); expect(node('second').status).toBe('delivered');
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
  });

  it('falls back when Lean reveals that a batch member actually uses another batch member', async () => {
    await preparePair();
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      if (request.items.length > 1) batch.results[0] = { ...batch.results[0]!, declarationReferences: {
        statement: [], proof: [{ name: 'Tutorial.batch_second', file: 'Submission.lean' }],
      } };
      return batch;
    });

    await integrate(); await drain();

    expect(calls().map(request => request.items.length)).toEqual([2, 1, 1]);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('integrated');
    expect(node().integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    expect(node('second').integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    expectNoFailure();
  });

  it('discards the entire pending union after a concurrent task revision', async () => {
    await preparePair();
    const gate = gateBatch(), operation = integrate(); await gate.entered;
    const revised = node('second');
    revised.task = { ...revised.task, revision: revised.task.revision + 1, type: 'True ∧ True' };
    revised.status = 'pending'; delete revised.proof; delete revised.assignment;
    (cooperative as any).changed();

    gate.release(); await operation;

    expect(node('second')).toBe(revised); expect(node('second').integratedCheck).toBeUndefined();
    expect(canonicalSource()).not.toContain('lemma batch_second');
    expect(node().integratedCheck?.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    expectNoFailure();
  });

  it('rechecks the complete pair after canonical advancement and preserves the added declaration', async () => {
    await preparePair();
    const gate = gateBatch(), operation = integrate(), original = await gate.entered;
    const advanced = writeLemma(workers[3]!, 'lemma independent_lemma : True := by trivial');
    state.cooperation!.canonicalCommit = advanced; (cooperative as any).changed();

    gate.release(); await operation;

    expect(calls().map(request => request.items.length)).toEqual([2, 2]);
    expect(calls()[1]!.targetCommit).not.toBe(original.targetCommit);
    expect(node().status).toBe('integrated'); expect(node('second').status).toBe('integrated');
    expect(canonicalSource()).toContain('lemma independent_lemma : True := by trivial');
    expect(canonicalSource()).toContain('lemma batch_first'); expect(canonicalSource()).toContain('lemma batch_second');
    expectNoFailure();
  });

  it.each(['pause', 'maxConcurrent'] as const)
  ('discards the pending shared receipt after a concurrent group %s edit', async control => {
    await preparePair();
    const gate = gateBatch(), operation = integrate(); await gate.entered;
    const group = state.cooperation!.groups![0]!;
    group.group = control === 'pause' ? { ...group.group, status: 'paused' } : { ...group.group, maxConcurrent: 2 };
    (cooperative as any).changed();

    gate.release(); await operation;

    if (control === 'pause') {
      expect(calls().map(request => request.items.length)).toEqual([2]);
      expect(node().status).toBe('delivered'); expect(node('second').status).toBe('delivered');
      expect(node().integratedCheck).toBeUndefined(); expect(node('second').integratedCheck).toBeUndefined();
      expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    } else {
      expect(calls().map(request => request.items.length)).toEqual([2, 2]);
      expect(node().status).toBe('integrated'); expect(node('second').status).toBe('integrated');
      expect(node().integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
      expect(node('second').integratedCheck!.verification.sessionId).not.toBe(receipts[0]!.sessionId);
    }
    expectNoFailure();
  });

  it.each(['unavailable', 'abort', 'storage', 'cleanup', 'corrupt-receipt'] as const)
  ('propagates a batch %s fault without expanding it into per-task verifier retries', async failure => {
    const proofs = await preparePair();
    const error = failure === 'abort' ? new DOMException('Fixture aborted.', 'AbortError') : failure === 'storage'
      ? Object.assign(new Error('Fixture storage failure.'), { code: 'EIO' }) : new Error('math_verifier_unavailable');
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (failure === 'abort' || failure === 'storage') throw error;
      const batch = verified(request);
      if (failure === 'unavailable') {
        batch.status = 'unavailable'; batch.results = batch.results.map(item => ({ ...item, status: 'unavailable', error: error.message }));
      } else if (failure === 'cleanup') {
        batch.status = 'failed';
        batch.results = batch.results.map(item => ({ ...item, status: 'failed', error: 'Lean exited with status 1.',
          stdoutPreview: 'Submission.lean:3:1: error: Fixture cleanup failure.', cleanupError: 'EIO removing scratch directory.' }));
      } else batch.results = batch.results.map(item => ({ ...item, targetCommit: '0'.repeat(40) }));
      return batch;
    });

    await expect(integrate()).rejects.toBeInstanceOf(Error);

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(2);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(node().status).toBe('delivered'); expect(node('second').status).toBe('delivered');
    expect(node().proof).toBe(proofs[0]); expect(node('second').proof).toBe(proofs[1]);
    expect(node().integratedCheck).toBeUndefined(); expect(node('second').integratedCheck).toBeUndefined();
    expectNoFailure();
  });

  it.each(['passed', 'failed', 'unavailable'] as const)
  ('discards a stale shared recheck after its %s result settles without per-task retries', async outcome => {
    await preparePair(); await integrate();
    const canonical = state.cooperation!.canonicalCommit!, tasks = structuredClone(state.cooperation!.tasks);
    const before = structuredClone(tasks), accepted = structuredClone(state.cooperation!.tasks);
    host.verify.mockClear(); receipts = []; events = [];
    const gate = gateBatch(request => {
      const batch = verified(request);
      if (outcome !== 'passed') {
        batch.status = outcome === 'failed' ? 'failed' : 'unavailable';
        batch.results = batch.results.map(item => ({ ...item, status: batch.status,
          error: outcome === 'failed' ? 'Lean exited with status 1.' : 'math_verifier_unavailable',
          ...(outcome === 'failed' ? { stdoutPreview: 'Submission.lean:3:1: error: unsolved goals' } : {}) }));
      }
      return batch;
    });
    const check = vi.spyOn(cooperative as any, 'check');
    let current = true;
    const rechecking = track((cooperative as any).recheckIntegrated(canonical, false, {
      tasks, ids: new Set(['first', 'second']), environment: {}, environmentDigest: state.environmentDigest,
      current: () => current,
    }) as Promise<boolean>);
    await gate.entered; current = false; gate.release();

    if (outcome === 'unavailable') await expect(rechecking).rejects.toThrow('math_verifier_unavailable');
    else await expect(rechecking).resolves.toBe(false);

    expect(calls().map(request => request.items.length)).toEqual([2]);
    expect(check).not.toHaveBeenCalled();
    expect(tasks).toEqual(before); expect(state.cooperation!.tasks).toEqual(accepted);
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect(events.some(item => ['task_recheck_batch_fallback', 'task_recheck_finished'].includes(item.event))).toBe(false);
    expectNoFailure();
  });

  it.each(['unavailable', 'abort', 'storage', 'cleanup', 'corrupt-receipt'] as const)
  ('preserves restored accepted tasks after a shared recheck %s fault without per-task retries', async failure => {
    await preparePair(); await integrate();
    const canonical = state.cooperation!.canonicalCommit!;
    for (const record of [node(), node('second')]) {
      record.proof = structuredClone(record.proof);
      record.integratedCheck = structuredClone(record.integratedCheck);
    }
    const before = [node(), node('second')].map(record => structuredClone(record));
    host.verify.mockClear(); receipts = [];
    const error = failure === 'abort' ? new DOMException('Fixture recheck interrupted.', 'AbortError') : failure === 'storage'
      ? Object.assign(new Error('Fixture recheck storage failure.'), { code: 'EIO' }) : new Error('math_verifier_unavailable');
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (failure === 'abort' || failure === 'storage') throw error;
      const batch = verified(request);
      if (failure === 'unavailable') {
        batch.status = 'unavailable'; batch.results = batch.results.map(item => ({ ...item, status: 'unavailable', error: error.message }));
      } else if (failure === 'cleanup') {
        batch.status = 'failed';
        batch.results = batch.results.map(item => ({ ...item, status: 'failed', error: 'Lean exited with status 1.',
          stdoutPreview: 'Submission.lean:3:1: error: Fixture cleanup failure.', cleanupError: 'EIO removing recheck checkout.' }));
      } else batch.results = batch.results.map(item => ({ ...item, targetCommit: '0'.repeat(40) }));
      return batch;
    });

    await expect(track((cooperative as any).recheckIntegrated(canonical, false))).rejects.toBeInstanceOf(Error);

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(2);
    expect(state.cooperation!.canonicalCommit).toBe(canonical);
    expect([node(), node('second')]).toEqual(before);
    expectNoFailure();
  });

  it.each(['corrupt-receipt', 'no-diagnostic-failure'] as const)
  ('preserves a single checked delivery after a %s result instead of recording a mathematical blocker', async failure => {
    const proofs = await preparePair();
    changeTask('second', { status: 'paused' });
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      if (failure === 'corrupt-receipt') batch.results = batch.results.map(item => ({ ...item, targetCommit: '0'.repeat(40) }));
      else {
        batch.status = 'failed';
        batch.results = batch.results.map(item => ({ ...item, status: 'failed', error: 'Verifier failed without a Lean diagnostic.' }));
      }
      return batch;
    });

    await expect(integrate()).rejects.toThrow('math_verifier_unavailable');

    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(node().status).toBe('delivered'); expect(node().proof).toBe(proofs[0]);
    expect(node().integratedCheck).toBeUndefined(); expect(node().feedback).toBeUndefined();
    expectNoFailure();
  });

  it('keeps a bound real draft-source rejection available as mathematical feedback', async () => {
    const record = node(), worker = workers.find(item => item.id === record.assignment!.workerId)!;
    const commit = writeLemma(worker, 'lemma batch_first : True := by sorry');
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      const batch = verified(request);
      expect(fs.readFileSync(path.join(request.projectRoot, request.items[0]!.proofPath), 'utf8')).toContain('by sorry');
      batch.status = 'failed';
      batch.results = batch.results.map(item => ({ ...item, status: 'failed', sorryCount: 1, admitCount: 0,
        axioms: [], error: 'Proof source contains sorry or admit.' }));
      return batch;
    });

    const delivered = await cooperative.deliver(worker, { kind: 'task', task: record.task, assignment: record.assignment! }, commit);

    expect(delivered.check?.passed).toBe(false); expect(record.status).toBe('pending');
    expect(record.feedback).toContain('Proof source contains sorry or admit.');
    expect(record.proof).toBe(delivered.check);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(state.cooperation!.deliveries?.filter(item => item.kind === 'proof')).toMatchObject([{ status: 'failed', commit }]);
    expect(events).toContainEqual(expect.objectContaining({ event: 'task_repair_requested',
      details: expect.objectContaining({ taskId: 'first', workerId: 'first' }) }));
    expect(calls()).toHaveLength(1); expect(calls()[0]!.items).toHaveLength(1);
  });
});
