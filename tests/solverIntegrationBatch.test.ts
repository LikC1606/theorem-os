import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LAKE_CONFIGURATION_FILES, mathLocalModuleBuildOrder } from '../src/math/mathConstructionSources';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import { captureDeliveryArtifacts } from '../src/solver/deliveryArtifacts';
import type { KnowledgeContextSnapshot } from '../src/solver/knowledgeContext';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask, type TaskAssignment, type TaskRecord } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch, workerAccess } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';

const host = vi.hoisted(() => ({ verify: vi.fn(), check: vi.fn(), identity: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/math/leanTypeDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanTypeDiagnostics')>(), checkLeanType: host.check,
}));
vi.mock('../src/math/leanResidualGoals', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanResidualGoals')>(), leanDiagnosticEnvironmentIdentity: host.identity,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

type Fault = 'unavailable' | 'abort' | 'storage' | 'cleanup' | 'corrupt-receipt';

describe('same-layer checked task integration batches', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController;
  let access: ReturnType<typeof workerAccess>;
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
  const drain = () => track((cooperative as any).integrateReady() as Promise<void>);
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
  const failVerifier = (failure: Fault, error: Error, cleanupError: string) =>
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (failure === 'abort' || failure === 'storage') throw error;
      const batch = verified(request);
      if (failure === 'unavailable') {
        batch.status = 'unavailable'; batch.results = batch.results.map(item => ({ ...item, status: 'unavailable', error: error.message }));
      } else if (failure === 'cleanup') {
        batch.status = 'failed';
        batch.results = batch.results.map(item => ({ ...item, status: 'failed', error: 'Lean exited with status 1.',
          stdoutPreview: 'Submission.lean:3:1: error: Fixture cleanup failure.', cleanupError }));
      } else batch.results = batch.results.map(item => ({ ...item, targetCommit: '0'.repeat(40) }));
      return batch;
    });
  const expectNoFailure = () => {
    expect(state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(state.cooperation!.blockers ?? []).toEqual([]);
    expect(state.cooperation!.deliveries?.filter(item => item.status === 'failed') ?? []).toEqual([]);
  };

  beforeEach(() => {
    receipts = []; sequence = 0; releases = []; pending = []; events = [];
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.check.mockReset().mockImplementation(() => { throw new Error('fixture_unexpected_knowledge_check'); });
    host.identity.mockReset().mockReturnValue({ environmentDigest: mathDigest('diagnostic-environment'), toolIdentity: mathDigest('fixture-tools') });
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-integration-batch-');
    ({ directory, workspace, problem } = example);
    workers = [leadWorker(problem, workspace), ...['first', 'second', 'independent'].map(id => peerWorker(example, id))];
    const tasks: TaskRecord[] = ['first', 'second'].map(id => {
      const task: CooperativeTask = { id, kind: 'lemma', objective: `Prove independent helper ${id}.`,
        theoremName: `Tutorial.batch_${id}`, proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
      const assignment: TaskAssignment = { taskId: id, taskDigest: taskVersion(task), workerId: id,
        seedCommit: problem.baseCommit, assignmentId: `batch-dispatch-${id}`, dependencies: [] };
      return { task, assignment, status: 'running', attempts: 1 };
    });
    state = solverState(problem, workspace, { runId: 'integration-batch-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [...tasks, ...problem.targets.map((target, index) => ({
          task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
            theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
          status: 'pending' as const, attempts: 0,
        }))] } });
    controller = new AbortController();
    let queue = Promise.resolve();
    access = workerAccess(workers, directory);
    cooperative = cooperativeResearch({ state, workers, access, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }),
      exclusiveCheck: async check => {
        const previous = queue, { promise, resolve } = deferred();
        queue = promise;
        await previous;
        try { return await check(); } finally { resolve(); }
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
      expect(events.find(item => item.event === 'task_integrated' && item.details?.taskId === record.task.id)?.details)
        .toMatchObject({ taskId: record.task.id, taskDigest: taskVersion(record.task),
          assignmentKey: assignmentDeliveryFile(record.assignment!), workerId: record.assignment!.workerId,
          seedCommit: record.assignment!.seedCommit, commit: check.commit, sourceDigest: check.sourceDigest,
          receiptIds: check.verification.results.map(result => result.receiptId) });
    }
    await drain(); await drain();
    expect(calls()).toHaveLength(1);
    expect(state.cooperation!.deliveries?.filter(item => item.kind === 'proof' && item.status === 'verified')).toHaveLength(2);
    for (const delivery of state.cooperation!.deliveries!.filter(item => item.kind === 'proof' && item.status === 'verified'))
      expect(events.find(item => item.event === 'delivery_published' && item.details?.deliveryId === delivery.id)?.details)
        .toMatchObject({ deliveryId: delivery.id, producer: delivery.producer, workerId: delivery.producer,
          taskId: delivery.taskId, taskDigest: delivery.taskDigest, assignmentKey: delivery.assignmentKey,
          commit: delivery.commit, sourceDigest: delivery.sourceDigest,
          receiptIds: delivery.evidence!.verification.results.map(result => result.receiptId) });
    expect(events.filter(item => item.event === 'task_integrated')).toHaveLength(2);
    expectNoFailure();
  });

  it('preserves a batched peer\'s incremental and direct metadata while publishing its knowledge once', async () => {
    const first = node(), second = node('second'), firstWorker = workers[1]!, secondWorker = workers[2]!;
    const firstAction: Extract<CooperativeAction, { kind: 'task' }> = { kind: 'task', task: first.task, assignment: first.assignment! };
    const secondAction: typeof firstAction = { kind: 'task', task: second.task, assignment: second.assignment! };
    const knowledge = { digest: 'batch-pinned-catalog', base: { entries: [{ id: 'saved-theorem' }] } } as KnowledgeContextSnapshot;
    for (const value of access.values()) value.environment = { PATH: '/usr/bin:/bin', ELAN_HOME: '', LEAN_PATH: '', LEAN_SYSROOT: '',
      DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'missing.env') };
    access.get(secondWorker.id)!.knowledgeSnapshot = knowledge;
    fs.writeFileSync(path.join(secondWorker.worktree, 'RESEARCH.md'), JSON.stringify({ summary: 'Second helper with selected experience.',
      knowledgeUses: [{ id: 'saved-theorem', catalogDigest: knowledge.digest,
        declaration: { name: 'Tutorial.batch_second', file: 'Submission.lean' },
        application: { expression: 'True.intro', expectedType: 'True',
          context: { file: 'Submission.lean', declaration: second.task.theoremName } } }] }));
    const firstCommit = writeLemma(firstWorker, 'lemma batch_first : True := by trivial');
    const secondCommit = writeLemma(secondWorker, 'lemma batch_second : True := by trivial');
    const artifacts = captureDeliveryArtifacts({ problem, worktree: secondWorker.worktree, commit: secondCommit, assignment: second.assignment! });
    type DiagnosticInput = Parameters<typeof import('../src/math/leanTypeDiagnostics').checkLeanType>[0];
    host.check.mockImplementation(async (input: DiagnosticInput) => {
      const files = [...mathLocalModuleBuildOrder(input.projectRoot, input.file).map(module => module.file),
        ...LAKE_CONFIGURATION_FILES.filter(file => fs.existsSync(path.join(input.projectRoot, file)))]
        .map(file => ({ file, digest: mathDigest(fs.readFileSync(path.join(input.projectRoot, file))) }));
      const contents = canonicalMathJson({ files, expression: input.expression, type: input.type });
      const artifact = { path: '.lake/batch-knowledge-application.json', digest: mathDigest(contents) };
      fs.mkdirSync(path.join(input.projectRoot, '.lake'), { recursive: true });
      fs.writeFileSync(path.join(input.projectRoot, artifact.path), contents);
      return { status: 'elaborated', exitCode: 0, timedOut: false, sourceFiles: files, artifact,
        sourceSnapshotDigest: mathDigest(canonicalMathJson(files)), projectionDigest: mathDigest('batch-application-projection'),
        environment: host.identity(), type: input.type, constants: ['True.intro'], stdout: '', stderr: '' };
    });
    const firstCheck = deferred<MathematicsVerifierBatchResult>(), secondCheck = deferred<MathematicsVerifierBatchResult>();
    const firstEntered = deferred<MathematicsVerifierBatchRequest>(), secondEntered = deferred<MathematicsVerifierBatchRequest>();
    const checking = new Set<string>();
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => {
      const name = request.items.length === 1 ? request.items[0]!.theoremName : undefined;
      if (name && name === first.task.theoremName && !checking.has(name)) {
        checking.add(name); firstEntered.resolve(request); return firstCheck.promise;
      }
      if (name && name === second.task.theoremName && !checking.has(name)) {
        checking.add(name); secondEntered.resolve(request); return secondCheck.promise;
      }
      return Promise.resolve(verified(request));
    });
    releases.push(() => {
      const firstRequest = calls().find(request => request.items.length === 1 && request.items[0]!.theoremName === first.task.theoremName);
      const secondRequest = calls().find(request => request.items.length === 1 && request.items[0]!.theoremName === second.task.theoremName);
      if (firstRequest) firstCheck.resolve(verified(firstRequest));
      if (secondRequest) secondCheck.resolve(verified(secondRequest));
    });
    const log = path.join(secondWorker.worktree, assignmentDeliveryFile(second.assignment!));
    fs.writeFileSync(log, JSON.stringify({ id: 'incremental-second', kind: 'proof', commit: secondCommit,
      summary: 'Second helper incremental evidence.', evidenceRefs: ['second-evidence-reference'] }) + '\n');
    cooperative.activate(secondWorker, secondAction, async () => {}, async () => {});
    const incremental = track(cooperative.pulse(secondWorker.id));
    const secondRequest = await secondEntered.promise;
    const direct = track(cooperative.deliver(secondWorker, secondAction, secondCommit));
    const firstDelivery = track(cooperative.deliver(firstWorker, firstAction, firstCommit));
    const firstRequest = await firstEntered.promise;
    // Both checks finish together so the first canonical operation can integrate the ready pair.
    firstCheck.resolve(verified(firstRequest)); secondCheck.resolve(verified(secondRequest));
    await Promise.all([firstDelivery, incremental, direct]);

    expect(calls().map(request => request.items.length)).toEqual([1, 1, 2]);
    expect(events.filter(item => item.event === 'task_integration_batch_started').map(item => item.details?.taskIds))
      .toEqual([['first', 'second']]);
    expect(canonicalSource()).toContain('lemma batch_first : True := by trivial');
    expect(canonicalSource()).toContain('lemma batch_second : True := by trivial');
    const records = () => state.cooperation!.deliveries?.filter(item => item.kind === 'proof' && item.taskId === second.task.id) ?? [];
    expect(records()).toHaveLength(1);
    expect(records()[0]).toMatchObject({ status: 'verified', submissionId: 'incremental-second',
      assignmentKey: assignmentDeliveryFile(second.assignment!), artifacts, evidenceRefs: ['second-evidence-reference'],
      knowledgeUses: [{ consumer: { taskId: second.task.id, taskDigest: taskVersion(second.task) },
        application: { check: { status: 'elaborated', proofAcceptance: 'not-assessed' } } }] });
    expect(host.check).toHaveBeenCalledTimes(1);
    expect(events.filter(item => item.event === 'knowledge_use_observed' && item.details?.taskId === second.task.id)).toHaveLength(1);
    expect(events.filter(item => item.event === 'delivery_published' && item.details?.taskId === second.task.id)).toHaveLength(1);
    const queueStarts = events.flatMap((item, index) => item.event === 'integration_queue_started' ? [index] : []);
    expect(queueStarts).toHaveLength(2);
    // The first operation publishes its batched peer before that peer's own canonical turn.
    expect(events.findIndex(item => item.event === 'delivery_published' && item.details?.taskId === second.task.id)).toBeLessThan(queueStarts[1]!);

    await track(cooperative.pulse(secondWorker.id));
    await track(cooperative.deliver(secondWorker, secondAction, secondCommit));

    expect(records()).toHaveLength(1); expect(host.check).toHaveBeenCalledTimes(1);
    expect(events.filter(item => item.event === 'knowledge_use_observed' && item.details?.taskId === second.task.id)).toHaveLength(1);
    expect(state.cooperation!.cursors?.[`${secondWorker.id}/${assignmentDeliveryFile(second.assignment!)}`]).toBe(fs.statSync(log).size);
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
    failVerifier(failure, error, 'EIO removing scratch directory.');

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
    failVerifier(failure, error, 'EIO removing recheck checkout.');

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
