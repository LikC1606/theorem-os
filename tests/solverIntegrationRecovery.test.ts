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
import { assignmentDeliveryFile, taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'integration-recovery-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`, targetCommit: request.targetCommit,
      status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type Failure = 'abort' | 'storage' | 'unavailable';
const failureError = (failure: Failure) => failure === 'abort' ? new DOMException('Merged check interrupted.', 'AbortError') :
  failure === 'storage' ? Object.assign(new Error('Transient integration storage failure.'), { code: 'EIO' }) :
    new Error('math_verifier_unavailable');
const failedBatch = (request: MathematicsVerifierBatchRequest, status: 'failed' | 'unavailable'): MathematicsVerifierBatchResult => {
  const batch = verified(request);
  return { ...batch, status, results: batch.results.map(item => ({ ...item, status, error: 'Fixture merged check failure.' })) };
};

describe('checked task integration recovery', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController, action: TaskAction;
  let cursors: Record<string, number>, snapshots: Record<string, number>[];
  let events: { event: string; details?: Record<string, unknown> }[];

  const node = (id = 'recovery') => state.cooperation!.tasks.find(item => item.task.id === id)!;
  const records = () => state.cooperation!.deliveries ?? [];
  const log = () => path.join(workers[1].worktree, assignmentDeliveryFile(action.assignment));
  const key = () => `${workers[1].id}/${assignmentDeliveryFile(action.assignment)}`;
  const poll = () => (cooperative as any).readWorkerDeliveries(workers[1], action, cursors) as Promise<void>;
  const append = (value: unknown) => fs.appendFileSync(log(), JSON.stringify(value) + '\n');
  const canonicalSource = () => committedSource(workspace, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const writeLemma = (worker: ResearchWorker, declaration: string) => {
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', declaration + '\ntheorem add_zero'));
    return commitSolverSources(problem, worker.worktree);
  };
  const assign = (task: CooperativeTask, worker: ResearchWorker, dependencies: TaskAction['assignment']['dependencies'] = []): TaskAction => ({
    kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: worker.id,
      seedCommit: problem.baseCommit, assignmentId: `dispatch-${task.id}`, dependencies },
  });
  const proofLog = (commit: string) => {
    append({ summary: 'Accepted prefix.' });
    const prefixEnd = fs.statSync(log()).size;
    append({ id: 'proof', kind: 'proof', commit, summary: 'A checked recovery lemma.' });
    append({ summary: 'Accepted suffix.' });
    return prefixEnd;
  };
  const failMergedOnce = (failure: Failure) => {
    const error = failureError(failure);
    let calls = 0;
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (++calls === 2) {
        if (failure === 'unavailable') return failedBatch(request, 'unavailable');
        throw error;
      }
      return verified(request);
    });
    return error;
  };
  const expectNoMathematicalFailure = (feedback?: string) => {
    expect(records().filter(record => record.kind === 'failure' || record.status === 'failed')).toEqual([]);
    expect(state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(state.cooperation!.blockers ?? []).toEqual([]);
    expect(node().feedback).toBe(feedback);
    expect(events.filter(item => item.event === 'delivery_rejected')).toEqual([]);
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'solver-integration-recovery-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    workers = [{ id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles },
      ...['parent', 'child'].map(id => {
        const worktree = path.join(directory, id);
        git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
        return { id, role: 'researcher' as const, worktree, ownedFiles: problem.ownedFiles };
      })];
    const task: CooperativeTask = { id: 'recovery', kind: 'lemma', objective: 'Prove a reusable recovery lemma.',
      theoremName: 'Tutorial.recovery_lemma', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    action = assign(task, workers[1]);
    state = { schema: 'deepscientist.math.solver.v1', runId: 'integration-recovery-fixture', problem,
      taskDigest: 'task', buildDigest: 'build', environmentDigest: 'environment', evaluatorDigest: 'evaluator',
      model: 'unused', effort: 'unused', worktree: workspace, phase: 'running', turns: 0, failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [{ task, assignment: action.assignment, status: 'running', attempts: 1 }, ...problem.targets.map((target, index) => ({
          task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
            theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
          status: 'pending' as const, attempts: 0,
        }))] } };
    cursors = {}; snapshots = []; events = []; controller = new AbortController();
    cooperative = new CooperativeResearch({ state, workers,
      access: new Map(workers.map(worker => [worker.id, { environment: {}, retrievalRoot: directory }])),
      signal: controller.signal, save: () => snapshots.push({ ...cursors }), emit: (event, details) => events.push({ event, details }),
      modules: directSolverModules, exclusiveCheck: async check => check() });
  });
  afterEach(async () => {
    controller.abort(); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each(['abort', 'storage', 'unavailable'] as const)
  ('retains a checked proof and the reader prefix after a merged %s failure, then retries only integration', async failure => {
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by trivial');
    const prefixEnd = proofLog(commit), error = failMergedOnce(failure);

    await expect(poll()).rejects.toMatchObject({ name: error.name, message: error.message });

    const checked = node().proof;
    expect(node()).toMatchObject({ status: 'delivered', proof: { passed: true, commit } });
    expect(node().integratedCheck).toBeUndefined();
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(cursors[key()]).toBe(prefixEnd);
    expect(snapshots.at(-1)?.[key()]).toBe(prefixEnd);
    expect(records().map(record => record.summary)).toEqual(['Accepted prefix.']);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expectNoMathematicalFailure();

    await poll(); await poll();

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node().proof).toBe(checked);
    expect(canonicalSource()).toContain('lemma recovery_lemma : True := by trivial');
    expect(records().map(record => [record.kind, record.status, record.summary])).toEqual([
      ['progress', 'advisory', 'Accepted prefix.'], ['proof', 'verified', 'A checked recovery lemma.'],
      ['progress', 'advisory', 'Accepted suffix.'],
    ]);
    expect(cursors[key()]).toBe(fs.statSync(log()).size);
    expect(host.verify).toHaveBeenCalledTimes(3);
    expectNoMathematicalFailure();
  });

  it.each(['abort', 'storage'] as const)
  ('preserves canonical acceptance when statement preparation has a %s failure and completes the publication on replay', async failure => {
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by trivial');
    const prefixEnd = proofLog(commit), error = failureError(failure);
    const prepare = vi.spyOn(cooperative as any, 'prepareStatementContexts').mockRejectedValueOnce(error);

    await expect(poll()).rejects.toBe(error);

    const accepted = state.cooperation!.canonicalCommit, receipt = node().integratedCheck, proof = node().proof;
    expect(accepted).not.toBe(problem.baseCommit);
    expect(node()).toMatchObject({ status: 'integrated', proof: { passed: true }, integratedCheck: { passed: true } });
    expect(canonicalSource()).toContain('lemma recovery_lemma : True := by trivial');
    expect(cursors[key()]).toBe(prefixEnd);
    expect(records().map(record => record.summary)).toEqual(['Accepted prefix.']);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expectNoMathematicalFailure();

    await poll(); await poll();

    expect(state.cooperation!.canonicalCommit).toBe(accepted);
    expect(node().proof).toBe(proof); expect(node().integratedCheck).toBe(receipt);
    expect(prepare).toHaveBeenCalledTimes(2);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(records().find(record => record.kind === 'proof')).toMatchObject({ status: 'verified', commit });
    expect(records().map(record => record.summary)).toEqual(['Accepted prefix.', 'A checked recovery lemma.', 'Accepted suffix.']);
    expect(cursors[key()]).toBe(fs.statSync(log()).size);
    expectNoMathematicalFailure();
  });

  it.each(['abort', 'storage', 'unavailable'] as const)
  ('propagates a direct delivery %s failure without rejecting the proved task and recovers on retry', async failure => {
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by trivial');
    const error = failMergedOnce(failure), rejected = vi.spyOn(cooperative, 'rejected');

    await expect(cooperative.deliver(workers[1], action, commit)).rejects.toMatchObject({ name: error.name, message: error.message });

    const checked = node().proof;
    expect(node()).toMatchObject({ status: 'delivered', proof: { passed: true } });
    expect(rejected).not.toHaveBeenCalled(); expectNoMathematicalFailure();

    await cooperative.deliver(workers[1], action, commit);

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node().proof).toBe(checked);
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(records().find(record => record.kind === 'proof')?.status).toBe('verified');
    expect(rejected).not.toHaveBeenCalled(); expectNoMathematicalFailure();
  });

  it.each(['abort', 'storage', 'unavailable'] as const)
  ('keeps the assignment pending after an initial %s check failure stops its worker', async failure => {
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by trivial');
    const error = failureError(failure), rejected = vi.spyOn(cooperative, 'rejected');
    host.verify.mockImplementationOnce(async (request: MathematicsVerifierBatchRequest) => {
      if (failure === 'unavailable') return failedBatch(request, 'unavailable');
      throw error;
    });

    await expect(cooperative.deliver(workers[1], action, commit)).rejects.toMatchObject({ name: error.name, message: error.message });

    expect(node().status).toBe('running');
    const checkpoint = node().proof;
    expect(rejected).not.toHaveBeenCalled(); expectNoMathematicalFailure();

    cooperative.stopped(workers[1], error.message);

    expect(node()).toMatchObject({ status: 'pending', attempts: 1, feedback: error.message });
    expect(node().assignment).toBe(action.assignment);
    expect(node().proof).toBe(checkpoint);
    expect(cooperative.current(action)).toBe(true);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(node().integratedCheck).toBeUndefined();
    expect(host.verify).toHaveBeenCalledTimes(1);
    expect(rejected).not.toHaveBeenCalled(); expectNoMathematicalFailure(error.message);
  });

  it('records a conditional proof once across incremental and direct delivery of the same assignment commit', async () => {
    const childTask: CooperativeTask = { id: 'child', kind: 'lemma', objective: 'Prove the child.',
      theoremName: 'Tutorial.recovery_child', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const parentTask = { ...action.task, dependsOn: ['child'], conditional: true };
    action = assign(parentTask, workers[1], [{ taskId: childTask.id, taskDigest: taskVersion(childTask) }]);
    Object.assign(node(), { task: parentTask, assignment: action.assignment });
    state.cooperation!.tasks.push({ task: childTask, status: 'pending', attempts: 0 });
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by exact recovery_child');
    proofLog(commit); await poll();
    const checked = node().proof, accepted = [...records()];
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{
      status: 'conditional', assignmentKey: assignmentDeliveryFile(action.assignment), submissionId: 'proof', commit,
    }]);

    const result = await cooperative.deliver(workers[1], action, commit);

    expect(result.check).toBe(checked);
    expect(node()).toMatchObject({ status: 'conditional', proof: { passed: true } });
    expect(node().proof).toBe(checked);
    expect(records()).toEqual(accepted);
    expect(records().filter(record => record.kind === 'proof')).toHaveLength(1);
    expect(host.verify).toHaveBeenCalledTimes(1);
    expectNoMathematicalFailure();
  });

  it('continues ready parent integration when an already recorded conditional proof is replayed', async () => {
    const childTask: CooperativeTask = { id: 'child', kind: 'lemma', objective: 'Prove the child.',
      theoremName: 'Tutorial.recovery_child', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const child = assign(childTask, workers[2]);
    const parentTask = { ...action.task, dependsOn: ['child'], conditional: true };
    action = assign(parentTask, workers[1], [{ taskId: childTask.id, taskDigest: taskVersion(childTask) }]);
    Object.assign(node(), { task: parentTask, assignment: action.assignment });
    state.cooperation!.tasks.push({ task: childTask, assignment: child.assignment, status: 'running', attempts: 1 });
    const parentCommit = writeLemma(workers[1], 'lemma recovery_lemma : True := by exact recovery_child');
    proofLog(parentCommit); await poll();
    expect(node()).toMatchObject({ status: 'conditional', proof: { passed: true, conditions: [{ taskId: 'child' }] } });
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ status: 'conditional', submissionId: 'proof' }]);
    const checked = node().proof;
    const childCommit = writeLemma(workers[2], 'lemma recovery_child : True := by trivial');
    const error = failureError('storage');
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      if (host.verify.mock.calls.length === 4) throw error;
      return verified(request);
    });

    await expect(cooperative.deliver(workers[2], child, childCommit)).rejects.toBe(error);

    expect(node('child').status).toBe('integrated'); expect(node().status).toBe('conditional');
    const acceptedChild = state.cooperation!.canonicalCommit;
    expect(canonicalSource()).toContain('lemma recovery_child : True := by trivial');
    expect(canonicalSource()).not.toContain('lemma recovery_lemma');
    expectNoMathematicalFailure();

    append({ id: 'proof', kind: 'proof', commit: parentCommit, summary: 'A checked recovery lemma.' });
    append({ summary: 'Parent recovery finished.' });
    await poll(); await poll();

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node().integratedCheck!.conditions ?? []).toEqual([]);
    expect(node().proof).toBe(checked);
    expect(state.cooperation!.canonicalCommit).not.toBe(acceptedChild);
    expect(canonicalSource()).toContain('lemma recovery_child : True := by trivial');
    expect(canonicalSource()).toContain('lemma recovery_lemma : True := by exact recovery_child');
    expect(host.verify).toHaveBeenCalledTimes(5);
    expect(records().filter(record => record.taskId === 'recovery' && record.kind === 'proof').map(record => record.status))
      .toEqual(['conditional', 'verified']);
    expect(records().filter(record => record.summary === 'Accepted prefix.')).toHaveLength(1);
    expect(cursors[key()]).toBe(fs.statSync(log()).size);
    expectNoMathematicalFailure();
  });

  it('finishes an accepted parent publication when replaying the child after statement preparation failed', async () => {
    const childTask: CooperativeTask = { id: 'child', kind: 'lemma', objective: 'Prove the child.',
      theoremName: 'Tutorial.recovery_child', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    const child = assign(childTask, workers[2]);
    const parentTask = { ...action.task, dependsOn: ['child'], conditional: true };
    action = assign(parentTask, workers[1], [{ taskId: childTask.id, taskDigest: taskVersion(childTask) }]);
    Object.assign(node(), { task: parentTask, assignment: action.assignment });
    state.cooperation!.tasks.push({ task: childTask, assignment: child.assignment, status: 'running', attempts: 1 });
    const parentCommit = writeLemma(workers[1], 'lemma recovery_lemma : True := by exact recovery_child');
    proofLog(parentCommit); await poll();
    const childCommit = writeLemma(workers[2], 'lemma recovery_child : True := by trivial');
    const childFile = path.join(workers[2].worktree, assignmentDeliveryFile(child.assignment));
    const childKey = `${workers[2].id}/${assignmentDeliveryFile(child.assignment)}`;
    fs.writeFileSync(childFile, JSON.stringify({ summary: 'Accepted child prefix.' }) + '\n');
    const prefixEnd = fs.statSync(childFile).size;
    fs.appendFileSync(childFile, JSON.stringify({ id: 'child-proof', kind: 'proof', commit: childCommit,
      summary: 'The accepted child proof.' }) + '\n');
    fs.appendFileSync(childFile, JSON.stringify({ summary: 'Accepted child suffix.' }) + '\n');
    const pollChild = () => (cooperative as any).readWorkerDeliveries(workers[2], child, cursors) as Promise<void>;
    const error = failureError('storage');
    const prepare = vi.spyOn(cooperative as any, 'prepareStatementContexts').mockImplementationOnce(() => undefined)
      .mockRejectedValueOnce(error);

    await expect(pollChild()).rejects.toBe(error);

    const accepted = state.cooperation!.canonicalCommit, receipt = node().integratedCheck;
    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node('child')).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(canonicalSource()).toContain('lemma recovery_child : True := by trivial');
    expect(canonicalSource()).toContain('lemma recovery_lemma : True := by exact recovery_child');
    expect(cursors[childKey]).toBe(prefixEnd);
    expect(records().filter(record => record.kind === 'proof').map(record => [record.taskId, record.status]))
      .toEqual([['recovery', 'conditional'], ['child', 'verified']]);
    expect(host.verify).toHaveBeenCalledTimes(4);
    expectNoMathematicalFailure();

    await pollChild(); await pollChild();

    expect(state.cooperation!.canonicalCommit).toBe(accepted);
    expect(node().integratedCheck).toBe(receipt);
    expect(prepare).toHaveBeenCalledTimes(3);
    expect(host.verify).toHaveBeenCalledTimes(4);
    expect(records().filter(record => record.kind === 'proof').map(record => [record.taskId, record.status]))
      .toEqual([['recovery', 'conditional'], ['child', 'verified'], ['recovery', 'verified']]);
    expect(records().filter(record => record.summary === 'Accepted child prefix.')).toHaveLength(1);
    expect(records().filter(record => record.summary === 'Accepted child suffix.')).toHaveLength(1);
    expect(cursors[childKey]).toBe(fs.statSync(childFile).size);
    expectNoMathematicalFailure();
  });

  it('still consumes an explicit merged proof failure as mathematical feedback', async () => {
    const commit = writeLemma(workers[1], 'lemma recovery_lemma : True := by trivial');
    proofLog(commit);
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) =>
      host.verify.mock.calls.length === 2 ? failedBatch(request, 'failed') : verified(request));

    await poll(); await poll();

    expect(node()).toMatchObject({ status: 'blocked', proof: { passed: true }, integratedCheck: { passed: false },
      feedback: expect.stringContaining('math_task_merged_proof_failed') });
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ status: 'failed', commit }]);
    expect(cursors[key()]).toBe(fs.statSync(log()).size);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });
});
