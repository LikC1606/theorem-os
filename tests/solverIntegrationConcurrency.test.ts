import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import type { SolverRunState } from '../src/solver/archive';
import type { CooperativeResearch } from '../src/solver/cooperation';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeAction, type CooperativeTask } from '../src/solver/tasks';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { failedBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: () => undefined,
  resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

const verified = (request: MathematicsVerifierBatchRequest) =>
  verifiedBatch(request, { sessionId: 'integration-concurrency-fixture', checks: true });
const settled = (request: MathematicsVerifierBatchRequest, status: 'failed' | 'unavailable'): MathematicsVerifierBatchResult => {
  const batch = verified(request);
  return status === 'failed' ? failedBatch(batch, { stdoutPreview: () => 'Submission.lean:3:1: error: Fixture merged proof failure.' })
    : { ...batch, status, results: batch.results.map(item => ({ ...item, status, error: 'Fixture merged check failure.' })) };
};
type TaskAction = Extract<CooperativeAction, { kind: 'task' }>;
type Failure = 'abort' | 'storage' | 'unavailable';

describe('task integration with concurrent host control', () => {
  let directory: string, workspace: string, problem: SolverProblem, state: SolverRunState;
  let workers: ResearchWorker[], cooperative: CooperativeResearch, controller: AbortController, action: TaskAction;
  let exclusive: <T>(check: () => Promise<T>) => Promise<T>, lockHeld: boolean;
  let pending: Promise<unknown>[], releases: (() => void)[];
  let events: { event: string; details?: Record<string, unknown> }[];

  const node = () => state.cooperation!.tasks.find(item => item.task.id === action.task.id)!;
  const records = () => state.cooperation!.deliveries ?? [];
  const canonicalSource = () => committedSource(workspace, state.cooperation!.canonicalCommit!,
    `${problem.projectRelative}/Submission.lean`);
  const track = <T,>(promise: Promise<T>) => {
    pending.push(promise); void promise.catch(() => {}); return promise;
  };
  const writeLemma = (worker: ResearchWorker, declaration: string) => {
    const file = path.join(worker.worktree, problem.projectRelative, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem add_zero', declaration + '\ntheorem add_zero'));
    return commitSolverSources(problem, worker.worktree);
  };
  const gateCheck = (call: number) => {
    const entered = deferred<MathematicsVerifierBatchRequest>(), result = deferred<MathematicsVerifierBatchResult>();
    let request: MathematicsVerifierBatchRequest | undefined, heldAtEntry: boolean | undefined, count = 0;
    host.verify.mockImplementation(async (input: MathematicsVerifierBatchRequest) => {
      if (++count !== call) return verified(input);
      request = input; heldAtEntry = lockHeld; entered.resolve(input); return result.promise;
    });
    const release = () => { if (request) result.resolve(verified(request)); };
    releases.push(release);
    return { entered: entered.promise, release, fail: (error: unknown) => result.reject(error),
      finish: (status: 'kernel_verified' | 'failed' | 'unavailable') => result.resolve(status === 'kernel_verified'
        ? verified(request!) : settled(request!, status)), heldAtEntry: () => heldAtEntry };
  };
  const edit = (id: string, change: (task: CooperativeTask) => CooperativeTask, group = (value: object): object => value) => {
    fs.appendFileSync(path.join(directory, 'edits.jsonl'), JSON.stringify({ id, baseVersion: state.cooperation!.planVersion,
      tasks: state.cooperation!.tasks.map(item => change(item.task)), groups: state.cooperation!.groups!.map(item => group(item.group)),
    }) + '\n');
    return track(cooperative.pulse(workers[0].id));
  };
  const expectNoMathematicalFailure = () => {
    expect(records().filter(record => record.kind === 'failure' || record.status === 'failed')).toEqual([]);
    expect(state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(state.cooperation!.blockers ?? []).toEqual([]);
    expect(events.filter(item => item.event === 'delivery_rejected')).toEqual([]);
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.createSession.mockReset().mockImplementation(() => { throw new Error('fixture_real_models_forbidden'); });
    const example = localExample('solver-integration-concurrency-');
    ({ directory, workspace, problem } = example);
    workers = [leadWorker(problem, workspace), ...['author', 'independent'].map(id => peerWorker(example, id))];
    const task: CooperativeTask = { id: 'integration', kind: 'lemma', objective: 'Prove a reusable integration lemma.',
      theoremName: 'Tutorial.integration_lemma', proofPath: 'Submission.lean', type: 'True', dependsOn: [], revision: 0 };
    action = { kind: 'task', task, assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: workers[1].id,
      seedCommit: problem.baseCommit, assignmentId: 'integration-dispatch', dependencies: [] } };
    state = solverState(problem, workspace, { runId: 'integration-concurrency-fixture', phase: 'running', failures: [],
      cooperation: { canonicalCommit: problem.baseCommit,
        groups: [{ group: { id: 'main', objective: 'Prove the original problem.', status: 'active', revision: 0 }, turns: 0 }],
        tasks: [{ task, assignment: action.assignment, status: 'running', attempts: 1 }, ...problem.targets.map((target, index) => ({
          task: { id: `goal_${index}`, kind: 'goal' as const, objective: `Prove ${target.theoremName}.`,
            theoremName: target.theoremName, proofPath: target.proofPath, dependsOn: [], revision: 0, status: 'paused' as const },
          status: 'pending' as const, attempts: 0,
        }))] } });
    events = []; pending = []; releases = []; lockHeld = false; controller = new AbortController();
    let queue = Promise.resolve();
    exclusive = async check => {
      const previous = queue;
      let release!: () => void;
      queue = new Promise<void>(resolve => { release = resolve; });
      await previous; lockHeld = true;
      try { return await check(); } finally { lockHeld = false; release(); }
    };
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      emit: (event, details) => events.push({ event, details }), exclusiveCheck: check => exclusive(check) });
    state.cooperation!.planVersion = (cooperative as any).planVersion();
  });
  afterEach(async () => {
    for (const release of releases) release();
    controller.abort(); await Promise.allSettled(pending); await cooperative.stop();
    expect(host.createSession).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it.each([
    { change: 'pause', verdict: 'kernel_verified' }, { change: 'pause', verdict: 'failed' },
    { change: 'revise', verdict: 'kernel_verified' }, { change: 'revise', verdict: 'failed' },
  ] as const)('applies a $change edit before the pending merged $verdict check finishes and discards its stale result', async ({ change, verdict }) => {
    const commit = writeLemma(workers[1], 'lemma integration_lemma : True := by trivial');
    const gate = gateCheck(2), delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    expect(node()).toMatchObject({ status: 'delivered', proof: { passed: true, commit } });
    const checked = node().proof;

    let applied = false;
    const pulse = edit('control-during-merge', task => task.id !== action.task.id ? task : change === 'pause'
      ? { ...task, status: 'paused' } : { ...task, revision: task.revision + 1, type: 'True ∧ True' });
    void pulse.then(() => { applied = true; });
    await vi.waitFor(() => {
      expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: 'control-during-merge', status: 'applied' }));
      expect(applied).toBe(true);
    });
    expect(gate.heldAtEntry()).toBe(false);
    expect(cooperative.current(action)).toBe(false);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    const current = node(), snapshot = JSON.parse(JSON.stringify(current));

    gate.finish(verdict); await delivery;

    expect(node()).toBe(current);
    expect(node()).toEqual(snapshot);
    expect(node().integratedCheck).toBeUndefined();
    if (change === 'pause') expect(node().proof).toBe(checked);
    else expect(node().proof).toBeUndefined();
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(canonicalSource()).not.toContain('lemma integration_lemma');
    expect(records().filter(record => record.kind === 'proof' && ['verified', 'failed'].includes(record.status))).toEqual([]);
    expect(events.filter(item => item.event === 'task_integrated')).toEqual([]);
    expectNoMathematicalFailure();
  });

  it.each(['maxConcurrent', 'maxTurns'] as const)
  ('rechecks a delivered proof after a concurrent group %s control change without publishing a failure', async control => {
    const commit = writeLemma(workers[1], 'lemma integration_lemma : True := by trivial');
    const gate = gateCheck(2), delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const delivered = node(), checked = delivered.proof;
    const editId = `group-${control}-during-merge`;
    let applied = false;
    const pulse = edit(editId, task => task, group => ({ ...group, [control]: 2 }));
    void pulse.then(() => { applied = true; });
    await vi.waitFor(() => {
      expect(state.cooperation!.edits).toContainEqual(expect.objectContaining({ id: editId, status: 'applied' }));
      expect(applied).toBe(true);
    });
    expect(gate.heldAtEntry()).toBe(false);
    expect(cooperative.current(action)).toBe(true);
    expect(node()).toBe(delivered);
    expect(node().proof).toBe(checked);
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expectNoMathematicalFailure();

    gate.release(); await delivery;

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node().proof).toBe(checked);
    expect(canonicalSource()).toContain('lemma integration_lemma : True := by trivial');
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ taskId: action.task.id, status: 'verified', commit }]);
    expect(events.filter(item => item.event === 'task_integrated')).toHaveLength(1);
    expectNoMathematicalFailure();
  });

  it('remerges and rechecks after canonical advancement without losing an independent declaration', async () => {
    const commit = writeLemma(workers[1], 'lemma integration_lemma : True := by trivial');
    const gate = gateCheck(2), delivery = track(cooperative.deliver(workers[1], action, commit));
    const originalMerged = await gate.entered;
    // This independent source checkpoint is not represented as a checked task or accepted proof.
    const independent = writeLemma(workers[2], 'lemma independent_lemma : True := by trivial');
    let advanced = false;
    const advance = track(exclusive(async () => {
      state.cooperation!.canonicalCommit = independent; (cooperative as any).changed(); advanced = true;
    }));
    await vi.waitFor(() => expect(advanced).toBe(true)); await advance;
    expect(gate.heldAtEntry()).toBe(false);
    expect(canonicalSource()).toContain('lemma independent_lemma : True := by trivial');

    gate.release(); await delivery;

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(state.cooperation!.canonicalCommit).not.toBe(independent);
    expect(canonicalSource()).toContain('lemma integration_lemma : True := by trivial');
    expect(canonicalSource()).toContain('lemma independent_lemma : True := by trivial');
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(host.verify.mock.calls[2][0].targetCommit).not.toBe(originalMerged.targetCommit);
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ taskId: action.task.id, status: 'verified', commit }]);
    expectNoMathematicalFailure();
  });

  it('shares an in-flight exact proof delivery so concurrent duplicates do not repeat verification', async () => {
    const commit = writeLemma(workers[1], 'lemma integration_lemma : True := by trivial');
    const gate = gateCheck(1), first = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const duplicate = track(cooperative.deliver(workers[1], action, commit));
    await Promise.resolve(); await Promise.resolve();
    expect(host.verify).toHaveBeenCalledTimes(1);

    gate.release(); await Promise.all([first, duplicate]);
    await cooperative.deliver(workers[1], action, commit);

    expect(node()).toMatchObject({ status: 'integrated', proof: { passed: true, commit }, integratedCheck: { passed: true } });
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ taskId: action.task.id, status: 'verified', commit }]);
    expect(events.filter(item => item.event === 'task_integrated')).toHaveLength(1);
    expectNoMathematicalFailure();
  });

  it.each(['abort', 'storage', 'unavailable'] as const)
  ('retains the checked delivery after a merged %s fault and retries only integration', async (failure: Failure) => {
    const commit = writeLemma(workers[1], 'lemma integration_lemma : True := by trivial');
    const gate = gateCheck(2), delivery = track(cooperative.deliver(workers[1], action, commit));
    await gate.entered;
    const checked = node().proof;
    const error = failure === 'abort' ? new DOMException('Merged check interrupted.', 'AbortError') :
      failure === 'storage' ? Object.assign(new Error('Transient integration storage failure.'), { code: 'EIO' }) :
        new Error('math_verifier_unavailable');
    if (failure === 'unavailable') gate.finish('unavailable');
    else gate.fail(error);

    await expect(delivery).rejects.toMatchObject({ name: error.name, message: error.message });

    expect(node()).toMatchObject({ status: 'delivered', proof: { passed: true, commit } });
    expect(node().proof).toBe(checked);
    expect(node().integratedCheck).toBeUndefined();
    expect(state.cooperation!.canonicalCommit).toBe(problem.baseCommit);
    expect(records()).toEqual([]);
    expectNoMathematicalFailure();

    await cooperative.deliver(workers[1], action, commit);

    expect(node()).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(node().proof).toBe(checked);
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(records().filter(record => record.kind === 'proof')).toMatchObject([{ status: 'verified', commit }]);
    expectNoMathematicalFailure();
  });
});
