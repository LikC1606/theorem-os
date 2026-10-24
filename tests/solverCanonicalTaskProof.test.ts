import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LOCAL_EXAMPLE_STATEMENT } from '../src/math/localExample';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { parseCooperationPlan, type CooperativeResearch } from '../src/solver/cooperation';
import { directSolverModules } from '../src/solver/modules';
import type { ResearchWorker } from '../src/solver/modules/organization';
import { committedSource, commitSolverSources, git } from '../src/solver/problem';
import { freshlyAccepted, taskVersion } from '../src/solver/tasks';
import { TaskTypePreflightCache } from '../src/solver/taskTypePreflight';
import { deferred } from './helpers/async';
import { cooperativeResearch } from './helpers/cooperation';
import { leadWorker, localExample, peerWorker, solverState } from './helpers/solver';
import { failedBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), model: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, formalVerificationToolIdentity: () => 'canonical-fixture-tools',
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: () => undefined,
}));

describe('canonical helper checks before model dispatch', () => {
  let directory: string, state: SolverRunState, workers: ResearchWorker[], cooperative: CooperativeResearch;
  let controller: AbortController, allowed: boolean, environment: NodeJS.ProcessEnv;
  let exclusive: <T>(operation: () => Promise<T>) => Promise<T>;
  const budget = { maxTurns: Infinity, remainingMs: Infinity };
  const node = () => state.cooperation!.tasks.find(item => item.task.id === 'helper')!;
  const verified = (request: MathematicsVerifierBatchRequest) => verifiedBatch(request, { sessionId: 'canonical-fixture', checks: true });
  const mismatchMessage = 'Helper declaration has a different type or additional assumptions';
  const rejectCandidate = (message = mismatchMessage) => host.verify.mockImplementationOnce(async request =>
    failedBatch(verified(request), { stdoutPreview: () => `Submission.lean:1:1: error: ${message}` }));
  const next = (index = 1) => cooperative.next(workers[index], budget);
  const noDelivery = () => {
    expect(state.cooperation!.deliveries ?? []).toEqual([]);
    expect(state.cooperation!.failedTaskInputs ?? []).toEqual([]);
    expect(node().proof).toBeUndefined(); expect(node().integratedCheck).toBeUndefined();
    expect(node().attempts).toBe(0);
  };
  const writeCanonical = (source: string) => {
    fs.writeFileSync(path.join(workers[0].worktree, state.problem.projectRelative, 'Submission.lean'), source);
    state.cooperation!.canonicalCommit = commitSolverSources(state.problem, workers[0].worktree);
  };
  const source = (declaration = 'lemma helper : True := by trivial') =>
    LOCAL_EXAMPLE_STATEMENT.replace('theorem add_zero', `${declaration}\ntheorem add_zero`);
  const holdVerifier = () => {
    const entered = deferred<MathematicsVerifierBatchRequest>(), release = deferred<void>();
    host.verify.mockImplementationOnce(async (request: MathematicsVerifierBatchRequest) => {
      entered.resolve(request); await release.promise; return verified(request);
    });
    return { entered: entered.promise, release: () => release.resolve() };
  };

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => verified(request));
    host.model.mockReset().mockImplementation(() => { throw new Error('fixture_models_forbidden'); });
    const example = localExample('solver-canonical-helper-'), { workspace, problem } = example;
    directory = example.directory;
    workers = [leadWorker(problem, workspace), peerWorker(example, 'proof'), peerWorker(example, 'other')];
    const plan = parseCooperationPlan(problem, { tasks: [
      { id: 'helper', kind: 'lemma', objective: 'Prove exact helper', theoremName: 'Tutorial.helper',
        proofPath: 'Submission.lean', type: 'True', ownerId: 'proof' },
      { id: 'followup', kind: 'research', objective: 'Observe dependency readiness', dependsOn: ['helper'], ownerId: 'proof' },
      { id: 'independent', kind: 'research', objective: 'Independent work', ownerId: 'other' },
      ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal', objective: 'Original goal',
        theoremName: target.theoremName, proofPath: target.proofPath, status: 'paused' })),
    ], groups: [{ id: 'main', objective: 'Original problem', status: 'active', maxConcurrent: 1 }] });
    state = solverState(problem, workspace, { runId: 'canonical-fixture', phase: 'running',
      cooperation: { canonicalCommit: problem.baseCommit, groups: plan.groups.map(group => ({ group, turns: 0 })),
        tasks: plan.tasks.map(task => ({ task, attempts: 0, status: 'pending' })) } });
    writeCanonical(source());
    const envFile = path.join(directory, 'math.env'); fs.writeFileSync(envFile, '');
    environment = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_ENV_FILE: envFile };
    controller = new AbortController(); allowed = true; exclusive = operation => operation();
    cooperative = cooperativeResearch({ state, workers, retrievalRoot: directory, signal: controller.signal,
      access: new Map(workers.map(worker => [worker.id, { environment, retrievalRoot: directory }])),
      modelDispatchAllowed: () => allowed, exclusiveCheck: operation => exclusive(operation),
      modules: { ...directSolverModules, M1: { ...directSolverModules.M1, open: host.model, execute: host.model } } });
    vi.spyOn(TaskTypePreflightCache.prototype, 'check').mockImplementation(async input => ({ current: () => !input.signal?.aborted,
      result: { taskDigest: taskVersion(input.task), inputDigest: 'fixture', evidence: 'advisory-type-elaboration',
        proofAcceptance: 'not-assessed', status: 'deferred', reason: 'fixture' } }));
  });
  afterEach(async () => {
    controller.abort(); await cooperative.stop();
    expect(host.model).not.toHaveBeenCalled();
    vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true });
  });

  it('integrates an existing exact helper, reuses its kernel check and returns its ready consumer', async () => {
    const canonical = state.cooperation!.canonicalCommit!, original = committedSource(workers[0].worktree,
      canonical, `${state.problem.projectRelative}/Submission.lean`);
    expect(await next()).toMatchObject({ kind: 'task', task: { id: 'followup' } });
    expect(node()).toMatchObject({ status: 'integrated', attempts: 0, proof: { passed: true, changes: [] },
      integratedCheck: { passed: true, changes: [] } });
    expect(node().proof!.conditions ?? []).toEqual([]);
    expect(freshlyAccepted(node(), taskVersion(node().task))).toBe(true);
    expect(freshlyAccepted(JSON.parse(JSON.stringify(node())), taskVersion(node().task))).toBe(false);
    expect(state.turns).toBe(0); expect(state.cooperation!.groups![0].turns).toBe(0);
    expect(state.cooperation!.deliveries).toContainEqual(expect.objectContaining({ taskId: 'helper', kind: 'proof', status: 'verified' }));
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][1].expectedDeclarationType).toBe('True');
    expect(state.cooperation!.tasks.filter(item => item.task.kind === 'goal').every(item =>
      item.status === 'pending' && !item.proof)).toBe(true);
    expect(state.check).toBeUndefined();
    expect(committedSource(workers[0].worktree, state.cooperation!.canonicalCommit!,
      `${state.problem.projectRelative}/Submission.lean`)).toBe(original);
  });

  it.each(['different-type', 'extra-assumptions'] as const)('returns normal model work after a %s rejection without recording failure', async kind => {
    if (kind === 'different-type') node().task = { ...node().task, type: 'False' };
    else writeCanonical(source('lemma helper (extra : False) : True := by trivial'));
    rejectCandidate();
    const action = await next();
    expect(action).toMatchObject({ kind: 'task', task: { id: 'helper' } });
    if (action?.kind !== 'task') throw new Error('expected_task_assignment');
    const context = directSolverModules.M4.build(state.problem,
      { ...state, cooperation: cooperative.contextState(action, workers[1]) }, {
        root: directory, worktree: workers[1].worktree, environment, retrievalRoot: directory,
        taskText: 'Prove the original problem.', assignment: action, maxOptionalContextBytes: 0,
      });
    for (const message of [context.message, context.continuationMessage])
      expect(message).toContain(mismatchMessage);
    for (const message of [context.instructions, context.continuationMessage])
      expect(message).toContain('historical source diagnostic, not a model failure or a mathematical refutation');
    expect(action.assignment.canonicalProbe).toMatchObject({ evidence: 'advisory-canonical-check', proofAcceptance: 'not-accepted',
      sourceCommit: action.assignment.seedCommit, environmentDigest: state.environmentDigest, verificationStatus: 'failed' });
    expect(action.assignment.canonicalProbe!.receiptIds).toHaveLength(1);
    expect(context.manifest!.optionalBytes).toBe(0);
    expect(context.manifest!.included).toContainEqual(expect.objectContaining({ id: 'assignment', required: true }));
    expect(host.verify).toHaveBeenCalledOnce(); noDelivery();
    expect(node().status).toBe('running');
    expect(node().feedback).toBeUndefined(); expect(node().repair).toBeUndefined();
  });

  it('preserves prior task feedback alongside the candidate diagnostic without charging a model failure', async () => {
    node().feedback = 'Existing source correction remains relevant.';
    rejectCandidate();
    const action = await next();
    expect(action?.kind === 'task' && action.assignment.canonicalProbe?.feedback).toContain(mismatchMessage);
    expect(node().feedback).toBe('Existing source correction remains relevant.');
    expect(node().sourceRepair).toBeUndefined(); noDelivery();
    expect(state.turns).toBe(0); expect(state.cooperation!.groups![0].turns).toBe(0);
  });

  it('keeps UTF-8 candidate diagnostics bounded before they become mandatory assignment input', async () => {
    rejectCandidate('类型不符：' + '完整诊断'.repeat(3000));
    const action = await next();
    if (action?.kind !== 'task') throw new Error('expected_task_assignment');
    const feedback = action.assignment.canonicalProbe!.feedback;
    expect(Buffer.byteLength(feedback)).toBeLessThanOrEqual(2000);
    expect(feedback).toContain('类型不符'); expect(feedback).not.toContain('\uFFFD');
    noDelivery();
  });

  it('preserves the advisory diagnostic through archive recovery without trusting it as proof', async () => {
    rejectCandidate(); await next();
    const file = path.join(directory, 'state.json'); writeSolverRunState(file, state);
    const restored = readSolverRunState(file), task = restored.cooperation!.tasks.find(item => item.task.id === 'helper')!;
    expect(task.assignment!.canonicalProbe).toEqual(node().assignment!.canonicalProbe);
    const context = directSolverModules.M4.build(restored.problem, restored, {
      root: directory, worktree: workers[1].worktree, environment, retrievalRoot: directory,
      taskText: 'Prove the original problem.', maxOptionalContextBytes: 0,
      assignment: { kind: 'task', task: task.task, assignment: task.assignment! },
    });
    expect(context.message).toContain(mismatchMessage); expect(context.continuationMessage).toContain(mismatchMessage);
    expect(task.proof).toBeUndefined(); expect(task.integratedCheck).toBeUndefined();
    expect(freshlyAccepted(task, taskVersion(task.task))).toBe(false);
    expect(host.verify).toHaveBeenCalledOnce(); noDelivery();
    delete task.assignment!.canonicalProbe; writeSolverRunState(file, restored);
    expect(readSolverRunState(file).cooperation!.tasks.find(item => item.task.id === 'helper')!.assignment!.canonicalProbe).toBeUndefined();
  });

  it('rejects an archive that relabels an advisory candidate diagnostic as accepted proof', async () => {
    rejectCandidate(); await next();
    const file = path.join(directory, 'state.json');
    (node().assignment!.canonicalProbe as any).proofAcceptance = 'kernel_verified';
    writeSolverRunState(file, state);
    expect(() => readSolverRunState(file)).toThrow('math_resume_state_invalid:cooperation.tasks.0.assignment.canonicalProbe.proofAcceptance');
    noDelivery();
  });

  it('shares the diagnostic only through the existing visible task scope', async () => {
    node().task = { ...node().task, groupId: 'private', sharing: 'group' };
    const followup = state.cooperation!.tasks.find(item => item.task.id === 'followup')!;
    followup.task = { ...followup.task, groupId: 'private', sharing: 'group' };
    state.cooperation!.groups!.push({ group: { id: 'private', objective: 'Private route', revision: 0,
      status: 'active', maxConcurrent: 1 }, turns: 0 });
    rejectCandidate(); await next();
    const view = (index: number) => JSON.parse(fs.readFileSync(path.join(workers[index].worktree, 'COOPERATION.json'), 'utf8'));
    for (const index of [0, 1]) expect(view(index).peers.find((item: any) => item.id === 'helper').canonicalProbe)
      .toEqual(node().assignment!.canonicalProbe);
    expect(view(2).peers.find((item: any) => item.id === 'helper').canonicalProbe).toBeUndefined();
    expect(JSON.stringify(view(2))).not.toContain(mismatchMessage); noDelivery();
  });

  it('drops an unstarted assignment diagnostic before redispatching from repaired canonical source', async () => {
    writeCanonical(source('lemma helper (extra : False) : True := by trivial'));
    rejectCandidate(); const rejected = await next();
    if (rejected?.kind !== 'task') throw new Error('expected_task_assignment');
    expect(rejected.assignment.canonicalProbe?.feedback).toContain(mismatchMessage);
    cooperative.release(workers[1], rejected); expect(node().assignment).toBeUndefined();
    writeCanonical(source());
    const ready = await next();
    expect(ready).toMatchObject({ kind: 'task', task: { id: 'followup' } });
    expect(node()).toMatchObject({ status: 'integrated', attempts: 0 });
    expect(node().assignment!.canonicalProbe).toBeUndefined();
    expect(ready?.kind === 'task' && ready.assignment.canonicalProbe).toBeUndefined();
    const view = JSON.parse(fs.readFileSync(path.join(workers[1].worktree, 'COOPERATION.json'), 'utf8'));
    expect(view.peers.find((item: any) => item.id === 'helper').canonicalProbe).toBeUndefined();
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it.each(['missing', 'wrong-namespace', 'ambiguous-leaf', 'sorry', 'admit', 'conditional', 'saved-assignment'] as const)
  ('keeps %s work on the existing model path without a canonical check', async kind => {
    if (kind === 'missing') writeCanonical(LOCAL_EXAMPLE_STATEMENT);
    if (kind === 'wrong-namespace') node().task = { ...node().task, theoremName: 'Other.helper' };
    if (kind === 'ambiguous-leaf') writeCanonical(source('lemma Other.helper : True := by trivial\nlemma helper : True := by trivial'));
    if (kind === 'sorry' || kind === 'admit') writeCanonical(source(`lemma helper : True := by ${kind}`));
    if (kind === 'conditional') node().task = { ...node().task, conditional: true };
    if (kind === 'saved-assignment') node().assignment = { taskId: 'helper', taskDigest: taskVersion(node().task),
      workerId: workers[1].id, seedCommit: state.cooperation!.canonicalCommit!, assignmentId: 'saved' };
    expect(await next()).toMatchObject({ kind: 'task', task: { id: 'helper' } });
    expect(host.verify).not.toHaveBeenCalled(); noDelivery();
  });

  it('preserves normal conditional connection dispatch for unfinished dependencies', async () => {
    const original = state.cooperation!.tasks.find(item => item.task.id === 'goal_0')!;
    original.task = { ...original.task, status: 'active', dependsOn: ['helper'], ownerId: 'other' };
    node().task = { ...node().task, dependsOn: ['child'] };
    state.cooperation!.tasks.push({ task: { id: 'child', kind: 'lemma', theoremName: 'Tutorial.child', type: 'True',
      proofPath: 'Submission.lean', objective: 'Unproved dependency', ownerId: 'other', revision: 0, dependsOn: [] },
      status: 'pending', attempts: 0 });
    expect(await next()).toMatchObject({ kind: 'task', task: { id: 'helper' }, assignment: { connectionCheck: expect.any(Object) } });
    expect(host.verify).not.toHaveBeenCalled(); noDelivery();
  });

  it('leaves independent work dispatchable while awaiting the canonical check', async () => {
    state.cooperation!.groups![0].group.maxConcurrent = 2;
    const held = holdVerifier(), pending = next(); await held.entered;
    expect(node()).toMatchObject({ status: 'pending', attempts: 0 });
    expect(node().assignment).toBeUndefined();
    expect(await next(2)).toMatchObject({ kind: 'task', task: { id: 'independent' } });
    held.release(); expect(await pending).toMatchObject({ kind: 'task', task: { id: 'followup' } });
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each(['canonical', 'contract', 'paused', 'route', 'lead-environment', 'worker-stopped'] as const)
  ('discards a check whose %s changes while Lean is running', async change => {
    const held = holdVerifier(), pending = next(); await held.entered;
    if (change === 'canonical') {
      git(workers[0].worktree, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
        'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'New canonical']);
      state.cooperation!.canonicalCommit = git(workers[0].worktree, ['rev-parse', 'HEAD']);
    }
    if (change === 'contract') node().task = { ...node().task, type: 'False', revision: node().task.revision + 1 };
    if (change === 'paused') node().task = { ...node().task, status: 'paused' };
    if (change === 'route') state.cooperation!.groups![0].group.status = 'paused';
    if (change === 'lead-environment') (cooperative as any).input.access.set(workers[0].id, { environment: {}, retrievalRoot: directory });
    if (change === 'worker-stopped') cooperative.stopped(workers[1]);
    allowed = false; cooperative.modelBudgetChanged(); held.release();
    expect(await pending).toBeUndefined(); noDelivery();
    expect(node().assignment).toBeUndefined(); expect(node().status).toBe('pending');
  });

  it('rechecks the canonical snapshot after waiting for the publication transaction', async () => {
    const entered = deferred<void>(), release = deferred<void>();
    exclusive = async operation => { entered.resolve(); await release.promise; return operation(); };
    const pending = next(); await entered.promise;
    expect(node().assignment).toBeUndefined();
    try {
      git(workers[0].worktree, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
        'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'New canonical before publication']);
      state.cooperation!.canonicalCommit = git(workers[0].worktree, ['rev-parse', 'HEAD']);
      allowed = false; cooperative.modelBudgetChanged();
    } finally { release.resolve(); }
    expect(await pending).toBeUndefined(); noDelivery();
    expect(node().status).toBe('pending'); expect(node().assignment).toBeUndefined();
  });

  it('waits for a cancelled canonical check to clean up before stop returns', async () => {
    const held = holdVerifier(), pending = next(); await held.entered;
    let stopped = false;
    const stopping = cooperative.stop().then(() => { stopped = true; });
    await new Promise<void>(resolve => setImmediate(resolve)); expect(stopped).toBe(false);
    held.release(); expect(await pending).toBeUndefined(); await stopping;
    expect(stopped).toBe(true); noDelivery(); expect(node().assignment).toBeUndefined();
  });
});
