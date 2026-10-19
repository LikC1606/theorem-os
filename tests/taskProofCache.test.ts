import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample, LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import * as leanSource from '../src/math/leanSource';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { checkTaskProofs, createTaskSourceProjector, isAttributedTaskProof, TaskProofCache,
  type TaskProof, type TaskProofRequest } from '../src/solver/cooperativeProof';
import * as problemApi from '../src/solver/problem';
import { commitSolverSources, readSolverProblem, type SolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';

const host = vi.hoisted(() => ({ verify: vi.fn(), environment: vi.fn(), tools: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
  formalVerificationToolIdentity: host.tools,
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: host.environment,
}));

function verified(input: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: input.targetCommit!, sessionId: 'cache-fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: input.items.map((item, index) => ({
      status: 'kernel_verified', targetCommit: input.targetCommit!, proofPath: item.proofPath, theoremName: item.theoremName,
      statementHash: item.statementHash, leanStatementHash: item.leanStatementHash, claim: item.claim ?? 'statement',
      sourceDeclarationHash: item.expectedSourceDeclarationHash, proofHash: 'fixture-proof',
      statementBinding: 'caller-bound-to-committed-declaration', toolchain: { lean: 'fixture-lean' }, verifier: 'lean-kernel',
      goalsRemaining: 0, sorryCount: 0, admitCount: 0, axioms: [], checkedAt: 2,
      checkId: item.id?.trim() || `check-${index + 1}`, receiptId: `receipt-${input.targetCommit}-${index}`, sessionId: 'cache-fixture',
      declarationReferences: { statement: [], proof: [] },
    })) };
}
function rejected(input: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  const batch = verified(input);
  batch.status = 'failed';
  for (const result of batch.results) Object.assign(result, { status: 'failed', goalsRemaining: 1,
    error: 'Lean exited with status 1.', stdoutPreview: `${result.proofPath}:4:1: error: unsolved goals` });
  return batch;
}

describe('run-local task proof projection cache', () => {
  let directory: string, workspace: string, project: string, problem: SolverProblem, seedCommit: string, commit: string;
  let tasks: CooperativeTask[], requests: TaskProofRequest[], env: NodeJS.ProcessEnv, cache: TaskProofCache, signal: AbortSignal;
  const request = (task: CooperativeTask, retainedGoals: string[] = []): TaskProofRequest => ({ task, retainedGoals,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'solver', seedCommit } });
  const check = (options: { requests?: TaskProofRequest[]; sourceCommit?: string; problem?: SolverProblem;
    env?: NodeJS.ProcessEnv; environmentDigest?: string; signal?: AbortSignal; cache?: TaskProofCache; timeoutMs?: number } = {}) =>
    checkTaskProofs(options.problem ?? problem, workspace, options.sourceCommit ?? commit, options.requests ?? requests,
      options.env ?? env, options.signal ?? signal, options.timeoutMs ?? 180000,
      options.environmentDigest ?? 'current-environment', options.cache ?? cache);

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async input => verified(input));
    host.environment.mockReset().mockReturnValue(undefined);
    host.tools.mockReset().mockReturnValue('fixture-tools-first');
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'task-proof-cache-')));
    workspace = path.join(directory, 'workspace');
    const receipt = bootstrapLocalExample(workspace);
    project = receipt.projectRoot;
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF);
    seedCommit = commitSolverSources(problem, workspace);
    fs.writeFileSync(file, LOCAL_EXAMPLE_PROOF.replace('theorem add_zero',
      'lemma first : True := by trivial\nlemma second : True := by trivial\n\ntheorem add_zero'));
    commit = commitSolverSources(problem, workspace);
    tasks = ['first', 'second'].map(name => ({ id: name, kind: 'lemma', objective: `Prove ${name}.`,
      proofPath: 'Submission.lean', theoremName: `Tutorial.${name}`, type: 'True', dependsOn: [], revision: 0 }));
    requests = [request(tasks[0]!)];
    env = { DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'math.env'), PATH: '/usr/bin:/bin' };
    cache = new TaskProofCache();
    signal = new AbortController().signal;
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('reuses only exact inputs in the same run while preserving live attribution on fresh result objects', async () => {
    const first = await check(), second = await check();
    expect(host.verify).toHaveBeenCalledOnce();
    expect(second).toEqual(first);
    expect(second).not.toBe(first);
    expect(second[0]).not.toBe(first[0]);
    expect(second[0]!.verification.results[0]).not.toBe(first[0]!.verification.results[0]);
    expect(first.map(isAttributedTaskProof)).toEqual([true]);
    expect(second.map(isAttributedTaskProof)).toEqual([true]);
    await check({ cache: new TaskProofCache() });
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('preserves unlimited verification and keeps its cache identity separate from a finite timeout', async () => {
    const first = await check({ timeoutMs: Infinity });
    const second = await check({ timeoutMs: Infinity });
    expect(first[0]!.passed).toBe(true);
    expect(second).toEqual(first);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0]![0].timeoutMs).toBe(Infinity);

    await check({ timeoutMs: 180000 });
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.verify.mock.calls[1]![0].timeoutMs).toBe(180000);
  });

  it('shares an in-flight verification only for callers using the same abort signal', async () => {
    let release!: () => void, started!: () => void;
    const gate = new Promise<void>(resolve => { release = resolve; });
    const entered = new Promise<void>(resolve => { started = resolve; });
    host.verify.mockImplementationOnce(async input => { started(); await gate; return verified(input); });
    const first = check();
    await entered;
    const second = check();
    expect(host.verify).toHaveBeenCalledOnce();
    release();
    const [left, right] = await Promise.all([first, second]);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(left).toEqual(right);
    expect(left[0]).not.toBe(right[0]);
    expect(left[0]!.verification.results[0]).not.toBe(right[0]!.verification.results[0]);
    expect(right.map(isAttributedTaskProof)).toEqual([true]);
  });

  it('keeps different cancellation domains out of the same in-flight verification', async () => {
    let release!: () => void, started!: () => void;
    const gate = new Promise<void>(resolve => { release = resolve; });
    const entered = new Promise<void>(resolve => { started = resolve; });
    host.verify.mockImplementationOnce(async input => { started(); await gate; return verified(input); });
    const first = check();
    await entered;
    const second = check({ signal: new AbortController().signal });
    try { expect((await second)[0]!.passed).toBe(true); }
    finally { release(); }
    await first;
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('does not let callers mutate saved receipts or proof edits through a cache hit', async () => {
    const first = await check(), receipt = first[0]!.verification.results[0]!.receiptId;
    first[0]!.verification.results[0]!.receiptId = 'caller-mutated';
    first[0]!.changes[0]!.after = 'caller-mutated-proof';
    first[0]!.passed = false;
    const next = await check();
    expect(next[0]!.passed).toBe(true);
    expect(next[0]!.verification.results[0]!.receiptId).toBe(receipt);
    expect(next[0]!.changes[0]!.after).not.toBe('caller-mutated-proof');
    expect(isAttributedTaskProof(first[0]!)).toBe(false);
    expect(isAttributedTaskProof(next[0]!)).toBe(true);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('does not restore process-local attribution or the cache from serialized proofs', async () => {
    const first = await check(), restored = JSON.parse(JSON.stringify(first));
    expect(restored.map(isAttributedTaskProof)).toEqual([false]);
    const next = await check({ cache: new TaskProofCache() });
    expect(next.map(isAttributedTaskProof)).toEqual([true]);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('rechecks changed proof bytes and source commits', async () => {
    const first = await check();
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by trivial', 'first : True := by exact True.intro'));
    const changed = commitSolverSources(problem, workspace);
    const [next] = await check({ sourceCommit: changed });
    expect(next!.sourceDigest).not.toBe(first[0]!.sourceDigest);
    expect(next!.commit).toBe(changed);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it.each(['seed', 'task', 'retained-goals', 'problem', 'environment-digest', 'environment-settings', 'configuration'] as const)
  ('rechecks changed %s inputs', async change => {
    await check();
    if (change === 'seed') await check({ requests: [{ ...requests[0]!, assignment: { ...requests[0]!.assignment, seedCommit: commit } }] });
    else if (change === 'task') await check({ requests: [request({ ...tasks[0]!, objective: 'Prove the same type for a revised consumer.' })] });
    else if (change === 'retained-goals') await check({ requests: [request(tasks[0]!, [problem.targets[0]!.theoremName])] });
    else if (change === 'problem') await check({ problem: { ...problem, receiptDigest: 'changed-problem-receipt' } });
    else if (change === 'environment-digest') await check({ environmentDigest: 'changed-environment' });
    else if (change === 'environment-settings') await check({ env: { ...env, LEAN_NUM_THREADS: '2' } });
    else {
      fs.mkdirSync(path.join(project, '.lake'), { recursive: true });
      fs.writeFileSync(path.join(project, '.lake/package-overrides.json'), '{"packages":[],"changed":true}\n');
      await check();
    }
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('rechecks changed explicit premises and retains their exact task versions', async () => {
    const task = { ...tasks[0]!, conditional: true }, dependency = tasks[1]!;
    const input = request(task);
    input.assignment.dependencies = [{ taskId: dependency.id, taskDigest: taskVersion(dependency) }];
    await check({ requests: [{ ...input, conditions: [] }] });
    const next = await check({ requests: [{ ...input, conditions: [dependency] }] });
    expect(next[0]!.conditions).toEqual(input.assignment.dependencies);
    const changed = { ...dependency, type: 'True -> True' };
    await check({ requests: [{ ...input, conditions: [changed], assignment: { ...input.assignment,
      dependencies: [{ taskId: changed.id, taskDigest: taskVersion(changed) }] } }] });
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('binds proof reuse to the currently selected verification tools', async () => {
    await check();
    host.tools.mockReturnValue('fixture-tools-replaced');
    await check();
    expect(host.verify).toHaveBeenCalledTimes(2);
    await check();
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('bypasses both old and new cache entries while the actual tool identity is unavailable', async () => {
    await check();
    host.tools.mockReturnValue(undefined);
    await check();
    await check();
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('tracks sealed package identities and environment-file changes without reusing mutable search paths', async () => {
    host.environment.mockReturnValue({ identity: 'sealed-first' });
    await check();
    host.environment.mockReturnValue({ identity: 'sealed-second' });
    await check();
    fs.writeFileSync(env.DEEPSCIENTIST_MATH_ENV_FILE!, 'DEEPSCIENTIST_MATH_SANDBOX_IMAGE=changed-fixture-image\n');
    await check();
    expect(host.verify).toHaveBeenCalledTimes(3);
    const environment = { ...env, LEAN_PATH: path.join(directory, 'mutable-library') };
    await check({ env: environment });
    await check({ env: environment });
    expect(host.verify).toHaveBeenCalledTimes(5);
  });

  it('retains deterministic Lean rejections without converting them into passed proofs', async () => {
    host.verify.mockImplementation(async input => rejected(input));
    const first = await check(), next = await check();
    expect(first[0]!.passed).toBe(false);
    expect(next[0]!.verification.status).toBe('failed');
    expect(isAttributedTaskProof(next[0]!)).toBe(true);
    expect(next).toEqual(first);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each(['blocked', 'unavailable', 'cleanup', 'timeout', 'crashed', 'no-diagnostic'] as const)
  ('does not save a transient %s result as an exact-input cache entry', async kind => {
    host.verify.mockImplementationOnce(async input => {
      const batch = rejected(input), result = batch.results[0]!;
      if (kind === 'blocked' || kind === 'unavailable') batch.status = result.status = kind;
      else if (kind === 'cleanup') result.cleanupError = 'Checkout cleanup failed.';
      else if (kind === 'timeout') result.error = 'Lean verification timed out.';
      else if (kind === 'crashed') result.error = 'Lean exited with status 137.';
      else { delete result.error; delete result.stdoutPreview; }
      return batch;
    });
    expect((await check())[0]!.passed).toBe(false);
    expect((await check())[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('does not save an interrupted verification or poison the next run of identical inputs', async () => {
    const controller = new AbortController();
    host.verify.mockImplementationOnce(async input => { controller.abort(); return verified(input); });
    await expect(check({ signal: controller.signal })).rejects.toMatchObject({ name: 'AbortError' });
    expect((await check())[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('retries after verifier exceptions instead of leaving a rejected singleflight entry', async () => {
    host.verify.mockRejectedValueOnce(new Error('temporary verifier transport failure'));
    await expect(check()).rejects.toThrow('temporary verifier transport failure');
    expect((await check())[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('shares snapshot source reads and declaration indexes across target projections', () => {
    const sources = vi.spyOn(problemApi, 'committedSource');
    const regions = vi.spyOn(leanSource, 'inspectLeanDeclarationRegions');
    const scoped = vi.spyOn(leanSource, 'inspectScopedLeanDeclarations');
    const projectSources = createTaskSourceProjector(problem, workspace, commit);
    const baseline = { sources: sources.mock.calls.length, regions: regions.mock.calls.length, scoped: scoped.mock.calls.length };
    expect(baseline.sources).toBe(problem.ownedFiles.length);
    expect(baseline.regions).toBeGreaterThan(0);
    expect(baseline.scoped).toBeGreaterThan(0);
    projectSources(tasks[0]!, []);
    projectSources(tasks[1]!, []);
    expect({ sources: sources.mock.calls.length, regions: regions.mock.calls.length, scoped: scoped.mock.calls.length }).toEqual(baseline);
  });

  it('returns independent maps and freezes problem/source inputs for the projector lifetime', () => {
    const original = structuredClone(problem);
    const projectSources = createTaskSourceProjector(problem, workspace, commit);
    const expected = projectSources(tasks[0]!, []);
    const changed = projectSources(tasks[0]!, []);
    changed.clear();
    changed.set('Submission.lean', 'caller-mutated-source');
    problem.ownedFiles = [...problem.ownedFiles, 'Missing.lean'];
    problem.targets = [];
    fs.writeFileSync(path.join(project, 'Submission.lean'), 'uncommitted source changes');
    expect(projectSources(tasks[0]!, [])).toEqual(expected);
    expect(projectSources(tasks[1]!, []).get('Submission.lean')).not.toContain('caller-mutated-source');
    expect(projectSources(tasks[0]!, []).has('Missing.lean')).toBe(false);
    problem = original;
  });
});

describe('task proof cache resource bounds', () => {
  const signal = () => new AbortController().signal;
  function value(label: string) {
    const proof = { commit: label, sourceDigest: 'source-digest', taskDigest: 'task-digest', seedCommit: 'seed',
      passed: true, changes: [{ file: 'Submission.lean', name: 'helper', after: `-- ${label}\n` }],
      verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
        targetCommit: label, sessionId: 'fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results: [] },
    } as TaskProof;
    return { proofs: [proof], attributed: [true] };
  }

  it('evicts the least recently used entry rather than a recently read proof', async () => {
    const cache = new TaskProofCache(2), run = vi.fn(async (key: string) => value(key));
    const read = (key: string) => cache.check(key, signal(), () => true, () => run(key));
    await read('A'); await read('B'); await read('A'); await read('C'); await read('A');
    expect(run.mock.calls.map(([key]) => key)).toEqual(['A', 'B', 'C']);
    await read('B');
    expect(run.mock.calls.map(([key]) => key)).toEqual(['A', 'B', 'C', 'B']);
  });

  it('enforces aggregate serialized byte limits independently of entry count', async () => {
    const bytes = Buffer.byteLength(JSON.stringify(value('A')));
    const cache = new TaskProofCache(100, bytes * 2 - 1), run = vi.fn(async (key: string) => value(key));
    const read = (key: string) => cache.check(key, signal(), () => true, () => run(key));
    await read('A'); await read('B'); await read('B'); await read('A');
    expect(run.mock.calls.map(([key]) => key)).toEqual(['A', 'B', 'A']);
  });

  it('does not retain oversized entries or cache entries when capacity is disabled', async () => {
    const bytes = Buffer.byteLength(JSON.stringify(value('A')));
    for (const cache of [new TaskProofCache(10, bytes - 1), new TaskProofCache(0)]) {
      const run = vi.fn(async () => value('A'));
      await cache.check('A', signal(), () => true, run);
      await cache.check('A', signal(), () => true, run);
      expect(run).toHaveBeenCalledTimes(2);
    }
  });

  it('invalidates a saved entry when its referenced verification commit is no longer available', async () => {
    const cache = new TaskProofCache(), run = vi.fn(async () => value('A'));
    await cache.check('A', signal(), () => true, run);
    await cache.check('A', signal(), () => false, run);
    await cache.check('A', signal(), () => true, run);
    expect(run).toHaveBeenCalledTimes(2);
  });
});
