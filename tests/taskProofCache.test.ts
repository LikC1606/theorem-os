import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { bootstrapLocalExample, LOCAL_EXAMPLE_PROOF } from '../src/math/localExample';
import * as leanSource from '../src/math/leanSource';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { checkTaskProofs, createTaskSourceProjector, isAttributedTaskProof, trustedTaskProjectionReuse, TaskProofCache,
  type TaskProof, type TaskProofRequest } from '../src/solver/cooperativeProof';
import * as problemApi from '../src/solver/problem';
import { commitSolverSources, git, readSolverProblem, withSolverWorktree, type SolverProblem } from '../src/solver/problem';
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
const proofViews = (proofs: TaskProof[]) => proofs.map(({ projectionReuse: _reuse, ...proof }) => proof);

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
  const recommit = () => {
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost',
      'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'Equivalent source snapshot']);
    return git(workspace, ['rev-parse', 'HEAD']);
  };

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
    expect(proofViews(second)).toEqual(proofViews(first));
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
    expect(proofViews(second)).toEqual(proofViews(first));
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
    expect(proofViews(left)).toEqual(proofViews(right));
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

  it('reuses a complete equal projection tree across raw commits and preserves the original receipt metadata', async () => {
    const [first] = await check();
    const changedCommit = recommit();
    const [next] = await check({ sourceCommit: changedCommit });
    expect(changedCommit).not.toBe(commit);
    expect(next!.commit).toBe(changedCommit);
    expect(next!.references?.sourceCommit).toBe(changedCommit);
    expect(next!.verification).toEqual(first!.verification);
    const reuse = trustedTaskProjectionReuse(next!);
    expect(reuse).toMatchObject({ schema: 'theorem-os.task-projection-reuse.v1',
      checkedProjectionCommit: first!.verification.targetCommit });
    expect(reuse!.projectionCommit).not.toBe(reuse!.checkedProjectionCommit);
    expect(git(workspace, ['rev-parse', `${reuse!.projectionCommit}^{tree}`])).toBe(reuse!.projectionTree);
    expect(git(workspace, ['rev-parse', `${reuse!.checkedProjectionCommit}^{tree}`])).toBe(reuse!.projectionTree);
    expect(isAttributedTaskProof(next!)).toBe(true);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('recomputes seed-relative changes and imports while reusing the same projection', async () => {
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, `import Mathlib.Data.Nat.Basic\n${fs.readFileSync(file, 'utf8')}`);
    const changedCommit = commitSolverSources(problem, workspace);
    const [first] = await check({ sourceCommit: changedCommit });
    expect(first!.changes.length).toBeGreaterThan(0);
    expect(first!.imports).toEqual([{ file: 'Submission.lean', module: 'Mathlib.Data.Nat.Basic' }]);
    const [next] = await check({ sourceCommit: changedCommit,
      requests: [{ ...requests[0]!, assignment: { ...requests[0]!.assignment, seedCommit: changedCommit } }] });
    expect(next!.seedCommit).toBe(changedCommit);
    expect(next!.changes).toEqual([]);
    expect(next!.imports).toBeUndefined();
    expect(next!.verification).toEqual(first!.verification);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('reuses a delivery when integration changes worktree, seed and worker and omits empty dependencies', async () => {
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, `import Mathlib.Data.Nat.Basic\n${fs.readFileSync(file, 'utf8')}`);
    const deliveryCommit = commitSolverSources(problem, workspace);
    const [delivery] = await check({ sourceCommit: deliveryCommit,
      requests: [{ ...requests[0]!, assignment: { ...requests[0]!.assignment, dependencies: [] } }] });
    const integrationCommit = recommit();
    const [integrated] = await withSolverWorktree(workspace, integrationCommit, checkout =>
      checkTaskProofs(problem, checkout, integrationCommit, [{ ...requests[0]!, assignment: {
        taskId: tasks[0]!.id, taskDigest: taskVersion(tasks[0]!), workerId: 'integration', seedCommit: integrationCommit,
      } }], env, signal, 180000, 'current-environment', cache));
    expect(delivery!.changes.length).toBeGreaterThan(0);
    expect(delivery!.imports).toEqual([{ file: 'Submission.lean', module: 'Mathlib.Data.Nat.Basic' }]);
    expect(integrated!.commit).toBe(integrationCommit);
    expect(integrated!.seedCommit).toBe(integrationCommit);
    expect(integrated!.changes).toEqual([]);
    expect(integrated!.imports).toBeUndefined();
    expect(integrated!.references?.sourceCommit).toBe(integrationCommit);
    expect(integrated!.verification).toEqual(delivery!.verification);
    expect(trustedTaskProjectionReuse(integrated!)).toMatchObject({ checkedProjectionCommit: delivery!.verification.targetCommit });
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('rebuilds each caller attribution when equal-tree commits share a verification in flight', async () => {
    let release!: () => void, started!: () => void;
    const gate = new Promise<void>(resolve => { release = resolve; });
    const entered = new Promise<void>(resolve => { started = resolve; });
    host.verify.mockImplementationOnce(async input => { started(); await gate; return verified(input); });
    const first = check();
    await entered;
    const changedCommit = recommit();
    const second = check({ sourceCommit: changedCommit,
      requests: [{ ...requests[0]!, assignment: { ...requests[0]!.assignment, seedCommit: changedCommit } }] });
    release();
    const [[original], [current]] = await Promise.all([first, second]);
    expect(original!.commit).toBe(commit);
    expect(original!.seedCommit).toBe(seedCommit);
    expect(original!.changes.length).toBeGreaterThan(0);
    expect(current!.commit).toBe(changedCommit);
    expect(current!.seedCommit).toBe(changedCommit);
    expect(current!.changes).toEqual([]);
    expect(current!.references?.sourceCommit).toBe(changedCommit);
    expect(current!.verification).toEqual(original!.verification);
    expect(trustedTaskProjectionReuse(current!)).toBeDefined();
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('never treats a restored, cloned, forged or edited projection mapping as process-local authority', async () => {
    await check();
    const changedCommit = recommit();
    const [next] = await check({ sourceCommit: changedCommit });
    expect(trustedTaskProjectionReuse(next!)).toBeDefined();
    for (const copy of [JSON.parse(JSON.stringify(next)), structuredClone(next), { ...next! },
      { ...next!, projectionReuse: { ...next!.projectionReuse!, inputDigest: 'forged-input' } }])
      expect(trustedTaskProjectionReuse(copy)).toBeUndefined();
    const mutations: ((proof: TaskProof) => void)[] = [
      proof => { proof.commit = seedCommit; },
      proof => { proof.seedCommit = commit; },
      proof => { proof.sourceDigest = 'forged-source'; },
      proof => { proof.changes[0]!.after = 'forged-edit'; },
      proof => { proof.verification.results[0]!.receiptId = 'forged-receipt'; },
      proof => { proof.projectionReuse = { ...proof.projectionReuse!, projectionTree: 'forged-tree' }; },
      proof => { proof.references!.sourceCommit = seedCommit; },
      proof => { proof.projection = { environmentDigest: 'env', problemReceiptDigest: 'problem', sourceDigest: 'source' }; },
    ];
    for (const mutate of mutations) {
      const [proof] = await check({ sourceCommit: changedCommit });
      expect(trustedTaskProjectionReuse(proof!)).toBeDefined();
      mutate(proof!);
      expect(trustedTaskProjectionReuse(proof!)).toBeUndefined();
    }
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('keeps all committed metadata in the projected Git tree identity', async () => {
    await check();
    fs.writeFileSync(path.join(workspace, 'COOPERATION.json'), '{"revision":1}\n');
    git(workspace, ['add', '--force', '--', 'COOPERATION.json']);
    const changedCommit = recommit();
    await check({ sourceCommit: changedCommit });
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('isolates equal-tree artifacts between repositories and ordered target contracts', async () => {
    const both = tasks.map(task => request(task));
    await check({ requests: both });
    const [second, first] = await check({ requests: [...both].reverse() });
    expect(second!.taskDigest).toBe(taskVersion(tasks[1]!));
    expect(first!.taskDigest).toBe(taskVersion(tasks[0]!));
    expect(host.verify).toHaveBeenCalledTimes(2);
    const clone = path.join(directory, 'repository-clone');
    git(directory, ['clone', '--quiet', '--no-hardlinks', workspace, clone]);
    await checkTaskProofs(problem, clone, commit, both, env, signal, 180000, 'current-environment', cache);
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('checks source ownership before considering an existing equal-input cache entry', async () => {
    await check();
    const lookup = vi.spyOn(cache, 'check');
    fs.writeFileSync(path.join(workspace, 'outside-scope.txt'), 'not owned\n');
    git(workspace, ['add', '--', 'outside-scope.txt']);
    const changedCommit = recommit();
    await expect(check({ sourceCommit: changedCommit })).rejects.toThrow('math_source_outside_ownership');
    expect(lookup).not.toHaveBeenCalled();
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each(['task', 'retained-goals', 'problem', 'environment-digest', 'environment-settings', 'configuration', 'dependencies'] as const)
  ('rechecks changed %s inputs', async change => {
    await check();
    if (change === 'task') await check({ requests: [request({ ...tasks[0]!, objective: 'Prove the same type for a revised consumer.' })] });
    else if (change === 'retained-goals') await check({ requests: [request(tasks[0]!, [problem.targets[0]!.theoremName])] });
    else if (change === 'problem') await check({ problem: { ...problem, receiptDigest: 'changed-problem-receipt' } });
    else if (change === 'environment-digest') await check({ environmentDigest: 'changed-environment' });
    else if (change === 'environment-settings') await check({ env: { ...env, LEAN_NUM_THREADS: '2' } });
    else if (change === 'dependencies') await check({ requests: [{ ...requests[0]!, assignment: { ...requests[0]!.assignment,
      dependencies: [{ taskId: tasks[1]!.id, taskDigest: taskVersion(tasks[1]!) }] } }] });
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

  it('rechecks conditional permissions and dependency versions before a possible cache hit', async () => {
    const task = { ...tasks[0]!, conditional: true }, dependency = tasks[1]!;
    const input = { ...request(task), conditions: [dependency] };
    input.assignment.dependencies = [{ taskId: dependency.id, taskDigest: taskVersion(dependency) }];
    await check({ requests: [input] });
    const lookup = vi.spyOn(cache, 'check');
    await expect(check({ requests: [{ ...input, assignment: { ...input.assignment, dependencies: [] } }] }))
      .rejects.toThrow('math_task_condition_version_invalid');
    expect(lookup).not.toHaveBeenCalled();
    expect(host.verify).toHaveBeenCalledOnce();
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

  it.each(['changed', 'unavailable'] as const)('reports %s tools during verification as an infrastructure failure', async change => {
    host.verify.mockImplementationOnce(async input => {
      host.tools.mockReturnValue(change === 'changed' ? 'fixture-tools-drifted' : undefined);
      return verified(input);
    });
    await expect(check()).rejects.toThrow(/^math_verifier_unavailable$/u);
    expect((await check())[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('retains infrastructure recovery when tool drift also makes verification throw', async () => {
    host.verify.mockImplementationOnce(async () => {
      host.tools.mockReturnValue('fixture-tools-drifted');
      throw new Error('failed to execute changed tool');
    });
    await expect(check()).rejects.toThrow(/^math_verifier_unavailable$/u);
    expect((await check())[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it.each(['sealed-packages', 'environment-file', 'mutable-settings'] as const)
  ('reports drifting %s during verification as an infrastructure failure', async change => {
    const environment = change === 'mutable-settings' ? { ...env, LEAN_PATH: path.join(directory, 'mutable-library') } : env;
    host.verify.mockImplementationOnce(async input => {
      if (change === 'sealed-packages') host.environment.mockReturnValue({ identity: 'sealed-drifted' });
      else if (change === 'environment-file')
        fs.writeFileSync(env.DEEPSCIENTIST_MATH_ENV_FILE!, 'DEEPSCIENTIST_MATH_SANDBOX_IMAGE=drifted-image\n');
      else environment.LEAN_NUM_THREADS = '2';
      return verified(input);
    });
    await expect(check({ env: environment })).rejects.toThrow(/^math_verifier_unavailable$/u);
    expect((await check({ env: environment }))[0]!.passed).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('checks actual tool identity again after awaiting a cache hit', async () => {
    await check();
    host.tools.mockReturnValueOnce('fixture-tools-first').mockReturnValue('fixture-tools-drifted');
    await expect(check()).rejects.toThrow(/^math_verifier_unavailable$/u);
    expect(host.verify).toHaveBeenCalledOnce();
    await check();
    expect(host.verify).toHaveBeenCalledTimes(2);
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
    expect(proofViews(next)).toEqual(proofViews(first));
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it('preserves ordered success and deterministic rejection receipts when reusing a full batch', async () => {
    host.verify.mockImplementation(async input => {
      const batch = verified(input), result = batch.results[1]!;
      batch.status = 'failed';
      Object.assign(result, { status: 'failed', goalsRemaining: 1, error: 'Lean exited with status 1.',
        stdoutPreview: `${result.proofPath}:4:1: error: unsolved goals` });
      return batch;
    });
    const both = tasks.map(task => request(task));
    const first = await check({ requests: both });
    const current = await check({ requests: both, sourceCommit: recommit() });
    expect(current.map(proof => proof.passed)).toEqual([true, false]);
    expect(current.map(isAttributedTaskProof)).toEqual([true, true]);
    expect(current[0]!.references).toBeDefined();
    expect(current[1]!.references).toBeUndefined();
    expect(current.map(proof => proof.verification)).toEqual(first.map(proof => proof.verification));
    expect(current.map(trustedTaskProjectionReuse).every(Boolean)).toBe(true);
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

  it('does not let cancellation in one domain poison a completed independent verification', async () => {
    const controller = new AbortController();
    let release!: () => void, started!: () => void;
    const gate = new Promise<void>(resolve => { release = resolve; });
    const entered = new Promise<void>(resolve => { started = resolve; });
    host.verify.mockImplementationOnce(async input => { started(); await gate; return verified(input); });
    const interrupted = check({ signal: controller.signal });
    const rejectedCheck = expect(interrupted).rejects.toMatchObject({ name: 'AbortError' });
    await entered;
    const independent = await check();
    controller.abort(); release();
    await rejectedCheck;
    const next = await check();
    expect(next[0]!.verification).toEqual(independent[0]!.verification);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('preserves current request snapshots while a verifier is running', async () => {
    host.verify.mockImplementationOnce(async input => {
      requests[0]!.assignment.seedCommit = 'caller-mutated-seed';
      return verified(input);
    });
    const [proof] = await check();
    expect(proof!.seedCommit).toBe(seedCommit);
    expect(proof!.changes.length).toBeGreaterThan(0);
    expect(isAttributedTaskProof(proof!)).toBe(true);
  });

  it('does not accept or cache verifier receipts bound to an unexpected commit', async () => {
    host.verify.mockImplementationOnce(async input => verified({ ...input, targetCommit: commit }));
    const [proof] = await check();
    expect(proof!.passed).toBe(false);
    expect(proof!.projectionReuse).toBeUndefined();
    expect(isAttributedTaskProof(proof!)).toBe(false);
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
    const verification: MathematicsVerifierBatchResult = { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
      targetCommit: label, sessionId: 'fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1, results: [] };
    return { projectionCommit: label, verification };
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
    const valid = vi.fn().mockReturnValueOnce(false).mockReturnValue(true);
    await cache.check('A', signal(), valid, run);
    await cache.check('A', signal(), () => true, run);
    expect(run).toHaveBeenCalledTimes(2);
  });
});
