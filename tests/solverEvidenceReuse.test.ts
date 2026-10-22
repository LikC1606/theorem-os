import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { checkSolverProof, type ProofCheck } from '../src/solver/modules/evidence';
import { git, type SolverProblem } from '../src/solver/problem';
import { localExample } from './helpers/solver';
import { failedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), environment: vi.fn() }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(), checkManyFormalVerifications: host.verify,
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(), resolveMathProofEnvironment: host.environment,
}));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'fixture', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `receipt-${request.targetCommit}-${item.theoremName}`, checkedAt: 2,
      targetCommit: request.targetCommit, status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

const rejected = (request: MathematicsVerifierBatchRequest) =>
  failedBatch(verified(request), { stdoutPreview: proofPath => `${proofPath}:4:1: error: unsolved goals` });

describe('process-local deterministic Lean rejection reuse', () => {
  let directory: string, workspace: string, project: string, problem: SolverProblem, env: NodeJS.ProcessEnv;
  const check = (previous?: ProofCheck, environment = env, task = problem) =>
    checkSolverProof(task, workspace, environment, undefined, previous);
  const writeNotes = () => fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Another research direction\n');

  beforeEach(() => {
    host.verify.mockReset().mockImplementation(async request => rejected(request));
    host.environment.mockReset().mockReturnValue(undefined);
    const example = localExample('solver-evidence-reuse-');
    ({ directory, workspace, problem } = example);
    project = example.receipt.projectRoot;
    env = { DEEPSCIENTIST_MATH_ENV_FILE: path.join(directory, 'math.env'), PATH: '/usr/bin:/bin' };
  });
  afterEach(() => { vi.restoreAllMocks(); fs.rmSync(directory, { recursive: true, force: true }); });

  it('preserves original receipts across a notes-only commit and bypasses reuse without a previous check', async () => {
    const first = await check();
    writeNotes();
    const next = await check(first);
    expect(next.commit).toBe(git(workspace, ['rev-parse', 'HEAD']));
    expect(next.commit).not.toBe(first.commit);
    expect(next.sourceDigest).toBe(first.sourceDigest);
    expect(next.verification).toBe(first.verification);
    expect(next.verification.targetCommit).toBe(first.commit);
    expect(next.verification.checkedAt).toBe(2);
    expect(next.verification.results[0]).toBe(first.verification.results[0]);
    expect(await check(next)).toBe(next);
    expect(host.verify).toHaveBeenCalledOnce();
    const fresh = await check();
    expect(fresh.verification.targetCommit).toBe(next.commit);
    expect(fresh.verification).not.toBe(first.verification);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('rechecks changed proof bytes', async () => {
    const first = await check();
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('by sorry', 'by rfl'));
    const next = await check(first);
    expect(next.sourceDigest).not.toBe(first.sourceDigest);
    expect(next.verification.targetCommit).toBe(next.commit);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('reuses a normal Lean rejection whose goal contains an interruption keyword', async () => {
    host.verify.mockImplementation(async request => {
      const batch = rejected(request);
      for (const result of batch.results) result.stdoutPreview =
        'Submission.lean:4:1: error: unsolved goals\ndeadline : Nat\n⊢ deadline = 0';
      return batch;
    });
    const first = await check();
    expect(await check(first)).toBe(first);
    expect(host.verify).toHaveBeenCalledOnce();
  });

  it.each(['receipt', 'targets', 'statement'] as const)('rechecks a changed %s identity', async change => {
    const first = await check();
    const changed = change === 'receipt' ? { ...problem, receiptDigest: 'new-problem' } :
      change === 'targets' ? { ...problem, targets: [...problem.targets].reverse() } :
        { ...problem, contract: { ...problem.contract, statementHash: 'new-statement' } };
    await check(first, env, changed);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it.each(['restored', 'forged', 'mutated-receipt'] as const)('rejects %s rejection provenance', async change => {
    const first = await check();
    if (change === 'mutated-receipt') first.verification.results[0]!.receiptId = 'changed-receipt';
    const previous = change === 'restored' ? JSON.parse(JSON.stringify(first)) : change === 'forged' ? { ...first } : first;
    expect((await check(previous)).verification).not.toBe(previous.verification);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('rechecks changed resolved environment settings and environment file contents', async () => {
    let previous = await check();
    previous = await check(previous, { ...env, LEAN_NUM_THREADS: '2' });
    expect(host.verify).toHaveBeenCalledTimes(2);
    fs.writeFileSync(env.DEEPSCIENTIST_MATH_ENV_FILE!, 'DEEPSCIENTIST_MATH_SANDBOX_IMAGE=fixture-image\n');
    await check(previous, { ...env, LEAN_NUM_THREADS: '2' });
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it.each(['LEAN_PATH', 'LEAN_SYSROOT', 'DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS'] as const)
    ('does not reuse unsealed external inputs from %s', async key => {
      const environment = { ...env, [key]: path.join(directory, 'mutable-input') };
      const first = await check(undefined, environment);
      await check(first, environment);
      expect(host.verify).toHaveBeenCalledTimes(2);
    });

  it('does not reuse mutable libraries at an unchanged package path', async () => {
    const packages = path.join(project, '.lake', 'packages');
    fs.mkdirSync(packages, { recursive: true });
    const file = path.join(packages, 'Library.lean');
    fs.writeFileSync(file, '-- first library\n');
    const first = await check();
    fs.writeFileSync(file, '-- changed library\n');
    await check(first);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('binds reusable package inputs to their current sealed identity', async () => {
    fs.mkdirSync(path.join(project, '.lake', 'packages'), { recursive: true });
    host.environment.mockReturnValue({ identity: 'sealed-first' });
    const first = await check();
    expect(await check(first)).toBe(first);
    host.environment.mockReturnValue({ identity: 'sealed-changed' });
    await check(first);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('rechecks changes to ignored package configuration', async () => {
    fs.mkdirSync(path.join(project, '.lake'), { recursive: true });
    const file = path.join(project, '.lake', 'package-overrides.json');
    fs.writeFileSync(file, '{"packages":[]}\n');
    const first = await check();
    fs.writeFileSync(file, '{"packages":[],"changed":true}\n');
    await check(first);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it.each(['blocked', 'unavailable', 'cleanup', 'timeout', 'aborted', 'crashed', 'no-diagnostic', 'wrong-commit'] as const)
    ('rechecks a failed batch containing %s evidence', async kind => {
      host.verify.mockImplementation(async request => {
        const batch = rejected(request), other = batch.results[1]!;
        if (kind === 'blocked' || kind === 'unavailable') other.status = kind;
        else if (kind === 'cleanup') other.cleanupError = 'checkout cleanup failed';
        else if (kind === 'timeout') other.error = 'Lean verification timed out.';
        else if (kind === 'aborted') other.error = 'Formal verification was aborted.';
        else if (kind === 'crashed') other.error = 'Lean exited with status 137.';
        else if (kind === 'wrong-commit') other.targetCommit = 'unrelated-commit';
        else other.stdoutPreview = 'Process exited without Lean diagnostics';
        return batch;
      });
      const first = await check();
      await check(first);
      expect(host.verify).toHaveBeenCalledTimes(2);
    });
});
