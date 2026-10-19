import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import * as processes from '../src/math/mathProcess';
import { withVerifierCheckout } from '../src/math/verifierCheckout';

const git = (root: string, ...args: string[]) => {
  const result = spawnSync('git', ['-C', root, ...args], { encoding: 'utf8', timeout: 5000 });
  if (result.status !== 0) throw result.error ?? new Error(result.stderr);
  return result.stdout.trim();
};

const failedProcess = (message: string): processes.MathProcessResult => ({
  started: true, exitCode: 1, signal: null, stdout: '', stderr: message,
  stdoutSha256: '', stderrSha256: '', timedOut: false, aborted: false, durationMs: 0,
});

describe('verifier checkout ownership', () => {
  let root: string;
  let commit: string;
  let before: string;
  let temporary: ReturnType<typeof vi.spyOn<typeof fs, 'mkdtempSync'>>;
  beforeEach(() => {
    root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'verifier-checkout-test-')));
    fs.writeFileSync(path.join(root, 'Proof.lean'), 'theorem result : True := by trivial\n');
    git(root, 'init', '--quiet');
    git(root, 'add', '.');
    git(root, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '-m', 'baseline');
    commit = git(root, 'rev-parse', 'HEAD');
    before = git(root, 'worktree', 'list', '--porcelain');
    temporary = vi.spyOn(fs, 'mkdtempSync');
  });
  afterEach(() => {
    const directories = temporary.mock.results.filter(result => result.type === 'return').map(result => String(result.value));
    vi.restoreAllMocks();
    for (const directory of [...directories, root]) fs.rmSync(directory, { recursive: true, force: true });
  });
  const options = () => ({ repositoryRoot: root, targetCommit: commit,
    temporaryPrefix: 'verifier-checkout-owned-', onCleanupFailure: vi.fn() });
  const expectClean = () => {
    expect(git(root, 'worktree', 'list', '--porcelain')).toBe(before);
    expect(temporary.mock.results.every(result => result.type !== 'return' || !fs.existsSync(String(result.value)))).toBe(true);
  };

  it.each(['return', 'throw', 'cancel'] as const)('cleans the detached commit after the operation %s', async mode => {
    const controller = new AbortController();
    const process = vi.spyOn(processes, 'runMathProcess');
    const run = () => withVerifierCheckout({ ...options(), signal: controller.signal }, async ({ checkoutRoot }) => {
      expect(git(checkoutRoot, 'rev-parse', 'HEAD')).toBe(commit);
      expect(fs.readFileSync(path.join(checkoutRoot, 'Proof.lean'), 'utf8')).toContain('theorem result');
      if (mode === 'cancel') controller.abort();
      if (mode !== 'return') throw new Error(`fixture_${mode}`);
      return 'checked';
    });
    if (mode === 'return') await expect(run()).resolves.toEqual({ ok: true, value: 'checked' });
    else await expect(run()).rejects.toThrow(`fixture_${mode}`);
    const cleanup = process.mock.calls.filter(([, args]) => args[0] === 'worktree' && args[1] !== 'add');
    expect(cleanup.map(([, args]) => args[1])).toEqual(['remove', 'prune']);
    expect(cleanup.every(([, , input]) => input.signal === undefined)).toBe(true);
    expectClean();
  });

  it('returns a failed Git creation without running the operation or leaving a temporary directory', async () => {
    const run = vi.fn();
    const result = await withVerifierCheckout({ ...options(), targetCommit: 'f'.repeat(40) }, run);
    expect(result.ok).toBe(false);
    expect(run).not.toHaveBeenCalled();
    expectClean();
  });

  it.each(['before', 'after', 'cancel', 'nonzero'] as const)('cleans an interrupted worktree creation: %s', async mode => {
    const run = vi.fn();
    const controller = new AbortController();
    const execute = processes.runMathProcess;
    vi.spyOn(processes, 'runMathProcess').mockImplementation(async (command, args, input) => {
      if (args[0] !== 'worktree' || args[1] !== 'add') return execute(command, args, input);
      if (mode !== 'before') expect((await execute(command, args, input)).exitCode).toBe(0);
      if (mode === 'nonzero') return failedProcess('fixture_partial_checkout');
      if (mode === 'cancel') controller.abort();
      throw new Error(`fixture_add_${mode}`);
    });
    const start = () => withVerifierCheckout({ ...options(), signal: controller.signal }, run);
    if (mode === 'nonzero') await expect(start()).resolves.toMatchObject({ ok: false });
    else await expect(start()).rejects.toThrow(`fixture_add_${mode}`);
    expect(run).not.toHaveBeenCalled();
    expectClean();
  });

  it.each(['remove', 'prune', 'both', 'temporary'] as const)('reports cleanup failure without replacing the operation error: %s', async stage => {
    const input = options();
    const execute = processes.runMathProcess;
    vi.spyOn(processes, 'runMathProcess').mockImplementation((command, args, settings) => {
      if (args[0] === 'worktree' && (stage === args[1] || stage === 'both' && args[1] !== 'add'))
        return Promise.resolve(failedProcess(`fixture_${args[1]}`));
      return execute(command, args, settings);
    });
    const remove = fs.rmSync;
    vi.spyOn(fs, 'rmSync').mockImplementation((file, settings) => {
      if (stage === 'temporary' && String(file).includes('verifier-checkout-owned-')) throw new Error('fixture_remove_directory');
      return remove(file, settings);
    });
    await expect(withVerifierCheckout(input, async () => { throw new Error('fixture_operation_error'); }))
      .rejects.toThrow('fixture_operation_error');
    expect(input.onCleanupFailure).toHaveBeenCalledOnce();
    expect(input.onCleanupFailure).toHaveBeenCalledWith(stage === 'temporary'
      ? { stage: 'temporary', message: 'fixture_remove_directory' }
      : { stage: 'worktree', message: stage === 'both'
          ? 'git worktree remove failed: fixture_remove; git worktree prune failed: fixture_prune'
          : `git worktree ${stage} failed: fixture_${stage}` });
    if (stage !== 'temporary') expect(temporary.mock.results.every(result =>
      result.type !== 'return' || !fs.existsSync(String(result.value)))).toBe(true);
  });
});
