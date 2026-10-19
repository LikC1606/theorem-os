import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { limitMathOutput, runMathProcess, type MathProcessResult } from './mathProcess';

export type VerifierCheckoutCleanupFailure = Readonly<{
  stage: 'worktree' | 'temporary';
  message: string;
}>;

type VerifierCheckoutOptions = Readonly<{
  repositoryRoot: string;
  targetCommit: string;
  temporaryPrefix: string;
  env?: NodeJS.ProcessEnv;
  signal?: AbortSignal;
  onCleanupFailure: (failure: VerifierCheckoutCleanupFailure) => void;
}>;

/** Own the detached checkout through creation, execution and uncancellable cleanup. */
export async function withVerifierCheckout<T>(
  options: VerifierCheckoutOptions,
  run: (checkout: Readonly<{ checkoutRoot: string; temporaryRoot: string }>) => Promise<T>
): Promise<{ ok: true; value: T } | { ok: false; result: MathProcessResult }> {
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), options.temporaryPrefix));
  const checkoutRoot = path.join(temporaryRoot, 'checkout');
  const git = (args: string[], signal?: AbortSignal) => runMathProcess('git', args, {
    cwd: options.repositoryRoot, timeoutMs: 10_000, env: options.env, signal,
  });
  let created = false;
  try {
    const added = await git(['worktree', 'add', '--detach', checkoutRoot, options.targetCommit], options.signal);
    if (added.exitCode !== 0) return { ok: false, result: added };
    created = true;
    return { ok: true, value: await run({ checkoutRoot, temporaryRoot }) };
  } finally {
    const failures: VerifierCheckoutCleanupFailure[] = [];
    const worktreeFailures: string[] = [];
    const cleanGit = async (operation: 'remove' | 'prune'): Promise<void> => {
      try {
        const result = await git(operation === 'remove'
          ? ['worktree', 'remove', '--force', checkoutRoot] : ['worktree', 'prune']);
        if (result.exitCode !== 0 && (operation === 'prune' || fs.existsSync(checkoutRoot))) {
          const detail = result.stderr.trim();
          worktreeFailures.push(`git worktree ${operation} failed: ${detail
            ? limitMathOutput(detail) : `exit ${result.exitCode ?? 'unknown'}`}`);
        }
      } catch (error) {
        worktreeFailures.push(`git worktree ${operation} failed: ${error instanceof Error ? error.message : String(error)}`);
      }
    };
    // Git can leave a partial checkout when creation fails or is cancelled.
    if (created || fs.existsSync(checkoutRoot)) await cleanGit('remove');
    await cleanGit('prune');
    if (worktreeFailures.length) failures.push({ stage: 'worktree', message: worktreeFailures.join('; ') });
    try {
      fs.rmSync(temporaryRoot, { recursive: true, force: true });
    } catch (error) {
      failures.push({ stage: 'temporary', message: error instanceof Error ? error.message : String(error) });
    }
    for (const failure of failures) options.onCleanupFailure(failure);
  }
}
