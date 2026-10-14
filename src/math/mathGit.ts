import { spawnSync } from 'node:child_process';

type GitOptions = { maxBuffer: number; timeout?: number; errorMessage?: string };

/** Keep source bytes intact; callers own Git identity and tree-mode checks. */
export const mathGitResult = (root: string, args: readonly string[], options: GitOptions) =>
  spawnSync('git', ['-C', root, ...args], {
    maxBuffer: options.maxBuffer, timeout: options.timeout ?? 30_000,
  });

export function mathGitBytes(root: string, args: readonly string[], options: GitOptions): Buffer {
  const result = mathGitResult(root, args, options);
  if (result.error || result.status !== 0) {
    throw new Error(options.errorMessage ?? (result.stderr?.toString('utf8').trim() || `git ${args.join(' ')} failed`));
  }
  return result.stdout;
}

export const mathGitText = (root: string, args: readonly string[], options: GitOptions): string =>
  mathGitBytes(root, args, options).toString('utf8').trim();
