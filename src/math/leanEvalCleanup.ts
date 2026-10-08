/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';

export type LeanEvalCleanupResult = Readonly<{
  removed: readonly string[];
  preserved: readonly string[];
  prunedWorktrees: boolean;
}>;

const CLEANUP_THROTTLE_MS = 5_000;
type CleanupThrottleEntry = Readonly<{ checkedAt: number; result: LeanEvalCleanupResult }>;
const cleanupThrottle = new Map<string, CleanupThrottleEntry>();

const TEMP_PREFIXES = [
  'deepscientist-lean-eval-',
  'deepscientist-lean-eval-source-',
  'deepscientist-lean-sandbox-',
  'deepscientist-lean-elab-',
];
const TEAM_WORKSPACE_INDEX = path.join('.deepscientist', 'math', 'lean-eval-team');

const isWithin = (parent: string, candidate: string): boolean => {
  const relative = path.relative(path.resolve(parent), path.resolve(candidate));
  return relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative));
};

/** Reap only runtime-owned, expired Lean-Eval artifacts. */
export function reapLeanEvalArtifacts(
  options: {
    repositoryRoot?: string;
    projectRoots?: readonly string[];
    tempRoot?: string;
    maxAgeMs?: number;
    now?: number;
    /** Run cleanup even when the same scope was checked recently. */
    force?: boolean;
  } = {}
): LeanEvalCleanupResult {
  const root = path.resolve(options.tempRoot || os.tmpdir());
  const maxAgeMs = Math.max(60_000, options.maxAgeMs ?? 24 * 60 * 60 * 1000);
  const now = options.now ?? Date.now();
  const hasCustomTiming = options.now !== undefined || options.maxAgeMs !== undefined;
  const shouldCache = !hasCustomTiming;
  const shouldThrottle = shouldCache && !options.force;
  const scopeKey = [
    options.repositoryRoot ? path.resolve(options.repositoryRoot) : '',
    root,
    ...[...(options.projectRoots ?? [])].map((projectRoot) => path.resolve(projectRoot)).toSorted(),
  ].join('\0');
  if (shouldThrottle) {
    const previous = cleanupThrottle.get(scopeKey);
    if (previous && now >= previous.checkedAt && now - previous.checkedAt < CLEANUP_THROTTLE_MS) {
      return previous.result;
    }
  }
  const finish = (result: LeanEvalCleanupResult): LeanEvalCleanupResult => {
    if (shouldCache) {
      cleanupThrottle.set(scopeKey, Object.freeze({ checkedAt: now, result }));
      for (const [key, entry] of cleanupThrottle) {
        if (now >= entry.checkedAt && now - entry.checkedAt >= CLEANUP_THROTTLE_MS * 4) {
          cleanupThrottle.delete(key);
        }
      }
    }
    return result;
  };
  const removed: string[] = [];
  const preserved: string[] = [];
  let entries: string[] = [];
  try {
    entries = fs.readdirSync(root);
  } catch {
    return finish(Object.freeze({ removed: [], preserved: [], prunedWorktrees: false }));
  }
  for (const entry of entries) {
    if (!TEMP_PREFIXES.some((prefix) => entry.startsWith(prefix))) continue;
    const absolute = path.join(root, entry);
    try {
      const stat = fs.lstatSync(absolute);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        preserved.push(absolute);
        continue;
      }
      if (now - stat.mtimeMs < maxAgeMs) {
        preserved.push(absolute);
        continue;
      }
      fs.rmSync(absolute, { recursive: true, force: true });
      removed.push(absolute);
    } catch {
      preserved.push(absolute);
    }
  }
  for (const projectRoot of options.projectRoots ?? []) {
    const checkpointRoot = path.join(path.resolve(projectRoot), '.deepscientist', 'math', 'lean-eval-proof');
    let checkpoints: string[] = [];
    try {
      checkpoints = fs.readdirSync(checkpointRoot);
    } catch {
      continue;
    }
    for (const checkpoint of checkpoints) {
      if (!checkpoint.endsWith('.json')) continue;
      const absolute = path.join(checkpointRoot, checkpoint);
      try {
        const stat = fs.lstatSync(absolute);
        if (!stat.isFile() || stat.isSymbolicLink()) {
          preserved.push(absolute);
          continue;
        }
        if (now - stat.mtimeMs < maxAgeMs) {
          preserved.push(absolute);
          continue;
        }
        fs.rmSync(absolute, { force: true });
        removed.push(absolute);
      } catch {
        preserved.push(absolute);
      }
    }
    const teamIndexRoot = path.join(path.resolve(projectRoot), TEAM_WORKSPACE_INDEX);
    let teamIndexes: string[] = [];
    try {
      teamIndexes = fs.readdirSync(teamIndexRoot);
    } catch {
      teamIndexes = [];
    }
    for (const entry of teamIndexes) {
      if (!entry.endsWith('.json')) continue;
      const indexPath = path.join(teamIndexRoot, entry);
      try {
        const stat = fs.lstatSync(indexPath);
        if (stat.isSymbolicLink() || !stat.isFile()) {
          preserved.push(indexPath);
          continue;
        }
        const value = JSON.parse(fs.readFileSync(indexPath, 'utf8')) as Record<string, unknown>;
        const workspace = typeof value.workspace === 'string' ? value.workspace : undefined;
        const repositoryRoot = typeof value.repositoryRoot === 'string' ? value.repositoryRoot : undefined;
        const integrated = value.integrated === true;
        if (!integrated || now - stat.mtimeMs < maxAgeMs) {
          preserved.push(indexPath);
          continue;
        }
        if (
          !workspace ||
          !path.isAbsolute(workspace) ||
          !isWithin(os.tmpdir(), workspace) ||
          (repositoryRoot && !path.isAbsolute(repositoryRoot))
        ) {
          preserved.push(indexPath);
          continue;
        }
        if (repositoryRoot) {
          for (const worktree of [value.verifierProjectRoot, value.sourceProjectRoot]) {
            if (
              typeof worktree !== 'string' ||
              !path.isAbsolute(worktree) ||
              !isWithin(os.tmpdir(), worktree) ||
              !fs.existsSync(worktree)
            )
              continue;
            spawnSync('git', ['-C', repositoryRoot, 'worktree', 'remove', '--force', worktree], {
              encoding: 'utf8',
            });
          }
          spawnSync('git', ['-C', repositoryRoot, 'worktree', 'prune'], { encoding: 'utf8' });
        }
        fs.rmSync(workspace, { recursive: true, force: true });
        fs.rmSync(indexPath, { force: true });
        removed.push(indexPath);
      } catch {
        preserved.push(indexPath);
      }
    }
  }
  let prunedWorktrees = false;
  if (options.repositoryRoot) {
    const result = spawnSync('git', ['-C', path.resolve(options.repositoryRoot), 'worktree', 'prune'], {
      encoding: 'utf8',
    });
    prunedWorktrees = result.status === 0;
  }
  return finish(
    Object.freeze({ removed: Object.freeze(removed), preserved: Object.freeze(preserved), prunedWorktrees })
  );
}
