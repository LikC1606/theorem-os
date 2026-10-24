import fs from 'node:fs';
import path from 'node:path';
import { mathDigest } from '../math/mathRuntimeIo';
import { assertMathCanonicalPath } from '../math/paths';
import type { SolverRunState } from './archive';
import { MAX_RESEARCH_NOTES_BYTES } from './deliveries';

type CheckpointResearch = Pick<SolverRunState, 'threadId' | 'contextCheckpoint'>;
const digestPattern = /^[a-f0-9]{64}$/u;

export function readCheckpointNotesDigest(worktree: string): string | undefined {
  const file = path.join(worktree, 'RESEARCH.md');
  let fd: number | undefined;
  try {
    assertMathCanonicalPath(file);
    fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
    const stat = fs.fstatSync(fd);
    if (!stat.isFile() || stat.nlink !== 1 || stat.size > MAX_RESEARCH_NOTES_BYTES) return undefined;
    const text = fs.readFileSync(fd, 'utf8');
    return text.trim() ? mathDigest(text) : undefined;
  } catch { return undefined; } finally { if (fd !== undefined) fs.closeSync(fd); }
}

/** A fresh publication hands back writing; unchanged accurate notes are sufficient. */
export function savedContextCheckpoint(research: CheckpointResearch, worktree: string): string | undefined {
  const request = research.contextCheckpoint;
  if (!research.threadId || request?.threadId !== research.threadId || !request.requestId ||
      !request.publishedNotesDigest || !digestPattern.test(request.publishedNotesDigest)) return undefined;
  return readCheckpointNotesDigest(worktree) === request.publishedNotesDigest ? request.publishedNotesDigest : undefined;
}

/** Scheduling acknowledgment only: this neither publishes mathematics nor accepts a proof. */
export function acceptContextCheckpoint(research: CheckpointResearch, worktree: string, value: unknown): void {
  const request = research.contextCheckpoint;
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_delivery_invalid');
  const event = value as Record<string, unknown>;
  if (event.kind !== 'checkpoint' || !research.threadId || request?.threadId !== research.threadId ||
      !request.requestId || event.requestId !== request.requestId || typeof event.notesDigest !== 'string' ||
      !digestPattern.test(event.notesDigest) || readCheckpointNotesDigest(worktree) !== event.notesDigest)
    throw new Error('math_delivery_invalid');
  request.publishedNotesDigest = event.notesDigest;
  request.publishedAt = Date.now();
}
