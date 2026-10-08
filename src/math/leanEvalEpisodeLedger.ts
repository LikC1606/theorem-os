/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";

export const LEAN_EVAL_EPISODE_LEDGER_PATH = '.deepscientist/math/lean-eval-episodes.jsonl' as const;
const MAX_LEDGER_BYTES = 32 * 1024 * 1024;
const MAX_LEDGER_RECORDS = 100_000;

export type LeanEvalEpisodeEventKind = 'episode_created' | 'episode_resumed' | 'episode_completed' | 'episode_failed';
export const LEAN_EVAL_PROGRESS_CLASSES = [
  'goal_progress',
  'frontier_progress',
  'scaffold_progress',
  'stalled',
  'infra_failed',
] as const;
export type LeanEvalProgressClass = (typeof LEAN_EVAL_PROGRESS_CLASSES)[number];

export type LeanEvalEpisodeEvent = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-episode.v1';
  eventId: string;
  episodeId: string;
  assignmentId: string;
  problemId: string;
  runIdentity?: string;
  statementHash: string;
  kind: LeanEvalEpisodeEventKind;
  recordedAt: number;
  elapsedMs?: number;
  modelMs?: number;
  leanMs?: number;
  orchestrationMs?: number;
  compileAttempts?: number;
  stateTransitions?: number;
  /** Runtime-derived progress class; absent on legacy records. */
  progressClass?: LeanEvalProgressClass;
  scaffoldOnlyStreak?: number;
  goalProgressCount?: number;
  frontierProgressCount?: number;
  progressFingerprint?: string;
  failureCategory?: string;
  previousHash?: string;
  recordHash?: string;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

const hashPayload = (record: LeanEvalEpisodeEvent): string =>
  JSON.stringify(
    Object.fromEntries(
      Object.entries(record)
        .filter(([key]) => key !== 'recordHash')
        .toSorted(([left], [right]) => left.localeCompare(right))
    )
  );

const effectiveHash = (record: LeanEvalEpisodeEvent): string => record.recordHash ?? sha256(hashPayload(record));

const ledgerFile = (projectRoot: string, create: boolean): string => {
  const root = path.resolve(projectRoot);
  const rootStat = fs.lstatSync(root);
  if (rootStat.isSymbolicLink() || !rootStat.isDirectory()) {
    throw new Error('Lean-Eval episode ledger project root is not a regular directory');
  }
  let cursor = root;
  for (const segment of ['.deepscientist', 'math']) {
    cursor = path.join(cursor, segment);
    if (!fs.existsSync(cursor)) {
      if (!create) return path.join(root, LEAN_EVAL_EPISODE_LEDGER_PATH);
      fs.mkdirSync(cursor, { mode: 0o700 });
      continue;
    }
    const stat = fs.lstatSync(cursor);
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new Error('Lean-Eval episode ledger directory is not a regular directory');
    }
  }
  const file = path.join(root, LEAN_EVAL_EPISODE_LEDGER_PATH);
  if (fs.existsSync(file)) {
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval episode ledger is not a regular file');
    if (stat.size > MAX_LEDGER_BYTES) throw new Error('Lean-Eval episode ledger exceeds its size limit');
  }
  return file;
};

const normalize = (value: unknown): LeanEvalEpisodeEvent | undefined => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const item = value as Record<string, unknown>;
  if (
    item.schema !== 'deepscientist.mathematics.lean-eval-episode.v1' ||
    typeof item.eventId !== 'string' ||
    typeof item.episodeId !== 'string' ||
    typeof item.assignmentId !== 'string' ||
    typeof item.problemId !== 'string' ||
    typeof item.statementHash !== 'string' ||
    !['episode_created', 'episode_resumed', 'episode_completed', 'episode_failed'].includes(String(item.kind)) ||
    !Number.isFinite(item.recordedAt) ||
    Number(item.recordedAt) <= 0
  )
    return undefined;
  for (const field of ['elapsedMs', 'modelMs', 'leanMs', 'orchestrationMs', 'compileAttempts', 'stateTransitions']) {
    if (
      item[field] !== undefined &&
      (typeof item[field] !== 'number' || !Number.isFinite(item[field]) || item[field] < 0)
    ) {
      return undefined;
    }
  }
  if (
    item.progressClass !== undefined &&
    !LEAN_EVAL_PROGRESS_CLASSES.includes(String(item.progressClass) as LeanEvalProgressClass)
  ) {
    return undefined;
  }
  for (const field of ['scaffoldOnlyStreak', 'goalProgressCount', 'frontierProgressCount']) {
    if (item[field] !== undefined && (!Number.isSafeInteger(item[field]) || Number(item[field]) < 0)) return undefined;
  }
  for (const field of ['previousHash', 'recordHash', 'runIdentity']) {
    if (item[field] !== undefined && (typeof item[field] !== 'string' || !/^[a-f0-9]{64}$/u.test(item[field]))) {
      return undefined;
    }
  }
  return Object.freeze(item as unknown as LeanEvalEpisodeEvent);
};

export function readLeanEvalEpisodeEvents(projectRoot: string): readonly LeanEvalEpisodeEvent[] {
  const file = ledgerFile(projectRoot, false);
  if (!fs.existsSync(file)) return Object.freeze([]);
  const lines = fs.readFileSync(file, 'utf8').split(/\r?\n/u);
  if (lines.length > MAX_LEDGER_RECORDS + 1) throw new Error('Lean-Eval episode ledger exceeds its record limit');
  const events: LeanEvalEpisodeEvent[] = [];
  let previousHash: string | undefined;
  for (const [index, line] of lines.entries()) {
    if (!line.trim()) continue;
    let value: unknown;
    try {
      value = JSON.parse(line);
    } catch (error) {
      throw new Error(`Lean-Eval episode ledger is corrupt at line ${index + 1}`, { cause: error });
    }
    const event = normalize(value);
    if (!event) throw new Error(`Lean-Eval episode ledger contains an invalid record at line ${index + 1}`);
    if (event.recordHash !== undefined) {
      if (event.previousHash !== previousHash || event.recordHash !== sha256(hashPayload(event))) {
        throw new Error(`Lean-Eval episode ledger hash chain mismatch at line ${index + 1}`);
      }
    }
    events.push(event);
    previousHash = effectiveHash(event);
  }
  return Object.freeze(events);
}

export function appendLeanEvalEpisodeEvent(
  projectRoot: string,
  input: Omit<LeanEvalEpisodeEvent, 'schema' | 'eventId' | 'recordedAt' | 'previousHash' | 'recordHash'> & {
    recordedAt?: number;
  }
): LeanEvalEpisodeEvent {
  const base = Object.freeze({
    ...input,
    schema: 'deepscientist.mathematics.lean-eval-episode.v1' as const,
    eventId: `episode-event-${sha256(JSON.stringify(input)).slice(0, 32)}`,
    recordedAt: input.recordedAt ?? Date.now(),
  });
  const file = ledgerFile(projectRoot, true);
  const lockPath = `${file}.lock`;
  const lockToken = `${process.pid}-${crypto.randomUUID()}`;
  const waitBuffer = new Int32Array(new SharedArrayBuffer(4));
  const deadline = Date.now() + 5_000;
  let lockDescriptor: number | undefined;
  try {
    for (;;) {
      try {
        lockDescriptor = fs.openSync(lockPath, 'wx', 0o600);
        fs.writeFileSync(lockDescriptor, `${JSON.stringify({ ...lockOwnerRecord(), token: lockToken })}\n`, 'utf8');
        break;
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'EEXIST' || Date.now() >= deadline) throw error;
        try {
          const lockStat = fs.statSync(lockPath);
          const lockValue: unknown = JSON.parse(fs.readFileSync(lockPath, 'utf8'));
          if (Date.now() - lockStat.mtimeMs > 30_000 && lockOwnerState(lockValue) !== 'alive') {
            fs.rmSync(lockPath, { force: true });
            continue;
          }
        } catch {
          // A concurrent writer may be replacing the lock file.
        }
        Atomics.wait(waitBuffer, 0, 0, 10);
      }
    }
    const existing = readLeanEvalEpisodeEvents(projectRoot);
    const duplicate = existing.find((event) => event.eventId === base.eventId);
    if (duplicate) return duplicate;
    if (existing.length >= MAX_LEDGER_RECORDS) throw new Error('Lean-Eval episode ledger exceeds its record limit');
    const previousHash = existing.length ? effectiveHash(existing.at(-1)!) : undefined;
    const event = Object.freeze({
      ...base,
      ...(previousHash ? { previousHash } : {}),
      recordHash: sha256(hashPayload({ ...base, ...(previousHash ? { previousHash } : {}) })),
    });
    const line = `${JSON.stringify(event)}\n`;
    const currentSize = fs.existsSync(file) ? fs.statSync(file).size : 0;
    if (currentSize + Buffer.byteLength(line, 'utf8') > MAX_LEDGER_BYTES) {
      throw new Error('Lean-Eval episode ledger exceeds its size limit');
    }
    const descriptor = fs.openSync(file, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_APPEND, 0o600);
    try {
      fs.writeFileSync(descriptor, line, 'utf8');
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    return event;
  } finally {
    if (lockDescriptor !== undefined) {
      fs.closeSync(lockDescriptor);
      try {
        const lockValue = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as { token?: unknown };
        if (lockValue.token === lockToken) fs.rmSync(lockPath, { force: true });
      } catch {
        // A crashed writer leaves a stale lock that a later writer can reap.
      }
    }
  }
}
