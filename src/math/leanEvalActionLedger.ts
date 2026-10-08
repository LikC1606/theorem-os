/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";

export const LEAN_EVAL_ACTION_LEDGER_PATH = '.deepscientist/math/lean-eval-actions.jsonl' as const;
const MAX_LEDGER_BYTES = 32 * 1024 * 1024;
const MAX_LEDGER_RECORDS = 200_000;

export type LeanEvalActionOutcome = 'advanced' | 'unchanged' | 'failed' | 'unavailable' | 'invalid' | 'duplicate';

export type LeanEvalActionRecord = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-action.v1';
  eventId: string;
  episodeId: string;
  problemId: string;
  runIdentity?: string;
  goalFingerprint: string;
  goalShape: string;
  failureCategory?: string;
  tactic: string;
  actionKind: string;
  outcome: LeanEvalActionOutcome;
  openGoalsBefore: number;
  openGoalsAfter: number;
  firstErrorImproved: boolean;
  leanMs: number;
  recordedAt: number;
  previousHash?: string;
  recordHash?: string;
}>;

export type LeanEvalActionBucket = Readonly<{
  attempts: number;
  advances: number;
  failures: number;
  goalReductions: number;
  errorImprovements: number;
  leanMs: number;
}>;

export type LeanEvalActionPerformanceSummary = Readonly<{
  byContext: Readonly<Record<string, LeanEvalActionBucket>>;
  byTactic: Readonly<Record<string, LeanEvalActionBucket>>;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

const hashPayload = (record: LeanEvalActionRecord): string =>
  JSON.stringify(
    Object.fromEntries(
      Object.entries(record)
        .filter(([key]) => key !== 'recordHash')
        .toSorted(([left], [right]) => left.localeCompare(right))
    )
  );

const effectiveHash = (record: LeanEvalActionRecord): string => record.recordHash ?? sha256(hashPayload(record));

const ledgerFile = (projectRoot: string, create: boolean): string => {
  const root = path.resolve(projectRoot);
  const rootStat = fs.lstatSync(root);
  if (rootStat.isSymbolicLink() || !rootStat.isDirectory()) throw new Error('Action ledger root is not a directory');
  let cursor = root;
  for (const segment of ['.deepscientist', 'math']) {
    cursor = path.join(cursor, segment);
    if (!fs.existsSync(cursor)) {
      if (!create) return path.join(root, LEAN_EVAL_ACTION_LEDGER_PATH);
      fs.mkdirSync(cursor, { mode: 0o700 });
    }
    const stat = fs.lstatSync(cursor);
    if (stat.isSymbolicLink() || !stat.isDirectory()) throw new Error('Action ledger directory is invalid');
  }
  const file = path.join(root, LEAN_EVAL_ACTION_LEDGER_PATH);
  if (fs.existsSync(file)) {
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Action ledger is not a regular file');
    if (stat.size > MAX_LEDGER_BYTES) throw new Error('Action ledger exceeds its size limit');
  }
  return file;
};

const normalize = (value: unknown): LeanEvalActionRecord | undefined => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const item = value as Record<string, unknown>;
  if (
    item.schema !== 'deepscientist.mathematics.lean-eval-action.v1' ||
    typeof item.eventId !== 'string' ||
    typeof item.episodeId !== 'string' ||
    typeof item.problemId !== 'string' ||
    typeof item.goalFingerprint !== 'string' ||
    typeof item.goalShape !== 'string' ||
    typeof item.tactic !== 'string' ||
    typeof item.actionKind !== 'string' ||
    !['advanced', 'unchanged', 'failed', 'unavailable', 'invalid', 'duplicate'].includes(String(item.outcome)) ||
    typeof item.firstErrorImproved !== 'boolean' ||
    !Number.isFinite(item.recordedAt) ||
    !Number.isFinite(item.openGoalsBefore) ||
    !Number.isFinite(item.openGoalsAfter) ||
    !Number.isFinite(item.leanMs) ||
    Number(item.openGoalsBefore) < 0 ||
    Number(item.openGoalsAfter) < 0 ||
    Number(item.leanMs) < 0
  )
    return undefined;
  for (const field of ['previousHash', 'recordHash', 'runIdentity']) {
    if (item[field] !== undefined && (typeof item[field] !== 'string' || !/^[a-f0-9]{64}$/u.test(item[field]))) {
      return undefined;
    }
  }
  return Object.freeze(item as unknown as LeanEvalActionRecord);
};

export function readLeanEvalActionLedger(projectRoot: string): readonly LeanEvalActionRecord[] {
  const file = ledgerFile(projectRoot, false);
  if (!fs.existsSync(file)) return Object.freeze([]);
  const lines = fs.readFileSync(file, 'utf8').split(/\r?\n/u);
  if (lines.length > MAX_LEDGER_RECORDS + 1) throw new Error('Action ledger exceeds its record limit');
  const records: LeanEvalActionRecord[] = [];
  let previousHash: string | undefined;
  for (const [index, line] of lines.entries()) {
    if (!line.trim()) continue;
    let value: unknown;
    try {
      value = JSON.parse(line);
    } catch (error) {
      throw new Error(`Action ledger is corrupt at line ${index + 1}`, { cause: error });
    }
    const record = normalize(value);
    if (!record) throw new Error(`Action ledger contains an invalid record at line ${index + 1}`);
    if (
      record.recordHash !== undefined &&
      (record.previousHash !== previousHash || record.recordHash !== sha256(hashPayload(record)))
    ) {
      throw new Error(`Action ledger hash chain mismatch at line ${index + 1}`);
    }
    records.push(record);
    previousHash = effectiveHash(record);
  }
  return Object.freeze(records);
}

export type LeanEvalActionRecordInput = Omit<
  LeanEvalActionRecord,
  'schema' | 'eventId' | 'recordedAt' | 'previousHash' | 'recordHash'
> & { recordedAt?: number };

export function appendLeanEvalActionRecords(
  projectRoot: string,
  inputs: readonly LeanEvalActionRecordInput[]
): readonly LeanEvalActionRecord[] {
  if (!inputs.length) return Object.freeze([]);
  const bases = inputs.map((input) =>
    Object.freeze({
      ...input,
      schema: 'deepscientist.mathematics.lean-eval-action.v1' as const,
      eventId: `action-event-${sha256(JSON.stringify(input)).slice(0, 32)}`,
      recordedAt: input.recordedAt ?? Date.now(),
    })
  );
  const file = ledgerFile(projectRoot, true);
  const lockPath = `${file}.lock`;
  const token = `${process.pid}-${crypto.randomUUID()}`;
  const deadline = Date.now() + 5_000;
  let descriptor: number | undefined;
  try {
    for (;;) {
      try {
        descriptor = fs.openSync(lockPath, 'wx', 0o600);
        fs.writeFileSync(descriptor, `${JSON.stringify({ ...lockOwnerRecord(), token })}\n`, 'utf8');
        break;
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'EEXIST' || Date.now() >= deadline) throw error;
        try {
          const stat = fs.statSync(lockPath);
          const lock: unknown = JSON.parse(fs.readFileSync(lockPath, 'utf8'));
          if (Date.now() - stat.mtimeMs > 30_000 && lockOwnerState(lock) !== 'alive')
            fs.rmSync(lockPath, { force: true });
        } catch {
          /* concurrent writer */
        }
        Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);
      }
    }
    const existing = readLeanEvalActionLedger(projectRoot);
    const existingById = new Map(existing.map((record) => [record.eventId, record]));
    let previousHash = existing.length ? effectiveHash(existing.at(-1)!) : undefined;
    const records: LeanEvalActionRecord[] = [];
    const lines: string[] = [];
    for (const base of bases) {
      const duplicate = existingById.get(base.eventId);
      if (duplicate) {
        records.push(duplicate);
        continue;
      }
      if (existing.length + lines.length >= MAX_LEDGER_RECORDS)
        throw new Error('Action ledger exceeds its record limit');
      const record = Object.freeze({
        ...base,
        ...(previousHash ? { previousHash } : {}),
        recordHash: sha256(hashPayload({ ...base, ...(previousHash ? { previousHash } : {}) })),
      });
      records.push(record);
      lines.push(`${JSON.stringify(record)}\n`);
      existingById.set(base.eventId, record);
      previousHash = record.recordHash;
    }
    if (lines.length) {
      const bytes = Buffer.byteLength(lines.join(''), 'utf8');
      if (fs.existsSync(file) && fs.statSync(file).size + bytes > MAX_LEDGER_BYTES) {
        throw new Error('Action ledger exceeds its size limit');
      }
      const out = fs.openSync(file, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_APPEND, 0o600);
      try {
        fs.writeFileSync(out, lines.join(''), 'utf8');
        fs.fsyncSync(out);
      } finally {
        fs.closeSync(out);
      }
      const cachePrefix = `${path.resolve(file)}\0`;
      for (const key of performanceCache.keys()) if (key.startsWith(cachePrefix)) performanceCache.delete(key);
    }
    return Object.freeze(records);
  } finally {
    if (descriptor !== undefined) {
      fs.closeSync(descriptor);
      try {
        const lock = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as { token?: unknown };
        if (lock.token === token) fs.rmSync(lockPath, { force: true });
      } catch {
        /* stale lock is reclaimed by a later writer */
      }
    }
  }
}

export function appendLeanEvalActionRecord(
  projectRoot: string,
  input: LeanEvalActionRecordInput
): LeanEvalActionRecord {
  return appendLeanEvalActionRecords(projectRoot, [input])[0]!;
}

const bucket = (): {
  attempts: number;
  advances: number;
  failures: number;
  goalReductions: number;
  errorImprovements: number;
  leanMs: number;
} => ({ attempts: 0, advances: 0, failures: 0, goalReductions: 0, errorImprovements: 0, leanMs: 0 });

const freezeBuckets = (
  value: Record<string, ReturnType<typeof bucket>>
): Readonly<Record<string, LeanEvalActionBucket>> =>
  Object.freeze(Object.fromEntries(Object.entries(value).map(([key, item]) => [key, Object.freeze(item)])));

export const actionContextKey = (goalShape: string, failureCategory: string | undefined, tactic: string): string =>
  `${goalShape}\u0000${failureCategory || 'unknown'}\u0000${tactic.trim()}`;

export function summarizeLeanEvalActions(records: readonly LeanEvalActionRecord[]): LeanEvalActionPerformanceSummary {
  const byContext: Record<string, ReturnType<typeof bucket>> = {};
  const byTactic: Record<string, ReturnType<typeof bucket>> = {};
  for (const record of records) {
    // Tool outages, malformed candidates, and duplicate probes describe the
    // runtime rather than tactic quality; retain them for audit but exclude
    // them from ranking statistics.
    if (record.outcome !== 'advanced' && record.outcome !== 'unchanged' && record.outcome !== 'failed') continue;
    const keys = [actionContextKey(record.goalShape, record.failureCategory, record.tactic), record.tactic.trim()];
    const targets = [byContext, byTactic];
    keys.forEach((key, index) => {
      const target = targets[index]!;
      const item = target[key] || (target[key] = bucket());
      item.attempts += 1;
      if (record.outcome === 'advanced') item.advances += 1;
      if (record.outcome === 'failed' || record.outcome === 'invalid' || record.outcome === 'unavailable')
        item.failures += 1;
      if (record.openGoalsAfter < record.openGoalsBefore)
        item.goalReductions += record.openGoalsBefore - record.openGoalsAfter;
      if (record.firstErrorImproved) item.errorImprovements += 1;
      item.leanMs += record.leanMs;
    });
  }
  return Object.freeze({ byContext: freezeBuckets(byContext), byTactic: freezeBuckets(byTactic) });
}

export function readLeanEvalActionPerformance(
  projectRoot: string,
  scope?: Readonly<{ runIdentity: string; problemId: string }>
): LeanEvalActionPerformanceSummary {
  const file = ledgerFile(projectRoot, false);
  if (!fs.existsSync(file)) return Object.freeze({ byContext: Object.freeze({}), byTactic: Object.freeze({}) });
  const stat = fs.statSync(file);
  const cacheKey = `${path.resolve(file)}\0${scope ? JSON.stringify(scope) : ''}`;
  const cached = performanceCache.get(cacheKey);
  if (cached && cached.mtimeMs === stat.mtimeMs && cached.size === stat.size) return cached.summary;
  const summary = summarizeLeanEvalActions(
    readLeanEvalActionLedger(projectRoot).filter(
      (record) => !scope || (record.runIdentity === scope.runIdentity && record.problemId === scope.problemId)
    )
  );
  performanceCache.set(cacheKey, { mtimeMs: stat.mtimeMs, size: stat.size, summary });
  return summary;
}

const performanceCache = new Map<
  string,
  { mtimeMs: number; size: number; summary: LeanEvalActionPerformanceSummary }
>();

/** Stable coarse shape used to transfer useful history across source edits. */
export function leanGoalShape(goal: string | undefined): string {
  return (
    (goal || 'unknown')
      .replace(/\b(?:h|h\d+|a|a\d+|x|x\d+|n|n\d+|m|m\d+|k|k\d+)\b/gu, '<id>')
      .replace(/\b\d+(?:\.\d+)?\b/gu, '<num>')
      .replace(/\s+/gu, ' ')
      .trim()
      .slice(0, 512) || 'unknown'
  );
}
