/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";
import { canonicalMathJson, mathDigest, readMathJson, writeMathJsonDurable } from "./mathRuntimeIo";

export const LEAN_EVAL_OUTCOME_LEDGER_PATH = '.deepscientist/math/lean-eval-outcomes.jsonl' as const;
export const LEAN_EVAL_OUTCOME_INDEX_PATH = '.deepscientist/math/lean-eval-outcomes.index.json' as const;
const MAX_LEDGER_BYTES = 32 * 1024 * 1024;
const MAX_LEDGER_RECORDS = 100_000;

export type LeanEvalOutcome = 'success' | 'proof_failure' | 'toolchain' | 'sandbox' | 'aborted' | 'comparator_failure';
export type LeanEvalOutcomeRecord = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-outcome.v1';
  eventId: string;
  problemId: string;
  runIdentity?: string;
  assignmentId?: string;
  statementRevision: number;
  statementHash?: string;
  modelId?: string;
  /** Tactic responsible for the terminal compiler result, when known. */
  tactic?: string;
  route?: string;
  archetype?: string;
  holeCount: number;
  criticalPath: number;
  compileAttempts: number;
  toolchain?: string;
  sandboxBackend?: string;
  outcome: LeanEvalOutcome;
  failureCategory?: string;
  elapsedMs: number;
  recordedAt: number;
  /** Hash-chain fields are optional for backwards-compatible legacy rows. */
  previousHash?: string;
  recordHash?: string;
}>;

export type LeanEvalOutcomeSummary = Readonly<{
  /** Total durable records, including infrastructure and comparator outcomes. */
  attempts: number;
  /** Solver-attributable records only: success or proof_failure. */
  mathematicalAttempts: number;
  mathematicalSuccesses: number;
  mathematicalSuccessRate: number;
  infrastructureAttempts: number;
  successes: number;
  /** Solver successes divided by solver-attributable attempts (infrastructure is excluded). */
  empiricalSuccessRate: number;
  /** Beta(1,1) posterior mean used for ranking under sparse history. */
  posteriorMean: number;
  /** Legacy alias for posteriorMean retained for existing callers. */
  successRate: number;
  confidenceInterval: Readonly<{ lower: number; upper: number; level: number }>;
  byOutcome: Readonly<Record<string, number>>;
  infrastructureByOutcome: Readonly<Record<string, number>>;
  byRoute: Readonly<Record<string, Readonly<{ attempts: number; successes: number }>>>;
  byArchetype: Readonly<Record<string, Readonly<{ attempts: number; successes: number }>>>;
  byModel: Readonly<Record<string, Readonly<{ attempts: number; successes: number }>>>;
  byTactic: Readonly<Record<string, Readonly<{ attempts: number; successes: number }>>>;
}>;

type OutcomeAggregate = {
  attempts: number;
  mathematicalAttempts: number;
  mathematicalSuccesses: number;
  infrastructureAttempts: number;
  successes: number;
  byOutcome: Record<string, number>;
  infrastructureByOutcome: Record<string, number>;
  byRoute: Record<string, { attempts: number; successes: number }>;
  byArchetype: Record<string, { attempts: number; successes: number }>;
  byModel: Record<string, { attempts: number; successes: number }>;
  byTactic: Record<string, { attempts: number; successes: number }>;
};

type OutcomeIndex = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-outcome-index.v1';
  ledgerRevision: string;
  aggregates: Readonly<Record<string, OutcomeAggregate>>;
  indexHash: string;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

const hashPayload = (record: LeanEvalOutcomeRecord): string => {
  const payload = Object.fromEntries(
    Object.entries(record)
      .filter(([key]) => key !== 'recordHash')
      .toSorted(([left], [right]) => left.localeCompare(right))
  );
  return JSON.stringify(payload);
};

const effectiveRecordHash = (record: LeanEvalOutcomeRecord): string => record.recordHash ?? sha256(hashPayload(record));

const ledgerPath = (projectRoot: string, createDirectories: boolean): string => {
  const root = path.resolve(projectRoot);
  const rootStat = fs.lstatSync(root);
  if (rootStat.isSymbolicLink() || !rootStat.isDirectory()) {
    throw new Error('Lean-Eval outcome ledger project root is not a regular directory');
  }
  let cursor = root;
  for (const segment of ['.deepscientist', 'math']) {
    cursor = path.join(cursor, segment);
    if (!fs.existsSync(cursor)) {
      if (!createDirectories) break;
      fs.mkdirSync(cursor, { mode: 0o700 });
      continue;
    }
    const stat = fs.lstatSync(cursor);
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new Error('Lean-Eval outcome ledger directory is not a regular directory');
    }
  }
  const file = path.join(root, LEAN_EVAL_OUTCOME_LEDGER_PATH);
  if (fs.existsSync(file)) {
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval outcome ledger is not a regular file');
    if (stat.size > MAX_LEDGER_BYTES) throw new Error('Lean-Eval outcome ledger exceeds its size limit');
  }
  return file;
};

const outcomeIndexPath = (projectRoot: string, createDirectories: boolean): string => {
  // Reuse ledgerPath so both files share exactly the same ownership checks and
  // directory creation semantics.
  const file = ledgerPath(projectRoot, createDirectories);
  const index = path.join(path.dirname(file), 'lean-eval-outcomes.index.json');
  if (fs.existsSync(index)) {
    const stat = fs.lstatSync(index);
    if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval outcome index is not a regular file');
  }
  return index;
};

const ensureLedgerPath = (projectRoot: string): string => ledgerPath(projectRoot, true);

const emptyAggregate = (): OutcomeAggregate => ({
  attempts: 0,
  mathematicalAttempts: 0,
  mathematicalSuccesses: 0,
  infrastructureAttempts: 0,
  successes: 0,
  byOutcome: {},
  infrastructureByOutcome: {},
  byRoute: {},
  byArchetype: {},
  byModel: {},
  byTactic: {},
});

const addDimension = (
  bucket: Record<string, { attempts: number; successes: number }>,
  key: string,
  success: boolean
): void => {
  const entry = bucket[key] ?? { attempts: 0, successes: 0 };
  entry.attempts += 1;
  if (success) entry.successes += 1;
  bucket[key] = entry;
};

const addRecordToAggregate = (aggregate: OutcomeAggregate, record: LeanEvalOutcomeRecord): void => {
  aggregate.attempts += 1;
  aggregate.byOutcome[record.outcome] = (aggregate.byOutcome[record.outcome] ?? 0) + 1;
  const mathematical = record.outcome === 'success' || record.outcome === 'proof_failure';
  if (!mathematical) {
    aggregate.infrastructureAttempts += 1;
    aggregate.infrastructureByOutcome[record.outcome] = (aggregate.infrastructureByOutcome[record.outcome] ?? 0) + 1;
    return;
  }
  aggregate.mathematicalAttempts += 1;
  if (record.outcome === 'success') {
    aggregate.mathematicalSuccesses += 1;
    aggregate.successes += 1;
  }
  const success = record.outcome === 'success';
  addDimension(aggregate.byRoute, record.route || 'unknown', success);
  addDimension(aggregate.byArchetype, record.archetype || 'unknown', success);
  addDimension(aggregate.byModel, record.modelId || 'unknown', success);
  addDimension(aggregate.byTactic, record.tactic || 'unknown', success);
};

const aggregateKey = (problemId?: string, runIdentity?: string): string =>
  JSON.stringify([problemId ?? '', runIdentity ?? '']);

const buildOutcomeIndex = (records: readonly LeanEvalOutcomeRecord[], ledgerRevision: string): OutcomeIndex => {
  const aggregates: Record<string, OutcomeAggregate> = {};
  for (const record of records) {
    for (const key of [
      aggregateKey(),
      aggregateKey(record.problemId),
      ...(record.runIdentity ? [aggregateKey(undefined, record.runIdentity)] : []),
      ...(record.runIdentity ? [aggregateKey(record.problemId, record.runIdentity)] : []),
    ]) {
      const aggregate = aggregates[key] ?? (aggregates[key] = emptyAggregate());
      addRecordToAggregate(aggregate, record);
    }
  }
  const payload = {
    schema: 'deepscientist.mathematics.lean-eval-outcome-index.v1',
    ledgerRevision,
    aggregates,
  } as const;
  return Object.freeze({
    ...payload,
    aggregates: Object.freeze(aggregates),
    indexHash: mathDigest(canonicalMathJson(payload)),
  });
};

const parseOutcomeIndex = (value: unknown): OutcomeIndex | undefined => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const item = value as Record<string, unknown>;
  if (
    item.schema !== 'deepscientist.mathematics.lean-eval-outcome-index.v1' ||
    typeof item.ledgerRevision !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(item.ledgerRevision) ||
    !item.aggregates ||
    typeof item.aggregates !== 'object' ||
    Array.isArray(item.aggregates) ||
    typeof item.indexHash !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(item.indexHash)
  )
    return undefined;
  const aggregates = item.aggregates as Record<string, unknown>;
  for (const aggregateValue of Object.values(aggregates)) {
    if (!aggregateValue || typeof aggregateValue !== 'object' || Array.isArray(aggregateValue)) return undefined;
    const aggregate = aggregateValue as Record<string, unknown>;
    for (const field of [
      'attempts',
      'mathematicalAttempts',
      'mathematicalSuccesses',
      'infrastructureAttempts',
      'successes',
    ]) {
      if (!Number.isSafeInteger(aggregate[field]) || Number(aggregate[field]) < 0) return undefined;
    }
    for (const field of ['byOutcome', 'infrastructureByOutcome', 'byRoute', 'byArchetype', 'byModel', 'byTactic']) {
      if (!aggregate[field] || typeof aggregate[field] !== 'object' || Array.isArray(aggregate[field]))
        return undefined;
    }
  }
  const { indexHash, ...payload } = item;
  if (mathDigest(canonicalMathJson(payload)) !== indexHash) return undefined;
  return item as unknown as OutcomeIndex;
};

const readOutcomeIndex = (projectRoot: string): OutcomeIndex | undefined => {
  const file = outcomeIndexPath(projectRoot, false);
  if (!fs.existsSync(file)) return undefined;
  try {
    return parseOutcomeIndex(readMathJson(file));
  } catch {
    return undefined;
  }
};

const persistOutcomeIndex = (projectRoot: string, index: OutcomeIndex): void => {
  const file = outcomeIndexPath(projectRoot, true);
  writeMathJsonDurable(file, index);
};

const cloneAggregate = (aggregate: OutcomeAggregate): OutcomeAggregate =>
  structuredClone(aggregate) as OutcomeAggregate;

const addRecordToIndex = (index: OutcomeIndex, record: LeanEvalOutcomeRecord, ledgerRevision: string): OutcomeIndex => {
  const aggregates: Record<string, OutcomeAggregate> = Object.fromEntries(
    Object.entries(index.aggregates).map(([key, value]) => [key, cloneAggregate(value)])
  );
  for (const key of [
    aggregateKey(),
    aggregateKey(record.problemId),
    ...(record.runIdentity ? [aggregateKey(undefined, record.runIdentity)] : []),
    ...(record.runIdentity ? [aggregateKey(record.problemId, record.runIdentity)] : []),
  ]) {
    const aggregate = aggregates[key] ?? (aggregates[key] = emptyAggregate());
    addRecordToAggregate(aggregate, record);
  }
  const payload = {
    schema: 'deepscientist.mathematics.lean-eval-outcome-index.v1' as const,
    ledgerRevision,
    aggregates,
  };
  return Object.freeze({
    ...payload,
    aggregates: Object.freeze(aggregates),
    indexHash: mathDigest(canonicalMathJson(payload)),
  });
};

const normalizeRecord = (value: unknown): LeanEvalOutcomeRecord | undefined => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const item = value as Record<string, unknown>;
  if (item.schema !== 'deepscientist.mathematics.lean-eval-outcome.v1') return undefined;
  if (
    typeof item.eventId !== 'string' ||
    !item.eventId.trim() ||
    typeof item.problemId !== 'string' ||
    !item.problemId.trim() ||
    !Number.isSafeInteger(item.statementRevision) ||
    Number(item.statementRevision) < 1
  )
    return undefined;
  if (
    !Number.isSafeInteger(item.holeCount) ||
    !Number.isSafeInteger(item.criticalPath) ||
    !Number.isSafeInteger(item.compileAttempts) ||
    Number(item.holeCount) < 0 ||
    Number(item.criticalPath) < 0 ||
    Number(item.compileAttempts) < 0
  )
    return undefined;
  if (
    !['success', 'proof_failure', 'toolchain', 'sandbox', 'aborted', 'comparator_failure'].includes(
      String(item.outcome)
    )
  )
    return undefined;
  if (typeof item.elapsedMs !== 'number' || !Number.isFinite(item.elapsedMs) || item.elapsedMs < 0) return undefined;
  if (!Number.isFinite(item.recordedAt) || Number(item.recordedAt) <= 0) return undefined;
  for (const field of [
    'assignmentId',
    'statementHash',
    'modelId',
    'tactic',
    'route',
    'archetype',
    'toolchain',
    'sandboxBackend',
    'failureCategory',
  ]) {
    const fieldValue = item[field];
    if (fieldValue !== undefined && (typeof fieldValue !== 'string' || !fieldValue.trim())) return undefined;
  }
  for (const field of ['previousHash', 'recordHash', 'runIdentity']) {
    const fieldValue = item[field];
    if (fieldValue !== undefined && (typeof fieldValue !== 'string' || !/^[a-f0-9]{64}$/u.test(fieldValue))) {
      return undefined;
    }
  }
  return Object.freeze(item as unknown as LeanEvalOutcomeRecord);
};

export function readLeanEvalOutcomeLedger(projectRoot: string): readonly LeanEvalOutcomeRecord[] {
  const file = ledgerPath(projectRoot, false);
  if (!fs.existsSync(file)) return Object.freeze([]);
  const stat = fs.lstatSync(file);
  if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval outcome ledger is not a regular file');
  if (stat.size > MAX_LEDGER_BYTES) throw new Error('Lean-Eval outcome ledger exceeds its size limit');
  const lines = fs.readFileSync(file, 'utf8').split(/\r?\n/u);
  if (lines.length > MAX_LEDGER_RECORDS + 1) throw new Error('Lean-Eval outcome ledger exceeds its record limit');
  const records: LeanEvalOutcomeRecord[] = [];
  let previousHash: string | undefined;
  let chainStarted = false;
  for (const [index, line] of lines.entries()) {
    if (!line.trim()) continue;
    let value: unknown;
    try {
      value = JSON.parse(line);
    } catch (error) {
      throw new Error(`Lean-Eval outcome ledger is corrupt at line ${index + 1}`, { cause: error });
    }
    const record = normalizeRecord(value);
    if (!record) throw new Error(`Lean-Eval outcome ledger contains an invalid record at line ${index + 1}`);
    if (record.recordHash) {
      if (record.previousHash !== previousHash) {
        throw new Error(`Lean-Eval outcome ledger hash chain mismatch at line ${index + 1}`);
      }
      if (record.recordHash !== sha256(hashPayload(record))) {
        throw new Error(`Lean-Eval outcome ledger record hash mismatch at line ${index + 1}`);
      }
      chainStarted = true;
    } else if (record.previousHash !== undefined) {
      throw new Error(`Lean-Eval outcome ledger has an invalid hash anchor at line ${index + 1}`);
    } else if (chainStarted) {
      // A legacy row after a chained row would make the tail unverifiable.
      throw new Error(`Lean-Eval outcome ledger hash chain is truncated at line ${index + 1}`);
    }
    records.push(record);
    previousHash = effectiveRecordHash(record);
  }
  return Object.freeze(records);
}

/** Content revision used to invalidate analysis caches after a new attempt. */
export function readLeanEvalOutcomeLedgerRevision(projectRoot: string): string {
  const file = ledgerPath(projectRoot, false);
  try {
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink() || !stat.isFile()) return '';
    return sha256(fs.readFileSync(file, 'utf8'));
  } catch {
    return '';
  }
}

export function appendLeanEvalOutcome(
  projectRoot: string,
  input: Omit<LeanEvalOutcomeRecord, 'schema' | 'eventId' | 'recordedAt' | 'previousHash' | 'recordHash'> & {
    recordedAt?: number;
  }
): LeanEvalOutcomeRecord {
  const recordBase: LeanEvalOutcomeRecord = Object.freeze({
    ...input,
    schema: 'deepscientist.mathematics.lean-eval-outcome.v1',
    eventId: `outcome-${sha256(JSON.stringify(input)).slice(0, 32)}`,
    recordedAt: input.recordedAt ?? Date.now(),
  });
  const file = ensureLedgerPath(projectRoot);
  const lockPath = `${file}.lock`;
  const lockToken = `${process.pid}-${crypto.randomUUID()}`;
  let lockDescriptor: number | undefined;
  const waitBuffer = new Int32Array(new SharedArrayBuffer(4));
  const deadline = Date.now() + 5_000;
  try {
    for (;;) {
      try {
        lockDescriptor = fs.openSync(lockPath, 'wx', 0o600);
        fs.writeFileSync(lockDescriptor, `${JSON.stringify({ ...lockOwnerRecord(), token: lockToken })}\n`, 'utf8');
        fs.fsyncSync(lockDescriptor);
        break;
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'EEXIST' || Date.now() >= deadline) throw error;
        let stale = false;
        try {
          const lockStat = fs.statSync(lockPath);
          const lockValue = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as Record<string, unknown>;
          stale = Date.now() - lockStat.mtimeMs > 30_000 && lockOwnerState(lockValue) !== 'alive';
        } catch {
          stale = false;
        }
        if (stale) {
          fs.rmSync(lockPath, { force: true });
          continue;
        }
        Atomics.wait(waitBuffer, 0, 0, 10);
      }
    }
    const existing = readLeanEvalOutcomeLedger(projectRoot);
    const previousLedgerRevision = sha256(fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '');
    const duplicate = existing.find(
      (item) =>
        item.eventId === recordBase.eventId ||
        (recordBase.assignmentId && item.assignmentId === recordBase.assignmentId)
    );
    if (duplicate) return duplicate;
    if (existing.length >= MAX_LEDGER_RECORDS) throw new Error('Lean-Eval outcome ledger exceeds its record limit');
    const previousHash = existing.length > 0 ? effectiveRecordHash(existing.at(-1)!) : undefined;
    const record: LeanEvalOutcomeRecord = Object.freeze({
      ...recordBase,
      ...(previousHash ? { previousHash } : {}),
      recordHash: sha256(hashPayload({ ...recordBase, ...(previousHash ? { previousHash } : {}) })),
    });
    const line = `${JSON.stringify(record)}\n`;
    const currentSize = fs.existsSync(file) ? fs.statSync(file).size : 0;
    if (Buffer.byteLength(line, 'utf8') + currentSize > MAX_LEDGER_BYTES) {
      throw new Error('Lean-Eval outcome ledger exceeds its size limit');
    }
    const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
    const descriptor = fs.openSync(
      file,
      fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_APPEND | noFollow,
      0o600
    );
    try {
      fs.writeFileSync(descriptor, line, 'utf8');
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    const nextLedgerRevision = sha256(fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '');
    const indexed = readOutcomeIndex(projectRoot);
    const baseIndex =
      indexed?.ledgerRevision === previousLedgerRevision
        ? indexed
        : buildOutcomeIndex(existing, previousLedgerRevision);
    try {
      persistOutcomeIndex(projectRoot, addRecordToIndex(baseIndex, record, nextLedgerRevision));
    } catch {
      // The append is authoritative. A later summary call will rebuild an
      // absent or stale optimization index from the verified ledger.
    }
    return record;
  } finally {
    if (lockDescriptor !== undefined) {
      fs.closeSync(lockDescriptor);
      try {
        const lockValue = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as Record<string, unknown>;
        if (lockValue.token === lockToken) fs.rmSync(lockPath, { force: true });
      } catch {
        // A crashed writer leaves a lock that the stale-owner path can reap.
      }
    }
  }
}

const summaryFromAggregate = (aggregate: OutcomeAggregate): LeanEvalOutcomeSummary => {
  const { attempts, mathematicalAttempts, mathematicalSuccesses, infrastructureAttempts, successes } = aggregate;
  const p = (mathematicalSuccesses + 1) / (mathematicalAttempts + 2);
  const z = 1.96;
  const denominator = 1 + (z * z) / Math.max(1, mathematicalAttempts);
  const center = (p + (z * z) / (2 * Math.max(1, mathematicalAttempts))) / denominator;
  const radius =
    (z / denominator) *
    Math.sqrt(
      (p * (1 - p)) / Math.max(1, mathematicalAttempts) + (z * z) / (4 * Math.max(1, mathematicalAttempts) ** 2)
    );
  return Object.freeze({
    attempts,
    mathematicalAttempts,
    mathematicalSuccesses,
    mathematicalSuccessRate:
      mathematicalAttempts === 0 ? 0 : Math.round((mathematicalSuccesses / mathematicalAttempts) * 10_000) / 10_000,
    infrastructureAttempts,
    successes,
    empiricalSuccessRate:
      mathematicalAttempts === 0 ? 0 : Math.round((mathematicalSuccesses / mathematicalAttempts) * 10_000) / 10_000,
    posteriorMean: Math.round(p * 10_000) / 10_000,
    successRate: Math.round(p * 10_000) / 10_000,
    confidenceInterval: Object.freeze({
      lower: Math.max(0, center - radius),
      upper: Math.min(1, center + radius),
      level: 0.95,
    }),
    byOutcome: Object.freeze(aggregate.byOutcome),
    infrastructureByOutcome: Object.freeze(aggregate.infrastructureByOutcome),
    byRoute: Object.freeze(
      Object.fromEntries(Object.entries(aggregate.byRoute).map(([key, value]) => [key, Object.freeze(value)]))
    ),
    byArchetype: Object.freeze(
      Object.fromEntries(Object.entries(aggregate.byArchetype).map(([key, value]) => [key, Object.freeze(value)]))
    ),
    byModel: Object.freeze(
      Object.fromEntries(Object.entries(aggregate.byModel).map(([key, value]) => [key, Object.freeze(value)]))
    ),
    byTactic: Object.freeze(
      Object.fromEntries(Object.entries(aggregate.byTactic).map(([key, value]) => [key, Object.freeze(value)]))
    ),
  });
};

/** Beta(1,1) posterior with a Wilson interval for ranking confidence. */
export function summarizeLeanEvalOutcomes(records: readonly LeanEvalOutcomeRecord[]): LeanEvalOutcomeSummary {
  const aggregate = emptyAggregate();
  for (const record of records) addRecordToAggregate(aggregate, record);
  return summaryFromAggregate(aggregate);
}

export function readLeanEvalOutcomeSummary(
  projectRoot: string,
  problemId?: string,
  runIdentity?: string
): LeanEvalOutcomeSummary {
  const file = ledgerPath(projectRoot, false);
  const revision = sha256(fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '');
  const key = aggregateKey(problemId, runIdentity);
  const index = readOutcomeIndex(projectRoot);
  if (index?.ledgerRevision === revision && index.aggregates[key]) return summaryFromAggregate(index.aggregates[key]);
  const ledger = readLeanEvalOutcomeLedger(projectRoot);
  const records = ledger.filter(
    (record) =>
      (!problemId || record.problemId === problemId) &&
      (runIdentity === undefined || record.runIdentity === runIdentity)
  );
  const summary = summarizeLeanEvalOutcomes(records);
  try {
    persistOutcomeIndex(projectRoot, buildOutcomeIndex(ledger, revision));
  } catch {
    // Indexing is an optimization; the verified ledger remains authoritative.
  }
  return summary;
}
