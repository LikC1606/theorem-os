/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import type { LeanEvalCatalog, LeanEvalCatalogProblem } from "./leanEvalCatalogAdapter";
import { LEAN_EVAL_EPISODE_LEDGER_PATH, readLeanEvalEpisodeEvents } from "./leanEvalEpisodeLedger";
import type { LeanEvalProofLoopResult } from "./leanEvalProofLoop";

export const LEAN_EVAL_HELD_OUT_FAMILIES = [
  'arithmetic',
  'finite_structure',
  'algebraic_identity',
  'induction',
] as const;
export type LeanEvalHeldOutFamily = (typeof LEAN_EVAL_HELD_OUT_FAMILIES)[number];

export type LeanEvalHeldOutSelection = Readonly<{
  problemId: string;
  family: LeanEvalHeldOutFamily;
  title: string;
  statementRevision: number;
  selectionScore: number;
}>;

export type LeanEvalHeldOutRun = Readonly<{
  problemId: string;
  family: LeanEvalHeldOutFamily;
  status: 'completed' | 'failed' | 'aborted' | 'skipped';
  completedHoles: number;
  totalHoles: number;
  compileAttempts: number;
  durationMs: number;
  failureReason?: string;
}>;

export type LeanEvalHeldOutSummary = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-held-out-summary.v1';
  benchmarkCommit: string;
  catalogHash: string;
  selectedProblemIds: readonly string[];
  totalRuns: number;
  solvedRuns: number;
  solveRate: number;
  byFamily: Readonly<
    Record<
      LeanEvalHeldOutFamily,
      Readonly<{
        selected: number;
        runs: number;
        solved: number;
        solveRate: number;
        averageDurationMs: number;
        averageCompileAttempts: number;
      }>
    >
  >;
  summaryHash: string;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

export type LeanEvalHeldOutHistory = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-held-out-history.v1';
  coverage: 'provided_files_only';
  excludedProblemIds: readonly string[];
  sources: readonly Readonly<{
    file: string;
    sourceHash: string;
    kind: 'bootstrap' | 'episodes' | 'public_preflight';
    problemIds: readonly string[];
  }>[];
  historyHash: string;
}>;

const historyProblemId = (value: unknown): string => {
  if (typeof value !== 'string' || !/^[A-Za-z0-9][A-Za-z0-9_-]{0,199}$/u.test(value)) {
    throw new Error('Invalid held-out history problem id');
  }
  return value;
};
const historyRecord = (value: unknown): Record<string, unknown> => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('Invalid held-out history record');
  return value as Record<string, unknown>;
};

/** Explicit metadata files only: never crawl a benchmark tree or a solution corpus. */
export function readLeanEvalHeldOutHistory(files: readonly string[]): LeanEvalHeldOutHistory {
  if (!Array.isArray(files) || files.length > 2048 || files.some((file) => typeof file !== 'string' || !file.trim())) {
    throw new Error('Held-out history requires at most 2048 explicit metadata files');
  }
  const sources = [...new Set(files.map((file) => path.resolve(file)))].toSorted().map((file) => {
    if (!/\.jsonl?$/u.test(file) || /(?:^|[/\\])(?:solutions?|comparators?)(?:[./\\]|$)/iu.test(file)) {
      throw new Error('Held-out history accepts metadata JSON only, not solution or comparator files');
    }
    let cursor = path.parse(file).root;
    for (const segment of path.relative(cursor, file).split(path.sep)) {
      cursor = path.join(cursor, segment);
      if (fs.lstatSync(cursor).isSymbolicLink()) throw new Error('Held-out history must not traverse symbolic links');
    }
    const stat = fs.lstatSync(file);
    if (!stat.isFile() || stat.size > 32 * 1024 * 1024) throw new Error('Invalid held-out history metadata file');
    const source = fs.readFileSync(file, 'utf8');
    let kind: LeanEvalHeldOutHistory['sources'][number]['kind'];
    let ids: string[];
    if (file.replaceAll(path.sep, '/').endsWith(`/${LEAN_EVAL_EPISODE_LEDGER_PATH}`)) {
      kind = 'episodes';
      ids = readLeanEvalEpisodeEvents(path.resolve(file, '../../..')).map((event) => historyProblemId(event.problemId));
      if (fs.readFileSync(file, 'utf8') !== source) throw new Error('Held-out history changed during inspection');
    } else {
      const record = historyRecord(JSON.parse(source));
      if (record.schema === 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1') {
        if (path.basename(file) !== 'active-problem.json') throw new Error('Unexpected bootstrap history filename');
        kind = 'bootstrap';
        ids = [historyProblemId(record.problemId)];
        if (historyProblemId(historyRecord(record.contract).problemId) !== ids[0])
          throw new Error('History problem identity mismatch');
      } else if (record.schema === 'deepscientist.mathematics.lean-eval-held-out-preflight.v1') {
        if (
          record.solverInvoked !== false ||
          record.stage !== 'public_challenge_preflight' ||
          !Array.isArray(record.selected)
        ) {
          throw new Error('Invalid public preflight history');
        }
        kind = 'public_preflight';
        // Exposure is conservatively excluded, but is not a solver attempt.
        ids = record.selected.map((item) => historyProblemId(historyRecord(item).problemId));
      } else throw new Error('Unknown held-out history schema');
    }
    return Object.freeze({
      file,
      sourceHash: sha256(source),
      kind,
      problemIds: Object.freeze([...new Set(ids)].toSorted()),
    });
  });
  const base = {
    schema: 'deepscientist.mathematics.lean-eval-held-out-history.v1' as const,
    coverage: 'provided_files_only' as const,
    excludedProblemIds: Object.freeze([...new Set(sources.flatMap((source) => source.problemIds))].toSorted()),
    sources: Object.freeze(sources),
  };
  return Object.freeze({ ...base, historyHash: sha256(JSON.stringify(base)) });
}

const normalizedSearchText = (problem: LeanEvalCatalogProblem): string =>
  [problem.id, problem.title, problem.module, ...problem.tags]
    .join(' ')
    .replace(/([a-z])([A-Z])/gu, '$1 $2')
    .replace(/[_-]+/gu, ' ')
    .toLowerCase();

/** Classify only from public catalog metadata; no statement or solution source is read. */
export function classifyLeanEvalHeldOutFamily(problem: LeanEvalCatalogProblem): LeanEvalHeldOutFamily | 'unclassified' {
  const text = normalizedSearchText(problem);
  if (/\b(?:induction|recursive|recursion|well founded)\b/u.test(text)) return 'induction';
  if (
    /\b(?:finite (?:sets?|groups?|graphs?|structures?)|combinatorics?|graphs?|permutations?|enumeration|fintype|finite structure)\b/u.test(
      text
    )
  ) {
    return 'finite_structure';
  }
  if (/\b(?:(?:algebraic|polynomial(?: ring)?|ring|field) identit(?:y|ies))\b/u.test(text)) {
    return 'algebraic_identity';
  }
  if (/\b(?:arithmetic|number theory|integer (?:inequalit(?:y|ies)|multiplication))\b/u.test(text)) return 'arithmetic';
  // A domain keyword is not evidence of difficulty or a proof mechanism.
  return 'unclassified';
}

const selectionScore = (problem: LeanEvalCatalogProblem): number => {
  let score = 0;
  if (problem.activeV1) score += 100;
  if (problem.eligible) score += 100;
  if (problem.zeroCredit) score += 50;
  if (problem.acceptedCreditCount === 0) score += 25;
  score -= Math.min(20, problem.holes.length);
  return score;
};

/** Select a deterministic, family-balanced public held-out slate. */
export function selectLeanEvalHeldOutProblems(
  catalog: LeanEvalCatalog,
  options: Readonly<{
    families?: readonly LeanEvalHeldOutFamily[];
    limit?: number;
    excludeProblemIds?: readonly string[];
    requireZeroCredit?: boolean;
  }> = {}
): readonly LeanEvalHeldOutSelection[] {
  const families = options.families?.length ? [...new Set(options.families)] : [...LEAN_EVAL_HELD_OUT_FAMILIES];
  const limit = options.limit ?? families.length;
  if (!Number.isSafeInteger(limit) || limit < 1 || limit > 64) {
    throw new Error('Held-out selection limit must be an integer from 1 to 64');
  }
  if (families.some((family) => !LEAN_EVAL_HELD_OUT_FAMILIES.includes(family))) {
    throw new Error('Unknown held-out family');
  }
  const excluded = new Set(options.excludeProblemIds ?? []);
  const requireZeroCredit = options.requireZeroCredit !== false;
  const buckets = new Map<LeanEvalHeldOutFamily, LeanEvalHeldOutSelection[]>();
  for (const family of families) buckets.set(family, []);
  for (const problem of catalog.problems) {
    const family = classifyLeanEvalHeldOutFamily(problem);
    if (family === 'unclassified' || !buckets.has(family) || excluded.has(problem.id)) continue;
    if (
      !problem.activeV1 ||
      !problem.eligible ||
      (requireZeroCredit && (!problem.zeroCredit || problem.acceptedCreditCount > 0))
    )
      continue;
    buckets.get(family)!.push(
      Object.freeze({
        problemId: problem.id,
        family,
        title: problem.title,
        statementRevision: problem.statementRevision,
        selectionScore: selectionScore(problem),
      })
    );
  }
  for (const values of buckets.values()) {
    values.sort(
      (left, right) =>
        right.selectionScore - left.selectionScore ||
        left.problemId.localeCompare(right.problemId) ||
        left.statementRevision - right.statementRevision
    );
  }
  const selected: LeanEvalHeldOutSelection[] = [];
  while (selected.length < limit) {
    let added = false;
    for (const family of families) {
      const candidate = buckets.get(family)?.shift();
      if (!candidate) continue;
      selected.push(candidate);
      added = true;
      if (selected.length >= limit) break;
    }
    if (!added) break;
  }
  return Object.freeze(selected);
}

type MutableFamilyMetric = {
  selected: number;
  runs: number;
  solved: number;
  durationMsTotal: number;
  compileAttemptsTotal: number;
};

const emptyFamilyMetric = (): MutableFamilyMetric => ({
  selected: 0,
  runs: 0,
  solved: 0,
  durationMsTotal: 0,
  compileAttemptsTotal: 0,
});

/** Convert a proof-loop receipt into the canonical held-out evaluation row. */
export function heldOutRunFromProofLoop(
  input: Readonly<{
    selection: LeanEvalHeldOutSelection;
    proofLoop: LeanEvalProofLoopResult;
    totalHoles: number;
    startedAt: number;
    finishedAt: number;
  }>
): LeanEvalHeldOutRun {
  return Object.freeze({
    problemId: input.selection.problemId,
    family: input.selection.family,
    status: input.proofLoop.status,
    completedHoles: input.proofLoop.completedNames.length,
    totalHoles: Math.max(0, Math.floor(input.totalHoles)),
    compileAttempts: input.proofLoop.steps.filter((step) => step.status !== 'skipped').length,
    durationMs: Math.max(0, input.finishedAt - input.startedAt),
  });
}

/** Convert the headless Team runner receipt without trusting model text as proof. */
export function heldOutRunFromProofTeamReceipt(input: Readonly<{
  selection: LeanEvalHeldOutSelection;
  receipt: Readonly<Record<string, unknown>>;
  totalHoles: number;
  startedAt: number;
  finishedAt: number;
}>): LeanEvalHeldOutRun {
  const runOutcome = String(input.receipt.run_outcome || 'not_started');
  const evaluator = input.receipt.evaluator;
  const evaluatorStatus =
    evaluator && typeof evaluator === 'object' && !Array.isArray(evaluator)
      ? String((evaluator as Record<string, unknown>).status || 'not_configured')
      : 'not_configured';
  const runtimeSolverReady = input.receipt.solver_ready_receipt_valid === true;
  const completed = runtimeSolverReady && input.receipt.completion_signal_valid === true && evaluatorStatus === 'passed';
  const status: LeanEvalHeldOutRun['status'] = completed
    ? 'completed'
    : runOutcome === 'timed_out'
      ? 'aborted'
      : 'failed';
  const failureReason = completed
    ? undefined
    : !runtimeSolverReady && evaluatorStatus !== 'skipped'
      ? 'solver_ready_receipt_missing'
      : evaluatorStatus === 'skipped'
        ? `evaluator_skipped:${String(
            evaluator && typeof evaluator === 'object' && !Array.isArray(evaluator)
              ? (evaluator as Record<string, unknown>).reason || 'unknown'
              : 'unknown'
          )}`
        : `team_${runOutcome}`;
  return Object.freeze({
    problemId: input.selection.problemId,
    family: input.selection.family,
    status,
    completedHoles: completed ? Math.max(0, Math.floor(input.totalHoles)) : 0,
    totalHoles: Math.max(0, Math.floor(input.totalHoles)),
    compileAttempts: 0,
    durationMs: Math.max(0, input.finishedAt - input.startedAt),
    ...(failureReason ? { failureReason } : {}),
  });
}

/** Aggregate only runtime-owned proof-loop outcomes into a stable report. */
export function summarizeLeanEvalHeldOutRuns(
  input: Readonly<{
    catalog: Pick<LeanEvalCatalog, 'benchmarkCommit' | 'catalogHash'>;
    selected: readonly LeanEvalHeldOutSelection[];
    runs: readonly LeanEvalHeldOutRun[];
  }>
): LeanEvalHeldOutSummary {
  const metrics = Object.fromEntries(
    LEAN_EVAL_HELD_OUT_FAMILIES.map((family) => [family, emptyFamilyMetric()])
  ) as Record<LeanEvalHeldOutFamily, MutableFamilyMetric>;
  for (const item of input.selected) metrics[item.family]!.selected += 1;
  let solvedRuns = 0;
  for (const run of input.runs) {
    const metric = metrics[run.family];
    if (!metric) continue;
    metric.runs += 1;
    metric.durationMsTotal += Math.max(0, run.durationMs);
    metric.compileAttemptsTotal += Math.max(0, run.compileAttempts);
    const solved = run.status === 'completed' && run.totalHoles > 0 && run.completedHoles >= run.totalHoles;
    if (solved) {
      metric.solved += 1;
      solvedRuns += 1;
    }
  }
  const byFamily = Object.fromEntries(
    LEAN_EVAL_HELD_OUT_FAMILIES.map((family) => {
      const metric = metrics[family]!;
      return [
        family,
        Object.freeze({
          selected: metric.selected,
          runs: metric.runs,
          solved: metric.solved,
          solveRate: metric.runs ? metric.solved / metric.runs : 0,
          averageDurationMs: metric.runs ? metric.durationMsTotal / metric.runs : 0,
          averageCompileAttempts: metric.runs ? metric.compileAttemptsTotal / metric.runs : 0,
        }),
      ];
    })
  ) as LeanEvalHeldOutSummary['byFamily'];
  const base = {
    schema: 'deepscientist.mathematics.lean-eval-held-out-summary.v1' as const,
    benchmarkCommit: input.catalog.benchmarkCommit,
    catalogHash: input.catalog.catalogHash,
    selectedProblemIds: Object.freeze(input.selected.map((item) => item.problemId)),
    totalRuns: input.runs.length,
    solvedRuns,
    solveRate: input.runs.length ? solvedRuns / input.runs.length : 0,
    byFamily: Object.freeze(byFamily),
  };
  return Object.freeze({ ...base, summaryHash: sha256(JSON.stringify(base)) });
}
