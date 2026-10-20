
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

export type MathProofRunMetric = Readonly<{
  schema: 'deepscientist.math.proof-run-metrics.v1';
  runId: string;
  /** Frozen run-input identity; never inferred from model text. */
  runIdentity: string;
  problemId: string;
  benchmarkMethod: string;
  repetition: number;
  elapsedMs: number | null;
  infrastructureFailure: boolean;
  verifiedSolve: boolean;
  /** Whether this run has a terminal, independently evaluable result. */
  evaluationDisposition: 'evaluable' | 'right_censored' | 'unavailable';
  /** Explicit denominator membership; equivalent to evaluationDisposition=evaluable. */
  evaluable: boolean;
  /** A run that ended before a terminal result and is retained as right-censored. */
  rightCensored: boolean;
  censorReason: string | null;
  /** Null means the run did not produce a verified proof or timing was absent. */
  timeToProofMs: number | null;
  /** Observed duration retained for a run that ended before evaluation. */
  rightCensoredElapsedMs: number | null;
  /** Null means provider usage was not independently observed for this run. */
  tokensToProof: number | null;
  /** Provenance of token telemetry; estimated tokenizer counts never become provider totals. */
  tokenUsageSource: 'provider' | 'estimated' | null;
  /** Optional local tokenizer estimate, retained separately from provider usage. */
  estimatedInputTokens: number | null;
  /** Null when the verifier was not independently classified. */
  verifierFailure: boolean | null;
  /** Null when no configured evaluator result was available. */
  evaluatorFailure: boolean | null;
}>;

export type MathProofBenchmarkSlate = Readonly<{
  benchmarkId: string;
  benchmarkCommit: string;
  catalogHash: string;
  randomSeed: string;
  problemIds: readonly string[];
  repetitions: number;
}>;

export type MathProofRunReportOptions = Readonly<{
  generatedAt?: number;
  slate?: MathProofBenchmarkSlate;
  controlMethod?: string;
  treatmentMethod?: string;
  sourceLedgerRevision?: string | null;
  sourceIndexHash?: string | null;
  generatorVersion?: string;
}>;

export type MathProofPairedComparison = Readonly<{
  controlMethod: string;
  treatmentMethod: string;
  matchedTrials: number;
  matchedProblems: number;
  rightCensoredPairs: number;
  infrastructurePairs: number;
  unavailablePairs: number;
  controlOnlySolved: number;
  treatmentOnlySolved: number;
  bothSolved: number;
  neitherSolved: number;
  problemWeightedSolveRateDifference: number | null;
}>;

type ProofRunReceipt = Readonly<Record<string, unknown>>;

const nonNegativeInteger = (value: unknown): number | null =>
  Number.isSafeInteger(value) && Number(value) >= 0 ? Number(value) : null;

const nonNegativeFinite = (value: unknown): number | null =>
  typeof value === 'number' && Number.isFinite(value) && value >= 0 ? value : null;

const receiptObject = (value: unknown): ProofRunReceipt | undefined =>
  value && typeof value === 'object' && !Array.isArray(value) ? (value as ProofRunReceipt) : undefined;

const readReceiptNumber = (receipt: ProofRunReceipt, key: string): number | null => {
  const direct = nonNegativeFinite(receipt[key]);
  if (direct !== null) return direct;
  const durations = receiptObject(receipt.durations_ms);
  return durations ? nonNegativeFinite(durations[key]) : null;
};

const average = (values: readonly number[]): number | null =>
  values.length ? values.reduce((sum, value) => sum + value, 0) / values.length : null;

const quantile = (values: readonly number[], probability: number): number | null => {
  if (!values.length) return null;
  const sorted = values.toSorted((left, right) => left - right);
  const position = (sorted.length - 1) * probability;
  const lower = Math.floor(position);
  const upper = Math.ceil(position);
  if (lower === upper) return sorted[lower]!;
  return sorted[lower]! + (sorted[upper]! - sorted[lower]!) * (position - lower);
};

const median = (values: readonly number[]): number | null => quantile(values, 0.5);
const iqr = (values: readonly number[]): number | null => {
  const lower = quantile(values, 0.25);
  const upper = quantile(values, 0.75);
  return lower === null || upper === null ? null : upper - lower;
};

const booleanRate = (values: readonly (boolean | null)[]): { observed: number; rate: number | null } => {
  const observed = values.filter((value): value is boolean => value !== null);
  return {
    observed: observed.length,
    rate: observed.length ? observed.filter(Boolean).length / observed.length : null,
  };
};

const wilsonInterval = (
  successes: number,
  trials: number,
  z = 1.96
): Readonly<{ lower: number; upper: number; level: number }> => {
  if (trials === 0) return Object.freeze({ lower: 0, upper: 0, level: 0.95 });
  const p = successes / trials;
  const denominator = 1 + (z * z) / trials;
  const center = (p + (z * z) / (2 * trials)) / denominator;
  const radius = (z / denominator) * Math.sqrt((p * (1 - p)) / trials + (z * z) / (4 * trials * trials));
  return Object.freeze({ lower: Math.max(0, center - radius), upper: Math.min(1, center + radius), level: 0.95 });
};

const methodSummary = (runs: readonly MathProofRunMetric[]) => {
  const verifier = booleanRate(runs.map((run) => run.verifierFailure));
  const evaluator = booleanRate(runs.map((run) => run.evaluatorFailure));
  const evaluableRuns = runs.filter((run) => run.evaluable).length;
  const rightCensoredRuns = runs.filter((run) => run.rightCensored).length;
  const unavailableRuns = runs.filter((run) => run.evaluationDisposition === 'unavailable').length;
  const verifiedSolves = runs.filter((run) => run.verifiedSolve).length;
  const times = runs.map((run) => run.timeToProofMs).filter((value): value is number => value !== null);
  const tokens = runs.map((run) => run.tokensToProof).filter((value): value is number => value !== null);
  return {
    totalRuns: runs.length,
    evaluableRuns,
    rightCensoredRuns,
    unavailableRuns,
    verifiedSolves,
    verifiedSolveRate: evaluableRuns ? verifiedSolves / evaluableRuns : 0,
    verifiedSolveConfidenceInterval: wilsonInterval(verifiedSolves, evaluableRuns),
    averageTimeToProofMs: average(times),
    medianTimeToProofMs: median(times),
    iqrTimeToProofMs: iqr(times),
    rightCensoredElapsedMs: average(
      runs.map((run) => run.rightCensoredElapsedMs).filter((value): value is number => value !== null)
    ),
    averageTokensToProof: average(tokens),
    medianTokensToProof: median(tokens),
    iqrTokensToProof: iqr(tokens),
    verifierFailureRate: verifier.rate,
    evaluatorFailureRate: evaluator.rate,
    observedVerifierRuns: verifier.observed,
    observedEvaluatorRuns: evaluator.observed,
    excludedRuns: runs.length - evaluableRuns,
  };
};

const defaultSlate = (runs: readonly MathProofRunMetric[]): MathProofBenchmarkSlate =>
  Object.freeze({
    benchmarkId: 'unspecified',
    benchmarkCommit: 'unspecified',
    catalogHash: 'unspecified',
    randomSeed: 'unspecified',
    problemIds: Object.freeze([...new Set(runs.map((run) => run.problemId))].toSorted()),
    repetitions: Math.max(0, ...runs.map((run) => run.repetition)),
  });

const pairRuns = (
  runs: readonly MathProofRunMetric[],
  controlMethod: string,
  treatmentMethod: string
): MathProofPairedComparison => {
  const controlRuns = runs.filter((run) => run.benchmarkMethod === controlMethod);
  const treatmentRuns = runs.filter((run) => run.benchmarkMethod === treatmentMethod);
  const treatmentByKey = new Map(treatmentRuns.map((run) => [`${run.problemId}\0${run.repetition}`, run]));
  const pairs = controlRuns
    .map((run) => ({ control: run, treatment: treatmentByKey.get(`${run.problemId}\0${run.repetition}`) }))
    .filter(
      (pair): pair is { control: MathProofRunMetric; treatment: MathProofRunMetric } => pair.treatment !== undefined
    );
  const valid = pairs.filter(
    ({ control: left, treatment: right }) =>
      left.evaluable && right.evaluable && !left.infrastructureFailure && !right.infrastructureFailure
  );
  const problems = [...new Set(valid.map(({ control }) => control.problemId))];
  const problemDifferences = problems.map((problemId) => {
    const rows = valid.filter(({ control }) => control.problemId === problemId);
    const left = rows.filter(({ control }) => control.verifiedSolve).length / rows.length;
    const right = rows.filter(({ treatment }) => treatment.verifiedSolve).length / rows.length;
    return right - left;
  });
  const totalPairs = pairs.length;
  const rightCensoredPairs = pairs.filter(
    ({ control, treatment }) => control.rightCensored || treatment.rightCensored
  ).length;
  const infrastructurePairs = pairs.filter(
    ({ control, treatment }) =>
      !control.rightCensored &&
      !treatment.rightCensored &&
      (control.infrastructureFailure || treatment.infrastructureFailure)
  ).length;
  const unavailablePairs = pairs.filter(
    ({ control, treatment }) =>
      !control.rightCensored &&
      !treatment.rightCensored &&
      !control.infrastructureFailure &&
      !treatment.infrastructureFailure &&
      (control.evaluationDisposition === 'unavailable' || treatment.evaluationDisposition === 'unavailable')
  ).length;
  return Object.freeze({
    controlMethod,
    treatmentMethod,
    matchedTrials: totalPairs,
    matchedProblems: problems.length,
    rightCensoredPairs,
    infrastructurePairs,
    unavailablePairs,
    controlOnlySolved: valid.filter(({ control, treatment }) => control.verifiedSolve && !treatment.verifiedSolve)
      .length,
    treatmentOnlySolved: valid.filter(({ control, treatment }) => treatment.verifiedSolve && !control.verifiedSolve)
      .length,
    bothSolved: valid.filter(({ control, treatment }) => control.verifiedSolve && treatment.verifiedSolve).length,
    neitherSolved: valid.filter(({ control, treatment }) => !control.verifiedSolve && !treatment.verifiedSolve).length,
    problemWeightedSolveRateDifference: problemDifferences.length
      ? problemDifferences.reduce((sum, difference) => sum + difference, 0) / problemDifferences.length
      : null,
  });
};

/** Evaluator statuses that decide failure; any other status (`not_configured`, `skipped`, unknown) is unavailable. */
const EVALUATOR_FAILURE: Readonly<Record<string, boolean>> = { error: true, failed: true, timeout: true, interrupted: true, passed: false };

/**
 * Convert a host runner receipt into a stable row.
 * Missing telemetry remains unavailable; it is never converted to zero.
 */
export function deriveMathProofRunMetric(
  input: Readonly<{
    runId: string;
    problemId: string;
    benchmarkMethod: string;
    receipt: ProofRunReceipt;
    runIdentity?: string;
    repetition?: number;
    /** Optional host usage override; otherwise use provider usage in the receipt. */
    totalTokens?: number;
    tokenUsageSource?: 'provider' | 'estimated';
    estimatedInputTokens?: number;
    verifierStatus?: 'passed' | 'failed' | 'missing' | 'unavailable';
  }>
): MathProofRunMetric {
  if (!input.runId.trim() || !input.problemId.trim() || !input.benchmarkMethod.trim())
    throw new Error('math_proof_run_metric_identity_invalid');
  const receipt = input.receipt;
  const totalTokens = nonNegativeInteger(input.totalTokens ?? receiptObject(receipt.usage)?.totalTokens);
  const evaluator = receiptObject(receipt.evaluator);
  const evaluatorStatus = typeof evaluator?.status === 'string' ? evaluator.status : undefined;
  const receiptStatus = typeof receipt.status === 'string' ? receipt.status : undefined;
  const verifierFailure = input.verifierStatus === 'failed' ? true : input.verifierStatus === 'passed' ? false : null;
  const evaluatorFailure = evaluatorStatus !== undefined && Object.hasOwn(EVALUATOR_FAILURE, evaluatorStatus)
    ? EVALUATOR_FAILURE[evaluatorStatus]! : null;
  // `evaluated_passed` and `evaluated_failed` are terminal results. A plain
  // incomplete or wall-limited run is right-censored because proof search
  // ended before a terminal result, provided no infrastructure failure occurred;
  // startup-only and runtime/evaluator failures are unavailable rather than
  // mathematical failures. This keeps the solve-rate denominator explicit.
  const infrastructureFailure =
    receiptStatus === 'runtime_error' ||
    receipt.startup_only === true ||
    ['toolchain', 'sandbox', 'aborted', 'comparator_failure'].includes(
      typeof receipt.error_code === 'string' ? receipt.error_code : ''
    ) ||
    ['error', 'timeout', 'interrupted'].includes(evaluatorStatus ?? '') ||
    input.verifierStatus === 'unavailable';
  const terminalReceipt = receiptStatus === 'evaluated_passed' || receiptStatus === 'evaluated_failed';
  const evaluatorClassified = evaluatorStatus === 'passed' || evaluatorStatus === 'failed';
  const evaluationDisposition: MathProofRunMetric['evaluationDisposition'] =
    terminalReceipt && evaluatorClassified && !infrastructureFailure
      ? 'evaluable'
      : !infrastructureFailure && (receiptStatus === 'incomplete' || receiptStatus === 'limit_reached')
        ? 'right_censored'
        : 'unavailable';
  const verifiedSolve =
    evaluationDisposition === 'evaluable' &&
    receiptStatus === 'evaluated_passed' &&
    receipt.solver_ready_receipt_valid === true &&
    receipt.completion_signal_valid === true &&
    evaluatorStatus === 'passed' &&
    input.verifierStatus !== 'failed' &&
    input.verifierStatus !== 'unavailable';
  const censorReason =
    evaluationDisposition === 'evaluable'
      ? null
      : typeof receipt.error_code === 'string' && receipt.error_code.trim()
        ? receipt.error_code.trim()
        : (receiptStatus ?? 'missing_terminal_result');
  const elapsedProof = readReceiptNumber(receipt, 'proof');
  const elapsedEvaluator = readReceiptNumber(receipt, 'evaluator');
  const elapsedMs =
    elapsedProof === null && elapsedEvaluator === null ? null : (elapsedProof ?? 0) + (elapsedEvaluator ?? 0);
  const repetition = input.repetition ?? nonNegativeInteger(receipt.repetition) ?? 1;
  if (repetition < 1) throw new Error('math_proof_run_repetition_invalid');
  return Object.freeze({
    schema: 'deepscientist.math.proof-run-metrics.v1',
    runId: input.runId,
    runIdentity: input.runIdentity?.trim() || input.runId,
    problemId: input.problemId,
    benchmarkMethod: input.benchmarkMethod,
    repetition,
    elapsedMs,
    infrastructureFailure,
    verifiedSolve,
    evaluationDisposition,
    evaluable: evaluationDisposition === 'evaluable',
    rightCensored: evaluationDisposition === 'right_censored',
    censorReason,
    timeToProofMs: verifiedSolve ? elapsedProof : null,
    rightCensoredElapsedMs: evaluationDisposition === 'right_censored' ? elapsedMs : null,
    tokensToProof:
      verifiedSolve && input.tokenUsageSource !== 'estimated' ? totalTokens : null,
    tokenUsageSource:
      totalTokens !== null
        ? (input.tokenUsageSource ?? 'provider')
        : input.estimatedInputTokens !== undefined
          ? 'estimated'
          : null,
    estimatedInputTokens: nonNegativeInteger(input.estimatedInputTokens),
    verifierFailure,
    evaluatorFailure,
  });
}

/** Aggregate rows from one frozen experiment slate. */
export function summarizeMathProofRunMetrics(
  runs: readonly MathProofRunMetric[],
  options: MathProofRunReportOptions = {}
) {
  const generatedAt = options.generatedAt ?? Date.now();
  if (!Number.isFinite(generatedAt) || generatedAt <= 0) throw new Error('math_proof_run_report_timestamp_invalid');
  const slate = options.slate ?? defaultSlate(runs);
  const allowedProblems = new Set(slate.problemIds);
  const identities = new Set<string>();
  for (const run of runs) {
    if (!allowedProblems.has(run.problemId) || run.repetition < 1 || run.repetition > slate.repetitions) {
      throw new Error('math_proof_run_outside_slate');
    }
    const key = `${run.problemId}\0${run.benchmarkMethod}\0${run.repetition}`;
    if (identities.has(key)) throw new Error('math_proof_run_duplicate_repetition');
    identities.add(key);
  }
  const all = methodSummary(runs);
  const byMethod = Object.fromEntries(
    [...new Set(runs.map((run) => run.benchmarkMethod))]
      .toSorted()
      .map((method) => [method, methodSummary(runs.filter((run) => run.benchmarkMethod === method))])
  );
  const base = {
    schema: 'deepscientist.math.proof-run-report.v1' as const,
    generatedAt,
    ...all,
    byMethod,
    runs: Object.freeze([...runs]),
    slate,
    sourceLedgerRevision: options.sourceLedgerRevision ?? null,
    sourceIndexHash: options.sourceIndexHash ?? null,
    generatorVersion: options.generatorVersion ?? 'math-proof-run-report.v1',
    pairedComparisons:
      options.controlMethod && options.treatmentMethod
        ? Object.freeze([pairRuns(runs, options.controlMethod, options.treatmentMethod)])
        : Object.freeze([]),
  };
  return Object.freeze({ ...base, reportHash: mathDigest(canonicalMathJson(base)) });
}
