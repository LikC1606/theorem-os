import { describe, expect, it } from 'vitest';
import { deriveMathProofRunMetric, summarizeMathProofRunMetrics } from '../src/math/mathProofRunReport';
import { buildMathProofRunReportFromJson } from '../scripts/mathematics/summarizeMathProofRuns';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';

const passed = { schema: 'deepscientist.math.run.v2', status: 'evaluated_passed',
  solver_ready_receipt_valid: true, completion_signal_valid: true, evaluator: { status: 'passed' } };
const metric = (problemId: string, method: string, receipt: Record<string, unknown> = passed) =>
  deriveMathProofRunMetric({ runId: `${problemId}:${method}`, problemId, benchmarkMethod: method, receipt });

describe('standalone proof-run reports', () => {
  it('reads provider usage and keeps missing, invalid and estimated usage distinct', () => {
    expect(metric('p', 'solver', { ...passed, usage: { totalTokens: 21 } }))
      .toMatchObject({ tokensToProof: 21, tokenUsageSource: 'provider', timeToProofMs: null });
    for (const totalTokens of [undefined, -1, 1.5, '21']) {
      expect(metric('p', 'solver', { ...passed, usage: { totalTokens } }))
        .toMatchObject({ tokensToProof: null, tokenUsageSource: null });
    }
    expect(metric('p', 'solver', { ...passed, usage: { totalTokens: 0 } }).tokensToProof).toBe(0);
    const report = buildMathProofRunReportFromJson({ generatedAt: 1,
      slate: { benchmarkId: 'fixture', benchmarkCommit: 'commit', catalogHash: 'hash', randomSeed: 'seed',
        problemIds: ['p'], repetitions: 1 },
      value: [{ runId: 'p', problemId: 'p', benchmarkMethod: 'solver', receipt: passed,
        totalTokens: 100, tokenUsageSource: 'estimated', estimatedInputTokens: 80 }],
    });
    expect(report.runs[0]).toMatchObject({ tokensToProof: null, tokenUsageSource: 'estimated', estimatedInputTokens: 80 });
    expect(report.averageTokensToProof).toBeNull();
  });

  it('requires host acceptance and independent evaluation to count a solve', () => {
    for (const changes of [{ solver_ready_receipt_valid: false }, { completion_signal_valid: false },
      { evaluator: { status: 'skipped' } }, { evaluator: { status: 'failed' } }]) {
      expect(metric('p', 'solver', { ...passed, ...changes }).verifiedSolve).toBe(false);
    }
    expect(deriveMathProofRunMetric({ runId: 'p', problemId: 'p', benchmarkMethod: 'solver', receipt: passed,
      verifierStatus: 'failed' }).verifiedSolve).toBe(false);
  });

  it('preserves solve statistics and paired comparisons while excluding unfinished and unavailable runs', () => {
    const runs = [
      metric('p1', 'control', { ...passed, durations_ms: { proof: 100 }, usage: { totalTokens: 20 } }),
      metric('p1', 'treatment', { ...passed, durations_ms: { proof: 200 }, usage: { totalTokens: 40 } }),
      metric('p2', 'control', { status: 'evaluated_failed', evaluator: { status: 'failed' } }),
      metric('p2', 'treatment', { ...passed, durations_ms: { proof: 300 }, usage: { totalTokens: 60 } }),
      metric('unfinished', 'treatment', { status: 'incomplete', durations_ms: { proof: 500 } }),
      metric('limited', 'treatment', { status: 'limit_reached' }),
      metric('infra', 'treatment', { status: 'runtime_error', evaluator: { status: 'error' } }),
    ];
    const report = summarizeMathProofRunMetrics(runs, { generatedAt: 1, controlMethod: 'control', treatmentMethod: 'treatment' });
    expect(report).toMatchObject({ totalRuns: 7, evaluableRuns: 4, verifiedSolves: 3, verifiedSolveRate: 0.75,
      rightCensoredRuns: 2, unavailableRuns: 1, excludedRuns: 3, averageTimeToProofMs: 200,
      medianTimeToProofMs: 200, iqrTimeToProofMs: 100, averageTokensToProof: 40, iqrTokensToProof: 20 });
    expect(report.byMethod.control).toMatchObject({ totalRuns: 2, verifiedSolveRate: 0.5 });
    expect(report.byMethod.treatment).toMatchObject({ evaluableRuns: 2, verifiedSolveRate: 1 });
    expect(report.pairedComparisons).toMatchObject([{ matchedTrials: 2, matchedProblems: 2, bothSolved: 1,
      treatmentOnlySolved: 1, problemWeightedSolveRateDifference: 0.5 }]);
    const { reportHash, ...payload } = report;
    expect(reportHash).toBe(mathDigest(canonicalMathJson(payload)));
  });

  it('rejects duplicate trials and runs outside the frozen slate', () => {
    const run = metric('p', 'solver');
    expect(() => summarizeMathProofRunMetrics([run, { ...run, runId: 'another' }])).toThrow('duplicate_repetition');
    const slate = { benchmarkId: 'fixture', benchmarkCommit: 'commit', catalogHash: 'hash', randomSeed: 'seed',
      problemIds: ['other'], repetitions: 1 };
    expect(() => summarizeMathProofRunMetrics([run], { slate })).toThrow('outside_slate');
  });
});
