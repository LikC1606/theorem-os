import { describe, expect, it } from 'vitest';
import { summarizeReport } from '../apps/web/report';
import type { WebRun } from '../apps/web/shared';

const run = (report: unknown, changes: Partial<WebRun> = {}): WebRun => ({
  id: 'web-run-id', title: 'Test proof', status: 'completed', phase: 'finished',
  createdAt: '2026-10-16T00:00:00.000Z', updatedAt: '2026-10-16T00:00:01.000Z',
  providerId: 'offline-fixture', model: 'fixture-model', effort: 'high', environment: 'mathlib',
  source: 'theorem sample : True := by sorry', task: 'Prove the theorem',
  maxTurns: 2, maxRunSeconds: 60, workers: 1, coordination: 'cooperative', events: [],
  result: { status: 'evaluated_passed', proof: 'theorem sample : True := by trivial',
    report: report as Record<string, unknown> }, ...changes,
});

// Minimal sanitized shape from the completed Mathlib browser smoke report.
const fixture = () => ({
  schema: 'deepscientist.math.run.v2', runId: 'solver-run-id', problemId: 'lean-task-fixture',
  status: 'evaluated_passed', solution_commit: 'a'.repeat(40), solver_ready_receipt_valid: true,
  completion_signal_valid: true, turns: 1, solveWallMs: 26_302, usage: { totalTokens: 0 },
  candidateCheck: { passed: true, status: 'kernel_verified', results: [
    { theoremName: 'Algebra.square_add', status: 'kernel_verified', sorryCount: 0, admitCount: 0,
      stdoutPreview: 'Algebra.square_add: verified declaration' },
  ] },
  evaluator: { method: 'host-lean-kernel-all-targets', official: false, status: 'passed', verification: {
    commit: 'a'.repeat(40), passed: true, sourceDigest: 'b'.repeat(64),
    verification: { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
      results: [{ theoremName: 'Algebra.square_add', status: 'kernel_verified', sorryCount: 0, admitCount: 0,
        stdoutPreview: 'Algebra.square_add: independently verified declaration' }] },
  } },
  environment: { id: 'mathlib', toolchain: 'leanprover/lean4:v4.33.0',
    dependencyDigest: 'c'.repeat(64), mathlibRevision: 'd'.repeat(40) },
});

describe('web report summaries from structured worker fields', () => {
  it('summarizes the real host-final report shape without merging candidate and final targets', () => {
    const summary = summarizeReport(run(fixture()));
    expect(summary.checks.map(check => check.id)).toEqual(['candidate', 'evaluation']);
    expect(summary.checks[0]).toMatchObject({ label: '候选检查', tone: 'passed', omittedTargets: 0,
      targets: [{ name: 'Algebra.square_add', tone: 'passed', sorryCount: 0, admitCount: 0,
        diagnostics: [{ text: 'Algebra.square_add: verified declaration' }] }] });
    expect(summary.checks[1]).toMatchObject({ label: '独立验收', status: '验收阶段通过', tone: 'passed',
      method: 'Lean 内核 · 全部目标', omittedTargets: 0,
      targets: [{ name: 'Algebra.square_add', diagnostics: [{ text: 'Algebra.square_add: independently verified declaration' }] }] });
    expect(summary.metrics).toEqual([
      { label: '研究轮次', value: '1' }, { label: '求解耗时', value: '26.302 秒' }, { label: '总 Token', value: '0' },
    ]);
    expect(summary.identity).toContainEqual({ label: '求解运行 ID', value: 'solver-run-id' });
    expect(summary.identity).not.toContainEqual({ label: '求解运行 ID', value: 'web-run-id' });
    expect(summary.identity).toContainEqual({ label: '验收源码摘要', value: 'b'.repeat(64) });
    expect(summary.identity.some(item => item.label === '原题摘要')).toBe(false);
    expect(summary.identity).toContainEqual({ label: 'Mathlib 版本', value: 'd'.repeat(40) });
    expect(summary).not.toHaveProperty('accepted');
  });

  it('never promotes candidate rows over a failed candidate receipt', () => {
    const report = fixture();
    report.candidateCheck.passed = false;
    const summary = summarizeReport(run(report));
    expect(summary.checks[0]).toMatchObject({ status: '候选检查未通过', tone: 'failed',
      targets: [{ status: 'Lean 内核通过', tone: 'passed' }] });
    expect(summary.checks[1].tone).toBe('passed');
  });

  it('keeps candidate success separate from skipped independent acceptance', () => {
    const summary = summarizeReport(run({ candidateCheck: { passed: true, results: [{ theoremName: 'Candidate', status: 'kernel_verified' }] },
      evaluator: { status: 'skipped', reason: 'proof_incomplete' } }));
    expect(summary.checks[0].tone).toBe('passed');
    expect(summary.checks[1]).toMatchObject({ tone: 'muted', status: '已跳过', reason: 'proof_incomplete', targets: [] });
    expect(summary).not.toHaveProperty('accepted');
  });

  it('treats evaluator passed as a stage status even for a still-running or failed run', () => {
    for (const status of ['running', 'error', 'cancelled'] as const) {
      const summary = summarizeReport(run({ evaluator: { status: 'passed' }, completion_signal_valid: true }, { status }));
      expect(summary.checks).toEqual([{ id: 'evaluation', label: '独立验收', status: '验收阶段通过',
        tone: 'passed', targets: [], omittedTargets: 0 }]);
      expect(summary).not.toHaveProperty('accepted');
    }
  });

  it.each([true, false])('uses a strict solver receipt boolean as a candidate fallback: %s', passed => {
    expect(summarizeReport(run({ solver_ready_receipt_valid: passed })).checks).toEqual([
      { id: 'candidate', label: '候选检查', status: passed ? '候选检查通过' : '候选检查未通过',
        tone: passed ? 'passed' : 'failed', targets: [], omittedTargets: 0 },
    ]);
  });

  it.each([null, [], {}, 'true', 'false', 0, 1])('does not coerce malformed receipt flags: %j', value => {
    expect(summarizeReport(run({ candidateCheck: { passed: value }, solver_ready_receipt_valid: value })).checks).toEqual([]);
  });

  it('uses an explicit candidate boolean before fallback receipt flags', () => {
    expect(summarizeReport(run({ candidateCheck: { passed: false }, solver_ready_receipt_valid: true })).checks[0].tone).toBe('failed');
    expect(summarizeReport(run({ candidateCheck: { passed: true }, solver_ready_receipt_valid: false })).checks[0].tone).toBe('passed');
  });

  it.each(['future_status', '__proto__', 'constructor', 'toString', '<b>unknown</b>'])('preserves unknown status text with a neutral tone: %s', value => {
    const summary = summarizeReport(run({ candidateCheck: { status: value, results: [{ theoremName: 'Target', status: value }] },
      evaluator: { status: value } }));
    expect(summary.checks[0]).toMatchObject({ status: value, tone: 'muted', targets: [{ status: value, tone: 'muted' }] });
    expect(summary.checks[1]).toMatchObject({ status: value, tone: 'muted' });
  });

  it.each([
    ['kernel_verified', 'Lean 内核通过', 'passed'], ['failed', '检查未通过', 'failed'],
    ['blocked', '检查受阻', 'warning'], ['unavailable', '检查不可用', 'warning'],
  ])('maps the known target status %s', (raw, label, tone) => {
    expect(summarizeReport(run({ candidateCheck: { results: [{ theoremName: 'Target', status: raw }] } })).checks[0].targets[0])
      .toMatchObject({ status: label, tone });
  });

  it.each([
    ['passed', '验收阶段通过', 'passed'], ['failed', '验收阶段未通过', 'failed'],
    ['error', '验收阶段错误', 'failed'], ['skipped', '已跳过', 'muted'],
  ])('maps the known evaluator stage status %s', (raw, label, tone) => {
    expect(summarizeReport(run({ evaluator: { status: raw } })).checks[0]).toMatchObject({ status: label, tone });
  });

  it('reports the real evaluator timeout shape as a failed timeout without changing candidate state', () => {
    const summary = summarizeReport(run({ candidateCheck: { passed: true },
      evaluator: { status: 'error', reason: 'math_evaluation_timeout', timedOut: true } }));
    expect(summary.checks[0].tone).toBe('passed');
    expect(summary.checks[1]).toMatchObject({ status: '验收超时', tone: 'failed', reason: 'math_evaluation_timeout' });
    expect(summary).not.toHaveProperty('accepted');
  });

  it('does not display a successful evaluator stage when a timeout was explicitly reported', () => {
    expect(summarizeReport(run({ evaluator: { status: 'passed', timedOut: true } })).checks[0])
      .toMatchObject({ status: '验收超时', tone: 'failed' });
    expect(summarizeReport(run({ evaluator: { timedOut: true } })).checks[0])
      .toMatchObject({ status: '验收超时', tone: 'failed' });
  });

  it.each([false, 'true', 1, null, [], {}])('does not coerce a malformed timeout flag: %j', timedOut => {
    expect(summarizeReport(run({ evaluator: { status: 'error', timedOut } })).checks[0])
      .toMatchObject({ status: '验收阶段错误', tone: 'failed' });
  });

  it.each([undefined, null, [], ['fake'], 0, true, 'fake'])('ignores a malformed report container: %j', value => {
    expect(summarizeReport(run(value))).toEqual({ checks: [], metrics: [], identity: [] });
  });

  it.each([undefined, null, [], 0, true, 'fake'])('safely ignores malformed run/result containers: %j', value => {
    expect(summarizeReport(value as unknown as WebRun)).toEqual({ checks: [], metrics: [], identity: [] });
    expect(summarizeReport({ result: value } as unknown as WebRun)).toEqual({ checks: [], metrics: [], identity: [] });
  });

  it('does not recursively guess similarly named fields or use the wrong final-result level', () => {
    const wrong = [{ theoremName: 'Wrong', status: 'kernel_verified' }];
    const summary = summarizeReport(run({
      nested: { evaluator: { status: 'passed' }, reason: 'not-a-top-level-reason' },
      candidateCheck: { verification: { results: wrong } },
      evaluator: { status: 'failed', results: wrong, verification: { results: wrong,
        verification: { events: [{ results: wrong }] } } },
    }));
    expect(summary).toEqual({ checks: [{ id: 'evaluation', label: '独立验收', status: '验收阶段未通过',
      tone: 'failed', targets: [], omittedTargets: 0 }], metrics: [], identity: [] });
  });

  it('ignores arrays used as objects and malformed rows while retaining known partial target fields', () => {
    expect(summarizeReport(run({ candidateCheck: [], evaluator: [], environment: [], usage: [] }))).toEqual({ checks: [], metrics: [], identity: [] });
    const summary = summarizeReport(run({ candidateCheck: { results: [
      null, [], true, 'target', {}, { other: 'ignored' }, { theoremName: ['wrong'], status: null, sorryCount: NaN },
      { theoremName: 'Named only' }, { status: 'blocked' }, { sorryCount: 0, admitCount: 0 },
    ] } }));
    expect(summary.checks[0]).toMatchObject({ status: '未提供状态', tone: 'muted', omittedTargets: 0 });
    expect(summary.checks[0].targets).toEqual([
      { name: 'Named only', status: '未提供状态', tone: 'muted', diagnostics: [] },
      { name: '未命名目标', status: '检查受阻', tone: 'warning', diagnostics: [] },
      { name: '未命名目标', status: '未提供状态', tone: 'muted', sorryCount: 0, admitCount: 0, diagnostics: [] },
    ]);
  });

  it('deduplicates failure diagnostics and preserves plain text for the rendering layer', () => {
    const summary = summarizeReport(run({ candidateCheck: { passed: false, results: [
      { theoremName: '<script>Target</script>', status: 'failed', sorryCount: 1, admitCount: 0,
        error: ' error: unsolved goals ', stdoutPreview: 'error: unsolved goals', stderrPreview: '<img src=x onerror=alert(1)>' },
      { theoremName: 'Malformed diagnostics', error: {}, stdoutPreview: ['not text'], stderrPreview: false },
    ] } }));
    expect(summary.checks[0].targets[0]).toMatchObject({ name: '<script>Target</script>', tone: 'failed', sorryCount: 1, admitCount: 0,
      diagnostics: [{ label: '错误', text: 'error: unsolved goals' }, { label: '标准错误', text: '<img src=x onerror=alert(1)>' }] });
    expect(summary.checks[0].targets[1].diagnostics).toEqual([]);
  });

  it('limits each text field to 4000 characters and deduplicates after truncation', () => {
    const prefix = 'a'.repeat(4_000);
    const summary = summarizeReport(run({ candidateCheck: { results: [
      { theoremName: 'Target', error: prefix + 'one', stdoutPreview: prefix + 'two', stderrPreview: 'b'.repeat(8_000) },
    ] } }));
    const diagnostics = summary.checks[0].targets[0].diagnostics;
    expect(diagnostics).toEqual([{ label: '错误', text: prefix }, { label: '标准错误', text: 'b'.repeat(4_000) }]);
  });

  it('limits each stage to 64 valid targets and counts only omitted valid targets', () => {
    const rows = [null, {}, [], ...Array.from({ length: 70 }, (_, index) => ({ theoremName: `Target${index}`, status: 'failed' })), false];
    const summary = summarizeReport(run({ candidateCheck: { results: rows },
      evaluator: { status: 'failed', verification: { verification: { results: rows } } } }));
    for (const check of summary.checks) {
      expect(check.targets).toHaveLength(64);
      expect(check.targets[63].name).toBe('Target63');
      expect(check.omittedTargets).toBe(6);
    }
  });

  it('preserves valid zero metrics without fabricating absent values or costs', () => {
    expect(summarizeReport(run({ turns: 0, solveWallMs: 0, usage: { totalTokens: 0 } })).metrics).toEqual([
      { label: '研究轮次', value: '0' }, { label: '求解耗时', value: '0 秒' }, { label: '总 Token', value: '0' },
    ]);
    expect(summarizeReport(run({})).metrics).toEqual([]);
    expect(summarizeReport(run({ usage: { inputTokens: 1, outputTokens: 2 }, workers: [{ usage: { totalTokens: 3 } }] })).metrics).toEqual([]);
  });

  it.each([-1, NaN, Infinity, -Infinity, '0', null, true, [], {}])('rejects malformed numeric metrics and target counts: %j', value => {
    const summary = summarizeReport(run({ turns: value, solveWallMs: value, usage: { totalTokens: value },
      candidateCheck: { results: [{ theoremName: 'Target', sorryCount: value, admitCount: value }] } }));
    expect(summary.metrics).toEqual([]);
    expect(summary.checks[0].targets[0]).not.toHaveProperty('sorryCount');
    expect(summary.checks[0].targets[0]).not.toHaveProperty('admitCount');
  });

  it.each([0.25, Number.MAX_SAFE_INTEGER + 1])('rejects fractional or unsafe counts but retains valid finite elapsed time: %s', value => {
    const summary = summarizeReport(run({ turns: value, solveWallMs: value, usage: { totalTokens: value },
      candidateCheck: { results: [{ theoremName: 'Target', sorryCount: value, admitCount: value }] } }));
    expect(summary.metrics).toEqual([{ label: '求解耗时', value: `${value / 1_000} 秒` }]);
    expect(summary.checks[0].targets[0]).not.toHaveProperty('sorryCount');
    expect(summary.checks[0].targets[0]).not.toHaveProperty('admitCount');
  });

  it('accepts the safe-integer boundary for all counts and fractional finite elapsed time', () => {
    const count = Number.MAX_SAFE_INTEGER;
    const summary = summarizeReport(run({ turns: count, solveWallMs: 0.5, usage: { totalTokens: count },
      candidateCheck: { results: [{ theoremName: 'Target', sorryCount: count, admitCount: count }] } }));
    expect(summary.metrics).toEqual([{ label: '研究轮次', value: String(count) },
      { label: '求解耗时', value: '0.0005 秒' }, { label: '总 Token', value: String(count) }]);
    expect(summary.checks[0].targets[0]).toMatchObject({ sorryCount: count, admitCount: count });
  });

  it('does not add worker usage to the already aggregated total', () => {
    expect(summarizeReport(run({ usage: { totalTokens: 10, cachedTokens: 8, reasoningTokens: 5 },
      workers: [{ usage: { totalTokens: 5 } }, { usage: { totalTokens: 5 } }] })).metrics)
      .toEqual([{ label: '总 Token', value: '10' }]);
  });

  it('retains only known populated string identity fields and top-level reasons', () => {
    const summary = summarizeReport(run({ runId: 'solver', problemId: null, solution_commit: '', sourceDigest: 'wrong-level',
      reason: 'math_integrated_proof_mismatch', evaluator: { status: 'skipped' },
      environment: { toolchain: 1, dependencyDigest: [], mathlibRevision: 'revision' },
      unknown: { runId: 'nested', sourceDigest: 'nested' } }, { error: 'generic failure' }));
    expect(summary.reason).toBe('math_integrated_proof_mismatch');
    expect(summary.identity).toEqual([{ label: '求解运行 ID', value: 'solver' }, { label: 'Mathlib 版本', value: 'revision' }]);
    expect(summarizeReport(run({ reason: {} }, { error: 'worker unavailable' })).reason).toBe('worker unavailable');
  });

  it.each([['external-command', '外部命令'], ['official-comparator', '官方比较器']])('keeps missing host rows empty for %s', (method, label) => {
    const summary = summarizeReport(run({ candidateCheck: { passed: true, results: [{ theoremName: 'Candidate', status: 'kernel_verified' }] },
      evaluator: { status: 'failed', method, reason: 'known failure', result: { stdout: 'Not a theorem row' },
        comparison: { results: [{ theoremName: 'Not a host row', status: 'kernel_verified' }] } } }));
    expect(summary.checks[1]).toMatchObject({ method: label, tone: 'failed', reason: 'known failure', targets: [] });
  });

  it.each(['future-method', '__proto__', 'constructor', '<b>method</b>'])('preserves an unknown method as plain text without changing stage status: %s', method => {
    const summary = summarizeReport(run({ evaluator: { status: 'passed', method } }));
    expect(summary.checks[0]).toMatchObject({ method, status: '验收阶段通过', tone: 'passed' });
    expect(summary).not.toHaveProperty('accepted');
  });

  it('does not mutate the run or report', () => {
    const input = run(fixture());
    const original = structuredClone(input);
    summarizeReport(input);
    expect(input).toEqual(original);
  });
});
