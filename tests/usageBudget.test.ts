import { describe, expect, it } from 'vitest';
import { aggregateUsage, beginRequestUsage, buildTokenBudget, initializeRequestUsageAccounting, initializeUsageAccounting,
  modelDispatchAllowed, recordThreadUsage, reportedTotalTokens, type RequestUsageAccounting, type UsageAccounting } from '../src/solver/usageBudget';

const accounting = (overrides: Partial<UsageAccounting> = {}): UsageAccounting =>
  ({ startedTurns: 1, reportedTurns: 1, pending: false, incomplete: false, ...overrides });

describe('provider observed token dispatch budget', () => {
  it('reads only valid totals and does not double count cached or reasoning subsets', () => {
    expect(reportedTotalTokens({ inputTokens: 80, outputTokens: 20, cachedInputTokens: 60, reasoningOutputTokens: 15 })).toBe(100);
    expect(reportedTotalTokens({ totalTokens: 10, inputTokens: 80, outputTokens: 20 })).toBe(10);
    for (const totalTokens of [undefined, -1, 1.5, NaN, Infinity, '21', Number.MAX_SAFE_INTEGER + 1])
      expect(reportedTotalTokens({ totalTokens })).toBeNull();
    expect(reportedTotalTokens({ inputTokens: Number.MAX_SAFE_INTEGER, outputTokens: 1 })).toBeNull();
    expect(reportedTotalTokens({ totalTokens: 0 })).toBe(0);
  });

  it('does not re-add repeated cumulative updates and retains prior-thread usage on context rotation', () => {
    const record = { turns: 2, usage: {} as Record<string, unknown>, usageBeforeThread: undefined as Record<string, unknown> | undefined };
    for (const totalTokens of [10, 30, 30]) expect(recordThreadUsage(record, { totalTokens })).toBe(true);
    expect(record.usage).toEqual({ totalTokens: 30 });
    record.usageBeforeThread = record.usage;
    recordThreadUsage(record, { totalTokens: 7 });
    expect(record.usage).toEqual({ totalTokens: 37 });
    recordThreadUsage(record, { totalTokens: 7 });
    expect(record.usage.totalTokens).toBe(37);
    recordThreadUsage(record, { totalTokens: 12 });
    expect(record.usage.totalTokens).toBe(42);
  });

  it('retains cumulative consumption when resuming the same thread', () => {
    const record = { turns: 2, usage: { totalTokens: 37 }, usageBeforeThread: { totalTokens: 30 } };
    recordThreadUsage(record, { totalTokens: 7 });
    expect(record.usage.totalTokens).toBe(37);
    recordThreadUsage(record, { totalTokens: 10 });
    expect(record.usage.totalTokens).toBe(40);
  });

  it('retains the known consumption and marks a decreasing provider total incomplete', () => {
    const record = { turns: 1, usage: { totalTokens: 30 }, usageAccounting: accounting() };
    expect(recordThreadUsage(record, { totalTokens: 10 })).toBe(false);
    expect(record.usage.totalTokens).toBe(30);
    expect(buildTokenBudget(100, [record])).toMatchObject({ status: 'usage-unavailable',
      reportedTotalTokens: 30, usageComplete: false });
  });

  it('stops new work on the shared threshold and reports finished in-flight overrun', () => {
    const records = [60, 40].map(totalTokens => ({ turns: 1, usage: { totalTokens }, usageAccounting: accounting() }));
    expect(aggregateUsage(records)).toEqual({ totalTokens: 100 });
    const reached = buildTokenBudget(100, records);
    expect(reached).toMatchObject({ status: 'exhausted', reportedTotalTokens: 100, overrunTokens: 0, usageComplete: true,
      enforcement: 'provider-observed-dispatch-limit', reason: 'math_total_token_limit' });
    expect(modelDispatchAllowed(reached)).toBe(false);
    records[1].usage.totalTokens = 75;
    expect(buildTokenBudget(100, records)).toMatchObject({ reportedTotalTokens: 135, overrunTokens: 35 });
  });

  it('allows parallel in-flight requests before telemetry arrives, then fails closed for missing completed usage', () => {
    const record = { turns: 1, usageAccounting: accounting({ reportedTurns: 0, pending: true }) };
    expect(buildTokenBudget(100, [record])).toMatchObject({ status: 'available', reportedTotalTokens: null, usageComplete: false });
    record.usageAccounting.pending = false;
    expect(buildTokenBudget(100, [record])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: null,
      usageComplete: false, overrunTokens: null, reason: 'math_model_usage_unavailable' });
  });

  it('shows partial usage separately from its completeness and never supplies unknown worker usage as zero', () => {
    const known = { turns: 1, usage: { totalTokens: 40 }, usageAccounting: accounting() };
    const missing = { turns: 1, usageAccounting: accounting({ reportedTurns: 0, incomplete: true }) };
    expect(buildTokenBudget(100, [known, missing])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 40,
      usageComplete: false });
    expect(aggregateUsage([known, missing])).toEqual({ totalTokens: 40 });
    expect(buildTokenBudget(100, [missing]).reportedTotalTokens).toBeNull();
  });

  it('keeps zero unlimited even when usage is unavailable, and permits extending or reducing a cumulative allowance', () => {
    const records = [{ turns: 1, usage: { totalTokens: 120 }, usageAccounting: accounting() }];
    expect(modelDispatchAllowed(buildTokenBudget(0, [{ turns: 1 }]))).toBe(true);
    expect(buildTokenBudget(0, [{ turns: 1 }])).toMatchObject({ status: 'unlimited', reportedTotalTokens: null, usageComplete: false });
    expect(buildTokenBudget(100, records).status).toBe('exhausted');
    expect(buildTokenBudget(200, records)).toMatchObject({ status: 'available', reportedTotalTokens: 120 });
    expect(buildTokenBudget(80, records)).toMatchObject({ status: 'exhausted', overrunTokens: 40 });
    expect(buildTokenBudget(0, [])).toMatchObject({ status: 'unlimited', reportedTotalTokens: 0, usageComplete: true });
    for (const limit of [-1, 1.5, Infinity, NaN]) expect(() => buildTokenBudget(limit, [])).toThrow('invalid --max-total-tokens');
  });

  it('marks interrupted accounting and legacy untracked usage incomplete without dropping known totals', () => {
    const interrupted = { turns: 1, usage: { totalTokens: 25 }, usageAccounting: accounting({ reportedTurns: 0, pending: true }) };
    initializeUsageAccounting(interrupted);
    expect(interrupted.usageAccounting).toMatchObject({ pending: false, incomplete: true });
    expect(buildTokenBudget(100, [interrupted])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 25 });
    const legacy = { turns: 3, usage: { totalTokens: 150 } };
    initializeUsageAccounting(legacy);
    expect(buildTokenBudget(1000, [legacy])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 150 });
    expect(buildTokenBudget(0, [legacy]).status).toBe('unlimited');
  });

  it('does not turn cumulative or aggregate overflow into an available budget', () => {
    const records = [Number.MAX_SAFE_INTEGER, 1, 2].map(totalTokens => ({ turns: 1, usage: { totalTokens }, usageAccounting: accounting() }));
    expect(aggregateUsage(records)).toEqual({ totalTokens: null });
    expect(buildTokenBudget(100, records)).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: null });
    const record = { turns: 2, usage: { totalTokens: Number.MAX_SAFE_INTEGER }, usageBeforeThread: { totalTokens: Number.MAX_SAFE_INTEGER } };
    expect(recordThreadUsage(record, { totalTokens: 1 })).toBe(false);
    expect(record.usage.totalTokens).toBe(Number.MAX_SAFE_INTEGER);
  });
});

describe('direct upstream request accounting', () => {
  function record() {
    const value = { turns: 0, usage: undefined as Record<string, unknown> | undefined,
      usageAccounting: accounting({ startedTurns: 0, reportedTurns: 0 }),
      requestUsageAccounting: undefined as RequestUsageAccounting | undefined };
    initializeRequestUsageAccounting(value);
    return value;
  }
  const receipt = (totalTokens: number, complete = true) => ({
    usage: { totalTokens, inputTokens: totalTokens - 5, outputTokens: 5, cachedInputTokens: 2, reasoningOutputTokens: 1 }, complete,
  });

  it('counts each request once across tool roundtrips and session rotations, without adding token subsets', () => {
    const value = record();
    const first = beginRequestUsage(value);
    expect(buildTokenBudget(100, [value])).toMatchObject({ reportedTotalTokens: null, usageComplete: false });
    first(receipt(40)); first(receipt(40));
    initializeRequestUsageAccounting(value);
    beginRequestUsage(value)(receipt(60));
    expect(value.usage).toEqual({ totalTokens: 100, inputTokens: 90, outputTokens: 10, cachedInputTokens: 4, reasoningOutputTokens: 2 });
    expect(value.requestUsageAccounting).toEqual({ startedRequests: 2, reportedRequests: 2, pendingRequests: 0, incomplete: false });
    expect(buildTokenBudget(100, [value], 'provider-observed-upstream-request-limit')).toMatchObject({
      status: 'exhausted', reportedTotalTokens: 100, usageComplete: true, enforcement: 'provider-observed-upstream-request-limit',
    });
  });

  it('preserves known receipts when another request fails, even if later requests complete', () => {
    const value = record();
    beginRequestUsage(value)(receipt(40));
    beginRequestUsage(value)({ complete: false });
    beginRequestUsage(value)(receipt(25));
    expect(buildTokenBudget(100, [value])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 65, usageComplete: false });
    expect(value.requestUsageAccounting).toEqual({ startedRequests: 3, reportedRequests: 2, pendingRequests: 0, incomplete: true });
  });

  it('retains a validated receipt from an interrupted response as known partial consumption', () => {
    const value = record();
    beginRequestUsage(value)(receipt(40, false));
    expect(buildTokenBudget(100, [value])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 40, usageComplete: false });
  });

  it('uses request receipts for failed local turns and preserves pending request uncertainty on resume', () => {
    const value = record();
    value.turns = 1;
    value.usageAccounting = accounting({ reportedTurns: 0, pending: true });
    beginRequestUsage(value)(receipt(40));
    initializeUsageAccounting(value);
    expect(buildTokenBudget(100, [value])).toMatchObject({ status: 'available', reportedTotalTokens: 40, usageComplete: true });
    beginRequestUsage(value);
    initializeUsageAccounting(value);
    expect(value.requestUsageAccounting).toMatchObject({ pendingRequests: 0, incomplete: true });
    expect(buildTokenBudget(100, [value])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 40, usageComplete: false });
  });

  it('keeps zero attempted requests distinct from missing usage and inherits legacy uncertainty', () => {
    const value = record();
    value.turns = 1;
    value.usageAccounting = accounting({ reportedTurns: 0, incomplete: true });
    expect(buildTokenBudget(100, [value])).toMatchObject({ reportedTotalTokens: 0, usageComplete: true });
    const legacy = { turns: 1, usage: { totalTokens: 30 }, usageAccounting: accounting({ reportedTurns: 0, incomplete: true }),
      requestUsageAccounting: undefined as RequestUsageAccounting | undefined };
    initializeRequestUsageAccounting(legacy);
    beginRequestUsage(legacy)(receipt(20));
    expect(buildTokenBudget(100, [legacy])).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 50, usageComplete: false });
  });

  it('does not wrap an overflowing sum into an available budget', () => {
    const value = record();
    beginRequestUsage(value)(receipt(Number.MAX_SAFE_INTEGER));
    beginRequestUsage(value)(receipt(10));
    expect(buildTokenBudget(100, [value])).toMatchObject({ status: 'usage-unavailable',
      reportedTotalTokens: Number.MAX_SAFE_INTEGER, usageComplete: false });
  });
});
