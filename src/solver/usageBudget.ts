export type UsageAccounting = {
  startedTurns: number;
  reportedTurns: number;
  pending: boolean;
  incomplete: boolean;
};

export type TokenBudget = {
  maxTotalTokens: number;
  /** Notifications arrive after consumption; this does not cap tokens in requests already in flight. */
  enforcement: 'provider-observed-dispatch-limit';
  status: 'unlimited' | 'available' | 'exhausted' | 'usage-unavailable';
  reportedTotalTokens: number | null;
  usageComplete: boolean;
  overrunTokens: number | null;
  reason?: 'math_total_token_limit' | 'math_model_usage_unavailable';
};

type UsageRecord = {
  turns: number;
  usage?: Record<string, unknown>;
  usageBeforeThread?: Record<string, unknown>;
  usageAccounting?: UsageAccounting;
};

const count = (value: unknown): value is number => typeof value === 'number' && Number.isSafeInteger(value) && value >= 0;

/** Cached input and reasoning output are subsets, never additional tokens. */
export function reportedTotalTokens(usage?: Record<string, unknown>): number | null {
  if (count(usage?.totalTokens)) return usage.totalTokens;
  if (count(usage?.inputTokens) && count(usage?.outputTokens)) {
    const total = usage.inputTokens + usage.outputTokens;
    if (count(total)) return total;
  }
  return null;
}

/** A resumed unfinished request and legacy untracked requests have no complete usage receipt. */
export function initializeUsageAccounting(record: UsageRecord): void {
  if (!record.usageAccounting) record.usageAccounting = {
    startedTurns: record.turns, reportedTurns: 0, pending: false, incomplete: record.turns > 0,
  };
  else if (record.usageAccounting.pending) {
    record.usageAccounting.pending = false;
    record.usageAccounting.incomplete = true;
  }
}

/** Merge a provider's thread total with prior threads, without counting duplicate notifications twice. */
export function recordThreadUsage(record: UsageRecord, reported: Record<string, unknown>): boolean {
  const merged = { ...record.usage };
  for (const [key, value] of Object.entries(reported)) {
    if (!count(value)) continue;
    const baseline = record.usageBeforeThread?.[key];
    const total = (count(baseline) ? baseline : 0) + value;
    if (count(total)) merged[key] = Math.max(count(merged[key]) ? merged[key] : 0, total);
  }
  const reportedTotal = reportedTotalTokens(reported);
  if (reportedTotal !== null) {
    const baseline = reportedTotalTokens(record.usageBeforeThread) ?? 0;
    const total = baseline + reportedTotal;
    const previous = reportedTotalTokens(record.usage) ?? 0;
    if (!count(total) || total < previous) {
      if (record.usageAccounting) record.usageAccounting.incomplete = true;
      record.usage = merged;
      return false;
    }
    merged.totalTokens = total;
  }
  record.usage = merged;
  return reportedTotal !== null;
}

export function aggregateUsage(records: readonly UsageRecord[]): Record<string, unknown> {
  const usage: Record<string, unknown> = {};
  for (const record of records) for (const [key, value] of Object.entries(record.usage ?? {})) {
    if (!count(value)) continue;
    if (usage[key] === null) continue;
    const total = Number(usage[key] ?? 0) + value;
    usage[key] = count(total) ? total : null;
  }
  return usage;
}

/** Partial reported consumption stays visible; missing reports never become zero-cost completed work. */
export function buildTokenBudget(maxTotalTokens: number, records: readonly UsageRecord[]): TokenBudget {
  if (!count(maxTotalTokens)) throw new Error('invalid --max-total-tokens');
  let total = 0;
  let reported = false;
  let worked = false;
  let incomplete = false;
  let pending = false;
  for (const record of records) {
    const accounting = record.usageAccounting;
    const hadWork = (accounting?.startedTurns ?? record.turns) > 0;
    const tokens = reportedTotalTokens(record.usage);
    worked ||= hadWork;
    incomplete ||= Boolean(accounting?.incomplete || (!accounting && hadWork) ||
      (accounting && accounting.startedTurns - accounting.reportedTurns > Number(accounting.pending)));
    pending ||= Boolean(accounting?.pending);
    if (tokens !== null) { total += tokens; reported = true; }
  }
  if (!count(total)) { incomplete = true; reported = false; }
  const reportedTotal = count(total) && (reported || !worked) ? total : null;
  const status = !maxTotalTokens ? 'unlimited' : incomplete ? 'usage-unavailable' :
    reportedTotal !== null && reportedTotal >= maxTotalTokens ? 'exhausted' : 'available';
  return { maxTotalTokens, enforcement: 'provider-observed-dispatch-limit', status,
    reportedTotalTokens: reportedTotal, usageComplete: !incomplete && !pending,
    overrunTokens: reportedTotal === null ? null : maxTotalTokens ? Math.max(0, reportedTotal - maxTotalTokens) : 0,
    ...(status === 'exhausted' ? { reason: 'math_total_token_limit' as const } :
      status === 'usage-unavailable' ? { reason: 'math_model_usage_unavailable' as const } : {}) };
}

export const modelDispatchAllowed = (budget: TokenBudget): boolean =>
  budget.status === 'unlimited' || budget.status === 'available';
