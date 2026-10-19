import type { ModelRequestReceipt } from '../runtime/modelRequest';

export type UsageAccounting = {
  startedTurns: number;
  reportedTurns: number;
  pending: boolean;
  incomplete: boolean;
};

export type RequestUsageAccounting = {
  startedRequests: number;
  reportedRequests: number;
  pendingRequests: number;
  incomplete: boolean;
};

export type TokenBudget = {
  maxTotalTokens: number;
  /** Notifications arrive after consumption; this does not cap tokens in requests already in flight. */
  enforcement: 'provider-observed-dispatch-limit' | 'provider-observed-upstream-request-limit';
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
  requestUsageAccounting?: RequestUsageAccounting;
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
    if (!record.requestUsageAccounting) record.usageAccounting.incomplete = true;
  }
  if (record.requestUsageAccounting?.pendingRequests) {
    record.requestUsageAccounting.pendingRequests = 0;
    record.requestUsageAccounting.incomplete = true;
  }
}

/** Preserve known legacy consumption when a resumed session switches to direct request receipts. */
export function initializeRequestUsageAccounting(record: UsageRecord): void {
  record.requestUsageAccounting ??= { startedRequests: 0, reportedRequests: 0, pendingRequests: 0,
    incomplete: Boolean(record.usageAccounting?.incomplete ||
      (record.usageAccounting && record.usageAccounting.startedTurns > record.usageAccounting.reportedTurns) ||
      (!record.usageAccounting && record.turns > 0)) };
}

/** Each lease represents exactly one attempted upstream request, independent of native thread counters. */
export function beginRequestUsage(record: UsageRecord): (receipt: ModelRequestReceipt) => void {
  const accounting = record.requestUsageAccounting!;
  accounting.startedRequests++;
  accounting.pendingRequests++;
  let settled = false;
  return receipt => {
    if (settled) return;
    settled = true;
    accounting.pendingRequests--;
    let valid = reportedTotalTokens(receipt.usage) !== null;
    const merged = { ...record.usage };
    for (const [key, value] of Object.entries(receipt.usage ?? {})) {
      const previous = merged[key] ?? 0;
      if (!count(value) || !count(previous) || !count(previous + value)) { valid = false; continue; }
      merged[key] = previous + value;
    }
    record.usage = merged;
    if (receipt.complete && valid) accounting.reportedRequests++;
    else accounting.incomplete = true;
  };
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
export function buildTokenBudget(maxTotalTokens: number, records: readonly UsageRecord[],
  enforcement: TokenBudget['enforcement'] = 'provider-observed-dispatch-limit'): TokenBudget {
  if (!count(maxTotalTokens)) throw new Error('invalid --max-total-tokens');
  let total = 0;
  let reported = false;
  let worked = false;
  let incomplete = false;
  let pending = false;
  for (const record of records) {
    const accounting = record.usageAccounting;
    const requests = record.requestUsageAccounting;
    const hadWork = requests ? requests.startedRequests > 0 || requests.incomplete
      : (accounting?.startedTurns ?? record.turns) > 0;
    const tokens = reportedTotalTokens(record.usage);
    worked ||= hadWork;
    incomplete ||= requests ? requests.incomplete || requests.startedRequests - requests.reportedRequests > requests.pendingRequests
      : Boolean(accounting?.incomplete || (!accounting && hadWork) ||
        (accounting && accounting.startedTurns - accounting.reportedTurns > Number(accounting.pending)));
    pending ||= requests ? requests.pendingRequests > 0 : Boolean(accounting?.pending);
    if (tokens !== null) { total += tokens; reported = true; }
  }
  if (!count(total)) { incomplete = true; reported = false; }
  const reportedTotal = count(total) && (reported || !worked) ? total : null;
  const status = !maxTotalTokens ? 'unlimited' : incomplete ? 'usage-unavailable' :
    reportedTotal !== null && reportedTotal >= maxTotalTokens ? 'exhausted' : 'available';
  return { maxTotalTokens, enforcement, status,
    reportedTotalTokens: reportedTotal, usageComplete: !incomplete && !pending,
    overrunTokens: reportedTotal === null ? null : maxTotalTokens ? Math.max(0, reportedTotal - maxTotalTokens) : 0,
    ...(status === 'exhausted' ? { reason: 'math_total_token_limit' as const } :
      status === 'usage-unavailable' ? { reason: 'math_model_usage_unavailable' as const } : {}) };
}

export const modelDispatchAllowed = (budget: TokenBudget): boolean =>
  budget.status === 'unlimited' || budget.status === 'available';
