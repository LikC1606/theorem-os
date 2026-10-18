import type { WebRun } from './shared';

export type ReportTone = 'passed' | 'failed' | 'warning' | 'muted';
export type ReportDiagnostic = { label: string; text: string; truncated: boolean };
export type ReportTarget = {
  name: string;
  status: string;
  tone: ReportTone;
  sorryCount?: number;
  admitCount?: number;
  diagnostics: ReportDiagnostic[];
};
export type ReportCheck = {
  id: 'candidate' | 'evaluation';
  label: string;
  status: string;
  tone: ReportTone;
  method?: string;
  reason?: string;
  targets: ReportTarget[];
  omittedTargets: number;
};
export type ReportSummary = {
  reason?: string;
  checks: ReportCheck[];
  metrics: { label: string; value: string }[];
  identity: { label: string; value: string }[];
};

const maximumText = 4_000;
const maximumTargets = 64;
type Status = Pick<ReportTarget, 'status' | 'tone'>;
const targetStatuses = new Map<string, Status>([
  ['kernel_verified', { status: 'Lean 内核通过', tone: 'passed' }],
  ['failed', { status: '检查未通过', tone: 'failed' }],
  ['blocked', { status: '检查受阻', tone: 'warning' }],
  ['unavailable', { status: '检查不可用', tone: 'warning' }],
]);
const evaluationStatuses = new Map<string, Status>([
  ['passed', { status: '验收阶段通过', tone: 'passed' }],
  ['failed', { status: '验收阶段未通过', tone: 'failed' }],
  ['error', { status: '验收阶段错误', tone: 'failed' }],
  ['skipped', { status: '已跳过', tone: 'muted' }],
]);
const evaluationMethods = new Map<string, string>([
  ['host-lean-kernel-all-targets', 'Lean 内核 · 全部目标'],
  ['external-command', '外部命令'],
  ['official-comparator', '官方比较器'],
]);

function object(value: unknown): Record<string, unknown> | undefined {
  return value !== null && typeof value === 'object' && !Array.isArray(value)
    ? value as Record<string, unknown> : undefined;
}

function text(value: unknown): string | undefined {
  return typeof value === 'string' && value.trim() ? value.slice(0, maximumText) : undefined;
}

function nonnegative(value: unknown): number | undefined {
  return typeof value === 'number' && Number.isFinite(value) && value >= 0 ? value : undefined;
}

function nonnegativeInteger(value: unknown): number | undefined {
  return typeof value === 'number' && Number.isSafeInteger(value) && value >= 0 ? value : undefined;
}

function status(value: string | undefined, labels: ReadonlyMap<string, Status>): Status {
  return value ? labels.get(value) ?? { status: value, tone: 'muted' }
    : { status: '未提供状态', tone: 'muted' };
}

function diagnostics(row: Record<string, unknown>): ReportDiagnostic[] {
  const result: ReportDiagnostic[] = [];
  const seen = new Set<string>();
  for (const [key, label] of [['error', '错误'], ['stdoutPreview', '标准输出'], ['stderrPreview', '标准错误']]) {
    const raw = row[key];
    const value = typeof raw === 'string' ? raw.trim() : '';
    if (!value || seen.has(value)) continue;
    seen.add(value);
    result.push({ label, text: value.slice(0, maximumText), truncated: value.length > maximumText });
  }
  return result;
}

function targets(value: unknown): Pick<ReportCheck, 'targets' | 'omittedTargets'> {
  const result: ReportTarget[] = [];
  let omittedTargets = 0;
  if (!Array.isArray(value)) return { targets: result, omittedTargets };
  for (const item of value) {
    const row = object(item);
    if (!row) continue;
    const name = text(row.theoremName), rawStatus = text(row.status);
    const sorryCount = nonnegativeInteger(row.sorryCount), admitCount = nonnegativeInteger(row.admitCount);
    const messages = diagnostics(row);
    if (!name && !rawStatus && sorryCount === undefined && admitCount === undefined && !messages.length) continue;
    if (result.length === maximumTargets) { omittedTargets++; continue; }
    result.push({ name: name ?? '未命名目标', ...status(rawStatus, targetStatuses),
      ...(sorryCount !== undefined ? { sorryCount } : {}),
      ...(admitCount !== undefined ? { admitCount } : {}), diagnostics: messages });
  }
  return { targets: result, omittedTargets };
}

export function summarizeReport(run: WebRun): ReportSummary {
  const record = object(run), result = object(record?.result), report = object(result?.report);
  const candidate = object(report?.candidateCheck), evaluator = object(report?.evaluator);
  const finalCheck = object(evaluator?.verification), finalBatch = object(finalCheck?.verification);
  const candidateTargets = targets(candidate?.results), evaluationTargets = targets(finalBatch?.results);
  const candidatePassed = typeof candidate?.passed === 'boolean' ? candidate.passed
    : typeof report?.solver_ready_receipt_valid === 'boolean' ? report.solver_ready_receipt_valid : undefined;
  const candidateStatus = text(candidate?.status), evaluationStatus = text(evaluator?.status);
  const method = text(evaluator?.method), evaluationReason = text(evaluator?.reason);
  const evaluationTimedOut = evaluator?.timedOut === true;
  const checks: ReportCheck[] = [];
  if (candidatePassed !== undefined || candidateStatus || candidateTargets.targets.length) {
    checks.push({ id: 'candidate', label: '候选检查',
      ...(candidatePassed === undefined ? status(candidateStatus, targetStatuses)
        : { status: candidatePassed ? '候选检查通过' : '候选检查未通过', tone: candidatePassed ? 'passed' : 'failed' }),
      ...candidateTargets });
  }
  if (evaluationStatus || method || evaluationReason || evaluationTimedOut || evaluationTargets.targets.length) {
    const evaluationState: Status = evaluationTimedOut ? { status: '验收超时', tone: 'failed' }
      : status(evaluationStatus, evaluationStatuses);
    checks.push({ id: 'evaluation', label: '独立验收', ...evaluationState,
      ...(method ? { method: evaluationMethods.get(method) ?? method } : {}),
      ...(evaluationReason ? { reason: evaluationReason } : {}), ...evaluationTargets });
  }
  const metrics: ReportSummary['metrics'] = [];
  const turns = nonnegativeInteger(report?.turns), solveWallMs = nonnegative(report?.solveWallMs);
  const totalTokens = nonnegativeInteger(object(report?.usage)?.totalTokens);
  if (turns !== undefined) metrics.push({ label: '研究轮次', value: String(turns) });
  if (solveWallMs !== undefined) metrics.push({ label: '求解耗时', value: `${solveWallMs / 1_000} 秒` });
  if (totalTokens !== undefined) metrics.push({ label: '总 Token', value: String(totalTokens) });
  const environment = object(report?.environment);
  const identity: ReportSummary['identity'] = [];
  for (const [label, value] of [
    ['求解运行 ID', report?.runId], ['题目 ID', report?.problemId], ['候选提交', report?.solution_commit],
    ['验收提交', finalCheck?.commit], ['验收源码摘要', finalCheck?.sourceDigest],
    ['Lean 工具链', environment?.toolchain], ['依赖摘要', environment?.dependencyDigest],
    ['Mathlib 版本', environment?.mathlibRevision],
  ]) {
    const content = text(value);
    if (content) identity.push({ label: String(label), value: content });
  }
  const reason = text(report?.reason) ?? text(record?.error);
  return { ...(reason ? { reason } : {}), checks, metrics, identity };
}
