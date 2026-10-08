/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  FINANCIAL_FACTOR_TIMESERIES_SCHEMA,
  buildInitialFinancialFactorPortfolio,
  isFinancialFactorPortfolio,
  isFinancialFactorTimeSeries,
  type FinancialFactorCandidate,
  type FinancialFactorCheck,
  type FinancialFactorMetric,
  type FinancialFactorPortfolio,
  type FinancialFactorPortfolioStatus,
  type FinancialFactorSeriesKind,
  type FinancialFactorStage,
  type FinancialFactorStatus,
  type FinancialFactorTimeSeries,
} from "./financialFactor";

export const FINANCIAL_FACTOR_IMPORT_TEMPLATE_NAME = 'deepscientist-factor-import-template.xlsx';
export const FINANCIAL_FACTOR_IMPORT_MIME = 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet';

export type FinancialFactorImportMode = 'merge' | 'replace';

export type FinancialFactorImportIssue = {
  severity: 'error' | 'warning';
  code: string;
  message: string;
  sheet?: string;
  row?: number;
  field?: string;
};

export type FinancialFactorImportSummary = {
  factorCount: number;
  newFactorCount: number;
  updatedFactorCount: number;
  metricCount: number;
  checkCount: number;
  runCount: number;
  seriesCount: number;
  pointCount: number;
  warningCount: number;
};

export type FinancialFactorImportResult = {
  valid: boolean;
  sourceName: string;
  portfolio?: FinancialFactorPortfolio;
  timeSeries: FinancialFactorTimeSeries[];
  issues: FinancialFactorImportIssue[];
  summary: FinancialFactorImportSummary;
};

export type ParseFinancialFactorImportOptions = {
  sourceName: string;
  projectRoot?: string;
  existingPortfolio?: FinancialFactorPortfolio;
  mode?: FinancialFactorImportMode;
  now?: number;
};

export type FinancialFactorImportRequest = {
  projectRoot: string;
  sourcePath: string;
  mode?: FinancialFactorImportMode;
};

export type FinancialFactorImportPreviewResponse = {
  valid: boolean;
  sourceName: string;
  issues: FinancialFactorImportIssue[];
  summary: FinancialFactorImportSummary;
};

export type FinancialFactorImportCommitResponse = FinancialFactorImportPreviewResponse & {
  portfolio: FinancialFactorPortfolio;
  writtenPaths: string[];
};

export type FinancialFactorImportTemplateResponse = {
  fileName: string;
  mimeType: string;
  contentBase64: string;
};

type Row = Record<string, unknown>;
type WorkbookRows = Partial<Record<'project' | 'factors' | 'metrics' | 'series' | 'checks', Row[]>>;

const FACTOR_STATUSES = new Set<FinancialFactorStatus>([
  'idea',
  'linted',
  'simulated',
  'qualified',
  'submit_pending',
  'active',
  'hold',
  'rejected',
  'failed',
]);
const PORTFOLIO_STATUSES = new Set<FinancialFactorPortfolioStatus>([
  'planning',
  'running',
  'needs_decision',
  'blocked',
  'complete',
]);
const STAGES = new Set<FinancialFactorStage>([
  'scope',
  'ideation',
  'linting',
  'simulation',
  'screening',
  'registration',
  'submission',
  'complete',
]);
const EVALUATION_RUNTIMES = new Set(['python', 'node', 'r', 'notebook']);

const isProjectRelativePath = (value: string): boolean =>
  Boolean(value.trim()) &&
  !value.startsWith('/') &&
  !/^[a-z]:[\\/]/iu.test(value) &&
  !value.split(/[\\/]+/u).includes('..') &&
  !value.includes('\0') &&
  !value.includes('\r') &&
  !value.includes('\n');
const SERIES_KINDS = new Set<FinancialFactorSeriesKind>([
  'cumulative_pnl',
  'benchmark',
  'rank_ic',
  'drawdown',
  'turnover',
  'exposure',
  'coverage',
  'other',
]);
const CHECK_STATUSES = new Set<FinancialFactorCheck['status']>(['passed', 'warning', 'failed', 'not_run']);
const SAFE_ID = /^[a-z0-9][a-z0-9._-]*$/iu;

const cleanHeader = (value: unknown): string =>
  String(value ?? '')
    .trim()
    .replace(/([a-z0-9])([A-Z])/gu, '$1_$2')
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '_')
    .replace(/^_+|_+$/gu, '');

const cleanRow = (row: Row): Row =>
  Object.fromEntries(Object.entries(row).map(([key, value]) => [cleanHeader(key), value]));

const textValue = (value: unknown): string => String(value ?? '').trim();

const optionalText = (value: unknown): string | undefined => {
  const text = textValue(value);
  return text || undefined;
};

const listValue = (value: unknown): string[] =>
  textValue(value)
    .split(/[;,|\n]/gu)
    .map((item) => item.trim())
    .filter(Boolean);

const numberValue = (value: unknown): number | undefined => {
  if (typeof value === 'number') return Number.isFinite(value) ? value : undefined;
  const text = textValue(value).replaceAll(',', '');
  if (!text) return undefined;
  const parsed = Number(text);
  return Number.isFinite(parsed) ? parsed : undefined;
};

const timestampValue = (value: unknown): string | undefined => {
  if (value instanceof Date && Number.isFinite(value.getTime())) return value.toISOString();
  const text = textValue(value);
  if (!text || !Number.isFinite(Date.parse(text))) return undefined;
  return text;
};

const sourceTitle = (sourceName: string): string =>
  sourceName
    .replace(/\.(csv|xlsx?|xlsm|ods)$/iu, '')
    .replaceAll(/[_-]+/gu, ' ')
    .trim() || 'Imported factor portfolio';

const issue = (
  issues: FinancialFactorImportIssue[],
  severity: FinancialFactorImportIssue['severity'],
  code: string,
  message: string,
  context: Pick<FinancialFactorImportIssue, 'sheet' | 'row' | 'field'> = {}
): void => {
  issues.push({ severity, code, message, ...context });
};

const requiredText = (
  row: Row,
  field: string,
  issues: FinancialFactorImportIssue[],
  sheet: string,
  rowNumber: number
): string | undefined => {
  const value = textValue(row[field]);
  if (!value) issue(issues, 'error', 'required_field', `${field} is required.`, { sheet, row: rowNumber, field });
  return value || undefined;
};

const worksheetKind = (name: string, rows: Row[]): keyof WorkbookRows | undefined => {
  const normalized = cleanHeader(name);
  if (['project', 'portfolio', 'context'].includes(normalized)) return 'project';
  if (['factors', 'factor', 'candidates'].includes(normalized)) return 'factors';
  if (['metrics', 'metric'].includes(normalized)) return 'metrics';
  if (['series', 'timeseries', 'time_series', 'performance'].includes(normalized)) return 'series';
  if (['checks', 'check', 'validations'].includes(normalized)) return 'checks';
  const headers = new Set(Object.keys(rows[0] || {}));
  if (headers.has('metric_name')) return 'metrics';
  if (headers.has('series_id') || headers.has('timestamp') || headers.has('date')) return 'series';
  if (headers.has('check_id') || headers.has('check_status')) return 'checks';
  if (headers.has('factor_id') && (headers.has('expression') || headers.has('hypothesis'))) return 'factors';
  return undefined;
};

const readWorkbookRows = async (
  data: ArrayBuffer | Uint8Array,
  sourceName: string,
  issues: FinancialFactorImportIssue[]
): Promise<WorkbookRows> => {
  const XLSX = await import('xlsx-republish');
  let workbook: import('xlsx-republish').WorkBook;
  try {
    workbook = XLSX.read(data, {
      type: data instanceof Uint8Array ? 'array' : 'array',
      cellDates: true,
      dense: false,
    });
  } catch (error) {
    issue(
      issues,
      'error',
      'invalid_workbook',
      `Unable to read ${sourceName}: ${error instanceof Error ? error.message : String(error)}`
    );
    return {};
  }
  const result: WorkbookRows = {};
  for (const sheetName of workbook.SheetNames) {
    const sheet = workbook.Sheets[sheetName];
    const rows = XLSX.utils.sheet_to_json<Row>(sheet, { defval: '', raw: true }).map(cleanRow);
    if (!rows.length) continue;
    const kind = worksheetKind(sheetName, rows);
    if (!kind) {
      issue(issues, 'warning', 'unknown_sheet', `Sheet "${sheetName}" was ignored because its purpose is unknown.`, {
        sheet: sheetName,
      });
      continue;
    }
    if (result[kind]) {
      issue(issues, 'warning', 'duplicate_sheet', `Additional ${kind} rows from "${sheetName}" were appended.`, {
        sheet: sheetName,
      });
    }
    result[kind] = [...(result[kind] || []), ...rows];
  }
  return result;
};

const applyProjectRow = (
  portfolio: FinancialFactorPortfolio,
  projectRow: Row | undefined,
  projectRoot: string | undefined,
  issues: FinancialFactorImportIssue[]
): void => {
  portfolio.context.projectRoot = projectRoot || portfolio.context.projectRoot;
  if (!projectRow) return;
  portfolio.title = optionalText(projectRow.title) || portfolio.title;
  portfolio.context.objective = optionalText(projectRow.objective) || portfolio.context.objective;
  portfolio.context.market = optionalText(projectRow.market) || portfolio.context.market;
  portfolio.context.region = optionalText(projectRow.region) || portfolio.context.region;
  portfolio.context.universe = optionalText(projectRow.universe) || portfolio.context.universe;
  portfolio.context.dataFamilies = listValue(projectRow.data_families).length
    ? listValue(projectRow.data_families)
    : portfolio.context.dataFamilies;
  const delay = numberValue(projectRow.delay);
  if (delay != null) portfolio.context.delay = delay;
  const executionMode = optionalText(projectRow.execution_mode);
  if (executionMode) {
    if (executionMode === 'manual' || executionMode === 'continuous') portfolio.context.executionMode = executionMode;
    else
      issue(issues, 'error', 'invalid_execution_mode', `Unsupported execution_mode: ${executionMode}`, {
        sheet: 'Project',
        row: 2,
      });
  }
  const automationPolicy = optionalText(projectRow.automation_policy);
  if (automationPolicy) {
    if (automationPolicy === 'verify_only' || automationPolicy === 'submit_qualified')
      portfolio.context.automationPolicy = automationPolicy;
    else
      issue(issues, 'error', 'invalid_automation_policy', `Unsupported automation_policy: ${automationPolicy}`, {
        sheet: 'Project',
        row: 2,
      });
  }
  const stage = optionalText(projectRow.stage);
  if (stage) {
    if (STAGES.has(stage as FinancialFactorStage)) portfolio.stage = stage as FinancialFactorStage;
    else issue(issues, 'error', 'invalid_stage', `Unsupported portfolio stage: ${stage}`, { sheet: 'Project', row: 2 });
  }
  const status = optionalText(projectRow.status);
  if (status) {
    if (PORTFOLIO_STATUSES.has(status as FinancialFactorPortfolioStatus))
      portfolio.status = status as FinancialFactorPortfolioStatus;
    else
      issue(issues, 'error', 'invalid_portfolio_status', `Unsupported portfolio status: ${status}`, {
        sheet: 'Project',
        row: 2,
      });
  }
};

const parseFactors = (
  rows: Row[],
  existing: Map<string, FinancialFactorCandidate>,
  now: number,
  issues: FinancialFactorImportIssue[]
): {
  factors: Map<string, FinancialFactorCandidate>;
  importedIds: Set<string>;
  newCount: number;
  updatedCount: number;
} => {
  const factors = new Map(existing);
  const importedIds = new Set<string>();
  let newCount = 0;
  let updatedCount = 0;
  rows.forEach((row, index) => {
    const rowNumber = index + 2;
    const id = requiredText(row, 'factor_id', issues, 'Factors', rowNumber);
    if (!id) return;
    if (!SAFE_ID.test(id)) {
      issue(
        issues,
        'error',
        'unsafe_factor_id',
        'factor_id may contain only letters, numbers, dots, underscores, and hyphens.',
        {
          sheet: 'Factors',
          row: rowNumber,
          field: 'factor_id',
        }
      );
      return;
    }
    if (importedIds.has(id)) {
      issue(issues, 'error', 'duplicate_factor', `factor_id ${id} appears more than once.`, {
        sheet: 'Factors',
        row: rowNumber,
        field: 'factor_id',
      });
      return;
    }
    importedIds.add(id);
    const previous = factors.get(id);
    const name = requiredText(row, 'name', issues, 'Factors', rowNumber);
    const expression = requiredText(row, 'expression', issues, 'Factors', rowNumber);
    const hypothesis = requiredText(row, 'hypothesis', issues, 'Factors', rowNumber);
    const selectionReason = requiredText(row, 'selection_reason', issues, 'Factors', rowNumber);
    const decisionReason = requiredText(row, 'decision_reason', issues, 'Factors', rowNumber);
    const rawStatus = requiredText(row, 'status', issues, 'Factors', rowNumber);
    if (!name || !expression || !hypothesis || !selectionReason || !decisionReason || !rawStatus) return;
    if (!FACTOR_STATUSES.has(rawStatus as FinancialFactorStatus)) {
      issue(issues, 'error', 'invalid_factor_status', `Unsupported factor status: ${rawStatus}`, {
        sheet: 'Factors',
        row: rowNumber,
        field: 'status',
      });
      return;
    }
    const updatedAt = timestampValue(row.updated_at);
    const factor: FinancialFactorCandidate = {
      ...previous,
      id,
      name,
      expression,
      family: optionalText(row.family),
      hypothesis,
      selectionReason,
      decisionReason,
      status: rawStatus as FinancialFactorStatus,
      checks: previous?.checks || [],
      evidenceIds: listValue(row.evidence_ids),
      updatedAt: updatedAt ? Date.parse(updatedAt) : now,
    };
    const contractId = optionalText(row.contract_id);
    const evaluationId = optionalText(row.evaluation_id);
    const evaluationCodePath = optionalText(row.evaluation_code_path);
    const evaluationRuntime = optionalText(row.evaluation_runtime)?.toLocaleLowerCase();
    const evaluationEntrypoint = optionalText(row.evaluation_entrypoint);
    const hasEvaluationCode = Boolean(evaluationCodePath || evaluationRuntime || evaluationEntrypoint);
    if (contractId || evaluationId || hasEvaluationCode) {
      if (!contractId || !evaluationId) {
        issue(
          issues,
          'error',
          'incomplete_metric_context',
          'contract_id and evaluation_id must be provided together.',
          {
            sheet: 'Factors',
            row: rowNumber,
          }
        );
      } else if (hasEvaluationCode && !evaluationCodePath) {
        issue(
          issues,
          'error',
          'missing_evaluation_code_path',
          'evaluation_code_path is required for evaluator metadata.',
          {
            sheet: 'Factors',
            row: rowNumber,
            field: 'evaluation_code_path',
          }
        );
      } else if (evaluationCodePath && !isProjectRelativePath(evaluationCodePath)) {
        issue(
          issues,
          'error',
          'invalid_evaluation_code_path',
          'evaluation_code_path must be a project-relative path without parent traversal.',
          {
            sheet: 'Factors',
            row: rowNumber,
            field: 'evaluation_code_path',
          }
        );
      } else if (evaluationRuntime && !EVALUATION_RUNTIMES.has(evaluationRuntime)) {
        issue(
          issues,
          'error',
          'invalid_evaluation_runtime',
          'evaluation_runtime must be python, node, r, or notebook.',
          {
            sheet: 'Factors',
            row: rowNumber,
            field: 'evaluation_runtime',
          }
        );
      } else {
        factor.metricContext = {
          ...previous?.metricContext,
          contractId,
          evaluationId,
          dataset: optionalText(row.dataset),
          sampleStart: timestampValue(row.sample_start),
          sampleEnd: timestampValue(row.sample_end),
          costModel: optionalText(row.cost_model),
          baselineCommit: optionalText(row.baseline_commit),
          ...(evaluationCodePath
            ? {
                evaluationCode: {
                  path: evaluationCodePath,
                  ...(evaluationRuntime ? { runtime: evaluationRuntime as 'python' | 'node' | 'r' | 'notebook' } : {}),
                  ...(evaluationEntrypoint ? { entrypoint: evaluationEntrypoint } : {}),
                },
              }
            : {}),
        };
      }
    }
    factors.set(id, factor);
    if (previous) updatedCount += 1;
    else newCount += 1;
  });
  return { factors, importedIds, newCount, updatedCount };
};

const requireFactor = (
  row: Row,
  factors: Map<string, FinancialFactorCandidate>,
  issues: FinancialFactorImportIssue[],
  sheet: string,
  rowNumber: number
): FinancialFactorCandidate | undefined => {
  const factorId = requiredText(row, 'factor_id', issues, sheet, rowNumber);
  if (!factorId) return undefined;
  const factor = factors.get(factorId);
  if (!factor)
    issue(
      issues,
      'error',
      'unknown_factor',
      `factor_id ${factorId} is not present in Factors or the existing portfolio.`,
      { sheet, row: rowNumber, field: 'factor_id' }
    );
  return factor;
};

const ensureMetricContext = (
  factor: FinancialFactorCandidate,
  row: Row,
  issues: FinancialFactorImportIssue[],
  sheet: string,
  rowNumber: number
): boolean => {
  const contractId = optionalText(row.contract_id) || factor.metricContext?.contractId;
  const evaluationId = optionalText(row.evaluation_id) || factor.metricContext?.evaluationId;
  if (!contractId || !evaluationId) {
    issue(
      issues,
      'error',
      'missing_metric_context',
      'Measured metrics and series require contract_id and evaluation_id.',
      {
        sheet,
        row: rowNumber,
      }
    );
    return false;
  }
  if (
    factor.metricContext &&
    (factor.metricContext.contractId !== contractId || factor.metricContext.evaluationId !== evaluationId)
  ) {
    issue(issues, 'error', 'metric_context_conflict', `Metric context conflicts with factor ${factor.id}.`, {
      sheet,
      row: rowNumber,
    });
    return false;
  }
  factor.metricContext = { ...factor.metricContext, contractId, evaluationId };
  return true;
};

const applyMetrics = (
  rows: Row[],
  factors: Map<string, FinancialFactorCandidate>,
  issues: FinancialFactorImportIssue[]
): number => {
  const metricsByFactor = new Map<string, Map<string, FinancialFactorMetric>>();
  rows.forEach((row, index) => {
    const rowNumber = index + 2;
    const factor = requireFactor(row, factors, issues, 'Metrics', rowNumber);
    const name = requiredText(row, 'metric_name', issues, 'Metrics', rowNumber);
    const value = numberValue(row.value);
    if (value == null)
      issue(issues, 'error', 'invalid_number', 'Metric value must be a finite number.', {
        sheet: 'Metrics',
        row: rowNumber,
        field: 'value',
      });
    if (!factor || !name || value == null || !ensureMetricContext(factor, row, issues, 'Metrics', rowNumber)) return;
    const direction = optionalText(row.direction);
    if (direction && direction !== 'maximize' && direction !== 'minimize') {
      issue(issues, 'error', 'invalid_metric_direction', `Unsupported metric direction: ${direction}`, {
        sheet: 'Metrics',
        row: rowNumber,
        field: 'direction',
      });
      return;
    }
    const metrics = metricsByFactor.get(factor.id) || new Map<string, FinancialFactorMetric>();
    if (metrics.has(name))
      issue(issues, 'warning', 'duplicate_metric', `The last ${name} value for ${factor.id} was used.`, {
        sheet: 'Metrics',
        row: rowNumber,
      });
    metrics.set(name, {
      name,
      value,
      unit: optionalText(row.unit),
      direction: direction as FinancialFactorMetric['direction'],
      evidenceIds: listValue(row.evidence_ids),
    });
    metricsByFactor.set(factor.id, metrics);
  });
  let count = 0;
  for (const [factorId, metrics] of metricsByFactor) {
    const factor = factors.get(factorId);
    if (!factor) continue;
    factor.metrics = [...metrics.values()];
    count += factor.metrics.length;
  }
  return count;
};

const applyChecks = (
  rows: Row[],
  factors: Map<string, FinancialFactorCandidate>,
  issues: FinancialFactorImportIssue[]
): number => {
  const checksByFactor = new Map<string, Map<string, FinancialFactorCheck>>();
  rows.forEach((row, index) => {
    const rowNumber = index + 2;
    const factor = requireFactor(row, factors, issues, 'Checks', rowNumber);
    const id = requiredText(row, 'check_id', issues, 'Checks', rowNumber);
    const label = requiredText(row, 'label', issues, 'Checks', rowNumber);
    const rawStatus = requiredText(row, 'status', issues, 'Checks', rowNumber);
    if (!factor || !id || !label || !rawStatus) return;
    if (!SAFE_ID.test(id) || !CHECK_STATUSES.has(rawStatus as FinancialFactorCheck['status'])) {
      issue(issues, 'error', 'invalid_check', `Invalid check_id or status for ${factor.id}.`, {
        sheet: 'Checks',
        row: rowNumber,
      });
      return;
    }
    const rawValue = row.value;
    const rawThreshold = row.threshold;
    const checks = checksByFactor.get(factor.id) || new Map<string, FinancialFactorCheck>();
    checks.set(id, {
      id,
      label,
      status: rawStatus as FinancialFactorCheck['status'],
      value: numberValue(rawValue) ?? optionalText(rawValue),
      threshold: numberValue(rawThreshold) ?? optionalText(rawThreshold),
      detail: optionalText(row.detail),
      evidenceIds: listValue(row.evidence_ids),
    });
    checksByFactor.set(factor.id, checks);
  });
  let count = 0;
  for (const [factorId, checks] of checksByFactor) {
    const factor = factors.get(factorId);
    if (!factor) continue;
    factor.checks = [...checks.values()];
    count += factor.checks.length;
  }
  return count;
};

type SeriesGroup = {
  factor: FinancialFactorCandidate;
  runId: string;
  contractId: string;
  evaluationId: string;
  frequency: string;
  generatedAt: number;
  items: Map<
    string,
    { label: string; kind: FinancialFactorSeriesKind; unit?: string; points: Array<[string, number]> }
  >;
};

const parseSeries = (
  rows: Row[],
  factors: Map<string, FinancialFactorCandidate>,
  now: number,
  issues: FinancialFactorImportIssue[]
): FinancialFactorTimeSeries[] => {
  const groups = new Map<string, SeriesGroup>();
  rows.forEach((row, index) => {
    const rowNumber = index + 2;
    const factor = requireFactor(row, factors, issues, 'Series', rowNumber);
    const runId = requiredText(row, 'run_id', issues, 'Series', rowNumber);
    const timestamp = timestampValue(row.timestamp ?? row.date);
    const seriesId = requiredText(row, 'series_id', issues, 'Series', rowNumber);
    const rawKind = requiredText(row, 'series_kind', issues, 'Series', rowNumber);
    const value = numberValue(row.value);
    const frequency = requiredText(row, 'frequency', issues, 'Series', rowNumber);
    if (!timestamp)
      issue(issues, 'error', 'invalid_timestamp', 'date or timestamp must be a valid date.', {
        sheet: 'Series',
        row: rowNumber,
        field: 'date',
      });
    if (value == null)
      issue(issues, 'error', 'invalid_number', 'Series value must be a finite number.', {
        sheet: 'Series',
        row: rowNumber,
        field: 'value',
      });
    if (!factor || !runId || !timestamp || !seriesId || !rawKind || value == null || !frequency) return;
    if (!SAFE_ID.test(runId) || !SAFE_ID.test(seriesId) || !SERIES_KINDS.has(rawKind as FinancialFactorSeriesKind)) {
      issue(issues, 'error', 'invalid_series_identity', 'run_id, series_id, or series_kind is invalid.', {
        sheet: 'Series',
        row: rowNumber,
      });
      return;
    }
    if (!ensureMetricContext(factor, row, issues, 'Series', rowNumber)) return;
    const contractId = factor.metricContext?.contractId as string;
    const evaluationId = factor.metricContext?.evaluationId as string;
    const key = `${factor.id}\u0000${runId}`;
    const previous = groups.get(key);
    if (
      previous &&
      (previous.contractId !== contractId || previous.evaluationId !== evaluationId || previous.frequency !== frequency)
    ) {
      issue(
        issues,
        'error',
        'series_context_conflict',
        `Rows for ${factor.id}/${runId} use inconsistent evaluation context.`,
        { sheet: 'Series', row: rowNumber }
      );
      return;
    }
    const group: SeriesGroup = previous || {
      factor,
      runId,
      contractId,
      evaluationId,
      frequency,
      generatedAt: timestampValue(row.generated_at) ? Date.parse(timestampValue(row.generated_at) as string) : now,
      items: new Map(),
    };
    const item = group.items.get(seriesId) || {
      label: optionalText(row.series_label) || seriesId,
      kind: rawKind as FinancialFactorSeriesKind,
      unit: optionalText(row.unit),
      points: [],
    };
    if (item.kind !== rawKind) {
      issue(issues, 'error', 'series_kind_conflict', `series_id ${seriesId} uses multiple kinds.`, {
        sheet: 'Series',
        row: rowNumber,
      });
      return;
    }
    item.points.push([timestamp, value]);
    group.items.set(seriesId, item);
    groups.set(key, group);
  });

  const result: FinancialFactorTimeSeries[] = [];
  for (const group of groups.values()) {
    if (group.items.size > 16) {
      issue(issues, 'error', 'too_many_series', `${group.factor.id}/${group.runId} contains more than 16 series.`, {
        sheet: 'Series',
      });
      continue;
    }
    for (const [seriesId, item] of group.items) {
      item.points.sort((left, right) => Date.parse(left[0]) - Date.parse(right[0]));
      if (new Set(item.points.map(([timestamp]) => Date.parse(timestamp))).size !== item.points.length) {
        issue(
          issues,
          'error',
          'duplicate_timestamp',
          `${group.factor.id}/${group.runId}/${seriesId} contains duplicate timestamps.`,
          { sheet: 'Series' }
        );
      }
    }
    const series: FinancialFactorTimeSeries = {
      schema: FINANCIAL_FACTOR_TIMESERIES_SCHEMA,
      version: 1,
      factorId: group.factor.id,
      runId: group.runId,
      contractId: group.contractId,
      evaluationId: group.evaluationId,
      frequency: group.frequency,
      generatedAt: group.generatedAt,
      series: [...group.items.entries()].map(([id, item]) => ({
        id,
        label: item.label,
        kind: item.kind,
        unit: item.unit,
        points: item.points,
      })),
    };
    if (!isFinancialFactorTimeSeries(series)) {
      issue(
        issues,
        'error',
        'invalid_series',
        `${group.factor.id}/${group.runId} does not satisfy the time-series contract.`,
        { sheet: 'Series' }
      );
      continue;
    }
    const artifactId = `financial_factor_series_${group.factor.id}_${group.runId}`;
    const path = `factor-research/factors/${group.factor.id}/runs/${group.runId}/result.json`;
    group.factor.artifacts = [
      ...(group.factor.artifacts || []).filter(
        (artifact) => !(artifact.role === 'timeseries' && artifact.runId === group.runId)
      ),
      {
        artifactId,
        artifactVersion: 1,
        role: 'timeseries',
        label: `${group.runId} · ${group.frequency}`,
        path,
        runId: group.runId,
        generatedAt: group.generatedAt,
        evidenceIds: group.factor.evidenceIds,
      },
    ];
    group.factor.updatedAt = Math.max(group.factor.updatedAt, group.generatedAt);
    result.push(series);
  }
  return result;
};

export async function parseFinancialFactorImport(
  data: ArrayBuffer | Uint8Array,
  options: ParseFinancialFactorImportOptions
): Promise<FinancialFactorImportResult> {
  const issues: FinancialFactorImportIssue[] = [];
  const rows = await readWorkbookRows(data, options.sourceName, issues);
  const now = options.now ?? Date.now();
  const mode = options.mode || 'merge';
  const existing = mode === 'merge' ? options.existingPortfolio : undefined;
  const portfolio = existing
    ? structuredClone(existing)
    : buildInitialFinancialFactorPortfolio({
        title: sourceTitle(options.sourceName),
        objective: 'Imported factor research',
        projectRoot: options.projectRoot,
        updatedAt: now,
      });
  applyProjectRow(portfolio, rows.project?.[0], options.projectRoot, issues);
  if (!rows.factors?.length && !existing) {
    issue(issues, 'error', 'missing_factors_sheet', 'A new import requires a non-empty Factors sheet.');
  }
  const existingFactors = new Map((existing?.factors || []).map((factor) => [factor.id, structuredClone(factor)]));
  const parsedFactors = parseFactors(rows.factors || [], existingFactors, now, issues);
  const metricCount = applyMetrics(rows.metrics || [], parsedFactors.factors, issues);
  const checkCount = applyChecks(rows.checks || [], parsedFactors.factors, issues);
  const timeSeries = parseSeries(rows.series || [], parsedFactors.factors, now, issues);
  portfolio.factors = [...parsedFactors.factors.values()];
  portfolio.updatedAt = Math.max(now, ...portfolio.factors.map((factor) => factor.updatedAt));
  if (!rows.project?.[0]?.stage)
    portfolio.stage = timeSeries.length ? 'screening' : portfolio.factors.length ? 'ideation' : 'scope';
  if (!rows.project?.[0]?.status) portfolio.status = portfolio.factors.length ? 'running' : 'planning';
  if (
    portfolio.nextActions.length === 1 &&
    portfolio.nextActions[0]?.id === 'define-factor-scope' &&
    portfolio.factors.length
  ) {
    portfolio.nextActions = [
      {
        id: timeSeries.length ? 'review-imported-results' : 'run-comparable-backtest',
        label: timeSeries.length ? 'Review imported factor results' : 'Run a comparable factor backtest',
        kind: timeSeries.length ? 'decision' : 'verification',
        priority: 'now',
        owner: 'user',
      },
    ];
  }
  if (!isFinancialFactorPortfolio(portfolio)) {
    issue(
      issues,
      'error',
      'invalid_portfolio',
      'The imported data could not be converted into a valid factor portfolio.'
    );
  }
  const pointCount = timeSeries.reduce(
    (total, run) => total + run.series.reduce((seriesTotal, item) => seriesTotal + item.points.length, 0),
    0
  );
  const summary: FinancialFactorImportSummary = {
    factorCount: parsedFactors.importedIds.size || portfolio.factors.length,
    newFactorCount: parsedFactors.newCount,
    updatedFactorCount: parsedFactors.updatedCount,
    metricCount,
    checkCount,
    runCount: timeSeries.length,
    seriesCount: timeSeries.reduce((total, run) => total + run.series.length, 0),
    pointCount,
    warningCount: issues.filter((item) => item.severity === 'warning').length,
  };
  const valid = !issues.some((item) => item.severity === 'error');
  return {
    valid,
    sourceName: options.sourceName,
    portfolio: valid ? portfolio : undefined,
    timeSeries: valid ? timeSeries : [],
    issues,
    summary,
  };
}

export async function buildFinancialFactorImportTemplate(): Promise<Uint8Array> {
  const XLSX = await import('xlsx-republish');
  const workbook = XLSX.utils.book_new();
  const append = (name: string, rows: Row[]): void => {
    XLSX.utils.book_append_sheet(workbook, XLSX.utils.json_to_sheet(rows), name);
  };
  append('Project', [
    {
      title: 'Example factor portfolio',
      objective: 'Find robust, reproducible alpha factors',
      stage: 'screening',
      status: 'running',
      execution_mode: 'manual',
      automation_policy: 'verify_only',
      market: 'Equity',
      region: 'Global',
      universe: 'Research universe',
      delay: 1,
      data_families: 'price; fundamentals',
    },
  ]);
  append('Factors', [
    {
      factor_id: 'quality_value_v1',
      name: 'Quality value',
      family: 'fundamental',
      expression: 'rank(book_to_price) * rank(roe)',
      hypothesis: 'Cheap profitable companies may earn a persistent premium.',
      selection_reason: 'Combines complementary value and quality mechanisms.',
      decision_reason: 'Ready for comparable validation.',
      status: 'simulated',
      contract_id: 'global-equity-v1',
      evaluation_id: 'eval-2026-07',
      evaluation_code_path: 'factor-research/evaluators/quality_value.py',
      evaluation_runtime: 'python',
      evaluation_entrypoint: 'evaluate',
      evidence_ids: 'backtest-log-1',
      updated_at: '2026-07-22T00:00:00Z',
    },
  ]);
  append('Metrics', [
    {
      factor_id: 'quality_value_v1',
      metric_name: 'Sharpe',
      value: 1.42,
      unit: 'ratio',
      direction: 'maximize',
      contract_id: 'global-equity-v1',
      evaluation_id: 'eval-2026-07',
      evidence_ids: 'backtest-log-1',
    },
  ]);
  append('Series', [
    {
      factor_id: 'quality_value_v1',
      run_id: 'backtest_20260722',
      date: '2026-07-01',
      series_id: 'factor_pnl',
      series_label: 'Factor',
      series_kind: 'cumulative_pnl',
      value: 0.01,
      unit: 'ratio',
      frequency: 'daily',
      contract_id: 'global-equity-v1',
      evaluation_id: 'eval-2026-07',
      generated_at: '2026-07-22T00:00:00Z',
    },
    {
      factor_id: 'quality_value_v1',
      run_id: 'backtest_20260722',
      date: '2026-07-02',
      series_id: 'factor_pnl',
      series_label: 'Factor',
      series_kind: 'cumulative_pnl',
      value: 0.018,
      unit: 'ratio',
      frequency: 'daily',
      contract_id: 'global-equity-v1',
      evaluation_id: 'eval-2026-07',
      generated_at: '2026-07-22T00:00:00Z',
    },
  ]);
  append('Checks', [
    {
      factor_id: 'quality_value_v1',
      check_id: 'turnover',
      label: 'Turnover limit',
      status: 'passed',
      value: 0.18,
      threshold: '<=0.25',
      detail: 'Measured on the same evaluation contract.',
      evidence_ids: 'backtest-log-1',
    },
  ]);
  return XLSX.write(workbook, { type: 'array', bookType: 'xlsx' }) as Uint8Array;
}
