/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import {
  FINANCIAL_FACTOR_PORTFOLIO_PATH,
  assertFinancialFactorPromotionMutation,
  readFinancialFactorPortfolio,
  type FinancialFactorPortfolio,
} from "../../common/chat/financialFactor";
import {
  buildFinancialFactorImportTemplate,
  FINANCIAL_FACTOR_IMPORT_MIME,
  FINANCIAL_FACTOR_IMPORT_TEMPLATE_NAME,
  parseFinancialFactorImport,
  type FinancialFactorImportCommitResponse,
  type FinancialFactorImportIssue,
  type FinancialFactorImportMode,
  type FinancialFactorImportPreviewResponse,
  type FinancialFactorImportResult,
  type FinancialFactorImportTemplateResponse,
} from "../../common/chat/financialFactorImport";

const MAX_IMPORT_BYTES = 20 * 1024 * 1024;
const ALLOWED_EXTENSIONS = new Set(['.csv', '.xls', '.xlsx', '.xlsm', '.ods']);

type LoadFinancialFactorImportOptions = {
  projectRoot: string;
  sourcePath: string;
  mode?: FinancialFactorImportMode;
  requireSourceInProject?: boolean;
};

export type FinancialFactorProjectPortfolioSnapshot =
  | { status: 'missing'; path: string }
  | { status: 'invalid'; path: string }
  | { status: 'ready'; path: string; portfolio: FinancialFactorPortfolio };

const emptySummary = (): FinancialFactorImportPreviewResponse['summary'] => ({
  factorCount: 0,
  newFactorCount: 0,
  updatedFactorCount: 0,
  metricCount: 0,
  checkCount: 0,
  runCount: 0,
  seriesCount: 0,
  pointCount: 0,
  warningCount: 0,
});

const invalidResult = (sourceName: string, item: FinancialFactorImportIssue): FinancialFactorImportResult => ({
  valid: false,
  sourceName,
  timeSeries: [],
  issues: [item],
  summary: emptySummary(),
});

const resolveProjectRoot = (candidate: string): string => {
  if (!candidate || candidate.includes('\0') || !path.isAbsolute(candidate)) {
    throw new Error('projectRoot must be an absolute local directory.');
  }
  const resolved = path.resolve(candidate);
  if (!fs.existsSync(resolved) || !fs.statSync(resolved).isDirectory()) {
    throw new Error('projectRoot does not exist or is not a directory.');
  }
  return resolved;
};

const isPathInside = (root: string, candidate: string): boolean => {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative));
};

export const readFinancialFactorProjectPortfolio = (projectRoot: string): FinancialFactorProjectPortfolioSnapshot => {
  const resolvedRoot = resolveProjectRoot(projectRoot);
  const portfolioPath = path.join(resolvedRoot, FINANCIAL_FACTOR_PORTFOLIO_PATH);
  if (!fs.existsSync(portfolioPath)) return { status: 'missing', path: FINANCIAL_FACTOR_PORTFOLIO_PATH };
  try {
    const portfolio = readFinancialFactorPortfolio(JSON.parse(fs.readFileSync(portfolioPath, 'utf8')));
    return portfolio
      ? { status: 'ready', path: FINANCIAL_FACTOR_PORTFOLIO_PATH, portfolio }
      : { status: 'invalid', path: FINANCIAL_FACTOR_PORTFOLIO_PATH };
  } catch {
    return { status: 'invalid', path: FINANCIAL_FACTOR_PORTFOLIO_PATH };
  }
};

const readExistingPortfolio = (projectRoot: string): FinancialFactorPortfolio | undefined | null => {
  const snapshot = readFinancialFactorProjectPortfolio(projectRoot);
  if (snapshot.status === 'missing') return undefined;
  return snapshot.status === 'ready' ? snapshot.portfolio : null;
};

export async function loadFinancialFactorImport(
  options: LoadFinancialFactorImportOptions
): Promise<FinancialFactorImportResult> {
  const projectRoot = resolveProjectRoot(options.projectRoot);
  const sourcePath = path.resolve(options.sourcePath);
  const sourceName = path.basename(sourcePath);
  if (options.requireSourceInProject && !isPathInside(projectRoot, sourcePath)) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'source_outside_project',
      message: 'sourcePath must stay inside projectRoot when called by an Agent.',
    });
  }
  if (!ALLOWED_EXTENSIONS.has(path.extname(sourcePath).toLowerCase())) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'unsupported_file_type',
      message: 'Supported import files are CSV, XLS, XLSX, XLSM, and ODS.',
    });
  }
  if (!fs.existsSync(sourcePath) || !fs.statSync(sourcePath).isFile()) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'source_missing',
      message: 'The selected import file does not exist.',
    });
  }
  const stat = fs.statSync(sourcePath);
  if (stat.size > MAX_IMPORT_BYTES) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'source_too_large',
      message: 'The import file exceeds the 20 MB safety limit.',
    });
  }
  const mode = options.mode || 'merge';
  const existingPortfolio = mode === 'merge' ? readExistingPortfolio(projectRoot) : undefined;
  if (existingPortfolio === null) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'invalid_existing_portfolio',
      message: 'The existing factor-research/portfolio.json is invalid and must be repaired before merging.',
    });
  }
  const bytes = fs.readFileSync(sourcePath);
  return parseFinancialFactorImport(new Uint8Array(bytes), {
    sourceName,
    projectRoot,
    existingPortfolio,
    mode,
  });
}

const previewResponse = (result: FinancialFactorImportResult): FinancialFactorImportPreviewResponse => ({
  valid: result.valid,
  sourceName: result.sourceName,
  issues: result.issues,
  summary: result.summary,
});

export async function previewFinancialFactorImport(
  options: LoadFinancialFactorImportOptions
): Promise<FinancialFactorImportPreviewResponse> {
  return previewResponse(await loadFinancialFactorImport(options));
}

const writeJsonAtomically = (targetPath: string, value: unknown): void => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  const temporaryPath = `${targetPath}.tmp-${process.pid}-${Date.now()}`;
  try {
    fs.writeFileSync(temporaryPath, `${JSON.stringify(value, null, 2)}\n`, { encoding: 'utf8', mode: 0o600 });
    fs.renameSync(temporaryPath, targetPath);
  } finally {
    if (fs.existsSync(temporaryPath)) fs.rmSync(temporaryPath, { force: true });
  }
};

export const writeFinancialFactorProjectPortfolio = (
  projectRoot: string,
  portfolio: FinancialFactorPortfolio
): string => {
  const resolvedRoot = resolveProjectRoot(projectRoot);
  const validatedPortfolio = readFinancialFactorPortfolio(portfolio);
  if (!validatedPortfolio) {
    throw new Error('portfolio must be a complete deepscientist.financial_factor.portfolio.v1 object.');
  }
  const previousPortfolio = readExistingPortfolio(resolvedRoot);
  if (previousPortfolio === null) {
    throw new Error('The existing factor-research/portfolio.json is invalid and must be repaired before writing.');
  }
  assertFinancialFactorPromotionMutation(validatedPortfolio, previousPortfolio);
  writeJsonAtomically(path.join(resolvedRoot, FINANCIAL_FACTOR_PORTFOLIO_PATH), validatedPortfolio);
  return FINANCIAL_FACTOR_PORTFOLIO_PATH;
};

export function commitLoadedFinancialFactorImport(
  projectRoot: string,
  result: FinancialFactorImportResult
): FinancialFactorImportCommitResponse {
  if (!result.valid || !result.portfolio) {
    throw new Error(
      result.issues.find((item) => item.severity === 'error')?.message || 'Factor import validation failed.'
    );
  }
  const resolvedRoot = resolveProjectRoot(projectRoot);
  const previousPortfolio = readExistingPortfolio(resolvedRoot);
  if (previousPortfolio === null) {
    throw new Error('The existing factor-research/portfolio.json is invalid and must be repaired before importing.');
  }
  assertFinancialFactorPromotionMutation(result.portfolio, previousPortfolio);
  const writtenPaths: string[] = [];
  for (const series of result.timeSeries) {
    const relativePath = path.join('factor-research', 'factors', series.factorId, 'runs', series.runId, 'result.json');
    writeJsonAtomically(path.join(resolvedRoot, relativePath), series);
    writtenPaths.push(relativePath.split(path.sep).join('/'));
  }
  writeFinancialFactorProjectPortfolio(resolvedRoot, result.portfolio);
  writtenPaths.push(FINANCIAL_FACTOR_PORTFOLIO_PATH);
  return {
    ...previewResponse(result),
    portfolio: result.portfolio,
    writtenPaths,
  };
}

export async function commitFinancialFactorImport(
  options: LoadFinancialFactorImportOptions
): Promise<FinancialFactorImportCommitResponse> {
  const result = await loadFinancialFactorImport(options);
  return commitLoadedFinancialFactorImport(options.projectRoot, result);
}

export async function createFinancialFactorImportTemplate(): Promise<FinancialFactorImportTemplateResponse> {
  const bytes = await buildFinancialFactorImportTemplate();
  return {
    fileName: FINANCIAL_FACTOR_IMPORT_TEMPLATE_NAME,
    mimeType: FINANCIAL_FACTOR_IMPORT_MIME,
    contentBase64: Buffer.from(bytes).toString('base64'),
  };
}
