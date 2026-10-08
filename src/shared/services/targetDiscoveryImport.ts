/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {
  readTargetDiscoveryPortfolio,
  TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH,
  TARGET_DISCOVERY_IMPORT_RECEIPT_PATH,
  TARGET_DISCOVERY_IMPORT_RECEIPT_SCHEMA,
  TARGET_DISCOVERY_PORTFOLIO_PATH,
  type TargetDiscoveryImportReceipt,
  type TargetDiscoveryPortfolio,
} from "../../common/chat/targetDiscovery";
import {
  buildTargetDiscoveryCandidateRegistry,
  buildTargetDiscoveryImportTemplate,
  parseTargetDiscoveryImport,
  TARGET_DISCOVERY_IMPORT_MIME,
  TARGET_DISCOVERY_IMPORT_TEMPLATE_NAME,
  type TargetDiscoveryImportCommitResponse,
  type TargetDiscoveryImportIssue,
  type TargetDiscoveryImportMode,
  type TargetDiscoveryImportPreviewResponse,
  type TargetDiscoveryImportReconcileRequest,
  type TargetDiscoveryImportReconcileResponse,
  type TargetDiscoveryImportRequest,
  type TargetDiscoveryImportResult,
  type TargetDiscoveryImportTemplateResponse,
} from "../../common/chat/targetDiscoveryImport";

const MAX_IMPORT_BYTES = 20 * 1024 * 1024;
const MAX_IMPORT_ROWS = 10_000;

type LoadOptions = TargetDiscoveryImportRequest & { requireSourceInProject?: boolean };

export type TargetDiscoveryProjectPortfolioSnapshot =
  | { status: 'missing'; path: string }
  | { status: 'invalid'; path: string }
  | { status: 'ready'; path: string; portfolio: TargetDiscoveryPortfolio };

const emptySummary = (): TargetDiscoveryImportPreviewResponse['summary'] => ({
  candidateCount: 0,
  newCandidateCount: 0,
  updatedCandidateCount: 0,
  warningCount: 0,
});

const invalidResult = (sourceName: string, item: TargetDiscoveryImportIssue): TargetDiscoveryImportResult => ({
  valid: false,
  sourceName,
  mode: 'merge',
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

export const readTargetDiscoveryProjectPortfolio = (projectRoot: string): TargetDiscoveryProjectPortfolioSnapshot => {
  const root = resolveProjectRoot(projectRoot);
  const portfolioPath = path.join(root, TARGET_DISCOVERY_PORTFOLIO_PATH);
  if (!fs.existsSync(portfolioPath)) return { status: 'missing', path: TARGET_DISCOVERY_PORTFOLIO_PATH };
  try {
    const portfolio = readTargetDiscoveryPortfolio(JSON.parse(fs.readFileSync(portfolioPath, 'utf8')));
    return portfolio
      ? { status: 'ready', path: TARGET_DISCOVERY_PORTFOLIO_PATH, portfolio }
      : { status: 'invalid', path: TARGET_DISCOVERY_PORTFOLIO_PATH };
  } catch {
    return { status: 'invalid', path: TARGET_DISCOVERY_PORTFOLIO_PATH };
  }
};

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

const writeBytesAtomically = (targetPath: string, value: Uint8Array): void => {
  fs.mkdirSync(path.dirname(targetPath), { recursive: true });
  const temporaryPath = `${targetPath}.tmp-${process.pid}-${Date.now()}`;
  try {
    fs.writeFileSync(temporaryPath, value, { mode: 0o600 });
    fs.renameSync(temporaryPath, targetPath);
  } finally {
    if (fs.existsSync(temporaryPath)) fs.rmSync(temporaryPath, { force: true });
  }
};

const sha256 = (value: Uint8Array | string): string => crypto.createHash('sha256').update(value).digest('hex');

const rankingSignature = (portfolio: TargetDiscoveryPortfolio): string =>
  JSON.stringify(
    portfolio.candidates.map((candidate) => ({
      id: candidate.id,
      symbol: candidate.symbol,
      rank: candidate.rank,
      priorityIndex: candidate.priorityIndex,
      maxPriorityIndex: candidate.maxPriorityIndex,
      coverage: candidate.coverage,
      rankStability: candidate.rankStability,
    }))
  );

export const readTargetDiscoveryImportReceipt = (projectRoot: string): TargetDiscoveryImportReceipt | undefined => {
  const root = resolveProjectRoot(projectRoot);
  const receiptPath = path.join(root, TARGET_DISCOVERY_IMPORT_RECEIPT_PATH);
  if (!fs.existsSync(receiptPath)) return undefined;
  try {
    const receipt = JSON.parse(fs.readFileSync(receiptPath, 'utf8')) as Partial<TargetDiscoveryImportReceipt>;
    return receipt.schema === TARGET_DISCOVERY_IMPORT_RECEIPT_SCHEMA &&
      receipt.sourcePath === TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH &&
      typeof receipt.sourceSha256 === 'string' &&
      typeof receipt.importedAt === 'number' &&
      (receipt.mode === 'merge' || receipt.mode === 'replace') &&
      typeof receipt.importedCandidateCount === 'number' &&
      typeof receipt.portfolioCandidateCount === 'number' &&
      typeof receipt.candidateIdsSha256 === 'string'
      ? (receipt as TargetDiscoveryImportReceipt)
      : undefined;
  } catch {
    return undefined;
  }
};

export const writeTargetDiscoveryProjectPortfolio = (
  projectRoot: string,
  portfolio: TargetDiscoveryPortfolio
): string => {
  const root = resolveProjectRoot(projectRoot);
  const validated = readTargetDiscoveryPortfolio(portfolio);
  if (!validated) throw new Error('portfolio must be a complete target-discovery portfolio.');
  writeJsonAtomically(path.join(root, TARGET_DISCOVERY_PORTFOLIO_PATH), validated);
  return TARGET_DISCOVERY_PORTFOLIO_PATH;
};

export async function loadTargetDiscoveryImport(options: LoadOptions): Promise<TargetDiscoveryImportResult> {
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
  if (path.extname(sourcePath).toLowerCase() !== '.csv') {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'unsupported_file_type',
      message: 'Target candidate imports must be UTF-8 CSV files.',
    });
  }
  if (!fs.existsSync(sourcePath) || !fs.statSync(sourcePath).isFile()) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'source_missing',
      message: 'The selected candidate CSV does not exist.',
    });
  }
  if (fs.statSync(sourcePath).size > MAX_IMPORT_BYTES) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'source_too_large',
      message: 'The candidate CSV exceeds the 20 MB safety limit.',
    });
  }
  const existingSnapshot = readTargetDiscoveryProjectPortfolio(projectRoot);
  const existingPortfolio =
    options.portfolio || (existingSnapshot.status === 'ready' ? existingSnapshot.portfolio : undefined);
  if (!options.portfolio && existingSnapshot.status === 'invalid' && (options.mode || 'merge') === 'merge') {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'invalid_existing_portfolio',
      message: 'The existing target-discovery/portfolio.json is invalid and must be repaired before merging.',
    });
  }
  const result = await parseTargetDiscoveryImport(new Uint8Array(fs.readFileSync(sourcePath)), {
    sourceName,
    projectRoot,
    existingPortfolio,
    knownEvidenceIds: options.knownEvidenceIds,
    mode: (options.mode || 'merge') as TargetDiscoveryImportMode,
  });
  if (result.summary.candidateCount > MAX_IMPORT_ROWS) {
    return invalidResult(sourceName, {
      severity: 'error',
      code: 'too_many_rows',
      message: `The candidate CSV exceeds the ${MAX_IMPORT_ROWS.toLocaleString()} row safety limit.`,
    });
  }
  return result;
}

const previewResponse = (result: TargetDiscoveryImportResult): TargetDiscoveryImportPreviewResponse => ({
  valid: result.valid,
  sourceName: result.sourceName,
  issues: result.issues,
  summary: result.summary,
});

export async function previewTargetDiscoveryImport(
  options: TargetDiscoveryImportRequest
): Promise<TargetDiscoveryImportPreviewResponse> {
  return previewResponse(await loadTargetDiscoveryImport(options));
}

export function commitLoadedTargetDiscoveryImport(
  projectRoot: string,
  result: TargetDiscoveryImportResult
): TargetDiscoveryImportCommitResponse {
  if (!result.valid || !result.portfolio) {
    throw new Error(
      result.issues.find((item) => item.severity === 'error')?.message || 'Target candidate import validation failed.'
    );
  }
  const root = resolveProjectRoot(projectRoot);
  const registry = buildTargetDiscoveryCandidateRegistry(result.portfolio);
  const candidateIds = result.portfolio.candidates
    .map((candidate) => candidate.id)
    .toSorted((left, right) => left.localeCompare(right));
  const receipt: TargetDiscoveryImportReceipt = {
    schema: TARGET_DISCOVERY_IMPORT_RECEIPT_SCHEMA,
    sourcePath: TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH,
    sourceSha256: sha256(registry),
    importedAt: Date.now(),
    mode: result.mode,
    importedCandidateCount: result.summary.candidateCount,
    portfolioCandidateCount: result.portfolio.candidates.length,
    candidateIdsSha256: sha256(candidateIds.join('\n')),
  };
  writeBytesAtomically(path.join(root, TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH), registry);
  writeTargetDiscoveryProjectPortfolio(root, result.portfolio);
  writeJsonAtomically(path.join(root, TARGET_DISCOVERY_IMPORT_RECEIPT_PATH), receipt);
  return {
    ...previewResponse(result),
    portfolio: result.portfolio,
    writtenPaths: [
      TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH,
      TARGET_DISCOVERY_PORTFOLIO_PATH,
      TARGET_DISCOVERY_IMPORT_RECEIPT_PATH,
    ],
  };
}

export async function commitTargetDiscoveryImport(
  options: TargetDiscoveryImportRequest
): Promise<TargetDiscoveryImportCommitResponse> {
  return commitLoadedTargetDiscoveryImport(options.projectRoot, await loadTargetDiscoveryImport(options));
}

export async function reconcileTargetDiscoveryProject(
  options: TargetDiscoveryImportReconcileRequest
): Promise<TargetDiscoveryImportReconcileResponse> {
  const root = resolveProjectRoot(options.projectRoot);
  const registryPath = path.join(root, TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH);
  if (!fs.existsSync(registryPath) || !fs.statSync(registryPath).isFile()) {
    return { valid: true, changed: false, canonicalRegistryExists: false, issues: [] };
  }
  const snapshot = readTargetDiscoveryProjectPortfolio(root);
  const loaded = await loadTargetDiscoveryImport({
    projectRoot: root,
    sourcePath: registryPath,
    mode: 'replace',
    portfolio: snapshot.status === 'ready' ? snapshot.portfolio : undefined,
    requireSourceInProject: true,
  });
  if (!loaded.valid || !loaded.portfolio) {
    return {
      valid: false,
      changed: false,
      canonicalRegistryExists: true,
      issues: loaded.issues,
    };
  }
  const registryHash = sha256(fs.readFileSync(registryPath));
  const candidateIdsHash = sha256(
    loaded.portfolio.candidates
      .map((candidate) => candidate.id)
      .toSorted((left, right) => left.localeCompare(right))
      .join('\n')
  );
  const receipt = readTargetDiscoveryImportReceipt(root);
  const receiptMatches =
    receipt?.sourceSha256 === registryHash &&
    receipt.portfolioCandidateCount === loaded.portfolio.candidates.length &&
    receipt.candidateIdsSha256 === candidateIdsHash;
  const portfolioMatches =
    snapshot.status === 'ready' && rankingSignature(snapshot.portfolio) === rankingSignature(loaded.portfolio);
  if (receiptMatches && portfolioMatches) {
    return {
      valid: true,
      changed: false,
      canonicalRegistryExists: true,
      updatedAt: snapshot.portfolio.updatedAt,
      issues: loaded.issues,
      receipt,
    };
  }
  const committed = commitLoadedTargetDiscoveryImport(root, loaded);
  return {
    valid: true,
    changed: true,
    canonicalRegistryExists: true,
    updatedAt: committed.portfolio.updatedAt,
    issues: committed.issues,
    receipt: readTargetDiscoveryImportReceipt(root),
  };
}

export function createTargetDiscoveryImportTemplate(): TargetDiscoveryImportTemplateResponse {
  return {
    fileName: TARGET_DISCOVERY_IMPORT_TEMPLATE_NAME,
    mimeType: TARGET_DISCOVERY_IMPORT_MIME,
    contentBase64: Buffer.from(buildTargetDiscoveryImportTemplate()).toString('base64'),
  };
}
