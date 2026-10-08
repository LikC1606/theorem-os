/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import type { MathFeasibilityProfile } from "../common/types/team/mathematicsTeam";
import type { LeanEvalCatalog, LeanEvalCatalogProblem } from "./leanEvalCatalogAdapter";
import type { LeanEvalProblemAnalysis } from "./leanEvalProblemAnalyzer";
import { routeLeanEvalProblem, type LeanEvalRoute } from "./leanEvalRouting";

export type LeanEvalAnalysisSummary = Readonly<{
  problemId: string;
  title: string;
  group: string;
  statementRevision: number;
  tags: readonly string[];
  imports: readonly string[];
  holeCount: number;
  holeKinds: Readonly<Record<string, number>>;
  dependencyCriticalPath: number;
  noncomputableDeclarationCount: number;
  formalDegeneracySignals: readonly string[];
  firstCompileProbe: Readonly<{ attempted: boolean; ok?: boolean; error?: string }>;
  feasibility: MathFeasibilityProfile;
  route: LeanEvalRoute;
}>;

export type LeanEvalIntakeReceipt = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-intake-receipt.v1';
  receiptId: string;
  catalogHash: string;
  benchmarkCommit: string;
  setId: string;
  leaderboardSource: string;
  generatedAt: number;
  analysisHashes: Readonly<Record<string, string>>;
  probeResults: Readonly<Record<string, Readonly<{ attempted: boolean; ok?: boolean }>>>;
  toolchain: string;
}>;

export type LeanEvalIntakePage = Readonly<{
  receipt: LeanEvalIntakeReceipt;
  eligibleProblemCount: number;
  zeroCreditProblemCount: number;
  page: number;
  pageSize: number;
  totalPages: number;
  analyses: readonly (LeanEvalAnalysisSummary | LeanEvalProblemAnalysis)[];
  ranking: readonly MathFeasibilityProfile[];
}>;

export type LeanEvalAnalysisCacheOptions = Readonly<{
  cacheRoot: string;
  benchmarkCommit: string;
  catalogHash: string;
  problemId: string;
  toolchain: string;
  /** Revision of the project-local outcome ledger used for calibration. */
  outcomeLedgerRevision?: string;
}>;

const ANALYSIS_CACHE_SCHEMA = 'deepscientist.mathematics.lean-eval-analysis-cache.v3' as const;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const cacheKey = (options: LeanEvalAnalysisCacheOptions): string =>
  sha256(
    `${options.benchmarkCommit}\0${options.catalogHash}\0${options.problemId}\0${options.toolchain}\0${options.outcomeLedgerRevision ?? ''}`
  );
const MAX_ANALYSIS_CACHE_ENTRIES = 512;
const MAX_ANALYSIS_CACHE_BYTES = 64 * 1024 * 1024;

const ensureDirectoryNoSymlink = (directory: string): void => {
  const resolved = path.resolve(directory);
  const segments = resolved.split(path.sep);
  let current = segments.shift() === '' ? path.sep : segments.shift()!;
  for (const segment of segments) {
    current = path.join(current, segment);
    if (!fs.existsSync(current)) {
      fs.mkdirSync(current, { mode: 0o700 });
      continue;
    }
    const stat = fs.lstatSync(current);
    if (stat.isSymbolicLink() || !stat.isDirectory())
      throw new Error(`LeanEval cache directory is not a regular directory: ${current}`);
  }
};

const atomicWrite = (target: string, content: string): void => {
  const directory = path.dirname(target);
  const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
  const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
  let descriptor: number | undefined;
  try {
    descriptor = fs.openSync(
      temporary,
      fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | noFollow,
      0o600
    );
    fs.writeFileSync(descriptor, content, { encoding: 'utf8' });
    fs.fsyncSync(descriptor);
    fs.closeSync(descriptor);
    descriptor = undefined;
    fs.renameSync(temporary, target);
    try {
      const directoryDescriptor = fs.openSync(directory, fs.constants.O_RDONLY);
      try {
        fs.fsyncSync(directoryDescriptor);
      } finally {
        fs.closeSync(directoryDescriptor);
      }
    } catch {
      // Directory fsync is unavailable on some supported filesystems.
    }
  } finally {
    if (descriptor !== undefined) fs.closeSync(descriptor);
    if (fs.existsSync(temporary)) fs.rmSync(temporary, { force: true });
  }
};

export function readCachedLeanEvalAnalysis(options: LeanEvalAnalysisCacheOptions): LeanEvalProblemAnalysis | undefined {
  const file = path.join(path.resolve(options.cacheRoot), 'lean-eval', `${cacheKey(options)}.json`);
  try {
    const stat = fs.lstatSync(file);
    if (!stat.isFile() || stat.isSymbolicLink() || stat.size > 4 * 1024 * 1024) return undefined;
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8')) as unknown;
    const envelope =
      parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? (parsed as Record<string, unknown>) : undefined;
    const analysis =
      envelope?.schema === ANALYSIS_CACHE_SCHEMA
        ? (envelope.analysis as LeanEvalProblemAnalysis)
        : (parsed as LeanEvalProblemAnalysis);
    if (
      !analysis ||
      analysis.problemId !== options.problemId ||
      analysis.benchmarkCommit !== options.benchmarkCommit ||
      (envelope?.schema === ANALYSIS_CACHE_SCHEMA &&
        (envelope.catalogHash !== options.catalogHash ||
          envelope.toolchain !== options.toolchain ||
          envelope.outcomeLedgerRevision !== (options.outcomeLedgerRevision ?? '')))
    )
      return undefined;
    if (envelope?.schema === ANALYSIS_CACHE_SCHEMA && envelope.analysisHash !== sha256(JSON.stringify(analysis))) {
      return undefined;
    }
    if (!Array.isArray(analysis.holes) || !analysis.holeSchedule || !analysis.feasibility) return undefined;
    return analysis;
  } catch {
    return undefined;
  }
}

export function writeCachedLeanEvalAnalysis(
  options: LeanEvalAnalysisCacheOptions,
  analysis: LeanEvalProblemAnalysis
): string {
  const directory = path.join(path.resolve(options.cacheRoot), 'lean-eval');
  ensureDirectoryNoSymlink(directory);
  const file = path.join(directory, `${cacheKey(options)}.json`);
  const envelope = {
    schema: ANALYSIS_CACHE_SCHEMA,
    catalogHash: options.catalogHash,
    benchmarkCommit: options.benchmarkCommit,
    problemId: options.problemId,
    toolchain: options.toolchain,
    outcomeLedgerRevision: options.outcomeLedgerRevision ?? '',
    analysisHash: sha256(JSON.stringify(analysis)),
    analysis,
  };
  atomicWrite(file, `${JSON.stringify(envelope)}\n`);
  const entries = fs
    .readdirSync(directory, { withFileTypes: true })
    .flatMap((entry) => {
      if (!entry.name.endsWith('.json')) return [];
      const candidate = path.join(directory, entry.name);
      const stat = fs.lstatSync(candidate);
      if (stat.isSymbolicLink() || !stat.isFile()) return [];
      return [{ path: candidate, mtimeMs: stat.mtimeMs, size: stat.size }];
    })
    .toSorted((left, right) => left.mtimeMs - right.mtimeMs || left.path.localeCompare(right.path));
  let totalBytes = entries.reduce((sum, entry) => sum + entry.size, 0);
  const stale = entries.filter((entry) => entry.path !== file);
  while (entries.length > MAX_ANALYSIS_CACHE_ENTRIES || totalBytes > MAX_ANALYSIS_CACHE_BYTES) {
    const candidate = stale.shift();
    if (!candidate) break;
    const index = entries.findIndex((entry) => entry.path === candidate.path);
    if (index >= 0) entries.splice(index, 1);
    totalBytes -= candidate.size;
    fs.rmSync(candidate.path, { force: true });
  }
  return file;
}
const criticalPath = (analysis: LeanEvalProblemAnalysis): number => {
  const byName = new Map(analysis.holes.map((hole) => [hole.basename, hole]));
  const depth = new Map<string, number>();
  const visit = (name: string, seen = new Set<string>()): number => {
    if (depth.has(name)) return depth.get(name)!;
    if (seen.has(name)) return 0;
    const hole = byName.get(name);
    if (!hole) return 0;
    const next = new Set(seen).add(name);
    const value = 1 + Math.max(0, ...hole.dependsOn.map((dependency) => visit(dependency, next)));
    depth.set(name, value);
    return value;
  };
  return Math.max(0, ...analysis.holes.map((hole) => visit(hole.basename)));
};

export function summarizeLeanEvalAnalysis(
  problem: LeanEvalCatalogProblem,
  analysis: LeanEvalProblemAnalysis,
  ranking: readonly MathFeasibilityProfile[]
): LeanEvalAnalysisSummary {
  const feasibility =
    ranking.find((entry) => entry.candidateId === problem.id) ??
    ({
      candidateId: problem.id,
      candidateIndex: 0,
      score: 0,
      calibratedSolveProbability: 0,
      eligible: problem.eligible,
      rejectionCodes: [],
      noveltyScore: problem.zeroCredit ? 1 : 0,
      evidence: {},
      zeroCredit: problem.zeroCredit,
      majorRisks: [],
      recommendedFirstMilestone: 'Compile the first hole-aligned lemma.',
      signals: analysis.feasibility,
    } satisfies MathFeasibilityProfile);
  const holeKinds: Record<string, number> = {};
  for (const hole of analysis.holes) holeKinds[hole.kind] = (holeKinds[hole.kind] ?? 0) + 1;
  return Object.freeze({
    problemId: problem.id,
    title: problem.title,
    group: problem.group,
    statementRevision: problem.statementRevision,
    tags: problem.tags,
    imports: analysis.imports,
    holeCount: analysis.holes.length,
    holeKinds: Object.freeze(holeKinds),
    dependencyCriticalPath: criticalPath(analysis),
    noncomputableDeclarationCount: analysis.noncomputableDeclarationCount,
    formalDegeneracySignals: analysis.formalDegeneracySignals,
    firstCompileProbe: analysis.firstCompileProbe,
    feasibility,
    route: routeLeanEvalProblem(analysis),
  });
}

export function createLeanEvalIntakeReceipt(
  catalog: LeanEvalCatalog,
  analyses: readonly LeanEvalProblemAnalysis[],
  leaderboardSource: string,
  toolchain = 'leanprover/lean4:v4.33.0'
): LeanEvalIntakeReceipt {
  const catalogProblems = new Map(catalog.problems.map((problem) => [problem.id, problem]));
  const analysisIds = new Set<string>();
  for (const analysis of analyses) {
    if (analysisIds.has(analysis.problemId)) {
      throw new Error(`Lean-Eval intake contains duplicate analysis for ${analysis.problemId}`);
    }
    analysisIds.add(analysis.problemId);
    const problem = catalogProblems.get(analysis.problemId);
    if (!problem) throw new Error(`Lean-Eval intake analysis is absent from the catalog: ${analysis.problemId}`);
    if (analysis.benchmarkCommit !== catalog.benchmarkCommit) {
      throw new Error(`Lean-Eval intake analysis benchmark does not match the catalog: ${analysis.problemId}`);
    }
  }
  const analysisHashes = Object.fromEntries(
    analyses.map((analysis) => [analysis.problemId, sha256(JSON.stringify({ ...analysis, holeDag: analysis.holeDag }))])
  );
  const probeResults = Object.fromEntries(
    analyses.map((analysis) => [
      analysis.problemId,
      {
        attempted: analysis.firstCompileProbe.attempted,
        ...(analysis.firstCompileProbe.ok !== undefined ? { ok: analysis.firstCompileProbe.ok } : {}),
      },
    ])
  );
  const payload = {
    catalogHash: catalog.catalogHash,
    benchmarkCommit: catalog.benchmarkCommit,
    setId: catalog.setId,
    generatedAt: catalog.generatedAt,
    analysisHashes,
    probeResults,
    toolchain,
  };
  return Object.freeze({
    schema: 'deepscientist.mathematics.lean-eval-intake-receipt.v1',
    receiptId: `lean-eval-intake:${sha256(JSON.stringify(payload)).slice(0, 32)}`,
    catalogHash: catalog.catalogHash,
    benchmarkCommit: catalog.benchmarkCommit,
    setId: catalog.setId,
    leaderboardSource,
    generatedAt: catalog.generatedAt,
    analysisHashes: Object.freeze(analysisHashes),
    probeResults: Object.freeze(probeResults),
    toolchain,
  });
}

export function persistLeanEvalIntakeReceipt(projectRoot: string, receipt: LeanEvalIntakeReceipt): string {
  const directory = path.join(path.resolve(projectRoot), '.deepscientist', 'math');
  ensureDirectoryNoSymlink(directory);
  const target = path.join(directory, 'lean-eval-intake.receipt.json');
  atomicWrite(target, `${JSON.stringify(receipt, null, 2)}\n`);
  return target;
}

export function paginateLeanEvalAnalyses(
  catalog: LeanEvalCatalog,
  analyses: readonly LeanEvalProblemAnalysis[],
  ranking: readonly MathFeasibilityProfile[],
  receipt: LeanEvalIntakeReceipt,
  options: Readonly<{ page?: number; pageSize?: number; problemId?: string }>
): LeanEvalIntakePage {
  const eligible = catalog.problems.filter((problem) => problem.eligible);
  const byId = new Map(analyses.map((analysis) => [analysis.problemId, analysis]));
  const summaries = eligible.flatMap((problem) => {
    const analysis = byId.get(problem.id);
    return analysis ? [summarizeLeanEvalAnalysis(problem, analysis, ranking)] : [];
  });
  const requested = options.problemId?.trim();
  if (requested) {
    const problem = eligible.find((candidate) => candidate.id === requested);
    const analysis = problem ? byId.get(problem.id) : undefined;
    if (!problem || !analysis) throw new Error(`LeanEval problem analysis is unavailable: ${requested}`);
    return Object.freeze({
      receipt,
      eligibleProblemCount: eligible.length,
      zeroCreditProblemCount: eligible.filter((item) => item.zeroCredit).length,
      page: 1,
      pageSize: 1,
      totalPages: 1,
      analyses: Object.freeze([analysis]),
      ranking: Object.freeze(ranking.filter((entry) => entry.candidateId === requested)),
    });
  }
  const pageSizeInput =
    typeof options.pageSize === 'number' && Number.isFinite(options.pageSize) ? options.pageSize : 16;
  const pageSize = Math.max(1, Math.min(32, Math.floor(pageSizeInput)));
  const totalPages = Math.max(1, Math.ceil(summaries.length / pageSize));
  const pageInput = typeof options.page === 'number' && Number.isFinite(options.page) ? options.page : 1;
  const page = Math.max(1, Math.min(totalPages, Math.floor(pageInput)));
  const start = (page - 1) * pageSize;
  return Object.freeze({
    receipt,
    eligibleProblemCount: eligible.length,
    zeroCreditProblemCount: eligible.filter((item) => item.zeroCredit).length,
    page,
    pageSize,
    totalPages,
    analyses: Object.freeze(summaries.slice(start, start + pageSize)),
    ranking: Object.freeze(ranking.slice(start, start + pageSize)),
  });
}
