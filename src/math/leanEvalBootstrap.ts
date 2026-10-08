/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import {
  mathActionablePlanSchedule,
  canonicalMathProblemNegationPayload,
  canonicalMathProblemStatementPayloads,
  isMathFoundationalLeanAxiom,
  normalizeMathProblemContract,
  normalizeMathRouteCard,
  normalizeMathExecutionPolicy,
  type MathExecutionPolicy,
  type MathProblemContract,
  type MathPlanNode,
  type MathRouteCard,
} from "../common/types/team/mathematicsTeam";
import {
  fetchLeanEvalLeaderboardCredits,
  findLeanEvalCatalogProblem,
  readLeanEvalCatalog,
  LEAN_EVAL_BENCHMARK_COMMIT,
  LEAN_EVAL_LEADERBOARD_URL,
  LEAN_EVAL_REPOSITORY_URL,
  type LeanEvalCatalog,
  type LeanEvalCatalogProblem,
} from "./leanEvalCatalogAdapter";
import {
  analyzeLeanEvalProblem,
  runLeanEvalSandboxedElaborationProbe,
  type LeanEvalProblemAnalysis,
} from "./leanEvalProblemAnalyzer";
import {
  collectLeanEvalSubmissionFiles,
  materializeLeanEvalProblemBinding,
  prepareLeanEvalProblemBinding,
  type LeanEvalProblemBinding,
} from "./leanEvalAdapter";
import { executionPolicyFromLeanEvalRoute, routeLeanEvalProblem, type LeanEvalRoute } from "./leanEvalRouting";
import {
  checkManyFormalVerifications,
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarations,
  resolveMathematicsLakePackagesCache,
  runOfficialComparator,
  type MathematicsVerifierBatchResult,
  type MathematicsVerifierResult,
  type MathematicsOfficialComparatorResult,
  type MathematicsVerifierExecutionOptions,
} from "./verifier";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import { readCachedLeanEvalAnalysis, writeCachedLeanEvalAnalysis } from "./leanEvalIntake";
import { readMathematicsReceiptSecret, signMathOfficialGateReceipt } from "./receiptAttestation";
import type { MathOfficialGateReceipt } from "../common/types/team/mathematicsTeam";
import { reapLeanEvalArtifacts } from "./leanEvalCleanup";

export type LeanEvalBootstrapReceipt = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1';
  receiptId: string;
  problemId: string;
  benchmarkCommit: string;
  catalogHash: string;
  evaluationMode?: 'official' | 'benchmark';
  leaderboardSource: string;
  leaderboardHash?: string;
  leaderboardGeneratedAt?: number;
  routeFingerprint: string;
  /** Frozen assignment policy derived from the same analysis as routeFingerprint. */
  executionPolicy?: MathExecutionPolicy;
  contract: MathProblemContract;
  /** Public input obligations; none may be replaced by an organizational parent. */
  publicObligations?: readonly Readonly<{ name: string; declarationHash: string; dependsOn: readonly string[] }>[];
  workspaceRoot: string;
  projectRoot: string;
  /** Git worktree that owns the immutable benchmark binding and later commits. */
  verifierProjectRoot?: string;
  /** Detached source worktree materialized at the pinned benchmark commit. */
  sourceProjectRoot?: string;
  trustedFiles: readonly string[];
  solverOwnedFiles: readonly string[];
  activeProblemPath: string;
  createdAt: number;
  toolchain?: string;
}>;

export type LeanEvalBootstrapResult = Readonly<{
  catalog: LeanEvalCatalog;
  problem: LeanEvalCatalogProblem;
  analysis: LeanEvalProblemAnalysis;
  binding: LeanEvalProblemBinding;
  routeCard: MathRouteCard;
  route: LeanEvalRoute;
  receipt: LeanEvalBootstrapReceipt;
}>;

export type LeanEvalSubmissionCommit = Readonly<{
  projectRoot: string;
  targetCommit: string;
  files: readonly string[];
}>;

export type LeanEvalOfficialGateOptions = Readonly<{
  commit?: LeanEvalSubmissionCommit;
  commitMessage?: string;
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  /** Test/runtime override; production always performs a fresh official fetch. */
  fetchLeaderboard?: () => Promise<
    Readonly<{ credits: readonly { problemId: string; statementRevision: number }[]; generatedAt: number }>
  >;
}>;

export type LeanEvalOfficialGateResult = Readonly<{
  submission: LeanEvalSubmissionCommit;
  localGate: MathematicsVerifierBatchResult;
  comparison: MathematicsOfficialComparatorResult;
  officialGateReceipt?: MathOfficialGateReceipt;
}>;

/** The immutable identity expected for each hole during LOCAL_GATE. */
export type LeanEvalLocalGateExpectedItem = Readonly<{
  proofPath: string;
  theoremName: string;
  statementHash: string;
  leanStatementHash?: string;
  claim?: 'statement' | 'negation';
  expectedSourceDeclarationHash?: string;
}>;

/**
 * Match a LOCAL_GATE result to the exact item that requested it.  The batch
 * verifier emits one result per item, but theorem names alone are not a safe
 * identity: a reused name can point at a different file, claim, statement,
 * or source declaration.
 */
export const isLeanEvalLocalGateResultBound = (
  item: LeanEvalLocalGateExpectedItem,
  result: MathematicsVerifierResult,
  targetCommit: string
): boolean => {
  let expectedPath: string;
  let resultPath: string;
  try {
    expectedPath = safeRelative(item.proofPath);
    resultPath = safeRelative(result.proofPath);
  } catch {
    return false;
  }
  return (
    result.status === 'kernel_verified' &&
    result.verifier === 'lean-kernel' &&
    result.targetCommit.toLowerCase() === targetCommit.trim().toLowerCase() &&
    resultPath === expectedPath &&
    result.statementHash === item.statementHash &&
    result.leanStatementHash === item.leanStatementHash &&
    (result.claim || 'statement') === (item.claim || 'statement') &&
    result.theoremName === item.theoremName &&
    result.goalsRemaining === 0 &&
    result.sorryCount === 0 &&
    result.admitCount === 0 &&
    result.axioms.every(isMathFoundationalLeanAxiom) &&
    Boolean(result.theoremDeclarationHash) &&
    result.sourceDeclarationHash === item.expectedSourceDeclarationHash
  );
};

/** Require a complete one-to-one LOCAL_GATE result set, independent of order. */
export const hasCompleteLeanEvalLocalGateResults = (
  items: readonly LeanEvalLocalGateExpectedItem[],
  batch: MathematicsVerifierBatchResult,
  targetCommit: string
): boolean => {
  if (
    batch.status !== 'kernel_verified' ||
    batch.results.length !== items.length ||
    batch.targetCommit.toLowerCase() !== targetCommit.trim().toLowerCase()
  )
    return false;
  const consumed = new Set<number>();
  const receiptIds = new Set<string>();
  const complete = items.every((item) => {
    const index = batch.results.findIndex(
      (result, resultIndex) => !consumed.has(resultIndex) && isLeanEvalLocalGateResultBound(item, result, targetCommit)
    );
    if (index < 0) return false;
    consumed.add(index);
    const receiptId = batch.results[index]!.receiptId.trim();
    if (!receiptId || receiptIds.has(receiptId)) return false;
    receiptIds.add(receiptId);
    return true;
  });
  return complete && consumed.size === batch.results.length;
};

/** Ensure a recovered solver view names the catalog problem's exact path. */
export const assertLeanEvalBootstrapProjectPath = (
  workspaceRoot: string,
  projectRoot: string,
  generatedPath: string
): void => {
  const relative = generatedPath.trim();
  if (
    !relative ||
    relative.includes('\\') ||
    relative.includes('\0') ||
    path.posix.isAbsolute(relative) ||
    /^[A-Za-z]:/u.test(relative) ||
    relative.split('/').some((part) => !part || part === '.' || part === '..') ||
    path.posix.normalize(relative) !== relative
  ) {
    throw new Error('Persisted Lean-Eval bootstrap generated path is unsafe');
  }
  const expected = path.join(path.resolve(workspaceRoot), relative);
  if (path.resolve(projectRoot) !== expected) {
    throw new Error('Persisted Lean-Eval bootstrap solver project is not bound to the pinned problem path');
  }
};

/** Reload the durable bootstrap workspace and run the same official gate after
 * a process restart. All public metadata is re-read from the pinned source
 * commit; mutable receipt fields are cross-checked before execution. */
export async function runPersistedLeanEvalOfficialGate(options: {
  activeProblemPath: string;
  repositoryRoot: string;
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  fetchLeaderboard?: LeanEvalOfficialGateOptions['fetchLeaderboard'];
}): Promise<LeanEvalOfficialGateResult> {
  const receipt = readLeanEvalBootstrapReceipt(options.activeProblemPath);
  if (receipt.leaderboardSource !== LEAN_EVAL_LEADERBOARD_URL) {
    throw new Error('Persisted Lean-Eval official gate requires an official leaderboard-backed bootstrap receipt');
  }
  const repositoryRoot = fs.realpathSync(path.resolve(options.repositoryRoot));
  let sourceRoot = receipt.sourceProjectRoot || repositoryRoot;
  let reloadedSource = false;
  if (!fs.existsSync(sourceRoot)) {
    sourceRoot = `${path.resolve(receipt.workspaceRoot)}.source-reloaded`;
    if (fs.existsSync(sourceRoot)) throw new Error('LeanEval source reload path already exists and is unsafe');
    git(repositoryRoot, ['worktree', 'add', '--detach', sourceRoot, LEAN_EVAL_BENCHMARK_COMMIT]);
    reloadedSource = true;
  } else {
    assertRegisteredWorktree(repositoryRoot, sourceRoot, 'source');
  }
  try {
    const persistedLeaderboard = await (options.fetchLeaderboard
      ? options.fetchLeaderboard()
      : fetchLeanEvalLeaderboardCredits({ forceRefresh: true }));
    if (receipt.leaderboardHash && sha256(JSON.stringify(persistedLeaderboard.credits)) !== receipt.leaderboardHash) {
      throw new Error('Persisted Lean-Eval bootstrap leaderboard provenance no longer matches the receipt');
    }
    if (
      receipt.leaderboardGeneratedAt !== undefined &&
      persistedLeaderboard.generatedAt !== receipt.leaderboardGeneratedAt
    ) {
      throw new Error('Persisted Lean-Eval bootstrap leaderboard snapshot time no longer matches the receipt');
    }
    const catalog = readLeanEvalCatalog({
      repositoryRoot: sourceRoot,
      benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
      credits: persistedLeaderboard.credits,
      generatedAt: persistedLeaderboard.generatedAt,
      verifyGitCommit: true,
    });
    if (catalog.catalogHash !== receipt.catalogHash) {
      throw new Error('Persisted Lean-Eval bootstrap catalog hash no longer matches the pinned receipt');
    }
    const problem = findLeanEvalCatalogProblem(catalog, receipt.problemId);
    if (!problem || !problem.eligible) throw new Error('Persisted Lean-Eval bootstrap problem is no longer eligible');
    assertLeanEvalBootstrapProjectPath(receipt.workspaceRoot, receipt.projectRoot, problem.generatedPath);
    const analysis = await analyzeLeanEvalProblem(problem, {
      repositoryRoot: sourceRoot,
      benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
      elaborationProbe: (problemRoot, declarations, dependencyTargets) =>
        runLeanEvalSandboxedElaborationProbe(problemRoot, declarations, 30_000, dependencyTargets),
    });
    const verifierRoot = receipt.verifierProjectRoot;
    if (!verifierRoot) throw new Error('Persisted Lean-Eval bootstrap has no verifier worktree');
    if (!fs.existsSync(verifierRoot)) throw new Error('Persisted Lean-Eval verifier worktree is missing');
    assertRegisteredWorktree(repositoryRoot, verifierRoot, 'verifier');
    const binding = prepareLeanEvalProblemBinding({
      projectRoot: path.join(verifierRoot, problem.generatedPath),
      problemId: problem.id,
      title: problem.title,
      informalStatement: problem.notes ?? problem.title,
      statementRevision: problem.statementRevision,
      baselineCommit: LEAN_EVAL_BENCHMARK_COMMIT,
      repositoryUrl: LEAN_EVAL_REPOSITORY_URL,
    });
    if (
      binding.problemContract.statementHash !== receipt.contract.statementHash ||
      binding.problemContract.leanStatementHash !== receipt.contract.leanStatementHash
    ) {
      throw new Error('Persisted Lean-Eval bootstrap contract no longer matches the pinned public statement');
    }
    if (
      binding.problemContract.officialManifestId !== receipt.contract.officialManifestId ||
      binding.problemContract.officialManifestHash !== receipt.contract.officialManifestHash
    ) {
      throw new Error('Persisted Lean-Eval bootstrap official binding identity no longer matches the receipt');
    }
    const expectedOwnership = pinnedOwnership(sourceRoot, problem, LEAN_EVAL_BENCHMARK_COMMIT);
    if (
      !sameStringList(receipt.trustedFiles, expectedOwnership.trustedFiles) ||
      !sameStringList(receipt.solverOwnedFiles, expectedOwnership.solverOwnedFiles)
    ) {
      throw new Error('Persisted Lean-Eval bootstrap file ownership no longer matches the pinned benchmark tree');
    }
    const routeCard = buildRouteCard(analysis, binding.problemContract.statementHash, 'bootstrap:reload');
    if (routeCard.routeFingerprint !== receipt.routeFingerprint) {
      throw new Error('Persisted Lean-Eval bootstrap route fingerprint no longer matches the pinned analysis');
    }
    if (
      receipt.executionPolicy &&
      JSON.stringify(receipt.executionPolicy) !==
        JSON.stringify(executionPolicyFromLeanEvalRoute(routeLeanEvalProblem(analysis)))
    ) {
      throw new Error('Persisted Lean-Eval bootstrap execution policy no longer matches the pinned analysis');
    }
    const bootstrapped = Object.freeze({
      catalog,
      problem,
      analysis,
      binding,
      routeCard,
      route: routeLeanEvalProblem(analysis),
      receipt,
    });
    return await runLeanEvalOfficialGate(bootstrapped, options);
  } finally {
    if (reloadedSource) {
      try {
        git(repositoryRoot, ['worktree', 'remove', '--force', sourceRoot]);
        git(repositoryRoot, ['worktree', 'prune']);
      } catch {
        // Maintenance reaper handles an orphaned reload worktree.
      }
    }
  }
}

export type LeanEvalBootstrapOptions = Readonly<{
  repositoryRoot: string;
  problemId: string;
  evaluationMode?: 'official' | 'benchmark';
  workspaceRoot?: string;
  workspaceParent?: string;
  /** Optional deterministic fixture credits; formal MCP entry points use official credits instead. */
  credits?: readonly Record<string, unknown>[];
  useOfficialCredits?: boolean;
  setId?: string;
  cleanupOnFailure?: boolean;
  supportedToolchains?: readonly string[];
  /** Run a bounded public-declaration elaborator probe during bootstrap. */
  enableElaborationProbe?: boolean;
}>;

export function assertLeanEvalBootstrapEligibility(
  problem: Pick<LeanEvalCatalogProblem, 'eligible' | 'eligibilityReasons'>,
  evaluationMode: 'official' | 'benchmark' = 'official'
): void {
  if (!['official', 'benchmark'].includes(evaluationMode)) throw new Error('Invalid LeanEval evaluation mode');
  const reasons = problem.eligibilityReasons.filter(
    (reason) => evaluationMode !== 'benchmark' || reason !== 'accepted_credit_exists'
  );
  if (reasons.length || (!problem.eligible && !problem.eligibilityReasons.length))
    throw new Error(`LeanEval problem is not eligible: ${reasons.join(', ') || 'unknown'}`);
}

/**
 * A static analysis cache is sufficient for the fast bootstrap path, but a
 * caller that requests elaboration evidence must never silently downgrade to
 * that cache. Keep this boundary explicit and pure so it is easy to verify.
 */
export const canReuseLeanEvalAnalysisCache = (
  cachedAnalysis: LeanEvalProblemAnalysis | undefined,
  enableElaborationProbe?: boolean
): cachedAnalysis is LeanEvalProblemAnalysis =>
  Boolean(cachedAnalysis && (enableElaborationProbe === false || cachedAnalysis.elaborationProbe?.attempted === true));

const bootstrapAnalysisCache = new Map<string, LeanEvalProblemAnalysis>();
const bootstrapAnalysisCacheKey = (repositoryRoot: string, problemId: string): string =>
  `${path.resolve(repositoryRoot)}\0${LEAN_EVAL_BENCHMARK_COMMIT}\0${problemId}`;

/** Share bootstrap analysis with the team session in the same process. */
export const rememberLeanEvalBootstrapAnalysis = (repositoryRoot: string, analysis: LeanEvalProblemAnalysis): void => {
  const key = bootstrapAnalysisCacheKey(repositoryRoot, analysis.problemId);
  bootstrapAnalysisCache.delete(key);
  bootstrapAnalysisCache.set(key, analysis);
  while (bootstrapAnalysisCache.size > 64) {
    const oldest = bootstrapAnalysisCache.keys().next().value;
    if (oldest === undefined) break;
    bootstrapAnalysisCache.delete(oldest);
  }
};

export const getLeanEvalBootstrapAnalysis = (
  repositoryRoot: string,
  problemId: string
): LeanEvalProblemAnalysis | undefined => {
  const key = bootstrapAnalysisCacheKey(repositoryRoot, problemId);
  const analysis = bootstrapAnalysisCache.get(key);
  if (!analysis) return undefined;
  bootstrapAnalysisCache.delete(key);
  bootstrapAnalysisCache.set(key, analysis);
  return analysis;
};

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const writeFileDurably = (target: string, contents: string | Uint8Array): void => {
  const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
  const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
  const flags = fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | noFollow;
  let descriptor: number | undefined;
  try {
    descriptor = fs.openSync(temporary, flags, 0o600);
    fs.writeFileSync(descriptor, contents);
    fs.fsyncSync(descriptor);
    fs.closeSync(descriptor);
    descriptor = undefined;
    fs.renameSync(temporary, target);
    try {
      const directory = fs.openSync(path.dirname(target), 'r');
      try {
        fs.fsyncSync(directory);
      } finally {
        fs.closeSync(directory);
      }
    } catch {
      // Directory fsync is unavailable on some supported filesystems.
    }
  } finally {
    if (descriptor !== undefined) fs.closeSync(descriptor);
    fs.rmSync(temporary, { force: true });
  }
};
const git = (root: string, args: readonly string[]): string => {
  const result = spawnSync('git', ['-C', root, ...args], { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  if (result.status !== 0) throw new Error(result.stderr?.trim() || `git ${args.join(' ')} failed`);
  return result.stdout.trim();
};

const assertRegisteredWorktree = (repositoryRoot: string, worktreeRoot: string, label: string): void => {
  const canonical = fs.realpathSync(path.resolve(worktreeRoot));
  const registered = git(repositoryRoot, ['worktree', 'list', '--porcelain'])
    .split(/\r?\n/u)
    .filter((line) => line.startsWith('worktree '))
    .map((line) => line.slice('worktree '.length).trim())
    .filter(Boolean)
    .flatMap((candidate) => {
      try {
        return [fs.realpathSync(candidate)];
      } catch {
        return [];
      }
    });
  if (!registered.includes(canonical)) {
    throw new Error(`LeanEval ${label} is not a registered detached worktree of the benchmark repository`);
  }
};

const safeRelative = (value: string): string => {
  const normalized = value.replaceAll('\\', '/').replace(/^\.\//u, '');
  if (
    !normalized ||
    normalized.startsWith('/') ||
    /^[A-Za-z]:/u.test(normalized) ||
    normalized.split('/').some((part) => !part || part === '.' || part === '..')
  ) {
    throw new Error(`LeanEval path is not repository-relative: ${value}`);
  }
  return normalized;
};

const ensureDirectoryNoSymlink = (directory: string): string => {
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
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
      throw new Error(`LeanEval workspace path is not a regular directory: ${current}`);
    }
  }
  return resolved;
};

const writeGitFile = (
  repositoryRoot: string,
  baselineCommit: string,
  relativePath: string,
  destination: string
): void => {
  const parent = path.dirname(destination);
  ensureDirectoryNoSymlink(parent);
  if (fs.existsSync(destination)) {
    const stat = fs.lstatSync(destination);
    if (stat.isSymbolicLink() || !stat.isFile())
      throw new Error(`LeanEval destination is not a regular file: ${destination}`);
  }
  const result = spawnSync('git', ['-C', repositoryRoot, 'show', `${baselineCommit}:${relativePath}`], {
    maxBuffer: 16 * 1024 * 1024,
  });
  if (result.status !== 0) throw new Error(`Unable to materialize LeanEval file ${relativePath}`);
  fs.writeFileSync(destination, result.stdout, { mode: 0o600 });
};

type LeanEvalLakeManifestRecord = Record<string, unknown>;

const parseLeanEvalLakeManifest = (contents: string, source: string): LeanEvalLakeManifestRecord => {
  let parsed: unknown;
  try {
    parsed = JSON.parse(contents);
  } catch (error) {
    throw new Error(`LeanEval Lake manifest is invalid: ${source}`, { cause: error });
  }
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    throw new Error(`LeanEval Lake manifest must be a JSON object: ${source}`);
  }
  return parsed as LeanEvalLakeManifestRecord;
};

/**
 * Lake manifests generated at repository root describe the umbrella
 * `lean-eval` package.  A solver workspace is an independent package, so its
 * manifest must carry the selected problem name while retaining the frozen
 * dependency revisions from the pinned benchmark commit.
 */
const normalizeSolverLakeManifest = (contents: string, source: string, problemId: string): string => {
  const manifest = parseLeanEvalLakeManifest(contents, source);
  const normalized: LeanEvalLakeManifestRecord = {
    ...manifest,
    version: manifest.version ?? manifest.schemaVersion ?? '1.2.0',
    name: problemId,
    lakeDir: '.lake',
    packagesDir: '.lake/packages',
  };
  return `${JSON.stringify(normalized, null, 2)}\n`;
};

/**
 * Point Lake's dependency entries at the validated shared cache.  Lake reads
 * this workspace-local file automatically, so the normal `lake build`
 * command remains usable without cloning or rebuilding Mathlib.
 */
const writeSolverLakePackageOverrides = (projectRoot: string, manifestPath: string): boolean => {
  const packagesRoot = resolveMathematicsLakePackagesCache(projectRoot, resolveMathematicsRuntimeEnvironment());
  if (!packagesRoot) return false;
  const manifest = parseLeanEvalLakeManifest(fs.readFileSync(manifestPath, 'utf8'), manifestPath);
  if (!Array.isArray(manifest.packages) || manifest.packages.length === 0) return false;
  const overrides: LeanEvalLakeManifestRecord[] = [];
  for (const item of manifest.packages) {
    if (!item || typeof item !== 'object' || Array.isArray(item)) return false;
    const entry = item as LeanEvalLakeManifestRecord;
    const name = typeof entry.name === 'string' ? entry.name : '';
    if (!name) return false;
    const packageDirectory = [name, name.replace(/^«(.+)»$/u, '$1')].find((candidate) =>
      fs.existsSync(path.join(packagesRoot, candidate))
    );
    if (!packageDirectory) return false;
    const override: LeanEvalLakeManifestRecord = {
      name,
      type: 'path',
      dir: path.join(packagesRoot, packageDirectory),
      inherited: typeof entry.inherited === 'boolean' ? entry.inherited : false,
    };
    for (const key of ['scope', 'configFile', 'manifestFile'] as const) {
      if (typeof entry[key] === 'string') override[key] = entry[key];
    }
    overrides.push(override);
  }
  const lakeDirectory = path.join(projectRoot, '.lake');
  ensureDirectoryNoSymlink(lakeDirectory);
  writeFileDurably(
    path.join(lakeDirectory, 'package-overrides.json'),
    `${JSON.stringify({ schemaVersion: '1.2.0', packages: overrides }, null, 2)}\n`
  );
  return true;
};

/** Materialize only public/trusted files and solver-owned files. Solution.lean is deliberately excluded. */
const materializeSolverWorkspace = (
  repositoryRoot: string,
  problem: LeanEvalCatalogProblem,
  baselineCommit: string,
  workspaceRoot: string
): Readonly<{ projectRoot: string; trustedFiles: readonly string[]; solverOwnedFiles: readonly string[] }> => {
  const projectRoot = path.join(workspaceRoot, problem.generatedPath);
  ensureDirectoryNoSymlink(projectRoot);
  const prefix = `${safeRelative(problem.generatedPath)}/`;
  const tree = git(repositoryRoot, ['ls-tree', '-r', '--name-only', baselineCommit, '--', problem.generatedPath])
    .split('\n')
    .map((item) => item.trim())
    .filter(Boolean);
  const trustedFiles: string[] = [];
  const solverOwnedFiles: string[] = [];
  let problemManifestWritten = false;
  for (const absoluteRelative of tree) {
    if (!absoluteRelative.startsWith(prefix)) continue;
    const relative = absoluteRelative.slice(prefix.length);
    safeRelative(relative);
    // Keep evaluator-only files and benchmark prose out of the blind solver
    // view even when a future benchmark nests them below the problem root.
    if (['Solution.lean', 'WorkspaceTest.lean', 'README.md'].includes(path.posix.basename(relative))) continue;
    if (
      !relative.endsWith('.lean') &&
      !['config.json', 'holes.json', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'].includes(
        relative
      )
    )
      continue;
    writeGitFile(repositoryRoot, baselineCommit, absoluteRelative, path.join(projectRoot, relative));
    if (relative === 'lake-manifest.json') problemManifestWritten = true;
    if (relative === 'Submission.lean' || (relative.startsWith('Submission/') && relative.endsWith('.lean')))
      solverOwnedFiles.push(relative);
    else trustedFiles.push(relative);
  }
  if (!solverOwnedFiles.includes('Submission.lean')) throw new Error(`LeanEval ${problem.id} has no Submission.lean`);
  const manifestPath = path.join(projectRoot, 'lake-manifest.json');
  if (!problemManifestWritten && fs.existsSync(path.join(repositoryRoot, 'lake-manifest.json')))
    writeGitFile(repositoryRoot, baselineCommit, 'lake-manifest.json', manifestPath);
  if (fs.existsSync(manifestPath)) {
    const manifestStat = fs.lstatSync(manifestPath);
    if (manifestStat.isSymbolicLink() || !manifestStat.isFile())
      throw new Error('LeanEval lake-manifest.json is invalid');
    writeFileDurably(
      manifestPath,
      normalizeSolverLakeManifest(fs.readFileSync(manifestPath, 'utf8'), manifestPath, problem.id)
    );
    writeSolverLakePackageOverrides(projectRoot, manifestPath);
  }
  return Object.freeze({
    projectRoot,
    trustedFiles: Object.freeze(trustedFiles.toSorted()),
    solverOwnedFiles: Object.freeze(solverOwnedFiles.toSorted()),
  });
};

const pinnedOwnership = (
  repositoryRoot: string,
  problem: LeanEvalCatalogProblem,
  baselineCommit: string
): Readonly<{ trustedFiles: readonly string[]; solverOwnedFiles: readonly string[] }> => {
  const prefix = `${safeRelative(problem.generatedPath)}/`;
  const trustedFiles: string[] = [];
  const solverOwnedFiles: string[] = [];
  for (const absoluteRelative of git(repositoryRoot, [
    'ls-tree',
    '-r',
    '--name-only',
    baselineCommit,
    '--',
    problem.generatedPath,
  ])
    .split('\n')
    .map((item) => item.trim())
    .filter(Boolean)) {
    if (!absoluteRelative.startsWith(prefix)) continue;
    const relative = absoluteRelative.slice(prefix.length);
    if (['Solution.lean', 'WorkspaceTest.lean', 'README.md'].includes(path.posix.basename(relative))) continue;
    if (
      !relative.endsWith('.lean') &&
      !['config.json', 'holes.json', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'].includes(
        relative
      )
    )
      continue;
    if (relative === 'Submission.lean' || (relative.startsWith('Submission/') && relative.endsWith('.lean')))
      solverOwnedFiles.push(relative);
    else trustedFiles.push(relative);
  }
  return Object.freeze({
    trustedFiles: Object.freeze(trustedFiles.toSorted()),
    solverOwnedFiles: Object.freeze(solverOwnedFiles.toSorted()),
  });
};

const sameStringList = (left: readonly string[], right: readonly string[]): boolean =>
  left.length === right.length && left.every((value, index) => value === right[index]);

const decisiveHole = (analysis: LeanEvalProblemAnalysis): LeanEvalProblemAnalysis['holes'][number] | undefined =>
  analysis.holes.toReversed().find((hole) => hole.kind === 'theorem') ?? analysis.holes.at(-1);

export const buildLeanEvalBootstrapRouteCard = (
  analysis: Pick<LeanEvalProblemAnalysis, 'holeDag' | 'holes' | 'challengeSha256' | 'problemId' | 'feasibility'>,
  statementHash: string,
  sessionId: string
): MathRouteCard => {
  const planNodes: MathPlanNode[] = analysis.holeDag.map((node) => ({
    ...node,
    estimatedEffort:
      node.estimatedEffort === undefined ? undefined : Math.min(5, Math.max(1, Math.round(node.estimatedEffort))),
  }));
  const byId = new Map(planNodes.map((node) => [node.id, node]));
  const reached = new Set<string>();
  const visit = (id: string): void => {
    if (reached.has(id)) return;
    reached.add(id);
    byId.get(id)?.dependsOn.forEach(visit);
  };
  const declaredGoal = planNodes.find((node) => node.role === 'goal');
  if (declaredGoal) visit(declaredGoal.id);
  if (declaredGoal && reached.size !== planNodes.length) {
    let completionId = 'public-obligations-completion';
    while (byId.has(completionId)) completionId += '-group';
    const dependencies = new Set(planNodes.flatMap((node) => node.dependsOn));
    // Containment records joint completion, not a mathematical implication
    // between independent public declarations. The official gate still checks each hole.
    for (let index = 0; index < planNodes.length; index += 1) {
      const node = planNodes[index]!;
      planNodes[index] = {
        ...node,
        role: node.role === 'goal' ? 'reduction' : node.role,
        ...(!dependencies.has(node.id) ? { parentNodeId: completionId } : {}),
      };
    }
    planNodes.push({
      id: completionId,
      role: 'goal',
      informalClaim: `Complete every public proof obligation for ${analysis.problemId}; organizational completion only.`,
      provisionalLeanStatement: analysis.holes.map((hole) => hole.declarationBody).join('\n\n'),
      dependsOn: [],
      status: 'proposed',
      evidenceRefs: [],
      expectedProgress:
        'Every original public obligation is verified by the unchanged official whole-submission gate. This grouping does not introduce a Lean declaration.',
      successCriteria: analysis.holes.map((hole) => `Verify the original public obligation ${hole.name}.`),
    });
  }
  const schedule = mathActionablePlanSchedule(planNodes);
  const rootNodeId = schedule.rootNodeId;
  const routePayload = JSON.stringify({
    statement: analysis.challengeSha256,
    nodes: planNodes.map((node) =>
      node.parentNodeId ? [node.id, node.dependsOn, node.parentNodeId] : [node.id, node.dependsOn]
    ),
  });
  const routeFingerprint = `lean-eval:${sha256(routePayload).slice(0, 48)}`;
  const card = {
    statementHash,
    routeFingerprint,
    proposerSessionId: sessionId,
    structuralCommitment: `Public Challenge hole DAG for ${analysis.problemId}`,
    decisiveLemma: analysis.holes.at(-1)?.name ?? analysis.problemId,
    decisiveTest: 'Compile the active Submission wave with the pinned Lean toolchain.',
    falsificationSignal: 'A public Challenge compile error or a target exact-probe failure.',
    premiseBundle: {
      strategySketch: 'Solve dependency-ready holes in wave order, preserving exact declarations.',
      leanSkeleton: 'namespace Submission\n\nend Submission',
      premises: [] as readonly [],
      coverage: planNodes.map((node) => ({
        planNodeId: node.id,
        premiseDeclarationNames: [] as readonly [],
        selfContained: false,
        unresolvedNeed: `Retrieve exact premises after a live-goal miss for ${node.id}.`,
      })),
      unresolvedNeeds: planNodes.map((node) => `Retrieve exact premises after a live-goal miss for ${node.id}.`),
    },
    planNodes,
    bridges: planNodes.flatMap((node) =>
      node.dependsOn.map((dependencyNodeId) => ({
        dependencyNodeId,
        consumerNodeId: node.id,
        mathematicalBridge: `Use ${dependencyNodeId} as the dependency for ${node.id}.`,
        leanUse: `Apply the compiled declaration represented by ${dependencyNodeId}.`,
      }))
    ),
    rootNodeId,
    ...(schedule.rankedNodeIds[0] ? { bottleneckNodeId: schedule.rankedNodeIds[0] } : {}),
    openFrontierNodeIds: schedule.openFrontierNodeIds,
    expectedInformationGain: 3,
    estimatedCost: Math.min(5, Math.max(1, Math.ceil(analysis.holes.length / 3))),
    formalizationRisk: Math.min(
      5,
      Math.max(
        1,
        Math.ceil(
          (analysis.feasibility.formalDegeneracyPotential + analysis.feasibility.missingFoundationDepth / 2) * 5
        )
      )
    ),
  } satisfies MathRouteCard;
  return normalizeMathRouteCard(card);
};

const buildRouteCard = buildLeanEvalBootstrapRouteCard;

/** Build a reproducible, solver-safe Lean-Eval project and route contract. */
export async function bootstrapLeanEvalProblem(options: LeanEvalBootstrapOptions): Promise<LeanEvalBootstrapResult> {
  const repositoryRoot = fs.realpathSync(path.resolve(options.repositoryRoot));
  reapLeanEvalArtifacts({ repositoryRoot });
  const baselineCommit = LEAN_EVAL_BENCHMARK_COMMIT;
  // The caller checkout may be dirty or on another branch.  Require only that
  // it contains the official object, then read every public input from a
  // detached worktree at that exact commit.
  try {
    git(repositoryRoot, ['cat-file', '-e', `${baselineCommit}^{commit}`]);
  } catch {
    throw new Error(`LeanEval checkout does not contain pinned benchmark commit ${baselineCommit}`);
  }
  // Reserve the solver workspace name before creating the pinned source
  // worktree. The Team workspace index binds detached paths to
  // `<workspace>.source` and `<workspace>.git`, so the default path must use
  // that same identity rather than an unrelated random source directory.
  const workspaceParent = options.workspaceParent
    ? ensureDirectoryNoSymlink(options.workspaceParent)
    : ensureDirectoryNoSymlink(os.tmpdir());
  const workspaceRoot = options.workspaceRoot
    ? ensureDirectoryNoSymlink(options.workspaceRoot)
    : path.join(workspaceParent, `deepscientist-lean-eval-${process.pid}-${crypto.randomUUID()}`);
  const sourceWorktree = `${workspaceRoot}.source`;
  // Explicit credits are reserved for deterministic tests.  In production,
  // callers leave credits undefined and the official leaderboard is fetched.
  const useOfficialCredits = options.useOfficialCredits ?? options.credits === undefined;
  const official = useOfficialCredits ? await fetchLeanEvalLeaderboardCredits() : undefined;
  let sourceWorktreeCreated = false;
  try {
    git(repositoryRoot, ['worktree', 'add', '--detach', sourceWorktree, baselineCommit]);
    sourceWorktreeCreated = true;
    // A sparse parent checkout propagates its filter to new worktrees. The
    // catalog integrity check needs manifests/ and generated/index.json, so
    // make the pinned source worktree a complete, deterministic checkout.
    git(sourceWorktree, ['sparse-checkout', 'disable']);
  } catch (error) {
    if (sourceWorktreeCreated) {
      try {
        git(repositoryRoot, ['worktree', 'remove', '--force', sourceWorktree]);
        git(repositoryRoot, ['worktree', 'prune']);
      } catch {
        // Preserve the original worktree creation error; maintenance can
        // prune an orphaned detached worktree later.
      }
    }
    throw new Error(
      `Unable to create pinned LeanEval source worktree: ${error instanceof Error ? error.message : String(error)}`,
      { cause: error }
    );
  }
  let catalog: LeanEvalCatalog;
  let problem: LeanEvalCatalogProblem | undefined;
  try {
    catalog = readLeanEvalCatalog({
      repositoryRoot: sourceWorktree,
      benchmarkCommit: baselineCommit,
      setId: options.setId,
      credits: official?.credits ?? options.credits,
      generatedAt: official?.generatedAt ?? Date.now(),
      verifyGitCommit: true,
    });
    problem = findLeanEvalCatalogProblem(catalog, options.problemId);
    if (!problem) throw new Error(`LeanEval problem is not in the pinned catalog: ${options.problemId}`);
    assertLeanEvalBootstrapEligibility(problem, options.evaluationMode);
  } catch (error) {
    try {
      git(repositoryRoot, ['worktree', 'remove', '--force', sourceWorktree]);
      git(repositoryRoot, ['worktree', 'prune']);
    } catch {
      // Preserve the catalog error; orphan cleanup is handled by maintenance.
    }
    throw error;
  }
  const selectedProblem = problem;
  const verifierProjectRoot = `${workspaceRoot}.git`;
  let verifierWorktreeCreated = false;
  try {
    const workspaceRelation = path.relative(repositoryRoot, workspaceRoot);
    if (!workspaceRelation || (!workspaceRelation.startsWith(`..${path.sep}`) && workspaceRelation !== '..')) {
      throw new Error('LeanEval solver workspace must be outside the benchmark checkout.');
    }
    if (!fs.existsSync(workspaceRoot)) ensureDirectoryNoSymlink(workspaceRoot);
    const existingEntries = fs.readdirSync(workspaceRoot);
    if (existingEntries.length > 0) {
      throw new Error('LeanEval solver workspace must be a fresh empty directory.');
    }
    if (fs.existsSync(verifierProjectRoot)) {
      throw new Error(`LeanEval verifier worktree already exists: ${verifierProjectRoot}`);
    }
    git(repositoryRoot, ['worktree', 'add', '--detach', verifierProjectRoot, baselineCommit]);
    verifierWorktreeCreated = true;
    // Keep the verifier worktree complete as well: official comparison may
    // inspect benchmark metadata outside the selected generated project.
    git(verifierProjectRoot, ['sparse-checkout', 'disable']);
    // The solver view is deliberately separate from the Git worktree.  The
    // latter retains protected evaluator files for official comparison while
    // the former never materializes Solution.lean into a Worker workspace.
    const materialized = materializeSolverWorkspace(sourceWorktree, selectedProblem, baselineCommit, workspaceRoot);
    const runtimeEnvironment = resolveMathematicsRuntimeEnvironment();
    const toolchain = (() => {
      for (const candidate of [
        path.join(sourceWorktree, selectedProblem.generatedPath, 'lean-toolchain'),
        path.join(sourceWorktree, 'lean-toolchain'),
      ]) {
        try {
          const value = fs.readFileSync(candidate, 'utf8').trim();
          if (value) return value;
        } catch {
          // Try the next pinned toolchain declaration.
        }
      }
      return 'unknown';
    })();
    const analysisCacheRoot = runtimeEnvironment.DEEPSCIENTIST_LEAN_EVAL_ROOT?.trim();
    const analysisCacheOptions = analysisCacheRoot
      ? {
          cacheRoot: analysisCacheRoot,
          benchmarkCommit: baselineCommit,
          catalogHash: catalog.catalogHash,
          problemId: selectedProblem.id,
          toolchain,
        }
      : undefined;
    const cachedAnalysis = analysisCacheOptions ? readCachedLeanEvalAnalysis(analysisCacheOptions) : undefined;
    // The cache key intentionally stays compatible with the shared intake
    // cache. Probe availability is therefore checked at the value boundary:
    // enabling elaboration may upgrade a cache that was created by a fast
    // static-only bootstrap, while disabling it can reuse either form.
    let analysis = canReuseLeanEvalAnalysisCache(cachedAnalysis, options.enableElaborationProbe)
      ? cachedAnalysis
      : undefined;
    if (!analysis) {
      analysis = await analyzeLeanEvalProblem(selectedProblem, {
        repositoryRoot: sourceWorktree,
        benchmarkCommit: baselineCommit,
        supportedToolchains: options.supportedToolchains,
        ...(options.enableElaborationProbe === false
          ? {}
          : {
              elaborationProbe: (
                problemRoot: string,
                declarations: readonly string[],
                dependencyTargets: readonly string[]
              ) => runLeanEvalSandboxedElaborationProbe(problemRoot, declarations, 30_000, dependencyTargets),
            }),
      });
      if (analysisCacheOptions) {
        try {
          writeCachedLeanEvalAnalysis(analysisCacheOptions, analysis);
        } catch {
          // Analysis caching is an acceleration only; a read-only or full
          // cache root must never make a valid bootstrap fail.
        }
      }
    }
    rememberLeanEvalBootstrapAnalysis(repositoryRoot, analysis);
    const binding = prepareLeanEvalProblemBinding({
      projectRoot: path.join(verifierProjectRoot, selectedProblem.generatedPath),
      problemId: selectedProblem.id,
      title: selectedProblem.title,
      informalStatement: selectedProblem.notes ?? selectedProblem.title,
      statementRevision: selectedProblem.statementRevision,
      baselineCommit,
      repositoryUrl: LEAN_EVAL_REPOSITORY_URL,
    });
    // The official manifest and its authority anchor are generated from the
    // pinned public Challenge and live in the verifier worktree.  They are
    // committed together with the solver files so the comparator can resolve
    // the exact manifest from targetCommit rather than from mutable state.
    materializeLeanEvalProblemBinding(binding);
    const routeCard = buildRouteCard(analysis, binding.problemContract.statementHash, `bootstrap:${process.pid}`);
    const route = routeLeanEvalProblem(analysis);
    const executionPolicy = executionPolicyFromLeanEvalRoute(route);
    const receipt: LeanEvalBootstrapReceipt = Object.freeze({
      schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1',
      receiptId: `lean-eval-bootstrap:${selectedProblem.id}:${sha256(`${catalog.catalogHash}\0${routeCard.routeFingerprint}`).slice(0, 24)}`,
      problemId: selectedProblem.id,
      benchmarkCommit: baselineCommit,
      catalogHash: catalog.catalogHash,
      leaderboardSource: official
        ? LEAN_EVAL_LEADERBOARD_URL
        : options.credits
          ? 'caller-supplied:test-only'
          : 'disabled',
      evaluationMode: options.evaluationMode ?? 'official',
      ...(official
        ? {
            leaderboardHash: sha256(JSON.stringify(official.credits)),
            leaderboardGeneratedAt: official.generatedAt,
          }
        : {}),
      routeFingerprint: routeCard.routeFingerprint,
      executionPolicy,
      contract: binding.problemContract,
      publicObligations: Object.freeze(
        analysis.holes.map((hole) =>
          Object.freeze({
            name: hole.name,
            declarationHash: hashMathFormalSourceDeclaration(hole.declarationBody, hole.basename),
            dependsOn: Object.freeze([...hole.dependsOn]),
          })
        )
      ),
      workspaceRoot,
      projectRoot: materialized.projectRoot,
      verifierProjectRoot,
      sourceProjectRoot: sourceWorktree,
      trustedFiles: materialized.trustedFiles,
      solverOwnedFiles: materialized.solverOwnedFiles,
      activeProblemPath: path.join(workspaceRoot, 'active-problem.json'),
      createdAt: Date.now(),
      ...(analysis.feasibility.toolchainCompatibility ? { toolchain: 'pinned' } : {}),
    });
    writeFileDurably(receipt.activeProblemPath, `${JSON.stringify(receipt, null, 2)}\n`);
    return Object.freeze({ catalog, problem: selectedProblem, analysis, binding, routeCard, route, receipt });
  } catch (error) {
    if (verifierWorktreeCreated) {
      try {
        git(repositoryRoot, ['worktree', 'remove', '--force', verifierProjectRoot]);
        git(repositoryRoot, ['worktree', 'prune']);
      } catch {
        // Preserve the original bootstrap error; a later maintenance pass can
        // prune an orphaned detached worktree safely.
      }
    }
    if (sourceWorktreeCreated) {
      try {
        git(repositoryRoot, ['worktree', 'remove', '--force', sourceWorktree]);
        git(repositoryRoot, ['worktree', 'prune']);
      } catch {
        // Preserve the original bootstrap error; maintenance can prune later.
      }
    }
    if (options.cleanupOnFailure !== false && !options.workspaceRoot)
      fs.rmSync(workspaceRoot, { recursive: true, force: true });
    throw error;
  }
}

/** Reload a bootstrap receipt after a process restart without trusting mutable
 * workspace metadata. The caller must still rebuild catalog/analysis before
 * executing a gate. */
export function readLeanEvalBootstrapReceipt(activeProblemPath: string): LeanEvalBootstrapReceipt {
  const absolute = path.resolve(activeProblemPath);
  const stat = fs.lstatSync(absolute);
  if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('LeanEval bootstrap receipt is not a regular file');
  const parsed = JSON.parse(fs.readFileSync(absolute, 'utf8')) as Partial<LeanEvalBootstrapReceipt>;
  if (
    parsed.schema !== 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1' ||
    typeof parsed.receiptId !== 'string' ||
    !parsed.receiptId.trim() ||
    typeof parsed.problemId !== 'string' ||
    !/^[A-Za-z0-9_.-]+$/u.test(parsed.problemId) ||
    parsed.benchmarkCommit !== LEAN_EVAL_BENCHMARK_COMMIT ||
    (parsed.evaluationMode !== undefined && !['official', 'benchmark'].includes(String(parsed.evaluationMode))) ||
    typeof parsed.catalogHash !== 'string' ||
    !/^[0-9a-f]{64}$/iu.test(parsed.catalogHash) ||
    typeof parsed.leaderboardSource !== 'string' ||
    !parsed.leaderboardSource.trim() ||
    (parsed.leaderboardSource === LEAN_EVAL_LEADERBOARD_URL &&
      (typeof parsed.leaderboardHash !== 'string' ||
        !/^[0-9a-f]{64}$/iu.test(parsed.leaderboardHash) ||
        !Number.isFinite(parsed.leaderboardGeneratedAt) ||
        Number(parsed.leaderboardGeneratedAt) <= 0)) ||
    (parsed.leaderboardHash !== undefined &&
      (typeof parsed.leaderboardHash !== 'string' || !/^[0-9a-f]{64}$/iu.test(parsed.leaderboardHash))) ||
    (parsed.leaderboardGeneratedAt !== undefined &&
      (!Number.isFinite(parsed.leaderboardGeneratedAt) || Number(parsed.leaderboardGeneratedAt) <= 0)) ||
    typeof parsed.routeFingerprint !== 'string' ||
    !parsed.routeFingerprint.trim() ||
    typeof parsed.workspaceRoot !== 'string' ||
    typeof parsed.projectRoot !== 'string' ||
    typeof parsed.activeProblemPath !== 'string' ||
    !parsed.contract ||
    !Array.isArray(parsed.solverOwnedFiles) ||
    !Array.isArray(parsed.trustedFiles) ||
    !Number.isFinite(parsed.createdAt) ||
    Number(parsed.createdAt) <= 0
  ) {
    throw new Error('LeanEval bootstrap receipt is invalid or not pinned');
  }
  let contract: MathProblemContract;
  if (
    parsed.publicObligations !== undefined &&
    (!Array.isArray(parsed.publicObligations) ||
      parsed.publicObligations.some(
        (item) =>
          !item ||
          typeof item.name !== 'string' ||
          !item.name.trim() ||
          !/^[a-f0-9]{64}$/u.test(item.declarationHash) ||
          !Array.isArray(item.dependsOn) ||
          item.dependsOn.some((name: unknown) => typeof name !== 'string' || !name.trim())
      ) ||
      new Set(parsed.publicObligations.map((item) => item.name)).size !== parsed.publicObligations.length)
  ) {
    throw new Error('LeanEval public obligations are invalid');
  }
  try {
    contract = normalizeMathProblemContract(parsed.contract as MathProblemContract);
  } catch (error) {
    throw new Error(
      `LeanEval bootstrap receipt contract is invalid: ${error instanceof Error ? error.message : String(error)}`,
      {
        cause: error,
      }
    );
  }
  const statementPayloads = canonicalMathProblemStatementPayloads(contract);
  if (
    sha256(statementPayloads.informal) !== contract.statementHash ||
    sha256(statementPayloads.lean) !== contract.leanStatementHash
  ) {
    throw new Error('LeanEval bootstrap receipt contract statement hashes are not canonical');
  }
  const negationPayload = canonicalMathProblemNegationPayload(contract);
  if (negationPayload && sha256(negationPayload) !== contract.leanNegationHash) {
    throw new Error('LeanEval bootstrap receipt contract negation hash is not canonical');
  }
  if (contract.problemId !== parsed.problemId) {
    throw new Error('LeanEval bootstrap receipt contract problemId does not match the receipt problemId');
  }
  const executionPolicy = parsed.executionPolicy
    ? normalizeMathExecutionPolicy(parsed.executionPolicy as MathExecutionPolicy)
    : undefined;
  const workspaceRoot = path.resolve(parsed.workspaceRoot);
  const projectRoot = path.resolve(parsed.projectRoot);
  const assertNoSymlinkComponents = (candidate: string, label: string): void => {
    const resolved = path.resolve(candidate);
    const parsedPath = path.parse(resolved);
    let cursor = parsedPath.root;
    for (const segment of resolved.slice(parsedPath.root.length).split(path.sep).filter(Boolean)) {
      cursor = path.join(cursor, segment);
      try {
        const candidateStat = fs.lstatSync(cursor);
        if (candidateStat.isSymbolicLink()) throw new Error(`${label} must not traverse a symbolic link`);
      } catch (error) {
        if (error instanceof Error && error.message.includes('must not traverse')) throw error;
        if ((error as NodeJS.ErrnoException).code === 'ENOENT') break;
        throw error;
      }
    }
  };
  if (
    path.resolve(parsed.activeProblemPath) !== absolute ||
    !path.isAbsolute(parsed.workspaceRoot) ||
    !path.isAbsolute(parsed.projectRoot) ||
    !absolute.startsWith(`${workspaceRoot}${path.sep}`) ||
    path.basename(absolute) !== 'active-problem.json' ||
    !projectRoot.startsWith(`${workspaceRoot}${path.sep}`)
  ) {
    throw new Error('LeanEval bootstrap receipt paths are invalid or inconsistent');
  }
  assertNoSymlinkComponents(workspaceRoot, 'LeanEval bootstrap workspaceRoot');
  assertNoSymlinkComponents(projectRoot, 'LeanEval bootstrap projectRoot');
  assertNoSymlinkComponents(absolute, 'LeanEval bootstrap activeProblemPath');
  const ownership = new Set<string>();
  for (const file of [...parsed.solverOwnedFiles, ...parsed.trustedFiles]) {
    if (
      typeof file !== 'string' ||
      !file ||
      file.startsWith('/') ||
      file.includes('\\') ||
      /^[A-Za-z]:/u.test(file) ||
      file.split('/').some((part) => !part || part === '.' || part === '..') ||
      ['Solution.lean', 'WorkspaceTest.lean', 'README.md'].includes(path.posix.basename(file)) ||
      ownership.has(file)
    ) {
      throw new Error('LeanEval bootstrap receipt contains an unsafe file ownership path');
    }
    ownership.add(file);
  }
  if (!parsed.solverOwnedFiles.includes('Submission.lean')) {
    throw new Error('LeanEval bootstrap receipt has no solver-owned Submission.lean');
  }
  for (const candidate of [parsed.verifierProjectRoot, parsed.sourceProjectRoot]) {
    if (
      candidate !== undefined &&
      (!path.isAbsolute(candidate) ||
        path.resolve(candidate) === workspaceRoot ||
        path.resolve(candidate) !== `${workspaceRoot}${candidate === parsed.verifierProjectRoot ? '.git' : '.source'}`)
    ) {
      throw new Error('LeanEval bootstrap receipt contains an unsafe detached worktree path');
    }
    if (candidate !== undefined) assertNoSymlinkComponents(path.resolve(candidate), 'LeanEval detached worktree');
  }
  return Object.freeze({
    ...parsed,
    workspaceRoot,
    projectRoot,
    activeProblemPath: absolute,
    contract,
    ...(executionPolicy ? { executionPolicy } : {}),
    trustedFiles: Object.freeze([...parsed.trustedFiles]),
    solverOwnedFiles: Object.freeze([...parsed.solverOwnedFiles]),
  } as LeanEvalBootstrapReceipt);
}

/**
 * Promote only solver-owned files into the detached verifier worktree and
 * create an immutable commit.  Protected Challenge/Solution/configuration
 * files remain byte-identical to the pinned benchmark commit.
 */
export function commitLeanEvalSubmission(
  bootstrapped: LeanEvalBootstrapResult,
  message = `Lean-Eval submission: ${bootstrapped.problem.id}`
): LeanEvalSubmissionCommit {
  const verifierRoot = bootstrapped.receipt.verifierProjectRoot;
  if (!verifierRoot) throw new Error('LeanEval bootstrap has no verifier worktree');
  const workspaceRoot = path.resolve(bootstrapped.receipt.workspaceRoot);
  if (path.resolve(verifierRoot) !== `${workspaceRoot}.git`) {
    throw new Error('LeanEval bootstrap verifier worktree is not bound to its solver workspace');
  }
  const solverRoot = path.resolve(bootstrapped.receipt.projectRoot);
  const workspaceStat = fs.lstatSync(workspaceRoot);
  if (workspaceStat.isSymbolicLink() || !workspaceStat.isDirectory()) {
    throw new Error('LeanEval bootstrap solver workspace is unsafe');
  }
  if (
    solverRoot === workspaceRoot ||
    !solverRoot.startsWith(`${workspaceRoot}${path.sep}`) ||
    !fs.existsSync(solverRoot) ||
    !fs.existsSync(verifierRoot)
  ) {
    throw new Error('LeanEval solver and verifier worktrees are outside the bootstrap workspace');
  }
  const canonicalWorkspace = fs.realpathSync(workspaceRoot);
  const canonicalSolver = fs.realpathSync(solverRoot);
  const canonicalVerifier = fs.realpathSync(verifierRoot);
  if (
    !canonicalSolver.startsWith(`${canonicalWorkspace}${path.sep}`) ||
    canonicalVerifier !== `${canonicalWorkspace}.git`
  ) {
    throw new Error('LeanEval solver and verifier worktrees resolve outside the bootstrap workspace');
  }
  for (const [label, candidate] of [
    ['solver', solverRoot],
    ['verifier', path.resolve(verifierRoot)],
  ] as const) {
    const stat = fs.lstatSync(candidate);
    if (stat.isSymbolicLink() || !stat.isDirectory()) throw new Error(`LeanEval ${label} worktree is unsafe`);
  }
  const verifierProject = path.join(verifierRoot, bootstrapped.problem.generatedPath);
  if (!fs.existsSync(verifierRoot) || !fs.existsSync(verifierProject)) {
    throw new Error('LeanEval verifier worktree is missing');
  }
  const files = collectSolverFilesForCommit(solverRoot, bootstrapped.receipt.solverOwnedFiles);
  const touched: string[] = [];
  for (const relative of files) {
    const source = path.join(solverRoot, relative);
    const destination = path.join(verifierProject, relative);
    ensureDirectoryNoSymlink(path.dirname(destination));
    const sourceStat = fs.lstatSync(source);
    if (sourceStat.isSymbolicLink() || !sourceStat.isFile())
      throw new Error(`LeanEval solver file is invalid: ${relative}`);
    fs.copyFileSync(source, destination);
    touched.push(path.join(bootstrapped.problem.generatedPath, relative).replaceAll(path.sep, '/'));
  }
  const bindingFiles = [bootstrapped.binding.officialManifestPath, bootstrapped.binding.authorityPath].map((file) =>
    safeRelative(file)
  );
  const commitFiles = [...new Set([...touched, ...bindingFiles])].toSorted();
  for (const relative of bindingFiles) {
    const absolute = path.join(verifierRoot, relative);
    const stat = fs.lstatSync(absolute);
    if (stat.isSymbolicLink() || !stat.isFile()) {
      throw new Error(`LeanEval official binding file is invalid: ${relative}`);
    }
  }
  const status = git(verifierRoot, ['status', '--short', '--', ...commitFiles]);
  if (
    status
      .split('\n')
      .map((line) => line.trim())
      .filter(Boolean)
      .some((line) => !commitFiles.some((file) => line.endsWith(` ${file}`) || line.endsWith(`M  ${file}`)))
  ) {
    throw new Error('LeanEval verifier worktree contains unexpected changes');
  }
  const currentHead = git(verifierRoot, ['rev-parse', 'HEAD']).toLowerCase();
  if (!status) {
    if (currentHead === bootstrapped.receipt.benchmarkCommit.toLowerCase()) {
      throw new Error('LeanEval submission has no solver-owned changes to commit');
    }
    // A retry after a successful commit is idempotent.  The verifier worktree
    // is detached and contains no unrelated user commits, so HEAD is the
    // exact previously promoted submission.
    return Object.freeze({ projectRoot: verifierRoot, targetCommit: currentHead, files: Object.freeze(commitFiles) });
  }
  const solverStatus = git(verifierRoot, ['status', '--short', '--', ...touched]);
  if (!solverStatus && currentHead === bootstrapped.receipt.benchmarkCommit.toLowerCase()) {
    throw new Error('LeanEval submission has no solver-owned changes to commit');
  }
  // Project templates commonly ignore `.deepscientist/`; force-add only the
  // two generated binding files (the solver paths remain ordinary `git add`).
  git(verifierRoot, ['add', '-f', '--', ...commitFiles]);
  const commitResult = spawnSync(
    'git',
    [
      '-C',
      verifierRoot,
      '-c',
      'user.name=DeepScientist Lean-Eval',
      '-c',
      'user.email=lean-eval@deepscientist.invalid',
      'commit',
      '--no-gpg-sign',
      '-m',
      message.slice(0, 200),
    ],
    { encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }
  );
  if (commitResult.status !== 0) throw new Error(commitResult.stderr?.trim() || 'LeanEval submission commit failed');
  const targetCommit = git(verifierRoot, ['rev-parse', 'HEAD']).toLowerCase();
  return Object.freeze({ projectRoot: verifierRoot, targetCommit, files: Object.freeze(commitFiles) });
}

const collectSolverFilesForCommit = (solverRoot: string, expected: readonly string[]): readonly string[] => {
  const actual = collectLeanEvalSubmissionFiles(solverRoot);
  const expectedSet = new Set(expected);
  if (actual.some((file) => !expectedSet.has(file)) || expected.some((file) => !actual.includes(file))) {
    throw new Error('LeanEval solver files do not match the bootstrap ownership manifest');
  }
  return actual;
};

const assertSubmissionCommitDelta = (bootstrapped: LeanEvalBootstrapResult, targetCommit: string): void => {
  const verifierRoot = bootstrapped.receipt.verifierProjectRoot;
  if (!verifierRoot) throw new Error('LeanEval submission has no verifier worktree');
  try {
    git(verifierRoot, ['merge-base', '--is-ancestor', bootstrapped.receipt.benchmarkCommit, targetCommit]);
  } catch {
    throw new Error('LeanEval submission commit must descend from the pinned benchmark commit');
  }
  const generatedPrefix = `${safeRelative(bootstrapped.problem.generatedPath)}/`;
  const allowed = new Set<string>([
    ...bootstrapped.receipt.solverOwnedFiles.map((file) => `${generatedPrefix}${safeRelative(file)}`),
    safeRelative(bootstrapped.binding.officialManifestPath),
    safeRelative(bootstrapped.binding.authorityPath),
  ]);
  const lines = git(verifierRoot, ['diff', '--name-status', bootstrapped.receipt.benchmarkCommit, targetCommit])
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter(Boolean);
  if (lines.length === 0) throw new Error('LeanEval submission commit contains no changes');
  let solverChange = false;
  for (const line of lines) {
    const fields = line.split(/\t/u);
    const status = fields[0]?.trim() || '';
    const paths = fields.slice(1).map((value) => safeRelative(value));
    if (!status || status.startsWith('D') || paths.length === 0 || paths.some((file) => !allowed.has(file))) {
      throw new Error('LeanEval submission commit contains changes outside solver-owned and official binding files');
    }
    if (paths.some((file) => file.startsWith(generatedPrefix))) solverChange = true;
  }
  if (!solverChange) throw new Error('LeanEval submission commit does not contain a solver-owned proof change');
};

/** Commit the solver output and run the pinned official comparator as one gate. */
export async function runLeanEvalOfficialGate(
  bootstrapped: LeanEvalBootstrapResult,
  options: LeanEvalOfficialGateOptions = {}
): Promise<LeanEvalOfficialGateResult> {
  // Eligibility is an authority decision, so a cached intake snapshot is not
  // sufficient. Refresh immediately before any submission commit/gate and
  // fail closed if the leaderboard cannot be reached.
  if (bootstrapped.receipt.leaderboardSource === LEAN_EVAL_LEADERBOARD_URL) {
    let freshLeaderboard: Readonly<{
      credits: readonly { problemId: string; statementRevision: number }[];
      generatedAt: number;
    }>;
    try {
      freshLeaderboard = await (options.fetchLeaderboard
        ? options.fetchLeaderboard()
        : fetchLeanEvalLeaderboardCredits({ forceRefresh: true }));
    } catch (error) {
      throw new Error(
        `Lean-Eval official gate is blocked because leaderboard freshness could not be verified: ${
          error instanceof Error ? error.message : String(error)
        }`,
        { cause: error }
      );
    }
    if (
      freshLeaderboard.credits.some(
        (credit) =>
          credit.problemId === bootstrapped.problem.id &&
          credit.statementRevision === bootstrapped.problem.statementRevision
      )
    ) {
      throw new Error(
        'Lean-Eval official gate refuses a problem that gained an accepted leaderboard credit after bootstrap'
      );
    }
  }
  const submission = options.commit ?? commitLeanEvalSubmission(bootstrapped, options.commitMessage);
  const verifierRoot = bootstrapped.receipt.verifierProjectRoot;
  if (!verifierRoot || path.resolve(submission.projectRoot) !== path.resolve(verifierRoot)) {
    throw new Error('LeanEval official gate submission must target the bootstrap verifier worktree');
  }
  if (submission.targetCommit.toLowerCase() === bootstrapped.receipt.benchmarkCommit.toLowerCase()) {
    throw new Error('LeanEval official gate refuses the unchanged benchmark commit');
  }
  if (!/^[0-9a-f]{40,64}$/iu.test(submission.targetCommit)) {
    throw new Error('LeanEval official gate submission targetCommit must be a full Git object id');
  }
  assertSubmissionCommitDelta(bootstrapped, submission.targetCommit);
  const solverProjectRoot = path.resolve(bootstrapped.receipt.projectRoot);
  const proofFiles = bootstrapped.receipt.solverOwnedFiles.filter((file) => file.endsWith('.lean'));
  const declarationFile = new Map<string, string>();
  for (const relative of proofFiles) {
    const absolute = path.join(solverProjectRoot, relative);
    const source = fs.readFileSync(absolute, 'utf8');
    for (const declaration of inspectLeanDeclarations(source)) {
      declarationFile.set(declaration.name, relative);
      const local = declaration.name.split('.').at(-1);
      if (local) declarationFile.set(local, relative);
    }
  }
  const localItems = bootstrapped.analysis.holes.map((hole) => ({
    id: hole.name,
    proofPath: declarationFile.get(hole.name) || declarationFile.get(hole.basename) || 'Submission.lean',
    theoremName: hole.name,
    statementHash: bootstrapped.binding.problemContract.statementHash,
    leanStatementHash: bootstrapped.binding.problemContract.leanStatementHash,
    expectedSourceDeclarationHash: hashMathFormalSourceDeclaration(hole.declarationBody, hole.basename),
  }));
  const localGate = await checkManyFormalVerifications(
    {
      projectRoot: verifierRoot,
      targetCommit: submission.targetCommit,
      timeoutMs: options.timeoutMs,
      items: localItems,
    },
    options.signal ? { signal: options.signal, env: options.env } : { env: options.env }
  );
  const decisive = decisiveHole(bootstrapped.analysis);
  const hasAllKernelReceipts =
    decisive !== undefined && hasCompleteLeanEvalLocalGateResults(localItems, localGate, submission.targetCommit);
  if (
    localGate.status !== 'kernel_verified' ||
    localGate.results.some((result) => result.status !== 'kernel_verified') ||
    !hasAllKernelReceipts
  ) {
    return Object.freeze({
      submission,
      localGate,
      comparison: Object.freeze({
        status: localGate.status === 'unavailable' ? 'unavailable' : 'blocked',
        targetCommit: submission.targetCommit,
        command: bootstrapped.binding.problemContract.officialVerificationCommand,
        exitCode: null,
        signal: null,
        timedOut: false,
        aborted: Boolean(options.signal?.aborted),
        stdoutSha256: sha256(''),
        stderrSha256: sha256('LOCAL_GATE did not produce a kernel-verified candidate.'),
        stdoutPreview: '',
        stderrPreview: 'LOCAL_GATE did not produce a kernel-verified candidate.',
        durationMs: 0,
        checkedAt: Date.now(),
        error: 'Lean-Eval LOCAL_GATE did not pass; official comparator was not started.',
      }),
    });
  }
  const execution: MathematicsVerifierExecutionOptions = {
    ...(options.signal ? { signal: options.signal } : {}),
    ...(options.env ? { env: options.env } : {}),
  };
  const comparison = await runOfficialComparator(
    {
      projectRoot: verifierRoot,
      targetCommit: submission.targetCommit,
      command: bootstrapped.binding.problemContract.officialVerificationCommand,
      officialManifestPath: bootstrapped.binding.officialManifestPath,
      officialManifest: bootstrapped.binding.officialManifest,
      expectedContract: bootstrapped.binding.problemContract,
      problemId: bootstrapped.problem.id,
      statementHash: bootstrapped.binding.problemContract.statementHash,
      ...(options.timeoutMs !== undefined ? { timeoutMs: options.timeoutMs } : {}),
    },
    execution
  );
  let officialGateReceipt: MathOfficialGateReceipt | undefined;
  if (comparison.status === 'official_verified') {
    const decisiveItem = decisive ? localItems.find((item) => item.theoremName === decisive.name) : undefined;
    const local = decisiveItem
      ? localGate.results.find((result) =>
          isLeanEvalLocalGateResultBound(decisiveItem, result, submission.targetCommit)
        )
      : undefined;
    const secret = readMathematicsReceiptSecret();
    if (!local || !secret || !local.theoremName || !local.theoremDeclarationHash) {
      throw new Error('Lean-Eval official gate cannot sign a receipt without a named kernel-verified theorem and key');
    }
    officialGateReceipt = signMathOfficialGateReceipt(
      {
        receiptId: `official-${sha256(`${submission.targetCommit}\0${local.receiptId}\0${comparison.stdoutSha256}`).slice(0, 24)}`,
        targetCommit: submission.targetCommit,
        statementHash: local.statementHash,
        claim: local.claim,
        routeFingerprint: bootstrapped.receipt.routeFingerprint,
        localGateReceiptId: local.receiptId,
        theoremName: local.theoremName,
        proofHash: local.proofHash,
        theoremDeclarationHash: local.theoremDeclarationHash,
        ...(local.sourceDeclarationHash ? { sourceDeclarationHash: local.sourceDeclarationHash } : {}),
        status: 'official_verified',
        verifier: 'official-comparator',
        command: comparison.command,
        exitCode: 0,
        timedOut: false,
        stdoutSha256: comparison.stdoutSha256,
        stderrSha256: comparison.stderrSha256,
        durationMs: comparison.durationMs,
        checkedAt: comparison.checkedAt,
        problemId: bootstrapped.problem.id,
        officialManifestPath: bootstrapped.binding.officialManifestPath,
        officialManifestId: comparison.officialManifestId!,
        officialManifestHash: comparison.officialManifestHash!,
        leanStatementHash: local.leanStatementHash,
        officialRepositoryUrl: comparison.officialRepositoryUrl!,
        officialBaselineCommit: comparison.officialBaselineCommit!,
        benchmarkAdapterId: comparison.benchmarkAdapterId!,
        benchmarkAdapterVersion: comparison.benchmarkAdapterVersion!,
      },
      secret
    );
    const receiptPath = path.join(
      bootstrapped.receipt.workspaceRoot,
      '.deepscientist',
      'math',
      'official-gate-receipt.json'
    );
    ensureDirectoryNoSymlink(path.dirname(receiptPath));
    writeFileDurably(receiptPath, `${JSON.stringify(officialGateReceipt, null, 2)}\n`);
  }
  return Object.freeze({ submission, localGate, comparison, ...(officialGateReceipt ? { officialGateReceipt } : {}) });
}

/** Remove the detached verifier worktree and disposable solver view. */
export function cleanupLeanEvalBootstrap(bootstrapped: LeanEvalBootstrapResult): void {
  const verifierRoot = bootstrapped.receipt.verifierProjectRoot;
  if (verifierRoot && fs.existsSync(verifierRoot)) {
    try {
      git(bootstrapped.binding.repositoryRoot, ['worktree', 'remove', '--force', verifierRoot]);
      git(bootstrapped.binding.repositoryRoot, ['worktree', 'prune']);
    } catch {
      // Keep cleanup best-effort; callers still receive the primary result.
    }
  }
  const sourceRoot = bootstrapped.receipt.sourceProjectRoot;
  if (sourceRoot && fs.existsSync(sourceRoot)) {
    try {
      git(bootstrapped.binding.repositoryRoot, ['worktree', 'remove', '--force', sourceRoot]);
      git(bootstrapped.binding.repositoryRoot, ['worktree', 'prune']);
    } catch {
      // Best effort; the reaper can remove an orphaned detached worktree.
    }
  }
  if (fs.existsSync(bootstrapped.receipt.workspaceRoot)) {
    fs.rmSync(bootstrapped.receipt.workspaceRoot, { recursive: true, force: true });
  }
}
