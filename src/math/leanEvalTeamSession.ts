/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import type { ResearchTeamAssignment } from "../common/types/team/researchTeamContracts";
import {
  findLeanEvalCatalogProblem,
  readLeanEvalCatalog,
  LEAN_EVAL_BENCHMARK_COMMIT,
  type LeanEvalCatalogProblem,
} from "./leanEvalCatalogAdapter";
import { analyzeLeanEvalProblem, type LeanEvalProblemAnalysis } from "./leanEvalProblemAnalyzer";
import {
  createLeanEvalProofExecutionFingerprint,
  runLeanEvalProofLoop,
  type LeanEvalProofAttempt,
  type LeanEvalProofAttemptContext,
  type LeanEvalSourceLocation,
  type LeanEvalProofStep,
  type LeanEvalProofLoopResult,
} from "./leanEvalProofLoop";
import { startMathematicsLeanSession, type MathematicsLeanProofSession } from "./leanInteractiveSession";
import type { LeanProofActionCandidate } from "./leanProofActionSearch";
import { leanEvalRetryDecision, type LeanEvalFailureCategory } from "./leanEvalFailurePolicy";
import { appendLeanEvalOutcome, readLeanEvalOutcomeSummary } from "./leanEvalOutcomeLedger";
import {
  appendLeanEvalEpisodeEvent,
  readLeanEvalEpisodeEvents,
  type LeanEvalProgressClass,
} from "./leanEvalEpisodeLedger";
import { calibrateLeanEvalExecutionPolicy } from "./leanEvalRouting";
import { reapLeanEvalArtifacts } from "./leanEvalCleanup";
import { getLeanEvalBootstrapAnalysis } from "./leanEvalBootstrap";
import { resolveMathRunHistory } from "./mathRunHistory";
import { createMathEvidencePacket } from "./mathSearchState";

export type LeanEvalTeamSessionRequest = Readonly<{
  assignment: ResearchTeamAssignment;
  workspaceRoot: string;
  /** Canonical project root for durable cross-assignment outcome calibration. */
  projectRoot?: string;
  repositoryRoot: string;
  signal?: AbortSignal;
  timeoutMs?: number;
  premiseCandidates?: readonly Readonly<{ name: string; type: string }>[];
  /** Optional structured search provider, still guarded by the proof loop. */
  structuredSearch?: (
    context: LeanEvalProofAttemptContext
  ) => Promise<LeanEvalProofAttempt | undefined> | LeanEvalProofAttempt | undefined;
  actionCandidates?: (
    context: LeanEvalProofAttemptContext
  ) => Promise<readonly LeanProofActionCandidate[]> | readonly LeanProofActionCandidate[];
  /** @deprecated Repair episodes are no longer capped; retained for callers upgrading in place. */
  maxCandidateAttempts?: number;
}>;

export type LeanEvalRepairRequest = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-repair.v1';
  assignmentId: string;
  problemId: string;
  attemptsUsed: number;
  failureCategory: LeanEvalFailureCategory;
  repairAction: ReturnType<typeof leanEvalRetryDecision>['action'];
  diagnostic: string;
  diagnosticHash: string;
  firstLeanError: string;
  firstLeanErrorOffset?: number;
  messageKind?: string;
  sourceFile?: string;
  sourceLocation?: LeanEvalSourceLocation;
  openGoal?: string;
  openGoalCount?: number;
  proofStateFingerprint: string;
  candidateProofHash?: string;
  rejectedCandidateHashes: readonly string[];
  nextObjective: string;
}>;

export type LeanEvalTeamSessionResult = Readonly<{
  proofLoop: LeanEvalProofLoopResult;
  gitHeadCommit: string;
  math: Readonly<Record<string, unknown>>;
  mathCheckpoint?: Readonly<Record<string, unknown>>;
  repairRequest?: LeanEvalRepairRequest;
  disposition: 'accepted' | 'refuted' | 'inconclusive' | 'blocked';
}>;

/**
 * A repair episode may span many Worker deliveries.  The proof loop already
 * deduplicates a candidate inside one invocation, but a resumed checkpoint
 * used to let the same rejected source re-enter on every later delivery.  Do
 * not cap useful search by time or tokens; only escalate when the durable
 * proof history proves that the frontier itself is repeating.
 */
export function isLeanEvalRepairStagnant(proofLoop: LeanEvalProofLoopResult): boolean {
  if (proofLoop.status !== 'failed') return false;
  const failed = proofLoop.steps.filter(
    (step) =>
      (step.status === 'failed' || step.status === 'skipped') &&
      step.category !== undefined &&
      ['actual_proof_failure', 'missing_hole', 'submission_namespace_mismatch', 'import_or_olean_mismatch'].includes(
        step.category
      )
  );
  const latest = failed.at(-1);
  if (!latest) return false;

  const latestHash = latest.candidateProofHash;
  if (
    latestHash &&
    failed.filter((step) => step.category === latest.category && step.candidateProofHash === latestHash).length >= 2
  ) {
    return true;
  }

  const diagnosticFingerprint = (step: (typeof failed)[number]): string =>
    step.diagnostic?.proofStateFingerprint ??
    sha256(
      `${step.category}\u0000${(step.diagnostic?.message ?? step.stderr ?? '')
        .replaceAll('\r\n', '\n')
        .replaceAll('\r', '\n')
        .trim()
        .replace(/\s+/gu, ' ')}`
    );
  const latestFingerprint = diagnosticFingerprint(latest);
  let repeatedFrontier = 0;
  for (const step of failed.toReversed()) {
    if (step.category !== latest.category || diagnosticFingerprint(step) !== latestFingerprint) break;
    repeatedFrontier += 1;
  }
  // Three independent candidate edits with the same first diagnostic are
  // enough evidence to return control to the Lead for route selection.
  return repeatedFrontier >= 3;
}

const fullGitObjectId = /^[0-9a-f]{40,64}$/u;
const publicBindingFiles = Object.freeze([
  'Challenge.lean',
  'ChallengeDeps.lean',
  'config.json',
  'holes.json',
  'lakefile.toml',
  'lakefile.lean',
  'lean-toolchain',
  'WorkspaceTest.lean',
  'README.md',
]);
const requiredPublicBindingFiles = new Set([
  'Challenge.lean',
  'config.json',
  'holes.json',
  'lakefile.toml',
  'lean-toolchain',
  'WorkspaceTest.lean',
]);
const pinnedPublicBindingCache = new Map<string, ReadonlyMap<string, string | undefined>>();
const MAX_PINNED_PUBLIC_BINDING_CACHE_ENTRIES = 32;

const sha256 = (value: Uint8Array | string): string => crypto.createHash('sha256').update(value).digest('hex');
const MAX_REPAIR_DIAGNOSTIC_BYTES = 12_000;

const failedProofStep = (proofLoop: LeanEvalProofLoopResult): LeanEvalProofStep | undefined =>
  proofLoop.steps.toReversed().find((step) => step.status === 'failed');

/** Build the runtime-owned instruction that keeps a repairable candidate in the same model turn. */
export function createLeanEvalRepairRequest(
  input: Readonly<{
    assignmentId: string;
    problemId: string;
    proofLoop: LeanEvalProofLoopResult;
    /** @deprecated Ignored. Cross-turn repair is governed by cancellation/deadline and diagnostics. */
    maxAttempts?: number;
  }>
): LeanEvalRepairRequest | undefined {
  if (input.proofLoop.status !== 'failed') return undefined;
  const failed = failedProofStep(input.proofLoop);
  const failureCategory = failed?.category ?? input.proofLoop.failure?.category;
  if (!failureCategory) return undefined;
  const retry = leanEvalRetryDecision(failureCategory);
  if (!retry.retryable || ['retry_sandbox', 'prepare_toolchain', 'inspect_comparator'].includes(retry.action)) {
    return undefined;
  }
  const attemptsUsed = input.proofLoop.steps.filter((step) => step.status !== 'skipped').length;
  if (attemptsUsed <= 0) return undefined;
  const compilerDiagnostic = failed?.diagnostic;
  const rawDiagnostic = compilerDiagnostic?.message ?? failed?.stderr ?? input.proofLoop.failure?.message;
  const diagnostic = rawDiagnostic?.trim().slice(0, MAX_REPAIR_DIAGNOSTIC_BYTES);
  if (!diagnostic) return undefined;
  const repairProofStateFingerprint =
    compilerDiagnostic?.proofStateFingerprint ??
    sha256(
      JSON.stringify({
        failureCategory,
        firstLeanError: diagnostic.replaceAll('\r\n', '\n').replaceAll('\r', '\n'),
      })
    );
  const rejectedCandidateHashes = [
    ...new Set(
      input.proofLoop.steps
        .filter((step) => step.status === 'failed')
        .flatMap((step) => (step.candidateProofHash ? [step.candidateProofHash] : []))
    ),
  ].slice(-8);
  return Object.freeze({
    schema: 'deepscientist.mathematics.lean-eval-repair.v1',
    assignmentId: input.assignmentId,
    problemId: input.problemId,
    attemptsUsed,
    failureCategory,
    repairAction: retry.action,
    diagnostic,
    diagnosticHash: sha256(diagnostic),
    firstLeanError: diagnostic,
    ...(compilerDiagnostic?.location?.sourceOffset !== undefined
      ? { firstLeanErrorOffset: compilerDiagnostic.location.sourceOffset }
      : {}),
    ...(compilerDiagnostic?.messageKind ? { messageKind: compilerDiagnostic.messageKind } : {}),
    ...(failed?.sourceFile ? { sourceFile: failed.sourceFile } : {}),
    ...(compilerDiagnostic?.location ? { sourceLocation: compilerDiagnostic.location } : {}),
    ...(compilerDiagnostic?.openGoal ? { openGoal: compilerDiagnostic.openGoal } : {}),
    ...(compilerDiagnostic?.openGoalCount !== undefined ? { openGoalCount: compilerDiagnostic.openGoalCount } : {}),
    proofStateFingerprint: repairProofStateFingerprint,
    ...(failed?.candidateProofHash ? { candidateProofHash: failed.candidateProofHash } : {}),
    rejectedCandidateHashes: Object.freeze(rejectedCandidateHashes),
    nextObjective:
      'Change the current Lean candidate to resolve the first reported diagnostic, preserve already valid declarations, and call deliver again from this same Worker conversation.',
  });
}

const gitHead = (workspaceRoot: string): string => {
  const value = execFileSync('git', ['-C', workspaceRoot, 'rev-parse', 'HEAD'], {
    encoding: 'utf8',
    maxBuffer: 128 * 1024,
  })
    .trim()
    .toLowerCase();
  if (!fullGitObjectId.test(value)) throw new Error('Lean-Eval proof session could not read a full Worker Git HEAD');
  return value;
};

/**
 * A prepared Worker may start from a candidate that is already complete. The
 * kernel check is still authoritative, but the delivery contract requires a
 * Worker-owned commit. Never manufacture an empty host commit to make an
 * unchanged candidate look like solver progress.
 */
const materializeSolverCompletionCommit = (workspaceRoot: string, initialHead: string): string => {
  const currentHead = gitHead(workspaceRoot);
  if (currentHead !== initialHead) return currentHead;
  const status = execFileSync('git', ['-C', workspaceRoot, 'status', '--porcelain=v1', '--untracked-files=normal'], {
    encoding: 'utf8',
    maxBuffer: 128 * 1024,
  }).trim();
  if (status) throw new Error('solver_worker_worktree_not_committed');
  throw new Error('solver_worker_commit_required');
};

const gitRoot = (workspaceRoot: string): string => {
  const value = execFileSync('git', ['-C', workspaceRoot, 'rev-parse', '--show-toplevel'], {
    encoding: 'utf8',
    maxBuffer: 128 * 1024,
  }).trim();
  if (!value || !path.isAbsolute(value))
    throw new Error('Lean-Eval proof session could not resolve the Worker Git root');
  return fs.realpathSync(value);
};

const regularFile = (file: string): boolean => {
  try {
    const stat = fs.lstatSync(file);
    return stat.isFile() && !stat.isSymbolicLink();
  } catch {
    return false;
  }
};

const resolveCandidateRoot = (workspaceRoot: string, generatedPath: string): string => {
  const resolvedWorkspaceRoot = path.resolve(workspaceRoot);
  const candidates = [path.join(resolvedWorkspaceRoot, generatedPath), resolvedWorkspaceRoot];
  for (const candidate of candidates) {
    try {
      const stat = fs.lstatSync(candidate);
      if (
        stat.isSymbolicLink() ||
        !stat.isDirectory() ||
        !regularFile(path.join(candidate, 'Submission.lean')) ||
        !regularFile(path.join(candidate, 'Challenge.lean'))
      )
        continue;
      return fs.realpathSync(candidate);
    } catch {
      // Try the other supported worktree shape.
    }
  }
  throw new Error('Lean-Eval proof session requires a worktree containing the selected generated problem');
};

/**
 * The Worker worktree is mutable. Before compiling, re-bind every public
 * evaluator input to the pinned benchmark so a Worker cannot change the
 * statement, hole declarations, or test driver and obtain a false local
 * success. Solution.lean is intentionally absent from this list and is never
 * read by the proof session.
 */
export const assertPinnedPublicBinding = (
  repositoryRoot: string,
  benchmarkCommit: string,
  problem: LeanEvalCatalogProblem,
  candidateRoot: string,
  pinnedSourceRoot = repositoryRoot
): void => {
  const cacheKey = `${path.resolve(repositoryRoot)}\0${benchmarkCommit}\0${problem.id}`;
  let pinnedHashes = pinnedPublicBindingCache.get(cacheKey);
  if (pinnedHashes) {
    pinnedPublicBindingCache.delete(cacheKey);
    pinnedPublicBindingCache.set(cacheKey, pinnedHashes);
  }
  if (!pinnedHashes) {
    const hashes = new Map<string, string | undefined>();
    for (const file of publicBindingFiles) {
      const relative = `${problem.generatedPath}/${file}`;
      try {
        hashes.set(
          file,
          sha256(
            execFileSync('git', ['-C', repositoryRoot, 'show', `${benchmarkCommit}:${relative}`], {
              maxBuffer: 16 * 1024 * 1024,
            })
          )
        );
      } catch {
        if (requiredPublicBindingFiles.has(file)) {
          throw new Error(`Lean-Eval pinned public file is missing: ${relative}`);
        }
        hashes.set(file, undefined);
      }
    }
    pinnedHashes = hashes;
    pinnedPublicBindingCache.set(cacheKey, pinnedHashes);
    while (pinnedPublicBindingCache.size > MAX_PINNED_PUBLIC_BINDING_CACHE_ENTRIES) {
      const oldest = pinnedPublicBindingCache.keys().next().value;
      if (oldest === undefined) break;
      pinnedPublicBindingCache.delete(oldest);
    }
  }
  const sourceRoot = path.resolve(pinnedSourceRoot);
  const candidateIsPinnedSource = path.resolve(candidateRoot) === sourceRoot;
  const intentionallyExcludedFromSolver = new Set(['WorkspaceTest.lean', 'README.md']);
  for (const file of publicBindingFiles) {
    const current = path.join(candidateRoot, file);
    const pinnedHash = pinnedHashes.get(file);
    if (!pinnedHash) {
      if (fs.existsSync(current)) {
        throw new Error(`Lean-Eval Worker public file is not present in the pinned benchmark: ${file}`);
      }
      continue;
    }

    // The immutable source worktree is the authority for public files that
    // are deliberately omitted from the solver view.  Checking it here keeps
    // the binding meaningful without requiring the solver workspace to carry
    // evaluator-only material such as WorkspaceTest.lean.
    const sourceProblemFile = path.join(sourceRoot, problem.generatedPath, file);
    const sourceFile = regularFile(sourceProblemFile)
      ? sourceProblemFile
      : candidateIsPinnedSource
        ? path.join(sourceRoot, file)
        : sourceProblemFile;
    if (!regularFile(sourceFile) || sha256(fs.readFileSync(sourceFile)) !== pinnedHash) {
      throw new Error(`Lean-Eval pinned source public file is missing or differs from the benchmark: ${file}`);
    }
    if (!candidateIsPinnedSource && intentionallyExcludedFromSolver.has(file)) continue;
    if (!regularFile(current)) throw new Error(`Lean-Eval Worker public file is missing or unsafe: ${file}`);
    const contents = fs.readFileSync(current);
    if (sha256(contents) !== pinnedHash) {
      throw new Error(`Lean-Eval Worker public file differs from the pinned benchmark: ${file}`);
    }
  }
};

const readCurrentSubmission = (workspaceRoot: string): Readonly<{ source: string; file: string }> => {
  const file = 'Submission.lean';
  const absolute = path.join(workspaceRoot, file);
  const stat = fs.lstatSync(absolute);
  if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Lean-Eval proof session requires Submission.lean');
  return Object.freeze({ source: fs.readFileSync(absolute, 'utf8'), file });
};

const submissionFingerprint = (workspaceRoot: string): string => {
  const files: Array<[string, string]> = [];
  const visit = (relative: string): void => {
    const absolute = path.join(workspaceRoot, relative);
    if (!fs.existsSync(absolute)) return;
    const stat = fs.lstatSync(absolute);
    if (stat.isSymbolicLink()) throw new Error(`Lean-Eval submission contains a symlink: ${relative}`);
    if (stat.isDirectory()) {
      for (const entry of fs.readdirSync(absolute).toSorted()) visit(`${relative}/${entry}`);
      return;
    }
    if (!stat.isFile() || (relative !== 'Submission.lean' && !relative.startsWith('Submission/'))) {
      throw new Error(`Lean-Eval submission contains an unauthorized file: ${relative}`);
    }
    files.push([relative, sha256(fs.readFileSync(absolute))]);
  };
  visit('Submission.lean');
  visit('Submission');
  return sha256(JSON.stringify(files));
};

const failureCategory = (loop: LeanEvalProofLoopResult): string | undefined => {
  // A deterministic duplicate can be recorded as a skipped step after the
  // original compiler failure. Keep the durable failure classification instead
  // of turning that episode into an ambiguous inconclusive result.
  const step = loop.steps.toReversed().find((candidate) => candidate.status === 'failed');
  if (!step) return undefined;
  if (step.category === 'landrun_failure') return 'landrun_failure';
  if (step.category === 'toolchain_unavailable') return 'toolchain';
  return 'actual_proof_failure';
};

type SessionAnalysis = Readonly<{
  problem: LeanEvalCatalogProblem;
  analysis: LeanEvalProblemAnalysis;
}>;

const sessionAnalysisCache = new Map<string, SessionAnalysis>();
const sessionAnalysisInflight = new Map<string, Promise<SessionAnalysis>>();
const proofLoopCache = new Map<string, LeanEvalProofLoopResult>();
const proofLoopInflight = new Map<string, Promise<LeanEvalProofLoopResult>>();
/**
 * Keep the source-backed Lean session alive across repair deliveries.  A
 * Research Team delivery is a transport boundary, not a proof boundary.
 * Reusing the session preserves its state/action de-duplication while the
 * worker edits the same episode workspace.
 */
const proofSessionCache = new Map<string, MathematicsLeanProofSession>();
const MAX_PROOF_SESSION_CACHE_ENTRIES = 32;
const MAX_PROOF_LOOP_CACHE_ENTRIES = 64;

const trustedLakePackagesPath = (repositoryRoot: string): string | undefined => {
  const candidate = path.join(repositoryRoot, '.lake', 'packages');
  try {
    const stat = fs.lstatSync(candidate);
    if (stat.isSymbolicLink() || !stat.isDirectory()) return undefined;
    return fs.realpathSync(candidate);
  } catch {
    return undefined;
  }
};

const cacheProofLoop = (key: string, result: LeanEvalProofLoopResult): void => {
  // Infrastructure failures must be allowed to recover in a later delivery;
  // deterministic proof failures and successful checks are safe to reuse for
  // an unchanged assignment/worktree candidate.
  const infrastructureFailure = result.steps.some(
    (step) => step.category === 'landrun_failure' || step.category === 'toolchain_unavailable'
  );
  if (result.status === 'aborted' || infrastructureFailure) return;
  proofLoopCache.delete(key);
  proofLoopCache.set(key, result);
  while (proofLoopCache.size > MAX_PROOF_LOOP_CACHE_ENTRIES) {
    const oldest = proofLoopCache.keys().next().value;
    if (oldest === undefined) break;
    proofLoopCache.delete(oldest);
  }
};

const proofSessionKey = (
  input: Readonly<{
    episodeId: string;
    workspaceRoot: string;
    statementHash: string;
    routeFingerprint: string;
    executionFingerprint: string;
    submissionFingerprint: string;
  }>
): string =>
  [
    input.episodeId,
    path.resolve(input.workspaceRoot),
    input.statementHash,
    input.routeFingerprint,
    input.executionFingerprint,
    input.submissionFingerprint,
  ].join('\0');

/** Stable identity shared by all repair assignments for one proof route. */
export const createLeanEvalSolverEpisodeId = (
  input: Readonly<{ problemId: string; statementHash: string; routeFingerprint: string; runIdentity?: string }>
): string => `lean-eval-episode-${sha256(JSON.stringify(input)).slice(0, 40)}`;

const cacheProofSession = (key: string, session: MathematicsLeanProofSession): void => {
  const [episode, workspace] = key.split('\0');
  for (const [previousKey, previous] of proofSessionCache) {
    const [previousEpisode, previousWorkspace] = previousKey.split('\0');
    if (previousEpisode === episode && previousWorkspace === workspace && previous !== session) {
      previous.close();
      proofSessionCache.delete(previousKey);
    }
  }
  proofSessionCache.delete(key);
  proofSessionCache.set(key, session);
  while (proofSessionCache.size > MAX_PROOF_SESSION_CACHE_ENTRIES) {
    const oldest = proofSessionCache.keys().next().value;
    if (oldest === undefined) break;
    proofSessionCache.get(oldest)?.close();
    proofSessionCache.delete(oldest);
  }
};

const catalogProblemAndAnalysis = async (
  repositoryRoot: string,
  problemId: string,
  historicalOutcomes?: Readonly<{ attempts: number; successes: number }>
): Promise<SessionAnalysis> => {
  const key = `${path.resolve(repositoryRoot)}\0${LEAN_EVAL_BENCHMARK_COMMIT}\0${problemId}\0${historicalOutcomes?.attempts ?? 0}\0${historicalOutcomes?.successes ?? 0}`;
  const cached = sessionAnalysisCache.get(key);
  if (cached) return cached;
  const active = sessionAnalysisInflight.get(key);
  if (active) return active;
  const pending = Promise.resolve()
    .then(() => {
      const catalog = readLeanEvalCatalog({
        repositoryRoot,
        benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
        credits: [],
        verifyGitCommit: true,
      });
      const problem = findLeanEvalCatalogProblem(catalog, problemId);
      if (!problem) throw new Error(`Lean-Eval problem is not in the pinned catalog: ${problemId}`);
      if (!problem.activeV1 || problem.status !== 'active' || !problem.visible || problem.statementRevision !== 1) {
        throw new Error(`Lean-Eval problem is not active at the pinned statement revision: ${problemId}`);
      }
      const bootstrappedAnalysis = getLeanEvalBootstrapAnalysis(repositoryRoot, problemId);
      if (
        bootstrappedAnalysis &&
        bootstrappedAnalysis.feasibility.acceptedCreditCount === problem.acceptedCreditCount
      ) {
        const analysis = historicalOutcomes
          ? Object.freeze({
              ...bootstrappedAnalysis,
              feasibility: Object.freeze({
                ...bootstrappedAnalysis.feasibility,
                historicalAttempts: historicalOutcomes.attempts,
                historicalSuccesses: historicalOutcomes.successes,
              }),
            })
          : bootstrappedAnalysis;
        return Promise.resolve(Object.freeze({ problem, analysis }));
      }
      return analyzeLeanEvalProblem(problem, {
        repositoryRoot,
        benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
        ...(historicalOutcomes ? { historicalOutcomes } : {}),
      }).then((analysis) => Object.freeze({ problem, analysis }));
    })
    .then((value) => {
      sessionAnalysisCache.set(key, value);
      return value;
    })
    .finally(() => {
      sessionAnalysisInflight.delete(key);
    });
  sessionAnalysisInflight.set(key, pending);
  return pending;
};

/**
 * Execute one official Lean-Eval direct proof episode from the assigned
 * Worker worktree.  The returned patch contains no Worker-provided goal or
 * error counts; all progress fields are derived from the proof loop result.
 */
export async function runLeanEvalTeamSession(request: LeanEvalTeamSessionRequest): Promise<LeanEvalTeamSessionResult> {
  const episodeStartedAt = Date.now();
  const assignment = request.assignment;
  const math = assignment.math;
  if (!math?.directAttempt || math.stage !== 'formalize') {
    throw new Error('Lean-Eval team session requires a direct FORMALIZE assignment');
  }
  const problemId = math.problemContract?.problemId;
  if (!problemId || !math.problemContract?.officialManifestId?.startsWith('lean-eval:')) {
    throw new Error('Lean-Eval team session requires an official Lean-Eval problem contract');
  }
  const repositoryRoot = path.resolve(request.repositoryRoot);
  const workerGitRoot = gitRoot(request.workspaceRoot);
  const pinnedSourceRoot = `${workerGitRoot}.source`;
  const catalogRepositoryRoot = fs.existsSync(path.join(pinnedSourceRoot, '.git')) ? pinnedSourceRoot : repositoryRoot;
  const historyProjectRoot = path.resolve(request.projectRoot || workerGitRoot);
  const history = resolveMathRunHistory(historyProjectRoot, problemId);
  const ledgerRoot = history.root;
  const checkpointRoot =
    historyProjectRoot === workerGitRoot ? ledgerRoot : resolveMathRunHistory(workerGitRoot, problemId).root;
  reapLeanEvalArtifacts({ repositoryRoot, projectRoots: [...new Set([ledgerRoot, checkpointRoot])] });
  const historical = readLeanEvalOutcomeSummary(ledgerRoot, problemId, history.runIdentity);
  const strategyHistory = history.runIdentity ? historical : readLeanEvalOutcomeSummary(ledgerRoot);
  const { problem, analysis } = await catalogProblemAndAnalysis(catalogRepositoryRoot, problemId, {
    attempts: historical.attempts,
    successes: historical.successes,
  });
  const candidateRoot = resolveCandidateRoot(request.workspaceRoot, problem.generatedPath);
  assertPinnedPublicBinding(repositoryRoot, LEAN_EVAL_BENCHMARK_COMMIT, problem, candidateRoot, pinnedSourceRoot);
  const currentSubmission = readCurrentSubmission(candidateRoot);
  const initialHead = gitHead(request.workspaceRoot);
  const packageCachePath = trustedLakePackagesPath(repositoryRoot);
  const episodeId = createLeanEvalSolverEpisodeId({
    problemId,
    statementHash: math.statementHash,
    routeFingerprint: math.routeFingerprint,
    ...(history.runIdentity ? { runIdentity: history.runIdentity } : {}),
  });
  // A direct FORMALIZE assignment owns one whole-contract candidate.
  const sessionAnalysis: LeanEvalProblemAnalysis = Object.freeze({
    ...analysis,
    holeSchedule: Object.freeze({
      ...analysis.holeSchedule,
      waves: Object.freeze([Object.freeze(analysis.holes.map((hole) => hole.name))]),
      ready: Object.freeze(analysis.holes.map((hole) => hole.name)),
      completed: Object.freeze([]),
      blocked: Object.freeze([]),
    }),
  });
  const executionFingerprint = createLeanEvalProofExecutionFingerprint({
    workspaceRoot: candidateRoot,
    analysis: sessionAnalysis,
    lakePackagesPath: packageCachePath,
    sandboxed: true,
  });
  const currentSubmissionFingerprint = submissionFingerprint(candidateRoot);
  const priorEpisodeEvents = readLeanEvalEpisodeEvents(ledgerRoot).filter(
    (event) => event.episodeId === episodeId && (!history.runIdentity || event.runIdentity === history.runIdentity)
  );
  const sessionKey = proofSessionKey({
    episodeId,
    workspaceRoot: candidateRoot,
    statementHash: math.statementHash,
    routeFingerprint: math.routeFingerprint,
    executionFingerprint,
    submissionFingerprint: currentSubmissionFingerprint,
  });
  const cachedSession = proofSessionCache.get(sessionKey);
  let proofSession = cachedSession;
  // A repair may replace the source outside the session.  The old source
  // backed state cannot safely be restored against a different source hash,
  // so start a fresh compiler-backed state while retaining the episode id.
  if (proofSession && proofSession.state.sourceHash !== sha256(currentSubmission.source)) {
    proofSession.close();
    proofSession = undefined;
  }
  if (!proofSession) {
    const interactiveSessionResult = await startMathematicsLeanSession({
      workspaceRoot: candidateRoot,
      sourceFile: 'Submission.lean',
      statementHash: math.statementHash,
      routeFingerprint: math.routeFingerprint,
      episodeId,
      signal: request.signal,
      lakePackagesPath: packageCachePath,
    });
    proofSession = interactiveSessionResult.status === 'started' ? interactiveSessionResult.session : undefined;
    if (proofSession) cacheProofSession(sessionKey, proofSession);
  } else {
    proofSessionCache.delete(sessionKey);
    proofSessionCache.set(sessionKey, proofSession);
  }
  try {
    appendLeanEvalEpisodeEvent(ledgerRoot, {
      ...(history.runIdentity ? { runIdentity: history.runIdentity } : {}),
      episodeId: proofSession?.episodeId ?? episodeId,
      assignmentId: assignment.assignmentId,
      problemId,
      statementHash: math.statementHash,
      kind: priorEpisodeEvents.length || (cachedSession && proofSession) ? 'episode_resumed' : 'episode_created',
    });
  } catch {
    // Telemetry must never change proof semantics. The outcome ledger and
    // checkpoint remain authoritative when an optional event ledger is not
    // writable.
  }
  const executionPolicy = assignment.math?.executionPolicy
    ? calibrateLeanEvalExecutionPolicy(assignment.math.executionPolicy, strategyHistory)
    : undefined;
  const proofLoopKey = [
    episodeId,
    workerGitRoot,
    initialHead,
    currentSubmissionFingerprint,
    request.timeoutMs ?? '',
    executionFingerprint,
    JSON.stringify(request.premiseCandidates ?? []),
    executionPolicy ? JSON.stringify(executionPolicy) : '',
  ].join('\0');
  const checkpointIdentity = `${episodeId}-${problem.id}`.replace(/[^A-Za-z0-9._-]+/gu, '_').slice(0, 180);
  const checkpointPath = path.join(
    checkpointRoot,
    '.deepscientist',
    'math',
    'lean-eval-proof',
    `${checkpointIdentity || 'session'}-${executionFingerprint.slice(0, 16)}.json`
  );
  let proofLoop = proofLoopCache.get(proofLoopKey);
  if (!proofLoop) {
    const active = proofLoopInflight.get(proofLoopKey);
    const pending =
      active ??
      runLeanEvalProofLoop({
        workspaceRoot: candidateRoot,
        historyProjectRoot,
        analysis: sessionAnalysis,
        episodeId: proofSession?.episodeId ?? episodeId,
        timeoutMs: request.timeoutMs,
        signal: request.signal,
        sandboxed: true,
        lakePackagesPath: packageCachePath,
        // Keep a bounded retry budget so the execution policy can actually
        // advance through tactic, premise, and model alternatives after a
        // failed Lean attempt. A single attempt leaves those runtime-owned
        // cursors inert.
        attemptsPerWave: 3,
        ...(executionPolicy ? { executionPolicy } : {}),
        ...(request.actionCandidates ? { actionCandidates: request.actionCandidates } : {}),
        ...(request.structuredSearch ? { structuredSearch: request.structuredSearch } : {}),
        executionFingerprint,
        checkpointPath,
        ...(fs.existsSync(checkpointPath)
          ? { resumeFromCheckpoint: checkpointPath, resumeSourcePolicy: 'accept_current_candidate' as const }
          : {}),
        // The Worker has already produced a candidate in its worktree.  Reading
        // it here makes the loop's compiler output authoritative without allowing
        // the Worker to inject a claimed goal/error summary.
        attempt: () => readCurrentSubmission(candidateRoot),
        ...(proofSession ? { proofSession } : {}),
      });
    if (!active) {
      proofLoopInflight.set(proofLoopKey, pending);
      pending
        .finally((): void => {
          proofLoopInflight.delete(proofLoopKey);
        })
        .catch((): void => {});
    }
    proofLoop = await pending;
    cacheProofLoop(proofLoopKey, proofLoop);
  }
  const completed = proofLoop.completedNames.length;
  const total = sessionAnalysis.holes.length;
  const complete = proofLoop.status === 'completed' && completed === total;
  const category = failureCategory(proofLoop);
  const failedStep = failedProofStep(proofLoop);
  const compilerDiagnostic = failedStep?.diagnostic;
  const repairRequest = createLeanEvalRepairRequest({
    assignmentId: assignment.assignmentId,
    problemId,
    proofLoop,
  });
  const stagnantRepair = Boolean(repairRequest && isLeanEvalRepairStagnant(proofLoop));
  const effectiveRepairRequest = stagnantRepair ? undefined : repairRequest;
  const outcome = complete
    ? ('success' as const)
    : proofLoop.status === 'aborted'
      ? ('aborted' as const)
      : category === 'landrun_failure'
        ? ('sandbox' as const)
        : category === 'toolchain'
          ? ('toolchain' as const)
          : ('proof_failure' as const);
  const existingOutcome = readLeanEvalOutcomeSummary(ledgerRoot, problemId, history.runIdentity);
  const decisiveStep = proofLoop.steps.toReversed().find((step) => step.status !== 'skipped');
  if (!repairRequest && existingOutcome.attempts <= historical.attempts) {
    appendLeanEvalOutcome(ledgerRoot, {
      ...(history.runIdentity ? { runIdentity: history.runIdentity } : {}),
      assignmentId: assignment.assignmentId,
      problemId,
      statementRevision: problem.statementRevision,
      statementHash: math.statementHash,
      route: math.routeFingerprint,
      archetype: 'direct-formalize',
      ...(decisiveStep?.selectedModel ? { modelId: decisiveStep.selectedModel } : {}),
      ...(decisiveStep?.tactic ? { tactic: decisiveStep.tactic } : {}),
      holeCount: total,
      criticalPath: analysis.feasibility.dependencyCriticalPath ?? total,
      compileAttempts: proofLoop.steps.length,
      toolchain: 'pinned',
      outcome,
      ...(category ? { failureCategory: category } : {}),
      elapsedMs: proofLoop.steps.reduce((sum, step) => sum + step.durationMs, 0),
    });
  }
  const openGoalCountAfter = complete ? 0 : Math.max(1, compilerDiagnostic?.openGoalCount ?? total - completed);
  const openGoalCountBefore = Math.max(1, total, openGoalCountAfter);
  const firstLeanError = complete
    ? undefined
    : (compilerDiagnostic?.message ?? failedStep?.stderr ?? proofLoop.failure?.message);
  const proofStateFingerprint = complete
    ? undefined
    : (compilerDiagnostic?.proofStateFingerprint ?? repairRequest?.proofStateFingerprint);
  const searchEvidence = createMathEvidencePacket({
    statementHash: math.statementHash,
    routeFingerprint: math.routeFingerprint,
    routeRevision: 0,
    proofStateFingerprint: proofStateFingerprint ?? (complete ? 'closed' : undefined),
    openGoals: compilerDiagnostic?.openGoal
      ? [compilerDiagnostic.openGoal]
      : complete
        ? []
        : [`${openGoalCountAfter} open goal(s) remain`],
    compiler: complete
      ? { status: 'passed', exitCode: 0 }
      : proofLoop.status === 'aborted'
        ? { status: 'timeout' }
        : category === 'landrun_failure' || category === 'toolchain'
          ? { status: 'unavailable' }
          : { status: 'failed', diagnostic: firstLeanError?.slice(0, 12_000) },
    unresolvedBridge: complete ? 'none' : 'unknown',
    counterexample: 'absent',
    elapsedMs: proofLoop.steps.reduce((sum, step) => sum + step.durationMs, 0),
    attempts: proofLoop.steps.filter((step) => step.status !== 'skipped').length,
    recentDelta: { goalCountBefore: openGoalCountBefore, goalCountAfter: openGoalCountAfter },
    independentEvaluator: 'missing',
    closedProof: complete,
    verifierReceipt: null,
    evidenceRefs: [
      `proof-loop:${episodeId}`,
      ...(compilerDiagnostic?.proofStateFingerprint ? [`proof-state:${compilerDiagnostic.proofStateFingerprint}`] : []),
    ],
  });
  const mathResult = Object.freeze({
    statementHash: math.statementHash,
    routeFingerprint: math.routeFingerprint,
    ...(math.activePlanNodeId ? { activePlanNodeId: math.activePlanNodeId } : {}),
    checkedDeclarationsAdded: completed,
    openGoalCountBefore,
    openGoalCountAfter,
    ...(compilerDiagnostic?.openGoal ? { openGoalAfter: compilerDiagnostic.openGoal } : {}),
    ...(proofStateFingerprint ? { openGoalFingerprintAfter: proofStateFingerprint } : {}),
    ...(firstLeanError ? { firstLeanErrorAfter: firstLeanError } : {}),
    ...(compilerDiagnostic?.location?.sourceOffset !== undefined
      ? { firstLeanErrorOffsetAfter: compilerDiagnostic.location.sourceOffset }
      : {}),
    evidencePacket: searchEvidence,
    evidenceDelta: Object.freeze([]),
    routeDisposition: complete ? 'advance' : 'blocked',
    nextSingleObjective: complete
      ? 'Send the unchanged solver-complete commit to LOCAL_GATE and the official comparator.'
      : stagnantRepair
        ? 'The same Lean-Eval proof frontier has repeated without new evidence. Return this delivery to the Lead so it can select a structurally distinct route or escalate the unresolved dependency.'
        : 'Repair the first Lean-Eval proof-loop diagnostic in the same candidate.',
    infraStatus:
      proofLoop.status === 'aborted' || category === 'landrun_failure' || category === 'toolchain'
        ? 'tool_unavailable'
        : 'ready',
    ...(category ? { failureCategory: category } : {}),
    ...(proofLoop.checkpoint.executionPolicy ? { executionPolicy: proofLoop.checkpoint.executionPolicy } : {}),
  });
  const previousProgressEvent = priorEpisodeEvents.toReversed().find((event) => event.progressClass !== undefined);
  const progressClassValue: string =
    proofLoop.status === 'aborted' || category === 'landrun_failure' || category === 'toolchain'
      ? 'infra_failed'
      : complete
        ? 'goal_progress'
        : completed > 0 && openGoalCountAfter < openGoalCountBefore
          ? 'goal_progress'
          : completed > 0
            ? 'frontier_progress'
            : 'stalled';
  const progressClass = progressClassValue as LeanEvalProgressClass;
  const scaffoldOnlyStreak =
    progressClass === 'scaffold_progress' ? (previousProgressEvent?.scaffoldOnlyStreak ?? 0) + 1 : 0;
  const goalProgressCount =
    (previousProgressEvent?.goalProgressCount ?? 0) + (progressClass === 'goal_progress' ? 1 : 0);
  const frontierProgressCount =
    (previousProgressEvent?.frontierProgressCount ?? 0) + (progressClass === 'frontier_progress' ? 1 : 0);
  try {
    const elapsedMs = Math.max(0, Date.now() - episodeStartedAt);
    const leanMs = proofLoop.steps.reduce((sum, step) => sum + step.durationMs, 0);
    appendLeanEvalEpisodeEvent(ledgerRoot, {
      ...(history.runIdentity ? { runIdentity: history.runIdentity } : {}),
      episodeId: proofSession?.episodeId ?? episodeId,
      assignmentId: assignment.assignmentId,
      problemId,
      statementHash: math.statementHash,
      kind: complete ? 'episode_completed' : 'episode_failed',
      elapsedMs,
      leanMs,
      orchestrationMs: Math.max(0, elapsedMs - leanMs),
      compileAttempts: proofLoop.steps.filter((step) => step.status !== 'skipped').length,
      stateTransitions: proofSession?.state.actionHistory.length ?? 0,
      progressClass,
      ...(scaffoldOnlyStreak > 0 ? { scaffoldOnlyStreak } : {}),
      goalProgressCount,
      frontierProgressCount,
      ...(proofStateFingerprint ? { progressFingerprint: proofStateFingerprint } : {}),
      ...(category ? { failureCategory: category } : {}),
    });
  } catch {
    // Best-effort observability; never turn a proof result into a telemetry error.
  }
  const needsInfrastructureCheckpoint =
    proofLoop.status === 'aborted' || category === 'landrun_failure' || category === 'toolchain';
  const proofHead = complete
    ? materializeSolverCompletionCommit(request.workspaceRoot, initialHead)
    : gitHead(request.workspaceRoot);
  const mathCheckpoint = needsInfrastructureCheckpoint
    ? Object.freeze({
        checkpointId: `lean-eval-proof:${episodeId}:${proofHead.slice(0, 16)}`,
        targetCommit: proofHead,
        updatedAt: Date.now(),
        ledger: Object.freeze({
          stage: 'formalize' as const,
          statementHash: math.statementHash,
          activeRoute: math.routeFingerprint,
          triedRoutes: Object.freeze([math.routeFingerprint]),
          nextSingleObjective: 'Restore the pinned Lean sandbox and retry the same direct candidate.',
          failureCategory: category === 'toolchain' ? ('toolchain' as const) : ('infra' as const),
          doNotRepeatRefs: Object.freeze([]),
        }),
      })
    : undefined;
  return Object.freeze({
    proofLoop,
    gitHeadCommit: proofHead,
    math: mathResult,
    ...(mathCheckpoint ? { mathCheckpoint } : {}),
    ...(effectiveRepairRequest ? { repairRequest: effectiveRepairRequest } : {}),
    disposition:
      complete || proofLoop.status === 'completed'
        ? 'accepted'
        : proofLoop.status === 'aborted' || category === 'landrun_failure' || category === 'toolchain'
          ? 'blocked'
          : 'inconclusive',
  });
}
