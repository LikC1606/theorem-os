import { runMathProcess as runProcess, runLeanProcess, limitMathOutput, MATH_PROCESS_OUTPUT_LIMIT, type MathProcessResult } from './mathProcess';
type ProcessResult = MathProcessResult & { sandboxBackend?: SandboxBackend };
import { declarationHashes, inspectLeanSource } from './leanSource';
export { hashMathFormalSourceDeclaration, inspectLeanDeclarationRegions, inspectLeanDeclarations, inspectLeanSource } from './leanSource';
export type { MathematicsLeanSourceDeclaration } from './leanSource';

import { resolveMathProofEnvironment, acquireMathProofEnvironmentLease } from "./mathProofEnvironment";
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { assertMathConstructionSources, mathLocalModuleBuildOrder, pruneMathConstructionCheckout } from "./mathConstructionSources";
import { spawnSync, type ChildProcess } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { MATHEMATICS_VERIFICATION_EVENT_SCHEMA, type MathematicsVerificationEvent, type MathematicsVerificationEventKind, type MathematicsVerificationEventPayloadMap } from "./leanTypes";
import { assertMathProblemContractMatchesOfficialManifest, isMathFoundationalLeanAxiom, normalizeMathOfficialProblemManifest, type MathOfficialProblemManifest, type MathProblemContract } from "./contracts";
import { readMathematicsReceiptSecret } from "./receiptAttestation";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import { createMathOperationLimiter } from "./concurrency";
import { mathFileIdentity, readMathText } from './mathRuntimeIo';
import { maskLeanCommentsAndStrings } from "./leanSyntax";
import { leanReferenceCommands, parseLeanReferences, type LeanDeclarationReferences } from './leanReferences';
import { leanDeclarationContextCommands } from './leanSource';

export type MathematicsVerifierBatchItem = {
  id?: string;
  proofPath: string;
  theoremName?: string;
  statementHash: string;
  /** Hash of the canonical Lean proposition from the immutable problem contract. */
  leanStatementHash?: string;
  /** Runtime-derived source-level theorem header hash from the immutable contract. */
  expectedSourceDeclarationHash?: string;
  claim?: 'statement' | 'negation';
};

export type MathematicsVerifierBatchRequest = {
  projectRoot: string;
  items: MathematicsVerifierBatchItem[];
  targetCommit?: string;
  /** Positive Infinity disables the per-file deadline. */
  timeoutMs?: number;
  /** Overall deadline for preparation plus all unique proof files; Infinity disables it. */
  batchTimeoutMs?: number;
};

export type MathematicsVerifierStatus = 'kernel_verified' | 'failed' | 'blocked' | 'unavailable';

export type MathematicsVerificationToolchain = {
  lean: string;
  lake?: string;
};

export type MathematicsVerifierExecutionOptions = {
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  /** Host-selected package caches; each still must match the frozen Lake manifest. */
  trustedLakePackagesRoots?: readonly string[];
  verifierCommandPath?: string;
  onEvent?: (event: MathematicsVerificationEvent) => void;
  /** Compile project-local imports in the disposable checkout without rebuilding packages. */
  prepareLocalDependencies?: boolean;
  /** Restrict source staging to construction files while preserving verifier source checks. */
  constructionSourcesOnly?: boolean;
  /** Exact closed type checked outside the source section, inline or after a module import. */
  expectedDeclarationType?: string;
  expectedDeclarationTypes?: Readonly<Record<string, string>>;
  forbiddenImportModules?: readonly string[];
  /** Report which selected declarations occur in the compiled proof dependency closure. */
  dependencyCandidates?: readonly string[];
  /** Export actual references to declarations in project-local modules, separately for type and proof. */
  collectDeclarationReferences?: boolean;
};

export type MathematicsVerifierResult = {
  status: MathematicsVerifierStatus;
  targetCommit: string;
  statementHash: string;
  leanStatementHash?: string;
  claim: 'statement' | 'negation';
  proofHash: string;
  proofPath: string;
  theoremName?: string;
  theoremDeclarationHash?: string;
  /** Complete kernel-exported declaration, including all implicit parameters and instances. */
  elaboratedDeclarationType?: string;
  /** Hash of the exact source header checked against the frozen declaration before elaboration. */
  sourceDeclarationHash?: string;
  usedDeclarationDependencies?: string[];
  declarationReferences?: LeanDeclarationReferences;
  statementBinding: 'caller-bound-to-committed-declaration';
  toolchain: MathematicsVerificationToolchain;
  verifier: 'lean-kernel' | 'bounded-check' | 'unavailable';
  goalsRemaining: number;
  sorryCount: number;
  admitCount: number;
  axioms: string[];
  checkedAt: number;
  checkId: string;
  receiptId: string;
  sessionId: string;
  events?: MathematicsVerificationEvent[];
  stdoutPreview?: string;
  stderrPreview?: string;
  /** A successful kernel check is never returned when its disposable checkout could not be cleaned up. */
  cleanupError?: string;
  error?: string;
};

export type MathematicsVerifierBatchResult = {
  schema: 'deepscientist.mathematics.verification-batch/v1';
  sessionId: string;
  status: MathematicsVerifierStatus;
  targetCommit: string;
  results: MathematicsVerifierResult[];
  events: MathematicsVerificationEvent[];
  startedAt: number;
  checkedAt: number;
  durationMs: number;
};

export type MathematicsOfficialComparatorRequest = {
  projectRoot: string;
  targetCommit: string;
  command: string;
  timeoutMs?: number;
  /** Relative path in the committed checkout to the official problem manifest. */
  officialManifestPath?: string;
  officialManifest?: MathOfficialProblemManifest;
  /** Frozen contract for the original problem. */
  expectedContract?: MathProblemContract;
  problemId?: string;
  statementHash?: string;
};

export type MathematicsOfficialComparatorResult = {
  status: 'official_verified' | 'failed' | 'blocked' | 'unavailable';
  targetCommit: string;
  command: string;
  exitCode: number | null;
  signal: NodeJS.Signals | null;
  timedOut: boolean;
  aborted: boolean;
  stdoutSha256: string;
  stderrSha256: string;
  stdoutPreview?: string;
  stderrPreview?: string;
  durationMs: number;
  checkedAt: number;
  officialManifestId?: string;
  officialManifestHash?: string;
  officialManifestProblemId?: string;
  officialManifestLeanStatementHash?: string;
  officialManifestLeanNegationHash?: string;
  officialRepositoryUrl?: string;
  officialBaselineCommit?: string;
  benchmarkAdapterId?: string;
  benchmarkAdapterVersion?: string;
  cleanupError?: string;
  error?: string;
};

/** Result shape shared by construction-time Lean sessions.  The public
 * wrapper below deliberately exposes diagnostics without exposing verifier
 * internals or allowing callers to bypass the sandbox. */
export type MathematicsSandboxCommandResult = Readonly<{
  started: boolean;
  exitCode: number | null;
  signal: NodeJS.Signals | null;
  stdout: string;
  stderr: string;
  timedOut: boolean;
  aborted: boolean;
  durationMs: number;
  errorCode?: string;
  errorMessage?: string;
  sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
}>;

type PreparedItem = MathematicsVerifierBatchItem & {
  checkId: string;
  absoluteProofPath: string;
  relativeProofPath: string;
};

type PreparedProofPath = Pick<PreparedItem, 'absoluteProofPath' | 'relativeProofPath'>;

type PreparedFile = {
  absoluteProofPath: string;
  relativeProofPath: string;
  source: string;
  declarationHashes: Map<string, string>;
  elaboratedDeclarationTypes?: Map<string, string>;
  sourceDeclarationHashes: Map<string, string>;
  axiomDependencies: Map<string, string[]>;
  usedDeclarationDependencies?: Map<string, string[]>;
  declarationReferences?: Map<string, LeanDeclarationReferences>;
  proofHash: string;
  inspection: Pick<MathematicsVerifierResult, 'sorryCount' | 'admitCount' | 'axioms'>;
  items: PreparedItem[];
};

type ProofSourceSnapshot = Readonly<{ source: string; hash: string; metadata: string }>;

type FormalVerificationCachePreparation = Readonly<{
  cacheKey: string;
  resolvedTargetCommit: string;
  preparedItems: readonly PreparedItem[];
  proofSources: ReadonlyMap<string, ProofSourceSnapshot>;
}>;

type ResultBase = Omit<
  MathematicsVerifierResult,
  'status' | 'verifier' | 'receiptId' | 'stdoutPreview' | 'stderrPreview' | 'error' | 'events'
>;

const MAX_OUTPUT = MATH_PROCESS_OUTPUT_LIMIT;
const MAX_PROOF_BYTES = 16 * 1024 * 1024;
// Construction-time JSON adapters use stdin for one bounded request. Keep the
// public sandbox entry point bounded too, so a future protocol adapter cannot
// bypass the request-size limit enforced by structured search.
const MAX_SANDBOX_STDIN_BYTES = 64 * 1024;
const MAX_OFFICIAL_MANIFEST_BYTES = 1 * 1024 * 1024;
const DEFAULT_CONCURRENT_VERIFICATIONS = 4;
const MAX_CONCURRENT_VERIFICATIONS = 16;
const DEFAULT_TIMEOUT_MS = 10 * 60 * 1000;
const MAX_TIMEOUT_MS = 24 * 60 * 60 * 1000;
const DEFAULT_BATCH_TIMEOUT_MS = 60 * 60 * 1000;
const MAX_BATCH_TIMEOUT_MS = 24 * 60 * 60 * 1000;
const DEFAULT_OFFICIAL_TIMEOUT_MS = 60 * 60 * 1000;
const MAX_OFFICIAL_TIMEOUT_MS = 24 * 60 * 60 * 1000;
const MIN_TIMEOUT_MS = 100;
const EVENT_SCHEMA = MATHEMATICS_VERIFICATION_EVENT_SCHEMA;

class FormalVerificationBatchDeadlineError extends Error {
  constructor() {
    super('Formal verification batch deadline exceeded.');
    this.name = 'FormalVerificationBatchDeadlineError';
  }
}

const configuredVerificationConcurrency = (): number => {
  const configured = Number.parseInt(process.env.DEEPSCIENTIST_MATH_VERIFIER_CONCURRENCY || '', 10);
  if (!Number.isFinite(configured)) return DEFAULT_CONCURRENT_VERIFICATIONS;
  return Math.max(1, Math.min(MAX_CONCURRENT_VERIFICATIONS, configured));
};

const hashBytes = (value: Uint8Array | string): string => crypto.createHash('sha256').update(value).digest('hex');

/**
 * Cache keys must include the dependency material that Lean actually reads,
 * not only tracked source files.  This deliberately hashes paths and bytes in
 * a deterministic order and records symlink targets without following them.
 */
const fingerprintPath = (candidate: string, limits = { files: 200_000, bytes: 2 * 1024 * 1024 * 1024 }): string => {
  const digest = crypto.createHash('sha256');
  let files = 0;
  let bytes = 0;
  const visit = (absolutePath: string, relativePath: string): void => {
    let stat: fs.Stats;
    try {
      stat = fs.lstatSync(absolutePath);
    } catch {
      digest.update(`missing\0${relativePath}\0`);
      return;
    }
    if (stat.isSymbolicLink()) {
      digest.update(`link\0${relativePath}\0${fs.readlinkSync(absolutePath)}\0`);
      return;
    }
    if (stat.isDirectory()) {
      digest.update(`dir\0${relativePath}\0`);
      for (const entry of fs
        .readdirSync(absolutePath, { withFileTypes: true })
        .toSorted((left, right) => left.name.localeCompare(right.name))) {
        if (files >= limits.files || bytes >= limits.bytes) {
          digest.update(`truncated\0${files}\0${bytes}\0`);
          return;
        }
        visit(path.join(absolutePath, entry.name), path.posix.join(relativePath, entry.name));
      }
      return;
    }
    if (!stat.isFile()) {
      digest.update(`other\0${relativePath}\0${stat.mode}\0`);
      return;
    }
    files += 1;
    if (bytes + stat.size > limits.bytes) {
      digest.update(`truncated\0${relativePath}\0${files}\0${bytes}\0`);
      return;
    }
    bytes += stat.size;
    digest.update(`file\0${relativePath}\0${stat.size}\0${hashBytes(fs.readFileSync(absolutePath))}\0`);
  };
  visit(candidate, '.');
  return digest.digest('hex');
};

/** Cheap dependency identity for non-Git Lake packages.  It deliberately
 * records metadata rather than reading every byte on the verifier's event
 * loop; the manifest and Git package identities remain the authoritative
 * dependency lock for normal projects. */
const fingerprintMetadataTree = (candidate: string, maxEntries = 50_000): string => {
  const digest = crypto.createHash('sha256');
  let entries = 0;
  const visit = (absolutePath: string, relativePath: string): void => {
    if (entries++ >= maxEntries) {
      digest.update(`truncated\0${relativePath}\0`);
      return;
    }
    let stat: fs.Stats;
    try {
      stat = fs.lstatSync(absolutePath);
    } catch {
      digest.update(`missing\0${relativePath}\0`);
      return;
    }
    digest.update(`entry\0${relativePath}\0${stat.mode}\0${stat.size}\0${stat.mtimeMs}\0`);
    if (!stat.isDirectory() || stat.isSymbolicLink()) return;
    for (const entry of fs
      .readdirSync(absolutePath, { withFileTypes: true })
      .toSorted((left, right) => left.name.localeCompare(right.name))) {
      visit(path.join(absolutePath, entry.name), path.posix.join(relativePath, entry.name));
    }
  };
  visit(candidate, '.');
  return digest.digest('hex');
};

type ExecutableFingerprintCacheEntry = Readonly<{
  metadata: string;
  fingerprint: string;
}>;

// Lean/Lake executables can be large. Cache their content fingerprint while
// retaining inode and ctime in the identity so an atomic replacement (or an
// in-place write) cannot reuse a stale verification cache key.
const executableFingerprintCache = new Map<string, ExecutableFingerprintCacheEntry>();
const EXECUTABLE_FINGERPRINT_CACHE_MAX_ENTRIES = 64;

const readPackageGitIdentity = (packageRoot: string): string | undefined => {
  try {
    let gitDirectory = path.join(packageRoot, '.git');
    if (fs.existsSync(gitDirectory) && fs.statSync(gitDirectory).isFile()) {
      const match = /^gitdir:\s*(.+)\s*$/im.exec(fs.readFileSync(gitDirectory, 'utf8'));
      if (match) gitDirectory = path.resolve(packageRoot, match[1]);
    }
    if (!fs.statSync(gitDirectory).isDirectory()) return undefined;
    const head = fs.readFileSync(path.join(gitDirectory, 'HEAD'), 'utf8').trim();
    const ref = /^ref:\s*(.+)$/u.exec(head)?.[1];
    const revision = ref
      ? fs.existsSync(path.join(gitDirectory, ref))
        ? fs.readFileSync(path.join(gitDirectory, ref), 'utf8').trim()
        : head
      : head;
    const index = path.join(gitDirectory, 'index');
    const indexStat = fs.existsSync(index) ? fs.statSync(index) : undefined;
    return `${revision}|dirty-marker:${indexStat ? `${indexStat.size}:${indexStat.mtimeMs}` : 'none'}|tree-marker:${fingerprintMetadataTree(packageRoot, 8_192)}`;
  } catch {
    return undefined;
  }
};

// Executable fingerprints are reused across retries when the file stat is
// unchanged. Directory trees are deliberately handled by their own Git-aware
// fingerprint below; a directory's root mtime is not a complete invalidation
// signal for nested files.
const memoizedFingerprintPath = (candidate: string): string => {
  try {
    const stat = fs.statSync(candidate);
    // Executables are small and security-sensitive.  Always hash regular
    // files so a replacement that preserves size/mtime cannot reuse a stale
    // verifier receipt.  Directory dependencies use their dedicated marker.
    if (!stat.isDirectory()) {
      const metadata = [stat.dev, stat.ino, stat.size, stat.mtimeMs, stat.ctimeMs, stat.mode].join(':');
      const cached = executableFingerprintCache.get(candidate);
      if (cached?.metadata === metadata) {
        executableFingerprintCache.delete(candidate);
        executableFingerprintCache.set(candidate, cached);
        return cached.fingerprint;
      }
      const fingerprint = fingerprintPath(candidate, { files: 4_096, bytes: 64 * 1024 * 1024 });
      const entry = Object.freeze({ metadata, fingerprint });
      executableFingerprintCache.delete(candidate);
      executableFingerprintCache.set(candidate, entry);
      while (executableFingerprintCache.size > EXECUTABLE_FINGERPRINT_CACHE_MAX_ENTRIES) {
        const oldest = executableFingerprintCache.keys().next().value;
        if (oldest === undefined) break;
        executableFingerprintCache.delete(oldest);
      }
      return fingerprint;
    }
    return fingerprintMetadataTree(candidate, 8_192);
  } catch {
    return fingerprintPath(candidate);
  }
};

const fingerprintLakePackages = (
  projectRoot: string,
  packagesRoot = path.join(projectRoot, '.lake', 'packages')
): string => {
  const manifest = path.join(projectRoot, 'lake-manifest.json');
  const digest = crypto.createHash('sha256');
  try {
    digest.update('lake-packages-v2\0');
    digest.update(fs.existsSync(manifest) ? fs.readFileSync(manifest) : 'missing-manifest');
    if (!fs.existsSync(packagesRoot)) {
      digest.update('missing-packages');
      return digest.digest('hex');
    }
    for (const entry of fs
      .readdirSync(packagesRoot, { withFileTypes: true })
      .toSorted((a, b) => a.name.localeCompare(b.name))) {
      if (!entry.isDirectory()) continue;
      const packageRoot = path.join(packagesRoot, entry.name);
      const gitIdentity = readPackageGitIdentity(packageRoot);
      if (gitIdentity) {
        digest.update(`git\0${entry.name}\0${gitIdentity}\0`);
      } else {
        digest.update(`tree\0${entry.name}\0${fingerprintMetadataTree(packageRoot)}\0`);
      }
    }
  } catch {
    digest.update('unreadable');
  }
  return digest.digest('hex');
};

const resolveCommandForFingerprint = (command: string, env: NodeJS.ProcessEnv | undefined): string | undefined => {
  const requested = command.trim();
  if (!requested) return undefined;
  if (path.isAbsolute(requested)) return requested;
  const pathValue = env?.PATH || process.env.PATH || '';
  for (const directory of pathValue.split(path.delimiter).filter(Boolean)) {
    const candidate = path.join(directory, requested);
    try {
      if (fs.statSync(candidate).isFile()) return candidate;
    } catch {
      // Keep searching the PATH.
    }
  }
  return undefined;
};

const withinProject = (projectRoot: string, candidate: string): boolean => {
  const root = path.resolve(projectRoot);
  const resolved = path.resolve(candidate);
  return resolved === root || resolved.startsWith(`${root}${path.sep}`);
};

const canonicalProjectRoot = (projectRoot: string): string => {
  const resolved = path.resolve(projectRoot);
  let canonical: string;
  try {
    canonical = fs.realpathSync(resolved);
  } catch (error) {
    throw new Error(
      `The project root could not be canonicalized: ${error instanceof Error ? error.message : String(error)}`,
      {
        cause: error,
      }
    );
  }
  if (!fs.statSync(canonical).isDirectory()) throw new Error('The project root must be a directory.');
  return canonical;
};

const resolveLakePackagesCaches = (projectRoot: string, env: NodeJS.ProcessEnv = process.env): string[] => {
  const trustedRoots: string[] = [];
  const addTrustedRoot = (root: string): void => {
    try {
      const canonical = fs.realpathSync(root);
      if (fs.statSync(canonical).isDirectory() && !trustedRoots.includes(canonical)) trustedRoots.push(canonical);
    } catch {
      // Ignore configured roots that do not resolve on this host.
    }
  };
  addTrustedRoot(projectRoot);
  for (const value of (env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS || '').split(path.delimiter)) {
    const root = value.trim();
    if (root) addTrustedRoot(root);
  }
  const candidates = [path.join(projectRoot, '.lake', 'packages'), ...trustedRoots.slice(1)];
  const resolved: string[] = [];
  for (const candidate of candidates) {
    try {
      const canonical = fs.realpathSync(candidate);
      if (!fs.statSync(canonical).isDirectory()) continue;
      if (trustedRoots.some((root) => withinProject(root, canonical))) resolved.push(canonical);
    } catch {
      // Try the next configured cache. A later manifest check still binds it
      // to the exact package revisions requested by this project.
    }
  }
  return [...new Set(resolved)];
};

const seedDetachedLakeCache = (
  sourceProjectRoot: string,
  targetProjectRoot: string,
  env: NodeJS.ProcessEnv = process.env,
  prepareManifest = false
): string | undefined => {
  const sourceManifest = path.join(sourceProjectRoot, 'lake-manifest.json');
  const targetManifest = path.join(targetProjectRoot, 'lake-manifest.json');
  // An ignored bootstrap lock is usable only with its verified, pinned cache.
  if (prepareManifest && !fs.existsSync(targetManifest) && fs.existsSync(sourceManifest)) {
    assertNoSymlinkTraversal(sourceProjectRoot, sourceManifest, 'Helper package manifest');
    if (resolveVerifiedLakePackagesCache(sourceProjectRoot, sourceProjectRoot, env))
      fs.copyFileSync(sourceManifest, targetManifest, fs.constants.COPYFILE_EXCL);
  }
  let packageLockMatches = false;
  try {
    packageLockMatches =
      fs.existsSync(sourceManifest) &&
      fs.existsSync(targetManifest) &&
      hashBytes(fs.readFileSync(sourceManifest)) === hashBytes(fs.readFileSync(targetManifest));
  } catch {
    packageLockMatches = false;
  }
  const packages = packageLockMatches
    ? resolveVerifiedLakePackagesCache(sourceProjectRoot, targetProjectRoot, env)
    : undefined;
  if (packages) {
    fs.mkdirSync(path.join(targetProjectRoot, '.lake', 'packages'), { recursive: true });
    assertNoSymlinkTraversal(targetProjectRoot, path.join(targetProjectRoot, '.lake'), 'Lake cache directory');
    const overridesPath = path.join(targetProjectRoot, '.lake', 'package-overrides.json');
    if (fs.existsSync(overridesPath)) assertNoSymlinkTraversal(targetProjectRoot, overridesPath, 'Lake package overrides');
    // The sandbox replaces these entries with paths to the verified cache.
    fs.writeFileSync(overridesPath, JSON.stringify({ schemaVersion: '1.2.0', packages: [] }) + '\n', { mode: 0o600 });
  }
  // Never copy generated build output into an immutable checkout.  Build
  // products may contain artifacts produced by a different target commit;
  // Lean/Lake must rebuild them in the disposable checkout instead.
  return packages;
};

/** A missing module is infrastructure only when the pinned dependency really supplies it. */
const hasUnavailablePinnedLeanModule = (
  diagnostic: string,
  projectRoot: string,
  lakePackagesPath: string | undefined
): boolean => {
  if (!lakePackagesPath) return false;
  const missing = [
    ...diagnostic.matchAll(/\berror: unknown module prefix '([A-Za-z_][A-Za-z0-9_'.]*)'/gu),
    ...diagnostic.matchAll(
      /\berror: object file '[^'\n]+\.olean' of module ([A-Za-z_][A-Za-z0-9_'.]*) does not exist/gu
    ),
  ];
  if (!missing.length) return false;
  try {
    const manifest = JSON.parse(fs.readFileSync(path.join(projectRoot, 'lake-manifest.json'), 'utf8'));
    const packageNames: string[] = Array.isArray(manifest.packages)
      ? manifest.packages
          .map((entry: { name?: unknown }) => entry.name)
          .filter((name: unknown): name is string => typeof name === 'string' && /^[A-Za-z0-9_-]+$/u.test(name))
      : [];
    return missing.some((match) => {
      const relative = match[1].split('.').join(path.sep);
      return packageNames.some((name) => {
        const packageRoot = path.join(lakePackagesPath, name);
        // Only dependency sources count, never candidate-created modules or an arbitrary path
        // printed by Lean. A typo such as Mathlib.DoesNotExist remains a proof rejection.
        const source = path.join(packageRoot, `${relative}.lean`);
        try {
          return withinProject(packageRoot, fs.realpathSync(source)) && fs.statSync(source).isFile();
        } catch {
          return false;
        }
      });
    });
  } catch {
    return false;
  }
};

const resolveVerifiedLakePackagesCache = (
  sourceProjectRoot: string,
  targetProjectRoot: string,
  env: NodeJS.ProcessEnv = process.env
): string | undefined => {
  const sealed = resolveMathProofEnvironment(targetProjectRoot, env);
  if (sealed) return sealed.packagesRoot;
  for (const packagesRoot of resolveLakePackagesCaches(sourceProjectRoot, env)) {
    const verified = verifyLakePackagesCache(packagesRoot, targetProjectRoot);
    if (verified) return verified;
  }
  return undefined;
};

const verifyLakePackagesCache = (packagesRoot: string, targetProjectRoot: string): string | undefined => {
  try {
    const manifest = JSON.parse(fs.readFileSync(path.join(targetProjectRoot, 'lake-manifest.json'), 'utf8')) as Record<
      string,
      unknown
    >;
    const packages = Array.isArray(manifest.packages) ? manifest.packages : [];
    if (!packages.length) return undefined;
    for (const item of packages) {
      if (!item || typeof item !== 'object') return undefined;
      const record = item as Record<string, unknown>;
      const name = typeof record.name === 'string' ? record.name : '';
      const git = record.git && typeof record.git === 'object' ? (record.git as Record<string, unknown>) : record;
      const revision = [git.rev, git.commit, git.revision].find((value): value is string => typeof value === 'string');
      if (!name || !revision || !/^[0-9a-f]{7,64}$/u.test(revision)) return undefined;
      const packageDirectory = [name, name.replace(/^«(.+)»$/u, '$1')].find((candidate) =>
        fs.existsSync(path.join(packagesRoot, candidate))
      );
      if (!packageDirectory) return undefined;
      const packageRoot = assertNoSymlinkTraversal(
        packagesRoot,
        path.join(packagesRoot, packageDirectory),
        `Lake package ${name}`
      );
      const identity = readPackageGitIdentity(packageRoot);
      const actualRevision = identity?.split('|', 1)[0] || '';
      if (!actualRevision || !actualRevision.toLowerCase().startsWith(revision.toLowerCase())) {
        return undefined;
      }
    }
    return packagesRoot;
  } catch {
    return undefined;
  }
};

/** Create the container bind target before Docker sees it. Otherwise Docker
 * creates the missing mount parent as root on the host, leaving probe
 * workspaces uncleanable by the caller. */
const BWRAP_RESERVED_ROOTS = [
  '/usr',
  '/bin',
  '/sbin',
  '/lib',
  '/lib64',
  '/etc',
  '/workspace',
  '/tmp',
  '/proc',
  '/dev',
  '/sys',
  '/run',
  '/toolchains',
  '/runtime',
];
/**
 * A worktree may link .lake/packages to an external cache. Inside bwrap the
 * link dangles, so bind the cache at the link's absolute target. The link only picks a path,
 * never the content, and cannot name a sandbox-owned or checkout path.
 * Returns that sandbox mount path, or undefined for an ordinary directory.
 */
const ensureLakePackagesMountPoint = (projectRoot: string, checkoutRoot: string): string | undefined => {
  const packages = path.join(path.resolve(projectRoot), '.lake', 'packages');
  const link = fs.lstatSync(packages, { throwIfNoEntry: false });
  if (link?.isSymbolicLink()) {
    const target = fs.realpathSync(packages);
    const checkout = fs.realpathSync(checkoutRoot);
    if (
      !path.isAbsolute(target) ||
      target.split(path.sep).filter(Boolean).length < 2 ||
      !fs.statSync(target).isDirectory() ||
      target === checkout ||
      target.startsWith(`${checkout}${path.sep}`) ||
      BWRAP_RESERVED_ROOTS.some((root) => target === root || (root !== '/tmp' && target.startsWith(`${root}/`)))
    ) {
      throw new Error('Lean sandbox Lake package mount target must be a regular directory.');
    }
    return target;
  }
  let current = path.resolve(projectRoot);
  for (const segment of ['.lake', 'packages']) {
    current = path.join(current, segment);
    try {
      const stat = fs.lstatSync(current);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error('Lean sandbox Lake package mount target must be a regular directory.');
      }
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
      fs.mkdirSync(current, { recursive: false, mode: 0o700 });
    }
  }
  return undefined;
};

/** Resolve a project-compatible package cache from the workspace or an
 * explicitly trusted runner cache. Every package is rebound to the project's
 * frozen Lake manifest before the cache may enter the Lean sandbox. */
export const resolveMathematicsLakePackagesCache = (
  projectRoot: string,
  env: NodeJS.ProcessEnv = process.env
): string | undefined => resolveVerifiedLakePackagesCache(projectRoot, projectRoot, env);

const assertNoSymlinkTraversal = (
  root: string,
  target: string,
  field: string,
  canonicalRoot = canonicalProjectRoot(root)
): string => {
  const lexicalTarget = path.resolve(target);
  const lexicalRelative = path.relative(path.resolve(root), lexicalTarget);
  if (lexicalRelative.startsWith('..') || path.isAbsolute(lexicalRelative)) {
    throw new Error(`${field} must remain inside the bound project root.`);
  }
  let cursor = path.resolve(root);
  for (const segment of lexicalRelative.split(path.sep).filter(Boolean)) {
    cursor = path.join(cursor, segment);
    if (fs.lstatSync(cursor).isSymbolicLink()) {
      throw new Error(`${field} must not traverse a symbolic link.`);
    }
  }
  let canonicalTarget: string;
  try {
    canonicalTarget = fs.realpathSync(lexicalTarget);
  } catch (error) {
    throw new Error(`${field} could not be canonicalized: ${error instanceof Error ? error.message : String(error)}`, {
      cause: error,
    });
  }
  if (!withinProject(canonicalRoot, canonicalTarget)) {
    throw new Error(`${field} must resolve inside the bound project root.`);
  }
  return canonicalTarget;
};

const abortReason = (signal: AbortSignal): unknown => signal.reason ?? new DOMException('Aborted', 'AbortError');

// A batch can contain several files, so batches and Lean processes need separate pools.
const withVerificationSlot = createMathOperationLimiter(configuredVerificationConcurrency);
const withLeanProcessSlot = createMathOperationLimiter(configuredVerificationConcurrency);

const preview = (value: string | null | undefined): string | undefined => {
  const normalized = value?.trim();
  return normalized ? limitMathOutput(normalized, MAX_OUTPUT) : undefined;
};

const clampTimeout = (timeoutMs: number | undefined, defaultMs = DEFAULT_TIMEOUT_MS,
  maximumMs = MAX_TIMEOUT_MS, field = 'formal_verifier timeoutMs'): number => {
  if (timeoutMs === undefined) return defaultMs;
  if (timeoutMs === Infinity) return Infinity;
  if (!Number.isFinite(timeoutMs) || timeoutMs < MIN_TIMEOUT_MS) {
    throw new Error(`${field} must be at least ${MIN_TIMEOUT_MS}.`);
  }
  return Math.min(Math.floor(timeoutMs), maximumMs);
};

const clampBatchTimeout = (timeoutMs: number | undefined): number =>
  clampTimeout(timeoutMs, DEFAULT_BATCH_TIMEOUT_MS, MAX_BATCH_TIMEOUT_MS, 'formal_verifier batchTimeoutMs');

const runGit = (
  projectRoot: string,
  args: string[],
  options: MathematicsVerifierExecutionOptions
): Promise<ProcessResult> =>
  runProcess('git', args, {
    cwd: projectRoot,
    timeoutMs: 10_000,
    signal: options.signal,
    env: options.env,
  });

const cleanupVerifierWorktree = async (
  repoRoot: string,
  worktreeRoot: string,
  options: MathematicsVerifierExecutionOptions,
  removeWorktree: boolean
): Promise<string[]> => {
  const failures: string[] = [];
  if (removeWorktree) {
    try {
      const removed = await runGit(repoRoot, ['worktree', 'remove', '--force', worktreeRoot], options);
      if (removed.exitCode !== 0 && fs.existsSync(worktreeRoot)) {
        failures.push(
          `git worktree remove failed: ${preview(removed.stderr) || `exit ${removed.exitCode ?? 'unknown'}`}`
        );
      }
    } catch (error) {
      failures.push(`git worktree remove failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  try {
    const pruned = await runGit(repoRoot, ['worktree', 'prune'], options);
    if (pruned.exitCode !== 0) {
      failures.push(`git worktree prune failed: ${preview(pruned.stderr) || `exit ${pruned.exitCode ?? 'unknown'}`}`);
    }
  } catch (error) {
    failures.push(`git worktree prune failed: ${error instanceof Error ? error.message : String(error)}`);
  }
  return failures;
};

const clampOfficialTimeout = (timeoutMs: number | undefined): number =>
  clampTimeout(timeoutMs, DEFAULT_OFFICIAL_TIMEOUT_MS, MAX_OFFICIAL_TIMEOUT_MS, 'Official comparator timeoutMs');

const OFFICIAL_EXECUTABLE_ALLOWLIST = new Set([
  'lake',
  'lean',
  'elan',
  'python',
  'python3',
  'pytest',
  'uv',
  'cargo',
  'grep',
  'test',
]);

const parseOfficialCommand = (command: string): { executable: string; argv: string[] } => {
  const argv: string[] = [];
  let token = '';
  let quote: "'" | '"' | undefined;
  let escaped = false;
  const push = (): void => {
    if (token) argv.push(token);
    token = '';
  };
  for (const character of command) {
    if (escaped) {
      token += character;
      escaped = false;
      continue;
    }
    if (character === '\\' && quote !== "'") {
      escaped = true;
      continue;
    }
    if (quote) {
      if (character === quote) quote = undefined;
      else token += character;
      continue;
    }
    if (character === "'" || character === '"') {
      quote = character;
      continue;
    }
    if (/\s/u.test(character)) {
      push();
      continue;
    }
    token += character;
  }
  if (escaped || quote) throw new Error('Official comparator command contains an incomplete escape or quote.');
  push();
  const [executable, ...args] = argv;
  if (!executable || executable !== path.basename(executable) || !OFFICIAL_EXECUTABLE_ALLOWLIST.has(executable)) {
    throw new Error('Official comparator executable is not present in the trusted verifier allowlist.');
  }
  if (args.some((arg) => arg === '-c' || arg === '-e' || path.isAbsolute(arg) || arg.split(/[\\/]/u).includes('..'))) {
    throw new Error('Official comparator arguments must be file-bound argv without inline code or external paths.');
  }
  return { executable, argv: args };
};

const officialComparatorEnvironment = (source: NodeJS.ProcessEnv | undefined): NodeJS.ProcessEnv => {
  const input = source || process.env;
  const allowed = ['PATH', 'LANG', 'LC_ALL'];
  const environment: NodeJS.ProcessEnv = {};
  for (const key of allowed) {
    const value = input[key];
    if (value) environment[key] = value;
  }
  return environment;
};

/**
 * The isolated MCP sandbox mounts one pinned toolchain and exposes it through
 * /opt/math-tools/{lean,lake} links, without elan. The inner Lean sandbox then
 * had no toolchain mount and every lean_workspace probe failed with
 * "lake: not found" (run 23e). Accept only a PATH lake that is a link into a
 * real toolchain directory (bin/lean, bin/lake and lib/lean present).
 */
const linkedLeanToolchain = (pathEntries: readonly string[]): string | undefined => {
  for (const entry of pathEntries) {
    const lake = path.join(entry, 'lake');
    try {
      if (!fs.lstatSync(lake).isSymbolicLink()) continue;
      const real = fs.realpathSync(lake);
      if (path.basename(real) !== 'lake' || path.basename(path.dirname(real)) !== 'bin') continue;
      const toolchain = path.dirname(path.dirname(real));
      if (
        fs.statSync(path.join(toolchain, 'bin', 'elan'), { throwIfNoEntry: false })?.isFile() ||
        (fs.statSync(path.join(toolchain, 'bin', 'lean')).isFile() &&
          fs.statSync(path.join(toolchain, 'lib', 'lean')).isDirectory())
      )
        return toolchain;
    } catch {
      // Not a linked toolchain; keep the caller's PATH tools authoritative.
    }
  }
  return undefined;
};

const resolveTrustedElanHome = (source: NodeJS.ProcessEnv | undefined): string => {
  const configured = source?.DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS || process.env.DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS;
  const requested = source?.ELAN_HOME || process.env.ELAN_HOME;
  const explicitCandidates = [
    ...(requested ? [requested] : []),
    ...(configured || '').split(path.delimiter).filter(Boolean),
  ];
  const candidates = [...explicitCandidates];
  // In development, infer the installation root from the resolved Lean/Lake
  // executable rather than assuming a particular host prefix.
  if (!candidates.length) {
    const pathEntries = (source?.PATH || process.env.PATH || '').split(path.delimiter).filter(Boolean);
    const linked = linkedLeanToolchain(pathEntries);
    if (linked) return linked;
    for (const entry of pathEntries) {
      if (path.basename(entry) === 'bin') candidates.push(path.dirname(entry));
    }
  }
  for (const candidate of candidates) {
    const resolved = path.resolve(candidate);
    if (!fs.existsSync(resolved)) continue;
    try {
      const canonical = fs.realpathSync(resolved);
      if (!fs.statSync(canonical).isDirectory()) continue;
      if (
        fs.existsSync(path.join(canonical, 'bin', 'elan')) ||
        ((fs.existsSync(path.join(canonical, 'bin', 'lean')) || fs.existsSync(path.join(canonical, 'bin', 'lake'))) &&
          fs.existsSync(path.join(canonical, 'lib', 'lean')))
      ) {
        return canonical;
      }
    } catch {
      // Try the next explicitly configured installation root.
    }
  }
  // A caller-provided Lean/Lake executable (including a test harness) must
  // remain authoritative.  Only infer the default elan installation when the
  // restricted PATH has no Lean tool at all.
  const pathEntries = (source?.PATH || process.env.PATH || '').split(path.delimiter).filter(Boolean);
  if (pathEntries.some((entry) => fs.existsSync(path.join(entry, 'lean')) || fs.existsSync(path.join(entry, 'lake')))) {
    return linkedLeanToolchain(pathEntries) ?? '';
  }
  // Inside the isolated MCP the frozen env file replaces PATH with host
  // directories that are not mounted, so the sandbox's own /opt/math-tools
  // links survive only in the process PATH (run 23i: "exec: lake: not found").
  // The same strict linked-toolchain check applies.
  const processLinked = linkedLeanToolchain((process.env.PATH || '').split(path.delimiter).filter(Boolean));
  if (processLinked) return processLinked;
  // The desktop/runner process often inherits a restricted PATH that omits
  // elan's shims.  The standard per-user installation is still a trusted
  // toolchain root; elan will select the version pinned by the project.
  const defaultHome = path.join(os.homedir(), '.elan');
  try {
    const canonical = fs.realpathSync(defaultHome);
    if (
      fs.statSync(canonical).isDirectory() &&
      (fs.existsSync(path.join(canonical, 'bin', 'lean')) || fs.existsSync(path.join(canonical, 'bin', 'lake')))
    ) {
      return canonical;
    }
  } catch {
    // No default elan installation is available; the caller will report the
    // normal toolchain-unavailable result.
  }
  return '';
};

const resolveTrustedToolchainBin = (
  projectRoot: string,
  projectRelative: string,
  source: NodeJS.ProcessEnv | undefined,
  elanHome: string
): string => {
  if (!elanHome) return '';
  const elan = path.join(elanHome, 'bin', 'elan');
  if (!fs.existsSync(elan)) {
    // A bare pinned toolchain (see linkedLeanToolchain) is its own bin directory.
    try {
      return fs.statSync(path.join(elanHome, 'bin', 'lake')).isFile() &&
        fs.statSync(path.join(elanHome, 'bin', 'lean')).isFile() &&
        fs.statSync(path.join(elanHome, 'lib', 'lean')).isDirectory()
        ? path.join(elanHome, 'bin')
        : '';
    } catch {
      return '';
    }
  }
  const result = spawnSync(elan, ['which', 'lean'], {
    cwd: path.join(projectRoot, projectRelative),
    env: { ...process.env, ...source, ELAN_HOME: elanHome },
    encoding: 'utf8',
    timeout: 2_000,
  });
  if (result.status !== 0) return '';
  const leanPath = result.stdout.trim();
  if (!path.isAbsolute(leanPath) || path.basename(leanPath) !== 'lean') return '';
  try {
    const resolved = fs.realpathSync(leanPath);
    const bin = path.dirname(resolved);
    return fs.statSync(path.join(bin, 'lake')).isFile() ? bin : '';
  } catch {
    return '';
  }
};

// Address-space cap (KiB) for namespace sandboxes. `ulimit -v` counts mapped
// files, and `import Mathlib` maps ~5.1 GiB of .olean/.olean.private data, so
// 8 GiB made Lean fail with "failed to read file '...olean.private'" (run 23
// attempt 10); a 450-line Q6 proof peaks at ~10.4 GiB virtual.
const LEAN_SANDBOX_ADDRESS_SPACE_KB = 16 * 1024 * 1024;

// Local verification may use an explicitly supplied test/toolchain wrapper
// (for example a Node-based Lean harness).  Keep the same sandbox boundary but
// optionally expose the trusted runtime that launched DeepScientist.
const LEAN_SANDBOX_SCRIPT = String.raw`
root=$1
candidate=$2
project_relative=$3
toolchain=$4
toolchain_bin=$5
runtime=$6
counter=$7
axioms=$8
packages=$9
shift 9
overrides=$1
shift
mount --make-rprivate /
ulimit -v ${LEAN_SANDBOX_ADDRESS_SPACE_KB} 2>/dev/null || true
ulimit -u 256 2>/dev/null || true
ulimit -n 4096 2>/dev/null || true
mount --bind /usr "$root/usr"
mount -o remount,bind,ro "$root/usr"
mount --bind "$candidate" "$root/workspace"
mount -t tmpfs -o mode=755,nosuid,noexec tmpfs "$root/dev"
for device in null zero full random urandom; do
  touch "$root/dev/$device"
  mount --bind "/dev/$device" "$root/dev/$device"
done
if [ -n "$packages" ]; then
  cache_target="$root/workspace"
  if [ -n "$project_relative" ]; then cache_target="$cache_target/$project_relative"; fi
  mkdir -p "$cache_target/.lake/packages"
  mount --bind "$packages" "$cache_target/.lake/packages"
  mount -o remount,bind,ro "$cache_target/.lake/packages"
fi
if [ -n "$overrides" ]; then
  override_target="$root/workspace"
  if [ -n "$project_relative" ]; then override_target="$override_target/$project_relative"; fi
  mount --bind "$overrides" "$override_target/.lake/package-overrides.json"
  mount -o remount,bind,ro "$override_target/.lake/package-overrides.json"
fi
if [ -n "$toolchain" ]; then
  mount --bind "$toolchain" "$root/toolchains/elan"
  mount -o remount,bind,ro "$root/toolchains/elan"
fi
if [ -n "$runtime" ]; then
  mkdir -p "$root/runtime/node"
  mount --bind "$runtime" "$root/runtime/node"
  mount -o remount,bind,ro "$root/runtime/node"
fi
mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs "$root/tmp"
mount -t proc -o nosuid,nodev,noexec proc "$root/proc"
if [ -n "$project_relative" ]; then
  sandbox_cwd=/workspace/$project_relative
else
  sandbox_cwd=/workspace
fi
if [ -z "$toolchain_bin" ]; then toolchain_bin=/toolchains/elan/bin; fi
exec chroot "$root" /usr/bin/env -i \
  PATH=/runtime/node/bin:$toolchain_bin:/usr/local/bin:/usr/bin:/bin \
  HOME=/tmp TMPDIR=/tmp LANG=C.UTF-8 ELAN_HOME=/toolchains/elan LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=8192 \
  DEEPSCIENTIST_TEST_LEAN_COUNTER="$counter" \
  DEEPSCIENTIST_TEST_LEAN_AXIOMS="$axioms" \
  /usr/bin/env --chdir="$sandbox_cwd" "$@"
`;

const unavailableProcessResult = (message: string): ProcessResult => ({
  started: false,
  exitCode: null,
  signal: null,
  stdout: '',
  stderr: message,
  stdoutSha256: crypto.createHash('sha256').update('').digest('hex'),
  stderrSha256: crypto.createHash('sha256').update(message).digest('hex'),
  timedOut: false,
  aborted: false,
  errorCode: 'SANDBOX_UNAVAILABLE',
  errorMessage: message,
  durationMs: 0,
});

type SandboxBackend = 'unshare' | 'bwrap' | 'docker' | 'podman';

const executableOnPath = (name: string, source = process.env.PATH || ''): string | undefined => {
  for (const entry of source.split(path.delimiter).filter(Boolean)) {
    const candidate = path.join(entry, name);
    try {
      if (fs.statSync(candidate).isFile()) return candidate;
    } catch {
      // Continue through the configured PATH entries.
    }
  }
  return undefined;
};

/** Return only backends that can be invoked without an unsafe host fallback. */
export function inspectMathematicsSandboxBackends(
  env: NodeJS.ProcessEnv = process.env
): Readonly<{ available: readonly SandboxBackend[]; preferred?: SandboxBackend; reason?: string }> {
  const available: SandboxBackend[] = [];
  if (process.platform === 'linux' && executableOnPath('unshare', env.PATH)) available.push('unshare');
  if (process.platform === 'linux' && executableOnPath('bwrap', env.PATH)) available.push('bwrap');
  const image = env.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || '';
  if (/@sha256:[0-9a-f]{64}$/iu.test(image)) {
    if (process.platform === 'linux' && executableOnPath('docker', env.PATH)) available.push('docker');
    if (process.platform === 'linux' && executableOnPath('podman', env.PATH)) available.push('podman');
  }
  const configured = env.DEEPSCIENTIST_MATH_SANDBOX_BACKEND as SandboxBackend | undefined;
  const preferred =
    configured && available.includes(configured)
      ? configured
      : /@sha256:[0-9a-f]{64}$/iu.test(image)
        ? available.find((backend) => backend === 'docker' || backend === 'podman') || available[0]
        : available[0];
  return Object.freeze({
    available: Object.freeze(available),
    ...(preferred ? { preferred } : {}),
    ...(!available.length
      ? {
          reason: /@sha256:[0-9a-f]{64}$/iu.test(image)
            ? 'No supported Linux sandbox backend is installed.'
            : 'No namespace sandbox is installed; Docker/Podman requires a digest-pinned image.',
        }
      : {}),
  });
}

type MathematicsSandboxBackend = Readonly<{
  kind: 'unshare' | 'bwrap' | 'docker' | 'podman';
  executable: string;
}>;

// A namespace permission failure is host-scoped for the lifetime of this
// verifier process. Keep the cache keyed by the effective sandbox environment
// so a failed default PATH cannot poison a later explicitly configured Docker
// image. Ordinary Lean failures remain uncached and continue through the normal
// path.
const sandboxUnavailableReasons = new Map<string, string>();
const sandboxBackendFailures = new Set<string>();

const sandboxEnvironmentKey = (env: NodeJS.ProcessEnv | undefined): string =>
  JSON.stringify({
    path: env?.PATH || process.env.PATH || '',
    backend: env?.DEEPSCIENTIST_MATH_SANDBOX_BACKEND || '',
    image: env?.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || '',
    sealedEnvironment: env?.DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT || '',
  });

const sandboxBackendKey = (environmentKey: string, backend: SandboxBackend): string => `${environmentKey}\0${backend}`;

const resolveSandboxBackends = (env: NodeJS.ProcessEnv | undefined,
  capability = inspectMathematicsSandboxBackends(env || process.env)): MathematicsSandboxBackend[] => {
  const environmentKey = sandboxEnvironmentKey(env);
  return capability.available
    .filter((kind) => !sandboxBackendFailures.has(sandboxBackendKey(environmentKey, kind)))
    .toSorted((left, right) => {
      if (left === capability.preferred) return -1;
      if (right === capability.preferred) return 1;
      return 0;
    })
    .map((kind) =>
      Object.freeze({
        kind,
        executable: executableOnPath(kind, env?.PATH) || `/usr/bin/${kind}`,
      })
    );
};

const isNamespaceSandboxFailure = (result: ProcessResult): boolean =>
  result.errorCode === 'EPERM' ||
  /(?:uid_map|gid_map|unshare:.*(?:operation not permitted|permission denied)|bwrap:.*(?:operation not permitted|permission denied)|(?:namespace|clone|loopback).*(?:operation not permitted|permission denied))/iu.test(
    `${result.stderr}\n${result.stdout}`
  );

const isContainerSandboxFailure = (backend: SandboxBackend, result: ProcessResult): boolean =>
  (backend === 'docker' || backend === 'podman') &&
  (result.exitCode === 125 || result.errorCode === 'EACCES' || result.errorCode === 'ENOENT');

const isSandboxBackendFailure = (backend: SandboxBackend, result: ProcessResult): boolean =>
  isNamespaceSandboxFailure(result) || isContainerSandboxFailure(backend, result);

const bwrapProjectPath = (projectRelative: string): string =>
  projectRelative ? `/workspace/${projectRelative}` : '/workspace';

const buildBwrapArguments = (input: {
  candidateRoot: string;
  projectRelative: string;
  toolchainRoot: string;
  toolchainBin: string;
  runtimeRoot: string;
  lakePackagesPath: string;
  lakePackagesMountPath?: string;
  writablePackageOverlay?: boolean;
  lakePackagesFd?: number;
  leanLauncherPath?: string;
  lakePackageOverridesPath?: string;
  command: string;
  commandArgs: readonly string[];
  testCounter: string;
  testAxioms: string;
}): string[] => {
  const projectPath = bwrapProjectPath(input.projectRelative);
  const packagesPath = input.lakePackagesMountPath ?? `${projectPath}/.lake/packages`;
  // bwrap applies mounts in argument order. Ensure the package mount target is
  // present in the disposable candidate before the workspace bind hides the
  // host root used to assemble the namespace. A linked target is created by bwrap.
  if (input.lakePackagesPath && !input.lakePackagesMountPath) {
    fs.mkdirSync(path.join(input.candidateRoot, input.projectRelative, '.lake', 'packages'), { recursive: true });
  }
  const args = [
    '--unshare-user',
    '--uid',
    '0',
    '--gid',
    '0',
    '--unshare-net',
    '--unshare-pid',
    '--die-with-parent',
    '--new-session',
    '--clearenv',
    '--ro-bind',
    '/usr',
    '/usr',
    '--symlink',
    'usr/bin',
    '/bin',
    '--symlink',
    'usr/sbin',
    '/sbin',
    '--symlink',
    'usr/lib',
    '/lib',
    '--symlink',
    'usr/lib64',
    '/lib64',
    '--bind',
    input.candidateRoot,
    '/workspace',
    '--tmpfs',
    '/tmp',
    '--proc',
    '/proc',
    '--dev',
    '/dev',
    '--dir',
    '/toolchains',
    '--dir',
    '/runtime',
  ];
  if (input.lakePackagesFd !== undefined) args.push('--ro-bind-fd', String(input.lakePackagesFd), packagesPath);
  else if (input.lakePackagesPath)
    args.push(input.writablePackageOverlay ? '--bind' : '--ro-bind', input.lakePackagesPath, packagesPath);
  if (input.lakePackageOverridesPath)
    args.push('--ro-bind', input.lakePackageOverridesPath, `${projectPath}/.lake/package-overrides.json`);
  if (input.toolchainRoot) args.push('--ro-bind', input.toolchainRoot, '/toolchains/elan');
  if (input.leanLauncherPath && input.toolchainBin) {
    const relativeBin = path.relative('/toolchains/elan', input.toolchainBin);
    args.push('--ro-bind', path.dirname(path.join(input.toolchainRoot, relativeBin)), '/runtime/pinned-lean');
    args.push('--ro-bind', input.leanLauncherPath, `${input.toolchainBin}/lean`);
  }
  if (input.runtimeRoot) args.push('--ro-bind', input.runtimeRoot, '/runtime/node');
  args.push(
    '--chdir',
    projectPath,
    '--setenv',
    'PATH',
    `${input.runtimeRoot ? '/runtime/node/bin:' : ''}${input.toolchainBin ? `${input.toolchainBin}:` : ''}/usr/local/bin:/usr/bin:/bin`,
    '--setenv',
    'HOME',
    '/tmp',
    '--setenv',
    'TMPDIR',
    '/tmp',
    '--setenv',
    'LANG',
    'C.UTF-8',
    '--setenv',
    'ELAN_HOME',
    '/toolchains/elan',
    '--setenv',
    'LEAN_NUM_THREADS',
    '1',
    '--setenv',
    'LEAN_STACK_SIZE_KB',
    '8192',
    '--setenv',
    'DEEPSCIENTIST_TEST_LEAN_COUNTER',
    input.testCounter,
    '--setenv',
    'DEEPSCIENTIST_TEST_LEAN_AXIOMS',
    input.testAxioms,
    '--',
    '/bin/sh',
    '-ceu',
    `ulimit -v ${LEAN_SANDBOX_ADDRESS_SPACE_KB} 2>/dev/null || true; ulimit -u 256 2>/dev/null || true; ulimit -n 4096 2>/dev/null || true; exec "$@"`,
    '--',
    input.command,
    ...input.commandArgs
  );
  return args;
};

const buildContainerArguments = (input: {
  checkoutRoot: string;
  projectRelative: string;
  toolchainRoot: string;
  toolchainBin: string;
  runtimeRoot: string;
  lakePackagesPath: string;
  lakePackageOverridesPath?: string;
  command: string;
  commandArgs: readonly string[];
  testCounter: string;
  testAxioms: string;
  image: string;
  interactive?: boolean;
  cidfile?: string;
}): string[] => {
  const projectPath = bwrapProjectPath(input.projectRelative);
  const args = [
    'run',
    '--rm',
    ...(input.interactive ? ['--interactive'] : []),
    ...(input.cidfile ? ['--cidfile', input.cidfile] : []),
    '--network=none',
    '--pull=never',
    '--read-only',
    '--pids-limit=256',
    '--memory=8g',
    '--cpus=4',
    '--ulimit',
    'nofile=4096:4096',
    '--ulimit',
    'fsize=67108864:67108864',
    '--cap-drop=ALL',
    '--security-opt=no-new-privileges',
    '--user',
    `${process.getuid?.() ?? 0}:${process.getgid?.() ?? 0}`,
    '--tmpfs',
    '/tmp:rw,nosuid,nodev,mode=1777',
    '--tmpfs',
    '/etc:ro,nosuid,nodev,noexec,mode=755',
    '--mount',
    `type=bind,src=${input.checkoutRoot},dst=/workspace`,
    ...(input.toolchainRoot ? ['--mount', `type=bind,src=${input.toolchainRoot},dst=/toolchains/elan,ro`] : []),
    ...(input.runtimeRoot ? ['--mount', `type=bind,src=${input.runtimeRoot},dst=/runtime/node,ro`] : []),
    ...(input.lakePackagesPath
      ? ['--mount', `type=bind,src=${input.lakePackagesPath},dst=${projectPath}/.lake/packages,ro`]
      : []),
    ...(input.lakePackageOverridesPath
      ? [
          '--mount',
          `type=bind,src=${input.lakePackageOverridesPath},dst=${projectPath}/.lake/package-overrides.json,ro`,
        ]
      : []),
    '--workdir',
    projectPath,
    '--env',
    `PATH=${input.runtimeRoot ? '/runtime/node/bin:' : ''}${input.toolchainBin ? `${input.toolchainBin}:` : ''}/usr/local/bin:/usr/bin:/bin`,
    '--env',
    'HOME=/tmp',
    '--env',
    'TMPDIR=/tmp',
    '--env',
    'LANG=C.UTF-8',
    '--env',
    'ELAN_HOME=/toolchains/elan',
    '--env',
    'LEAN_NUM_THREADS=1',
    '--env',
    'LEAN_STACK_SIZE_KB=8192',
    ...(input.testCounter ? ['--env', `DEEPSCIENTIST_TEST_LEAN_COUNTER=${input.testCounter}`] : []),
    ...(input.testAxioms ? ['--env', `DEEPSCIENTIST_TEST_LEAN_AXIOMS=${input.testAxioms}`] : []),
    input.image,
    input.command,
    ...input.commandArgs,
  ];
  return args;
};

const createMathematicsSandboxRoot = (temporaryRoot: string): string => {
  const sandboxRoot = path.join(temporaryRoot, 'sandbox');
  for (const directory of ['usr', 'workspace', 'tmp', 'proc', 'dev', 'toolchains/elan']) {
    fs.mkdirSync(path.join(sandboxRoot, directory), { recursive: true });
  }
  for (const [link, target] of [
    ['bin', 'usr/bin'],
    ['sbin', 'usr/sbin'],
    ['lib', 'usr/lib'],
    ['lib64', 'usr/lib64'],
  ] as const) {
    fs.symlinkSync(target, path.join(sandboxRoot, link));
  }
  return sandboxRoot;
};

const runLeanSandboxed = async (input: {
  checkoutRoot: string;
  projectRelative: string;
  command: string;
  args: string[];
  stdin?: string;
  timeoutMs: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  /** Sandbox path of a linked .lake/packages target; supported only by bwrap. */
  lakePackagesMountPath?: string;
  outputCapture?: 'head' | 'tail';
  outputLimit?: number;
  onDuplexSpawn?: (child: ChildProcess) => void;
  sandboxCapability?: ReturnType<typeof inspectMathematicsSandboxBackends>;
}): Promise<ProcessResult> => {
  const leaseStartedAt = Date.now();
  let proofLease: Awaited<ReturnType<typeof acquireMathProofEnvironmentLease>>;
  try {
    proofLease = await acquireMathProofEnvironmentLease(
      path.join(input.checkoutRoot, input.projectRelative),
      input.env ?? process.env,
      input.signal,
      leaseStartedAt + input.timeoutMs
    );
  } catch (error) {
    if (input.signal?.aborted || (error instanceof Error && error.name === 'AbortError'))
      return { ...unavailableProcessResult('Lean environment lease was cancelled.'), aborted: true };
    if (error instanceof Error && error.name === 'TimeoutError')
      return { ...unavailableProcessResult('Lean environment lease exceeded the operation deadline.'), timedOut: true };
    throw error;
  }
  let sealedRootFd: number | undefined;
  let temporaryRoot: string | undefined;
  let stagedCommandPath: string | undefined;
  try {
    if (proofLease) {
      input = { ...input, timeoutMs: input.timeoutMs - (Date.now() - leaseStartedAt) };
      if (input.timeoutMs <= 0)
        return {
          ...unavailableProcessResult('Lean environment lease exceeded the operation deadline.'),
          timedOut: true,
        };
    }
    if (proofLease && input.lakePackagesPath !== proofLease.packagesRoot)
      return unavailableProcessResult('Lean sandbox sealed package binding mismatch.');
    // Bind linked package caches at their validated target inside the sandbox.
    if (
      input.lakePackagesPath &&
      !input.lakePackagesMountPath &&
      fs
        .lstatSync(path.join(input.checkoutRoot, input.projectRelative, '.lake', 'packages'), {
          throwIfNoEntry: false,
        })
        ?.isSymbolicLink()
    ) {
      try {
        const mountPath = ensureLakePackagesMountPoint(
          path.join(input.checkoutRoot, input.projectRelative),
          input.checkoutRoot
        );
        if (mountPath) input = { ...input, lakePackagesMountPath: mountPath };
      } catch (error) {
        return unavailableProcessResult(error instanceof Error ? error.message : String(error));
      }
    }
    const environmentKey = sandboxEnvironmentKey(input.env);
    const capability = input.sandboxCapability ?? inspectMathematicsSandboxBackends(input.env || process.env);
    const unavailableReason = sandboxUnavailableReasons.get(environmentKey);
    if (unavailableReason) return unavailableProcessResult(unavailableReason);
    // A procfs magic link cannot safely be resolved again inside a new user
    // namespace or by a container daemon. Bind the already verified descriptor.
    // Other existing backends currently have no equivalent descriptor handoff.
    const backends = resolveSandboxBackends(input.env, capability).filter(
      (backend) => (!proofLease && !input.lakePackagesMountPath) || backend.kind === 'bwrap'
    );
    if (backends.length === 0) {
      if (proofLease)
        return unavailableProcessResult('Sealed proof environments require the bwrap file-descriptor mount backend.');
      const reason = capability.available.length
        ? 'Lean verification capability unavailable: this host does not permit the required Linux namespace or container sandbox.'
        : 'Lean verification capability unavailable: this host has no supported Linux sandbox backend (unshare, bwrap, Docker, or Podman).';
      if (capability.available.length === 0) sandboxUnavailableReasons.set(environmentKey, reason);
      return unavailableProcessResult(reason);
    }
    if (proofLease) {
      const before = fs.statSync(proofLease.packagesRoot, { bigint: true });
      sealedRootFd = fs.openSync(proofLease.packagesRoot, fs.constants.O_RDONLY | fs.constants.O_DIRECTORY);
      const opened = fs.fstatSync(sealedRootFd, { bigint: true });
      resolveMathProofEnvironment(
        path.join(input.checkoutRoot, input.projectRelative),
        input.env ?? process.env
      )!.verify();
      if (!opened.isDirectory() || opened.dev !== before.dev || opened.ino !== before.ino)
        return unavailableProcessResult('Sealed proof environment descriptor changed before sandbox execution.');
    }
    const sandboxCommand = path.basename(input.command);
    const pathEntries = (input.env?.PATH || process.env.PATH || '').split(path.delimiter).filter(Boolean);
    const resolvedCommand = path.isAbsolute(input.command)
      ? input.command
      : pathEntries.map((entry) => path.join(entry, input.command)).find((candidate) => fs.existsSync(candidate));
    const trustedElanHome = resolveTrustedElanHome(input.env);
    const trustedToolchainBin = resolveTrustedToolchainBin(
      input.checkoutRoot,
      input.projectRelative,
      input.env,
      trustedElanHome
    );
    // Elan may link a toolchain outside ELAN_HOME. Mount the selected real
    // installation, so neither that link nor a relative path can escape it.
    const mountedElanHome = trustedToolchainBin ? path.dirname(trustedToolchainBin) : trustedElanHome;
    const mountedToolchainBin = trustedToolchainBin
      ? '/toolchains/elan/bin'
      : '';
    const trustedCommandRoot = (candidate: string): boolean => {
      try {
        const canonical = fs.realpathSync(candidate);
        return Boolean(
          (trustedElanHome && canonical === path.join(trustedElanHome, 'bin', sandboxCommand)) ||
          (trustedToolchainBin && canonical === path.join(trustedToolchainBin, sandboxCommand))
        );
      } catch {
        return false;
      }
    };
    const customSourceCommand =
      resolvedCommand &&
      fs.existsSync(resolvedCommand) &&
      !trustedCommandRoot(path.resolve(resolvedCommand)) &&
      !OFFICIAL_EXECUTABLE_ALLOWLIST.has(sandboxCommand)
        ? resolvedCommand
        : undefined;
    const customCommand = Boolean(customSourceCommand);
    temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-sandbox-'));
    const sandboxRoot = createMathematicsSandboxRoot(temporaryRoot);
    let leanLauncherPath: string | undefined;
    if (trustedToolchainBin && mountedToolchainBin) {
      leanLauncherPath = path.join(temporaryRoot, 'lean-launcher');
      const prefix = `'${path.dirname(mountedToolchainBin).replaceAll("'", "'\\''")}'`;
      // Lake spawns Lean directly and otherwise chooses hardware-sized CLI
      // concurrency. Keep its original prefix while executing the same pinned
      // binary from a read-only alias with a bounded job count.
      fs.writeFileSync(
        leanLauncherPath,
        `#!/bin/sh
if [ "$#" = 1 ] && [ "$1" = --print-prefix ]; then printf '%s\\n' ${prefix}; exit 0; fi
exec /runtime/pinned-lean/bin/lean "$@" -j1
`,
        { mode: 0o500 }
      );
    }
    const sessionContainerIdFile = input.onDuplexSpawn ? path.join(temporaryRoot, 'session.cid') : undefined;
    let sessionContainerExecutable: string | undefined;
    // Replace host Lake overrides with paths to the sealed sandbox mount.
    // A linked package directory is mounted at its validated link target.
    const projectOverridesPath = path.join(
      input.checkoutRoot,
      input.projectRelative,
      '.lake',
      'package-overrides.json'
    );
    let sandboxPackageOverridesPath: string | undefined;
    if (input.lakePackagesPath && (proofLease || fs.existsSync(projectOverridesPath))) {
      if (proofLease && !fs.existsSync(projectOverridesPath)) {
        fs.mkdirSync(path.dirname(projectOverridesPath), { recursive: true, mode: 0o700 });
        // Lake also reads this mount target on the host, so use a valid empty override.
        fs.writeFileSync(projectOverridesPath, `${JSON.stringify({ schemaVersion: '1.2.0', packages: [] })}\n`, {
          flag: 'wx',
          mode: 0o600,
        });
      }
      sandboxPackageOverridesPath = path.join(temporaryRoot, 'package-overrides.json');
      const manifest = JSON.parse(
        fs.readFileSync(path.join(input.checkoutRoot, input.projectRelative, 'lake-manifest.json'), 'utf8')
      );
      const packages = manifest.packages.map((entry: Record<string, unknown>) => {
        const name = typeof entry.name === 'string' ? entry.name : '';
        if (!name || /[/\\]/u.test(name) || name.includes('\0') || name === '.' || name === '..')
          throw new Error('Sealed environment contains an invalid package name.');
        const directory = [name, name.replace(/^«(.+)»$/u, '$1')].find((candidate) =>
          fs.statSync(path.join(input.lakePackagesPath!, candidate), { throwIfNoEntry: false })?.isDirectory()
        );
        if (!directory) throw new Error('Sealed environment package is absent.');
        return {
          ...entry,
          type: 'path',
          dir: path.posix.join(
            input.lakePackagesMountPath ?? path.posix.join('/workspace', input.projectRelative, '.lake/packages'),
            directory
          ),
        };
      });
      fs.writeFileSync(sandboxPackageOverridesPath, JSON.stringify({ schemaVersion: '1.2.0', packages }) + '\n', {
        mode: 0o600,
      });
    }
    let commandForSandbox = sandboxCommand;
    if (customCommand) {
      // Explicit test/toolchain commands are copied into the sandbox instead of
      // executing an arbitrary host path.  The copied executable still runs
      // with the same namespace and clean environment as Lean itself.
      const customName = `deepscientist-verifier-${crypto.randomUUID()}`;
      const customPath = path.join(input.checkoutRoot, `.${customName}`);
      stagedCommandPath = customPath;
      try {
        fs.copyFileSync(customSourceCommand as string, customPath);
        fs.chmodSync(customPath, 0o755);
      } catch {
        return unavailableProcessResult(
          `Lean verifier executable could not be staged: ${customSourceCommand || input.command}`
        );
      }
      commandForSandbox = `/workspace/.${customName}`;
    } else if (!OFFICIAL_EXECUTABLE_ALLOWLIST.has(sandboxCommand)) {
      return unavailableProcessResult(`Lean verifier executable is not allowed in the sandbox: ${sandboxCommand}`);
    }
    const testCounterPath = input.env?.DEEPSCIENTIST_TEST_LEAN_COUNTER;
    const sandboxEnv = officialComparatorEnvironment(input.env);
    const sandboxCounterPath = path.join(input.checkoutRoot, '.deepscientist-test-counter');
    if (testCounterPath) sandboxEnv.DEEPSCIENTIST_TEST_LEAN_COUNTER = '/workspace/.deepscientist-test-counter';
    const nodeExecutable = pathEntries
      .map((entry) => path.join(entry, 'node'))
      .find((candidate) => fs.existsSync(candidate));
    const runtimeRoot = path.resolve(path.dirname(nodeExecutable || process.execPath), '..');
    const configuredRuntimeRoot =
      input.env?.DEEPSCIENTIST_MATH_TRUSTED_RUNTIME_ROOT || process.env.DEEPSCIENTIST_MATH_TRUSTED_RUNTIME_ROOT;
    const configuredToolsRoot = input.env?.DEEPSCIENTIST_LEAN_EVAL_TOOLS_ROOT;
    let trustedRuntimeRoot = '';
    if (customCommand || configuredToolsRoot) {
      try {
        const canonicalRuntime = fs.realpathSync(customCommand ? configuredRuntimeRoot || runtimeRoot : configuredToolsRoot!);
        if (fs.statSync(canonicalRuntime).isDirectory()) trustedRuntimeRoot = canonicalRuntime;
      } catch {
        trustedRuntimeRoot = '';
      }
    }
    try {
      const mounts = {
        projectRelative: input.projectRelative.replaceAll(path.sep, '/'),
        toolchainRoot: mountedElanHome, toolchainBin: mountedToolchainBin, runtimeRoot: trustedRuntimeRoot,
        lakePackagesPath: input.lakePackagesPath || '', lakePackageOverridesPath: sandboxPackageOverridesPath,
        command: commandForSandbox, commandArgs: input.args,
        testCounter: testCounterPath ? '/workspace/.deepscientist-test-counter' : '',
        testAxioms: input.env?.DEEPSCIENTIST_TEST_LEAN_AXIOMS || '',
      };
      const runBackend = (backend: MathematicsSandboxBackend): Promise<ProcessResult> => {
        const args = backend.kind === 'unshare'
          ? [
              '--user', '--map-root-user', '--net', '--mount', '--pid', '--fork', '--kill-child=SIGKILL',
              '/bin/sh', '-ceu', LEAN_SANDBOX_SCRIPT, '--', sandboxRoot, input.checkoutRoot,
              mounts.projectRelative, mountedElanHome, mountedToolchainBin, trustedRuntimeRoot,
              '/workspace/.deepscientist-test-counter', mounts.testAxioms, input.lakePackagesPath || '',
              sandboxPackageOverridesPath || '', commandForSandbox, ...input.args,
            ]
          : backend.kind === 'bwrap'
            ? buildBwrapArguments({
                ...mounts, candidateRoot: input.checkoutRoot, lakePackagesMountPath: input.lakePackagesMountPath,
                lakePackagesFd: sealedRootFd === undefined ? undefined : 3, leanLauncherPath,
              })
            : buildContainerArguments({
                ...mounts, checkoutRoot: input.checkoutRoot,
                interactive: Boolean(input.onDuplexSpawn || input.stdin !== undefined), cidfile: sessionContainerIdFile,
                image: input.env?.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || process.env.DEEPSCIENTIST_MATH_SANDBOX_IMAGE || '',
              });
        return runLeanProcess(backend.executable, args, {
          cwd: path.join(input.checkoutRoot, input.projectRelative), timeoutMs: input.timeoutMs,
          signal: input.signal, env: { ...sandboxEnv, DEEPSCIENTIST_MATH_LEAN_LOCK: input.env?.DEEPSCIENTIST_MATH_LEAN_LOCK }, stdin: input.stdin,
          outputCapture: input.outputCapture, outputLimit: input.outputLimit, onDuplexSpawn: input.onDuplexSpawn,
          ...(backend.kind === 'bwrap' && sealedRootFd !== undefined ? { inheritedFds: [sealedRootFd] } : {}),
        });
      };
      let result: ProcessResult | undefined;
      for (const backend of backends) {
        if (sessionContainerIdFile && (backend.kind === 'docker' || backend.kind === 'podman'))
          sessionContainerExecutable = backend.executable;
        // Backends are fallbacks, so a permission failure must finish before
        // trying the next one; running both would race two sandboxes.
        // eslint-disable-next-line no-await-in-loop
        result = Object.freeze({ ...(await runBackend(backend)), sandboxBackend: backend.kind });
        if (!isSandboxBackendFailure(backend.kind, result)) {
          break;
        }
        sandboxBackendFailures.add(sandboxBackendKey(environmentKey, backend.kind));
        // The caller owns the first stream handle. A silent replacement would
        // leave an unreachable server running; a later call may use a fallback.
        if (input.onDuplexSpawn) break;
      }
      if (!result) {
        const reason =
          'Lean verification capability unavailable: this host does not permit the required Linux namespace sandbox.';
        return unavailableProcessResult(reason);
      }
      if (isSandboxBackendFailure(result.sandboxBackend || backends[backends.length - 1].kind, result)) {
        const reason =
          'Lean verification capability unavailable: this host does not permit the required Linux namespace or container sandbox.';
        sandboxUnavailableReasons.set(environmentKey, reason);
        return unavailableProcessResult(reason);
      }
      if (testCounterPath?.startsWith('/') && fs.existsSync(sandboxCounterPath)) {
        fs.copyFileSync(sandboxCounterPath, testCounterPath);
        fs.rmSync(sandboxCounterPath, { force: true });
      }
      return result;
    } finally {
      if (sessionContainerExecutable && sessionContainerIdFile && fs.existsSync(sessionContainerIdFile)) {
        const containerId = fs.readFileSync(sessionContainerIdFile, 'utf8').trim();
        if (/^[a-f0-9]{12,64}$/u.test(containerId)) {
          await runProcess(sessionContainerExecutable, ['rm', '--force', containerId], {
            cwd: input.checkoutRoot,
            timeoutMs: 5_000,
            env: sandboxEnv,
          });
        }
      }
    }
  } finally {
    try {
      if (stagedCommandPath) fs.rmSync(stagedCommandPath, { force: true });
      if (temporaryRoot) fs.rmSync(temporaryRoot, { recursive: true, force: true });
    } finally {
      if (sealedRootFd !== undefined) fs.closeSync(sealedRootFd);
      await proofLease?.release();
    }
  }
};

/**
 * Run a construction-time Lean/Lake command in the same namespace boundary as
 * formal verification.  This is intentionally narrow: callers provide a
 * disposable checkout and repository-relative project directory, while the
 * verifier owns executable allowlisting, environment scrubbing, resource
 * limits, timeout handling, and cleanup.
 */
export async function runMathematicsSandboxedCommand(input: {
  checkoutRoot: string;
  projectRelative?: string;
  command: string;
  args?: readonly string[];
  /** Optional bounded input for a JSON-lines construction-time backend. */
  stdin?: string;
  timeoutMs: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  /** Opaque host-owned transport for immutable construction-time packages. */
  /** Preserve the first bounded output segment for JSON-lines diagnostic consumers. */
  outputCapture?: 'head' | 'tail';
  /** Use package copies already inside a disposable checkout without attaching shared caches. */
  useWorkspacePackagesOnly?: boolean;
  /** Internal transport hook; process lifetime is owned by the caller's abort signal. */
  onDuplexSpawn?: (child: ChildProcess) => void;
}): Promise<MathematicsSandboxCommandResult> {
  // Every construction-time command gets the same pinned Lean environment as
  // the proof loop, even when a caller does not explicitly pass `env`.
  const runtimeEnv = resolveMathematicsRuntimeEnvironment(input.env || process.env);
  if (input.stdin !== undefined) {
    if (typeof input.stdin !== 'string') {
      return unavailableProcessResult('Lean sandbox stdin must be a string.');
    }
    if (input.stdin.includes('\0')) {
      return unavailableProcessResult('Lean sandbox stdin must not contain NUL bytes.');
    }
    if (Buffer.byteLength(input.stdin, 'utf8') > MAX_SANDBOX_STDIN_BYTES) {
      return unavailableProcessResult(`Lean sandbox stdin exceeds the ${MAX_SANDBOX_STDIN_BYTES}-byte limit.`);
    }
  }
  const checkoutRoot = path.resolve(input.checkoutRoot);
  const projectRelative = (input.projectRelative ?? '').trim().replaceAll('\\', '/');
  if (
    projectRelative &&
    (projectRelative.startsWith('/') ||
      projectRelative.split('/').some((part) => !part || part === '.' || part === '..'))
  ) {
    return unavailableProcessResult('Lean sandbox project path must be repository-relative.');
  }
  const projectRoot = path.join(checkoutRoot, projectRelative);
  try {
    const rootStat = fs.lstatSync(checkoutRoot);
    const projectStat = fs.lstatSync(projectRoot);
    if (
      rootStat.isSymbolicLink() ||
      !rootStat.isDirectory() ||
      projectStat.isSymbolicLink() ||
      !projectStat.isDirectory()
    ) {
      return unavailableProcessResult('Lean sandbox checkout and project must be regular directories.');
    }
    // A regular directory at the leaf is insufficient: an intermediate
    // symlink could redirect the command outside the disposable checkout.
    // Reuse the same canonical path policy as formal and official verifiers.
    assertNoSymlinkTraversal(checkoutRoot, projectRoot, 'Lean sandbox project');
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return unavailableProcessResult(
      message.includes('symlink') ? message : 'Lean sandbox checkout or project directory is missing.'
    );
  }
  const sealed = resolveMathProofEnvironment(projectRoot, runtimeEnv);
  let lakePackagesPath: string | undefined;
  if (input.useWorkspacePackagesOnly && input.lakePackagesPath) {
    return unavailableProcessResult('Private workspace packages cannot be combined with an external package mount.');
  }
  if (sealed) {
    if (input.useWorkspacePackagesOnly || (input.lakePackagesPath && input.lakePackagesPath !== sealed.packagesRoot))
      return unavailableProcessResult('Lean sandbox sealed package binding mismatch.');
    lakePackagesPath = sealed.packagesRoot;
  } else if (input.lakePackagesPath) {
    try {
      const packageStat = fs.lstatSync(input.lakePackagesPath);
      if (packageStat.isSymbolicLink() || !packageStat.isDirectory()) {
        return unavailableProcessResult('Lean sandbox Lake package cache must be a regular directory.');
      }
      lakePackagesPath = fs.realpathSync(input.lakePackagesPath);
    } catch {
      return unavailableProcessResult('Lean sandbox Lake package cache is missing.');
    }
  } else if (!input.useWorkspacePackagesOnly) {
    lakePackagesPath = resolveMathematicsLakePackagesCache(projectRoot, runtimeEnv);
  }
  let lakePackagesMountPath: string | undefined;
  if (lakePackagesPath) {
    try {
      lakePackagesMountPath = ensureLakePackagesMountPoint(projectRoot, checkoutRoot);
    } catch (error) {
      return unavailableProcessResult(error instanceof Error ? error.message : String(error));
    }
  }
  return runLeanSandboxed({
    ...(lakePackagesMountPath ? { lakePackagesMountPath } : {}),
    checkoutRoot,
    projectRelative,
    command: input.command,
    args: [...(input.args ?? [])],
    ...(input.stdin !== undefined ? { stdin: input.stdin } : {}),
    timeoutMs: input.timeoutMs,
    signal: input.signal,
    env: runtimeEnv,
    lakePackagesPath,
    outputCapture: input.outputCapture,
    onDuplexSpawn: input.onDuplexSpawn,
  });
}

const readGitHead = async (
  projectRoot: string,
  options: MathematicsVerifierExecutionOptions
): Promise<string | undefined> => {
  const result = await runGit(projectRoot, ['rev-parse', 'HEAD'], options);
  return result.exitCode === 0 ? result.stdout.trim() || undefined : undefined;
};

const resolveGitCommit = async (
  projectRoot: string,
  reference: string,
  options: MathematicsVerifierExecutionOptions
): Promise<string | undefined> => {
  const result = await runGit(projectRoot, ['rev-parse', '--verify', `${reference}^{commit}`], options);
  return result.exitCode === 0 ? result.stdout.trim() || undefined : undefined;
};

const readGitStatus = async (
  projectRoot: string,
  options: MathematicsVerifierExecutionOptions
): Promise<{ ok: boolean; output?: string }> => {
  const result = await runGit(projectRoot, ['status', '--porcelain=v1', '--untracked-files=all'], options);
  const output = String(result.stdout || '');
  return {
    ok: result.exitCode === 0,
    output: preview(output) || preview(result.stderr),
  };
};

/**
 * Resolve all proof blob identities with two Git invocations instead of two
 * invocations per proof file. `ls-tree -z` keeps committed paths unambiguous
 * even when a path contains whitespace or a newline.
 */
const readGitBlobIds = async (
  projectRoot: string,
  targetCommit: string,
  relativePaths: readonly string[],
  options: MathematicsVerifierExecutionOptions
): Promise<ReadonlyMap<string, { committed?: string; working?: string }>> => {
  const result = new Map<string, { committed?: string; working?: string }>();
  if (relativePaths.length === 0) return result;
  // `runProcess` intentionally keeps only a bounded output tail. Keep each
  // ls-tree response below that budget so long proof paths cannot make a
  // valid committed file disappear from the identity map.
  const committedChunks: string[][] = [];
  let chunk: string[] = [];
  let estimatedBytes = 0;
  for (const relativePath of relativePaths) {
    const pathBytes = Buffer.byteLength(relativePath, 'utf8') + 64;
    if (chunk.length > 0 && estimatedBytes + pathBytes > MAX_OUTPUT - 1_024) {
      committedChunks.push(chunk);
      chunk = [];
      estimatedBytes = 0;
    }
    chunk.push(relativePath);
    estimatedBytes += pathBytes;
  }
  if (chunk.length > 0) committedChunks.push(chunk);
  const [committedResults, working] = await Promise.all([
    Promise.all(
      committedChunks.map((paths) =>
        runGit(projectRoot, ['ls-tree', '-r', '-z', targetCommit, '--', ...paths], options)
      )
    ),
    runGit(projectRoot, ['hash-object', '--no-filters', '--', ...relativePaths], options),
  ]);
  for (const committed of committedResults) {
    if (committed.exitCode !== 0) continue;
    for (const record of committed.stdout.split('\0')) {
      const separator = record.indexOf('\t');
      if (separator < 0) continue;
      const header = record.slice(0, separator).split(/\s+/u);
      const objectId = header[2]?.trim();
      const relativePath = record.slice(separator + 1);
      if (!objectId || !relativePath) continue;
      result.set(relativePath, { ...result.get(relativePath), committed: objectId });
    }
  }
  if (working.exitCode === 0) {
    const hashes = working.stdout
      .split(/\r?\n/u)
      .map((value) => value.trim())
      .filter(Boolean);
    if (hashes.length === relativePaths.length) {
      relativePaths.forEach((relativePath, index) => {
        result.set(relativePath, { ...result.get(relativePath), working: hashes[index] });
      });
    }
  }
  return result;
};

const proofFileMetadataAsync = async (absolutePath: string): Promise<string | undefined> => {
  try {
    const stat = await fs.promises.lstat(absolutePath, { bigint: true });
    if (!stat.isFile()) return undefined;
    return mathFileIdentity(stat);
  } catch {
    return undefined;
  }
};

const normalizeItem = (
  projectRoot: string,
  item: MathematicsVerifierBatchItem,
  index: number,
  preparedPathByInput: Map<string, PreparedProofPath>
): PreparedItem => {
  let preparedPath = preparedPathByInput.get(item.proofPath);
  if (!preparedPath) {
    const lexicalProofPath = path.resolve(projectRoot, item.proofPath);
    const absoluteProofPath = assertNoSymlinkTraversal(projectRoot, lexicalProofPath, 'proofPath', projectRoot);
    const relativeProofPath = path.relative(projectRoot, absoluteProofPath).replaceAll(path.sep, '/');
    if (!relativeProofPath || path.extname(absoluteProofPath).toLowerCase() !== '.lean') {
      throw new Error('formal_verifier currently accepts a .lean proofPath.');
    }
    const stat = fs.statSync(absoluteProofPath);
    if (!stat.isFile()) throw new Error('proofPath must refer to a regular file.');
    if (stat.size > MAX_PROOF_BYTES) {
      throw new Error(`proofPath exceeds the ${MAX_PROOF_BYTES}-byte verifier input limit.`);
    }
    preparedPath = { absoluteProofPath, relativeProofPath };
    preparedPathByInput.set(item.proofPath, preparedPath);
  }
  return {
    ...item,
    checkId: item.id?.trim() || `check-${index + 1}`,
    ...preparedPath,
  };
};

const normalizeItems = (
  projectRoot: string,
  items: readonly MathematicsVerifierBatchItem[]
): readonly PreparedItem[] => {
  const preparedPathByInput = new Map<string, PreparedProofPath>();
  return items.map((item, index) => normalizeItem(projectRoot, item, index, preparedPathByInput));
};

const prepareFiles = async (
  projectRoot: string,
  items: readonly PreparedItem[],
  cachePreparation?: Pick<FormalVerificationCachePreparation, 'proofSources'>
): Promise<PreparedFile[]> => {
  const grouped = new Map<string, PreparedItem[]>();
  items.forEach((item) => {
    const existing = grouped.get(item.relativeProofPath);
    if (existing) existing.push(item);
    else grouped.set(item.relativeProofPath, [item]);
  });
  return Promise.all(
    Array.from(grouped.values(), async (groupItems) => {
      const first = groupItems[0];
      let source: string;
      const cached = cachePreparation?.proofSources.get(first.relativeProofPath);
      const useCachedSource =
        cached !== undefined && (await proofFileMetadataAsync(first.absoluteProofPath)) === cached.metadata;
      if (useCachedSource) {
        source = cached.source;
      } else {
        try {
          source = await fs.promises.readFile(first.absoluteProofPath, 'utf8');
        } catch (error) {
          const code = (error as NodeJS.ErrnoException).code;
          if (code === 'ENOENT') {
            throw new Error(`Proof file not found: ${first.relativeProofPath}`, { cause: error });
          }
          throw error;
        }
      }
      const sourceDeclarationHashes = declarationHashes(source);
      return {
        absoluteProofPath: first.absoluteProofPath,
        relativeProofPath: first.relativeProofPath,
        source,
        declarationHashes: sourceDeclarationHashes,
        sourceDeclarationHashes,
        axiomDependencies: new Map(),
        proofHash:
          useCachedSource ? cached.hash : crypto.createHash('sha256').update(source).digest('hex'),
        inspection: inspectLeanSource(source),
        items: groupItems,
      };
    })
  );
};

type LeanDeclarationQuery = Readonly<{
  relativePath: string;
  absolutePath: string;
  parse: (stdout: string) => {
    hashes?: Map<string, string>;
    types?: Map<string, string>;
    axioms?: Map<string, string[]>;
    usedDependencies?: Map<string, string[]>;
    references?: Map<string, LeanDeclarationReferences>;
    error?: string;
  };
}>;

const prepareLeanDeclarationQuery = async (
  verificationProjectRoot: string,
  file: PreparedFile,
  items: readonly PreparedItem[],
  options?: Readonly<{
    moduleName?: string;
    expectedDeclarationType?: string;
    expectedDeclarationTypes?: Readonly<Record<string, string>>;
    forbiddenImportModules?: readonly string[];
    dependencyCandidates?: readonly string[];
    referenceModules?: readonly { module: string; file: string }[];
  }>
): Promise<LeanDeclarationQuery | undefined> => {
  const theoremNameSet = new Set<string>();
  for (const item of items) {
    if (item.theoremName) theoremNameSet.add(item.theoremName);
  }
  const theoremNames = [...theoremNameSet];
  if (theoremNames.length === 0) return undefined;
  const queryRelativePath = path.posix.join(
    path.posix.dirname(file.relativeProofPath),
    `.deepscientist-declarations-${crypto.randomUUID()}.lean`
  );
  const queryAbsolutePath = path.join(verificationProjectRoot, ...queryRelativePath.split('/'));
  const theoremQueries = theoremNames.map((name) => {
    const markerId = crypto.createHash('sha256').update(name).digest('hex').slice(0, 16);
    return {
      name,
      localName: name.split('.').at(-1),
      declarationBegin: `DEEPSCIENTIST_DECL_BEGIN_${markerId}`,
      declarationEnd: `DEEPSCIENTIST_DECL_END_${markerId}`,
      axiomBegin: `DEEPSCIENTIST_AXIOMS_BEGIN_${markerId}`,
      axiomEnd: `DEEPSCIENTIST_AXIOMS_END_${markerId}`,
    };
  });
  const queries = theoremQueries
    .map(
      ({ name, declarationBegin, declarationEnd, axiomBegin, axiomEnd }) =>
        `#eval IO.println ${JSON.stringify(declarationBegin)}\n#check ${name}\n#eval IO.println ${JSON.stringify(declarationEnd)}\n#eval IO.println ${JSON.stringify(axiomBegin)}\n#print axioms ${name}\n#eval IO.println ${JSON.stringify(axiomEnd)}`
    )
    .join('\n');
  const expectedType = options?.expectedDeclarationType;
  const expectedTypes = theoremNames.flatMap(name => {
    const type = options?.expectedDeclarationTypes?.[name] ?? expectedType;
    return type === undefined ? [] : [{ name, type, context: leanDeclarationContextCommands(file.source, name) }];
  });
  const dependencyCandidates = options?.dependencyCandidates;
  if (
    dependencyCandidates &&
    (theoremNames.length > 32 ||
      dependencyCandidates.length > 32 ||
      dependencyCandidates.some((name) => !/^[A-Za-z_][A-Za-z0-9_'.]*$/u.test(name)))
  )
    throw new Error('Dependency attribution requires bounded theorem and declaration names.');
  const dependencyMarkers = new Map(
    theoremNames.map((name) => [name, `DS_PROOF_DEPENDENCIES_${crypto.randomBytes(16).toString('hex')}:`])
  );
  const referenceMarkers = new Map(theoremNames.map(name => [name, `DS_DECL_REFERENCES_${crypto.randomBytes(16).toString('hex')}:`]));
  if ((expectedType && theoremNames.length !== 1) || expectedTypes.some(item => !item.type || item.type.length > 12_000))
    throw new Error('Helper expected type requires one bounded declaration.');
  const externalChecks = options
    ? [
        'import Lean.Elab.BuiltinCommand\nimport Lean.Elab.SyntheticMVars',
        options.moduleName ? `import ${options.moduleName}` : file.source,
        ...(options.forbiddenImportModules?.length
          ? [
              'run_cmd do',
              `  let forbidden : List String := ${JSON.stringify(options.forbiddenImportModules)}`,
              '  for moduleName in (<- Lean.getEnv).header.moduleNames do',
              '    if forbidden.contains moduleName.toString then throwError "Forbidden helper dependency: {moduleName}"',
            ]
          : []),
        ...expectedTypes.flatMap(({ name, type, context }) => [
              ...context.before,
              'run_cmd Lean.Elab.Command.liftTermElabM do',
              `  let parsedType <- match Lean.Parser.runParserCategory (<- Lean.getEnv) (Lean.Name.mkSimple "term") ${JSON.stringify(type)} with`,
              '    | .ok stx => pure stx',
              '    | .error message => throwError "{message}"',
              '  let expected <- Lean.Elab.Term.elabType parsedType',
              '  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing',
              '  let expected <- Lean.instantiateMVars expected',
              '  if expected.hasMVar || expected.hasFVar then throwError "Helper expected type must be closed without metavariables"',
              `  let declaration <- Lean.Meta.mkConstWithFreshMVarLevels (${JSON.stringify(name)}.toName)`,
              '  let actual <- Lean.Meta.inferType declaration',
              '  unless (<- Lean.Meta.isDefEq actual expected) do throwError "Helper declaration has a different type or additional assumptions"',
              ...context.after,
            ]),
        ...(dependencyCandidates
          ? theoremNames.flatMap((theoremName) => [
              'run_cmd do',
              '  let env <- Lean.getEnv',
              `  let root <- Lean.getConstInfo (${JSON.stringify(theoremName)}.toName)`,
              '  let some proof := root.value? (allowOpaque := true) | throwError "Declaration has no proof value"',
              '  let mut todo := Lean.Expr.getUsedConstants proof |>.toList',
              '  let mut visited : Lean.NameSet := {}',
              '  let mut fuel := 200000',
              '  while !todo.isEmpty do',
              '    if fuel == 0 then throwError "Proof dependency closure exceeds its bound"',
              '    fuel := fuel - 1',
              '    let name := todo.head!',
              '    todo := todo.tail!',
              '    if !visited.contains name then',
              '      visited := visited.insert name',
              '      if let some info := env.find? name then',
              '        if let some value := info.value? (allowOpaque := true) then todo := (Lean.Expr.getUsedConstants value).toList ++ todo',
              `  let candidates : List String := ${JSON.stringify(dependencyCandidates)}`,
              '  let used := candidates.filter fun name => visited.contains name.toName',
              `  Lean.logInfo m!"${dependencyMarkers.get(theoremName)!}{(Lean.toJson used).compress}"`,
            ])
          : []),
        ...(options.referenceModules ? theoremNames.flatMap(name =>
          leanReferenceCommands(name, options.referenceModules!, referenceMarkers.get(name)!)) : []),
      ].join('\n')
    : file.source;
  await fs.promises.writeFile(queryAbsolutePath, `${externalChecks}\n${queries}\n`, 'utf8');
  return {
    relativePath: queryRelativePath,
    absolutePath: queryAbsolutePath,
    parse: (stdout: string): ReturnType<LeanDeclarationQuery['parse']> => {
      const hashes = new Map<string, string>();
      const types = new Map<string, string>();
      const axioms = new Map<string, string[]>();
      const usedDependencies = new Map<string, string[]>();
      const references = new Map<string, LeanDeclarationReferences>();
      if (options?.referenceModules) for (const [name, marker] of referenceMarkers) {
        const report = parseLeanReferences(stdout, marker, options.referenceModules.map(module => module.file));
        if (report) references.set(name, report);
      }
      if (dependencyCandidates) {
        for (const [theoremName, dependencyMarker] of dependencyMarkers) {
          const lines = stdout.split('\n').filter((line) => line.includes(dependencyMarker));
          try {
            if (lines.length !== 1) throw new Error('Missing unique dependency report');
            const values: unknown = JSON.parse(
              lines[0].slice(lines[0].indexOf(dependencyMarker) + dependencyMarker.length)
            );
            if (
              !Array.isArray(values) ||
              values.some((value) => typeof value !== 'string' || !dependencyCandidates.includes(value))
            )
              throw new Error('Invalid dependency report');
            usedDependencies.set(theoremName, values as string[]);
          } catch {
            return { error: `Lean did not export a valid proof dependency report for ${theoremName}.` };
          }
        }
      }
      for (const query of theoremQueries) {
        const start = stdout.indexOf(query.declarationBegin);
        const finish = start >= 0 ? stdout.indexOf(query.declarationEnd, start + query.declarationBegin.length) : -1;
        if (start < 0 || finish < 0) {
          return { error: `Lean did not export the requested theorem declaration: ${query.name}` };
        }
        const elaboratedType = stdout
          .slice(start + query.declarationBegin.length, finish)
          .trim()
          .replace(/\s+/gu, ' ');
        if (!elaboratedType) return { error: `Lean exported an empty theorem declaration: ${query.name}` };
        const hash = crypto.createHash('sha256').update(elaboratedType).digest('hex');
        types.set(query.name, elaboratedType);
        if (query.localName) types.set(query.localName, elaboratedType);
        hashes.set(query.name, hash);
        if (query.localName) hashes.set(query.localName, hash);

        const axiomStart = stdout.indexOf(query.axiomBegin, finish + query.declarationEnd.length);
        const axiomFinish = axiomStart >= 0 ? stdout.indexOf(query.axiomEnd, axiomStart + query.axiomBegin.length) : -1;
        if (axiomStart < 0 || axiomFinish < 0) {
          return { error: `Lean did not export axiom dependencies for the requested theorem: ${query.name}` };
        }
        const axiomOutput = stdout.slice(axiomStart + query.axiomBegin.length, axiomFinish);
        const dependencyMatch = /depends on axioms:\s*\[([^\]]*)\]/iu.exec(axiomOutput);
        const dependencies = dependencyMatch?.[1]
          ? dependencyMatch[1]
              .split(',')
              .map((axiom) => axiom.trim())
              .filter(Boolean)
          : /does not depend on any axioms/iu.test(axiomOutput)
            ? []
            : undefined;
        if (!dependencies) {
          return {
            error: `Lean returned an unrecognized axiom dependency report for the requested theorem: ${query.name}`,
          };
        }
        axioms.set(query.name, dependencies);
        if (query.localName) axioms.set(query.localName, dependencies);
      }
      return { hashes, types, axioms, usedDependencies, references };
    },
  };
};

const receiptIdFor = (base: ResultBase): string =>
  `lean-${crypto
    .createHash('sha256')
    .update(
      JSON.stringify({
        checkId: base.checkId,
        targetCommit: base.targetCommit,
        statementHash: base.statementHash,
        leanStatementHash: base.leanStatementHash || null,
        claim: base.claim,
        proofHash: base.proofHash,
        proofPath: base.proofPath,
        theoremName: base.theoremName || null,
        theoremDeclarationHash: base.theoremDeclarationHash || null,
      })
    )
    .digest('hex')
    .slice(0, 24)}`;

const aggregateStatus = (results: MathematicsVerifierResult[]): MathematicsVerifierStatus => {
  if (results.length > 0 && results.every((result) => result.status === 'kernel_verified')) return 'kernel_verified';
  if (results.some((result) => result.status === 'failed')) return 'failed';
  if (results.some((result) => result.status === 'blocked')) return 'blocked';
  return 'unavailable';
};

const isUnavailableProcess = (result: ProcessResult): boolean => {
  if (result.errorCode === 'ENOENT' || result.errorCode === 'EACCES') return true;
  if (result.exitCode !== 127) return false;
  return /(?:command not found|not recognized|no such file|could not find)/iu.test(
    `${result.stderr}\n${result.stdout}`
  );
};

function classifyLeanCheck(result: ProcessResult, context: {
  command: string; batchDeadlineAt: number; projectRoot: string; packagesPath?: string; exportError?: string;
}): Pick<MathematicsVerifierResult, 'status' | 'verifier' | 'error'> {
  const blocked = (error: string) => ({ status: 'blocked' as const, verifier: 'lean-kernel' as const, error });
  if (isUnavailableProcess(result)) return { status: 'unavailable', verifier: 'unavailable',
    error: `${context.command} is not installed or could not be started.` };
  if (result.aborted) return blocked('Formal verification was aborted.');
  if (result.timedOut) return blocked(Date.now() >= context.batchDeadlineAt
    ? 'Formal verification batch deadline exceeded.' : 'Lean verification timed out.');
  if (result.errorMessage) return blocked(`Lean could not be executed: ${result.errorMessage}`);
  if (result.exitCode !== 0) {
    if (/(?:^|\n)(?:error: (?:external command 'git'|toolchain |failed to (?:fetch|download|clone))|git: 'remote-https' is not a git command)/u.test(result.stderr))
      return blocked('Lean verification environment could not initialize; retry the same frozen candidate after restoring dependencies.');
    if (hasUnavailablePinnedLeanModule(`${result.stdout}\n${result.stderr}`, context.projectRoot, context.packagesPath))
      return blocked('Lean verification cannot load a module supplied by the pinned dependencies; restore the compiled cache or search path and retry the same frozen candidate.');
    return { status: 'failed', verifier: 'lean-kernel', error: `Lean exited with status ${result.exitCode ?? 'unknown'}.` };
  }
  return context.exportError ? blocked(context.exportError) : { status: 'kernel_verified', verifier: 'lean-kernel' };
}

type FormalFileVerificationContext = {
  request: MathematicsVerifierBatchRequest;
  options: MathematicsVerifierExecutionOptions;
  command: 'lake' | 'lean'; verifierCommand: string; lakeFile?: string;
  requiresPackages: boolean; toolUnavailable: boolean; batchDeadlineAt: number;
  verificationProjectRoot: string; relativeProjectRoot: string; checkoutRoot: string;
  runtimeEnvironment: NodeJS.ProcessEnv; lakePackagesPath?: string;
  sandboxCapability: ReturnType<typeof inspectMathematicsSandboxBackends>;
  blobIdsByPath: ReadonlyMap<string, { committed?: string; working?: string }>;
  emit: <Kind extends MathematicsVerificationEventKind>(kind: Kind, payload: MathematicsVerificationEventPayloadMap[Kind]) => void;
  publishResults: (file: PreparedFile, status: MathematicsVerifierStatus, verifier: MathematicsVerifierResult['verifier'],
    error?: string, output?: { stdoutPreview?: string; stderrPreview?: string }, selectedItems?: PreparedItem[]) => void;
};

/** Consume one prepared checkout; preparation, ordering and cleanup belong to the batch. */
async function verifyFormalFile(file: PreparedFile, context: FormalFileVerificationContext): Promise<void> {
  const { request, options, command, verifierCommand, lakeFile, requiresPackages, batchDeadlineAt,
    verificationProjectRoot, relativeProjectRoot, checkoutRoot, runtimeEnvironment, lakePackagesPath, blobIdsByPath,
    emit, publishResults } = context;
  const reject = (message: string, items: PreparedItem[]) => {
    emit('diagnostic.emitted', { source: 'safety', severity: 'error', message, proofPath: file.relativeProofPath });
    publishResults(file, 'failed', 'lean-kernel', message, undefined, items);
  };
  if (options.signal?.aborted) {
    publishResults(file, 'blocked', 'lean-kernel', 'Formal verification was aborted.');
    return;
  }
  if (requiresPackages) {
    publishResults(file, 'blocked', 'lean-kernel',
      'Lean verification blocked: no manifest-compatible Lake package cache is configured; sandboxed verification never downloads dependencies.');
    return;
  }
  const remainingBatchMs = batchDeadlineAt - Date.now();
  if (remainingBatchMs < MIN_TIMEOUT_MS) {
    const error = 'Formal verification batch deadline exceeded.';
    emit('diagnostic.emitted', { source: 'process', severity: 'error', message: error });
    publishResults(file, 'blocked', 'lean-kernel', error);
    return;
  }
  if (context.toolUnavailable) {
    publishResults(
      file,
      'unavailable',
      'unavailable',
      `${command} is not installed or could not be started.`
    );
    return;
  }

  // Check each immutable proof independently before starting Lean.
  // The identities were collected in one batched Git pass above so
  // large FORMALIZE waves do not pay two process startups per file.
  const blobIds = blobIdsByPath.get(file.relativeProofPath);
  const committedBlobId = blobIds?.committed;
  const workingBlobId = blobIds?.working;
  if (options.signal?.aborted) {
    publishResults(file, 'blocked', 'lean-kernel', 'Formal verification was aborted.');
    return;
  }
  if (!committedBlobId || !workingBlobId || committedBlobId !== workingBlobId) {
    const error = 'The proof file must be tracked and byte-identical to the file at targetCommit.';
    emit('diagnostic.emitted', {
      source: 'git',
      severity: 'error',
      message: error,
      proofPath: file.relativeProofPath,
    });
    publishResults(file, 'blocked', 'lean-kernel', error);
    return;
  }

  const missingDeclarationItems: PreparedItem[] = [];
  const declarationMismatchItems: PreparedItem[] = [];
  const verifiableItems: PreparedItem[] = [];
  for (const item of file.items) {
    if (!item.theoremName) {
      verifiableItems.push(item);
      continue;
    }
    let excluded = false;
    const localName = item.theoremName.split('.').at(-1) || item.theoremName;
    if (!file.declarationHashes.has(item.theoremName) && !file.declarationHashes.has(localName)) {
      missingDeclarationItems.push(item);
      excluded = true;
    }
    if (item.expectedSourceDeclarationHash) {
      const actual =
        file.sourceDeclarationHashes.get(item.theoremName) || file.sourceDeclarationHashes.get(localName);
      if (actual !== item.expectedSourceDeclarationHash) {
        declarationMismatchItems.push(item);
        excluded = true;
      }
    }
    if (!excluded) verifiableItems.push(item);
  }
  for (const item of missingDeclarationItems)
    reject(`The requested theorem declaration was not found in ${file.relativeProofPath}: ${item.theoremName}`, [item]);
  for (const item of declarationMismatchItems)
    reject(`The theorem declaration in ${file.relativeProofPath} does not match the immutable formal statement: ${item.theoremName}`, [item]);
  if (verifiableItems.length === 0) return;

  const draftAccepted =
    file.inspection.sorryCount === 0 &&
    file.inspection.admitCount === 0 &&
    file.inspection.axioms.length === 0;
  emit('check.draft_checked', {
    proofPath: file.relativeProofPath,
    status: draftAccepted ? 'accepted' : 'rejected',
    ...file.inspection,
  });
  if (!draftAccepted) {
    const error =
      file.inspection.sorryCount > 0 || file.inspection.admitCount > 0
        ? 'Proof source contains sorry or admit.'
        : `Proof source declares explicit axioms: ${file.inspection.axioms.join(', ')}.`;
    reject(error, verifiableItems);
    return;
  }

  // The temporary query is the exact committed proof plus #check markers,
  // so one Lean kernel run both compiles the proof and exports declaration types.
  // eslint-disable-next-line no-await-in-loop
  const localModules = (options.prepareLocalDependencies || options.collectDeclarationReferences) && lakeFile
    ? mathLocalModuleBuildOrder(verificationProjectRoot, file.relativeProofPath) : undefined;
  const helperModule =
    localModules && (options.expectedDeclarationType || options.expectedDeclarationTypes || options.forbiddenImportModules || options.dependencyCandidates || options.collectDeclarationReferences)
      ? localModules!.at(-1)!.module
      : undefined;
  if (helperModule && !/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/u.test(helperModule))
    throw new Error('Helper proof path cannot be represented as a Lake module target.');
  if ((options.dependencyCandidates || options.forbiddenImportModules) && !helperModule)
    throw new Error('Helper dependency validation requires a Lake module.');
  const declarationQuery = await prepareLeanDeclarationQuery(
    verificationProjectRoot,
    file,
    verifiableItems,
    helperModule || options.expectedDeclarationType || options.expectedDeclarationTypes || options.collectDeclarationReferences
      ? {
          moduleName: helperModule,
          expectedDeclarationType: options.expectedDeclarationType,
          expectedDeclarationTypes: options.expectedDeclarationTypes,
          forbiddenImportModules: options.forbiddenImportModules,
          dependencyCandidates: options.dependencyCandidates,
          referenceModules: options.collectDeclarationReferences
            ? localModules ?? [{ module: '', file: file.relativeProofPath }] : undefined,
        }
      : undefined
  );
  const verificationPath = declarationQuery?.relativePath || file.relativeProofPath;
  let processResult: ProcessResult;
  const requestedTimeoutMs = clampTimeout(request.timeoutMs);
  try {
    processResult = await withLeanProcessSlot(async () => {
      const availableMs = batchDeadlineAt - Date.now();
      if (availableMs < MIN_TIMEOUT_MS) throw new FormalVerificationBatchDeadlineError();
      const modulesToBuild = helperModule ? localModules : localModules?.slice(0, -1);
      // Keep dependency compilation and declaration queries under one sandbox
      // invocation, so the shared compiler lock covers the entire check.
      let args = lakeFile ? ['env', 'lean', '-j', '1', verificationPath] : ['-j', '1', verificationPath];
      if (modulesToBuild?.length) {
        const quote = (value: string): string => `'${value.replaceAll("'", "'\\''")}'`;
        const commands = modulesToBuild.map(module => {
          const output = `.lake/build/lib/lean/${path.posix.relative(module.sourceRoot, module.file).replace(/\.lean$/u, '.olean')}`;
          return `mkdir -p ${quote(path.posix.dirname(output))}\nlean -j1 -R ${quote(module.sourceRoot)} -o ${quote(output)} ${quote(module.file)} 1>&2`;
        }).join('\n');
        args = ['env', '/bin/sh', '-ceu', `${commands}\nexec lean -j1 ${quote(verificationPath)}`];
      }
      return runLeanSandboxed({
        checkoutRoot: checkoutRoot,
        projectRelative: relativeProjectRoot,
        command: verifierCommand,
        args,
        env: runtimeEnvironment,
        sandboxCapability: context.sandboxCapability,
        signal: options.signal,
        timeoutMs: Math.min(requestedTimeoutMs, availableMs),
        outputLimit: MATH_PROCESS_OUTPUT_LIMIT * Math.min(64, verifiableItems.length),
        lakePackagesPath,
      });
    }, options.signal);
  } catch (error) {
    if (error instanceof FormalVerificationBatchDeadlineError) {
      emit('diagnostic.emitted', {
        source: 'process',
        severity: 'error',
        message: error.message,
        proofPath: file.relativeProofPath,
      });
      publishResults(file, 'blocked', 'lean-kernel', error.message);
      return;
    }
    if (!options.signal?.aborted) throw error;
    publishResults(file, 'blocked', 'lean-kernel', 'Formal verification was aborted.');
    return;
  } finally {
    if (declarationQuery) fs.rmSync(declarationQuery.absolutePath, { force: true });
  }
  const stdoutPreview = preview(processResult.stdout);
  const stderrPreview = preview(processResult.stderr);
  if (stdoutPreview) {
    emit('diagnostic.emitted', {
      source: 'stdout',
      severity: processResult.exitCode === 0 ? 'info' : 'warning',
      message: stdoutPreview,
      proofPath: file.relativeProofPath,
    });
  }
  if (stderrPreview) {
    emit('diagnostic.emitted', {
      source: 'stderr',
      severity: processResult.exitCode === 0 ? 'warning' : 'error',
      message: stderrPreview,
      proofPath: file.relativeProofPath,
    });
  }

  const declarationExport =
    processResult.exitCode === 0 && declarationQuery
      ? declarationQuery.parse(processResult.stdout)
      : undefined;
  if (declarationExport?.hashes) file.declarationHashes = declarationExport.hashes;
  if (declarationExport?.types) file.elaboratedDeclarationTypes = declarationExport.types;
  if (declarationExport?.axioms) file.axiomDependencies = declarationExport.axioms;
  if (declarationExport?.usedDependencies)
    file.usedDeclarationDependencies = declarationExport.usedDependencies;
  if (declarationExport?.references) file.declarationReferences = declarationExport.references;

  const axiomDependenciesFor = (item: PreparedItem): string[] => {
    if (!item.theoremName) return file.inspection.axioms;
    return (
      file.axiomDependencies.get(item.theoremName) ||
      file.axiomDependencies.get(item.theoremName.split('.').at(-1) || item.theoremName) ||
      file.inspection.axioms
    );
  };
  const unsupportedAxiomItems: PreparedItem[] = [];
  const axiomSafeItems: PreparedItem[] = [];
  const unsupportedAxioms = new Set<string>();
  for (const item of verifiableItems) {
    let hasUnsupportedAxiom = false;
    for (const axiom of axiomDependenciesFor(item)) {
      if (isMathFoundationalLeanAxiom(axiom)) continue;
      hasUnsupportedAxiom = true;
      unsupportedAxioms.add(axiom);
    }
    if (hasUnsupportedAxiom) {
      unsupportedAxiomItems.push(item);
    } else {
      axiomSafeItems.push(item);
    }
  }
  if (unsupportedAxiomItems.length > 0 && !declarationExport?.error) {
    const error = `Theorem depends on non-foundational Lean axioms: ${[...unsupportedAxioms].join(', ')}.`;
    reject(error, unsupportedAxiomItems);
  }
  if (axiomSafeItems.length === 0) return;

  const { status, verifier, error } = classifyLeanCheck(processResult, {
    command, batchDeadlineAt, projectRoot: verificationProjectRoot,
    packagesPath: lakePackagesPath, exportError: declarationExport?.error,
  });
  context.toolUnavailable ||= status === 'unavailable';
  emit('check.kernel_checked', {
    proofPath: file.relativeProofPath,
    status,
    exitCode: processResult.exitCode,
    signal: processResult.signal,
    timedOut: processResult.timedOut,
    aborted: processResult.aborted,
    durationMs: processResult.durationMs,
  });
  if (error) {
    emit('diagnostic.emitted', {
      source: 'process',
      severity: 'error',
      message: error,
      proofPath: file.relativeProofPath,
    });
  }
  publishResults(file, status, verifier, error, { stdoutPreview, stderrPreview }, axiomSafeItems);
}

async function checkManyFormalVerificationsUnbounded(
  request: MathematicsVerifierBatchRequest,
  options: MathematicsVerifierExecutionOptions & { env: NodeJS.ProcessEnv },
  cachePreparation?: FormalVerificationCachePreparation
): Promise<MathematicsVerifierBatchResult> {
  if (!Array.isArray(request.items) || request.items.length === 0) {
    throw new Error('formal_verifier requires at least one verification item.');
  }
  if (request.items.length > 64) throw new Error('formal_verifier accepts at most 64 verification items per batch.');

  const runtimeEnvironment = { ...options.env };

  // These roots come from the host integration port, not model-controlled
  // environment overrides. Resolve the frozen projection first so it cannot
  // erase the cache selected for a detached source checkout.
  if (options.trustedLakePackagesRoots?.length) {
    runtimeEnvironment.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS = [
      ...options.trustedLakePackagesRoots,
      runtimeEnvironment.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS,
    ]
      .filter(Boolean)
      .join(path.delimiter);
  }

  const seenIds = new Set<string>();
  const duplicateIds: string[] = [];
  for (const item of request.items) {
    const id = item.id?.trim();
    if (!id) continue;
    if (seenIds.has(id)) duplicateIds.push(id);
    else seenIds.add(id);
  }
  if (duplicateIds.length > 0) throw new Error(`Verification item ids must be unique: ${duplicateIds.join(', ')}`);

  const startedAt = Date.now();
  const batchDeadlineAt = startedAt + clampBatchTimeout(request.batchTimeoutMs);
  const sessionId = crypto.randomUUID();
  const events: MathematicsVerificationEvent[] = [];
  const emit = <Kind extends MathematicsVerificationEventKind>(
    kind: Kind,
    payload: MathematicsVerificationEventPayloadMap[Kind]
  ): void => {
    const event = {
      schema: EVENT_SCHEMA,
      eventId: crypto.randomUUID(),
      sessionId,
      timestamp: Date.now(),
      kind,
      payload,
    } as MathematicsVerificationEvent;
    events.push(event);
    try {
      options.onEvent?.(event);
    } catch {
      // An observer must not change the verification result.
    }
  };

  const lexicalProjectRoot = path.resolve(request.projectRoot);
  for (const item of request.items) {
    const lexicalProofPath = path.resolve(lexicalProjectRoot, item.proofPath);
    if (
      !withinProject(lexicalProjectRoot, lexicalProofPath) ||
      path.relative(lexicalProjectRoot, lexicalProofPath).startsWith('..')
    ) {
      throw new Error('proofPath must remain inside the bound project root.');
    }
  }
  const projectRoot = canonicalProjectRoot(request.projectRoot);
  if (options.constructionSourcesOnly)
    assertMathConstructionSources(
      projectRoot,
      request.items.map((item) => item.proofPath)
    );
  const preparedItems = cachePreparation?.preparedItems ?? normalizeItems(projectRoot, request.items);
  const preparedFiles = await prepareFiles(projectRoot, preparedItems, cachePreparation);
  emit('session.opened', {
    projectRoot,
    itemCount: preparedItems.length,
    uniqueFileCount: preparedFiles.length,
  });
  preparedFiles.forEach((file) => {
    emit('file.opened', {
      proofPath: file.relativeProofPath,
      proofHash: file.proofHash,
      bytes: Buffer.byteLength(file.source),
      checkCount: file.items.length,
    });
  });

  const lakeFile = ['lakefile.toml', 'lakefile.lean'].find((file) => fs.existsSync(path.join(projectRoot, file)));
  const command: 'lake' | 'lean' = lakeFile ? 'lake' : 'lean';
  const verifierCommand = options.verifierCommandPath || command;
  const toolchain: MathematicsVerificationToolchain = {
    lean: command,
    ...(lakeFile ? { lake: lakeFile } : {}),
  };
  emit('toolchain.resolved', {
    command,
    executable: verifierCommand,
    ...(lakeFile ? { lakeFile } : {}),
  });

  const currentHead = await readGitHead(projectRoot, options);
  const requestedCommit = request.targetCommit?.trim();
  const resolvedRequestedCommit = cachePreparation?.resolvedTargetCommit
    ? cachePreparation.resolvedTargetCommit
    : requestedCommit
      ? await resolveGitCommit(projectRoot, requestedCommit, options)
      : undefined;
  const targetCommit = resolvedRequestedCommit || currentHead || 'WORKTREE';
  const results: MathematicsVerifierResult[] = [];

  const publishResults = (
    file: PreparedFile,
    status: MathematicsVerifierStatus,
    verifier: MathematicsVerifierResult['verifier'],
    error?: string,
    output?: { stdoutPreview?: string; stderrPreview?: string },
    selectedItems: PreparedItem[] = file.items
  ): void => {
    const checkedAt = Date.now();
    for (const item of selectedItems) {
      const theoremName = item.theoremName;
      const localTheoremName = theoremName?.split('.').at(-1) || theoremName;
      const base: ResultBase = {
        targetCommit,
        statementHash: item.statementHash,
        ...(item.leanStatementHash ? { leanStatementHash: item.leanStatementHash } : {}),
        claim: item.claim || 'statement',
        proofHash: file.proofHash,
        proofPath: file.relativeProofPath,
        theoremName,
        ...(theoremName
          ? {
              theoremDeclarationHash:
                file.declarationHashes.get(theoremName) || file.declarationHashes.get(localTheoremName),
              elaboratedDeclarationType:
                file.elaboratedDeclarationTypes?.get(theoremName) ||
                file.elaboratedDeclarationTypes?.get(localTheoremName),
              sourceDeclarationHash:
                file.sourceDeclarationHashes.get(theoremName) || file.sourceDeclarationHashes.get(localTheoremName),
              ...(file.usedDeclarationDependencies?.has(theoremName)
                ? { usedDeclarationDependencies: file.usedDeclarationDependencies.get(theoremName) }
                : {}),
              ...(file.declarationReferences?.has(theoremName)
                ? { declarationReferences: file.declarationReferences.get(theoremName) } : {}),
            }
          : {}),
        statementBinding: 'caller-bound-to-committed-declaration',
        toolchain,
        goalsRemaining: status === 'kernel_verified' ? 0 : 1,
        sorryCount: file.inspection.sorryCount,
        admitCount: file.inspection.admitCount,
        axioms:
          (theoremName && file.axiomDependencies.get(theoremName)) ||
          (theoremName && file.axiomDependencies.get(localTheoremName)) ||
          file.inspection.axioms,
        checkedAt,
        checkId: item.checkId,
        sessionId,
      };
      const receiptId = receiptIdFor(base);
      const result: MathematicsVerifierResult = {
        ...base,
        status,
        verifier,
        receiptId,
        ...(output?.stdoutPreview ? { stdoutPreview: output.stdoutPreview } : {}),
        ...(output?.stderrPreview ? { stderrPreview: output.stderrPreview } : {}),
        ...(error ? { error } : {}),
      };
      results.push(result);
      emit('receipt.published', {
        receiptId,
        checkId: item.checkId,
        proofPath: file.relativeProofPath,
        theoremName,
        status,
      });
    }
  };

  const publishAll = (
    status: MathematicsVerifierStatus,
    verifier: MathematicsVerifierResult['verifier'],
    error: string,
    diagnosticSource: MathematicsVerificationEventPayloadMap['diagnostic.emitted']['source']
  ): void => {
    emit('diagnostic.emitted', { source: diagnosticSource, severity: 'error', message: error });
    preparedFiles.forEach((file) => publishResults(file, status, verifier, error));
  };

  if (options.signal?.aborted) {
    publishAll('blocked', 'lean-kernel', 'Formal verification was aborted.', 'process');
  } else if (!currentHead) {
    publishAll('blocked', 'lean-kernel', 'Formal verification requires a Git repository with a committed HEAD.', 'git');
  } else if (requestedCommit && !resolvedRequestedCommit) {
    publishAll(
      'blocked',
      'lean-kernel',
      `The requested target commit could not be resolved: ${requestedCommit}`,
      'git'
    );
  } else if (resolvedRequestedCommit && resolvedRequestedCommit !== currentHead) {
    publishAll(
      'blocked',
      'lean-kernel',
      `The verifier reads the current checkout, but targetCommit ${resolvedRequestedCommit} does not match HEAD ${currentHead}.`,
      'git'
    );
  } else {
    const gitStatus = await readGitStatus(projectRoot, options);
    if (options.signal?.aborted) {
      publishAll('blocked', 'lean-kernel', 'Formal verification was aborted.', 'process');
    } else if (!gitStatus.ok) {
      publishAll('blocked', 'lean-kernel', 'The project Git status could not be inspected.', 'git');
    } else if (gitStatus.output) {
      publishAll(
        'blocked',
        'lean-kernel',
        `Formal verification requires a clean committed checkout. Dirty entries: ${gitStatus.output}`,
        'git'
      );
    } else {
      const repoRootResult = await runGit(projectRoot, ['rev-parse', '--show-toplevel'], options);
      const repoRoot = repoRootResult.exitCode === 0 ? repoRootResult.stdout.trim() : '';
      const relativeProjectRoot = repoRoot ? path.relative(path.resolve(repoRoot), projectRoot) : '..';
      const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-lean-'));
      const checkoutRoot = path.join(temporaryRoot, 'checkout');
      const added =
        repoRoot && !relativeProjectRoot.startsWith('..') && !path.isAbsolute(relativeProjectRoot)
          ? await runGit(repoRoot, ['worktree', 'add', '--detach', checkoutRoot, targetCommit], options)
          : undefined;
      if (!added || added.exitCode !== 0) {
        publishAll(
          'blocked',
          'lean-kernel',
          'Formal verification could not create an immutable checkout at targetCommit.',
          'git'
        );
      } else {
        const cleanupOptions: MathematicsVerifierExecutionOptions = { ...options, signal: undefined };
        try {
          const verificationProjectRoot = path.join(checkoutRoot, relativeProjectRoot);
          if (options.prepareLocalDependencies) {
            const buildPath = path.join(verificationProjectRoot, '.lake', 'build');
            const lakePath = path.dirname(buildPath);
            if (fs.existsSync(lakePath)) assertNoSymlinkTraversal(checkoutRoot, lakePath, 'Helper Lake directory');
            if (fs.existsSync(buildPath)) {
              assertNoSymlinkTraversal(checkoutRoot, buildPath, 'Helper build output');
              fs.rmSync(buildPath, { recursive: true, force: true });
            }
          }
          const lakePackagesPath = seedDetachedLakeCache(projectRoot, verificationProjectRoot, runtimeEnvironment,
            options.prepareLocalDependencies);
          if (options.constructionSourcesOnly) pruneMathConstructionCheckout(checkoutRoot, verificationProjectRoot);
          if (options.constructionSourcesOnly)
            assertMathConstructionSources(
              verificationProjectRoot,
              preparedFiles.map((file) => file.relativeProofPath)
            );
          const blobIdsByPath = await readGitBlobIds(
            projectRoot,
            currentHead,
            preparedFiles.map((file) => file.relativeProofPath),
            options
          );
          let requiresPackages = false;
          if (lakeFile && !lakePackagesPath) {
            try {
              const manifest = JSON.parse(fs.readFileSync(path.join(verificationProjectRoot, 'lake-manifest.json'), 'utf8'));
              requiresPackages = Array.isArray(manifest.packages) && manifest.packages.length > 0;
            } catch { /* Lake reports malformed configuration; do not infer a proof failure from startup errors. */ }
          }
          const context: FormalFileVerificationContext = { request, options, command, verifierCommand, lakeFile,
            requiresPackages, toolUnavailable: false, batchDeadlineAt, verificationProjectRoot, relativeProjectRoot,
            checkoutRoot, runtimeEnvironment, lakePackagesPath, blobIdsByPath, emit, publishResults,
            sandboxCapability: inspectMathematicsSandboxBackends(runtimeEnvironment) };
          // The outer semaphore limits concurrent batches.  Within one batch,
          // use the configured host capacity for independent proof files so
          // parallel FORMALIZE nodes do not become a serial queue.
          const workerCount = Math.min(configuredVerificationConcurrency(), preparedFiles.length);
          let nextFileIndex = 0;
          const runWorker = async (): Promise<void> => {
            for (;;) {
              const index = nextFileIndex++;
              if (index >= preparedFiles.length) return;
              // eslint-disable-next-line no-await-in-loop
              await verifyFormalFile(preparedFiles[index], context);
            }
          };
          await Promise.all(Array.from({ length: workerCount }, () => runWorker()));
        } finally {
          const cleanupFailures = await cleanupVerifierWorktree(repoRoot, checkoutRoot, cleanupOptions, true);
          if (cleanupFailures.length > 0) {
            const message = `Formal verification cleanup incomplete: ${cleanupFailures.join('; ')}`;
            emit('diagnostic.emitted', { source: 'git', severity: 'error', message });
            console.warn(`[MathematicsVerifier] ${message}`);
            for (const result of results) {
              if (result.status !== 'kernel_verified') continue;
              result.status = 'blocked';
              result.cleanupError = message;
              result.error = message;
            }
          }
          try {
            fs.rmSync(temporaryRoot, { recursive: true, force: true });
          } catch (error) {
            const message = `Formal verification temporary directory cleanup failed: ${error instanceof Error ? error.message : String(error)}`;
            emit('diagnostic.emitted', { source: 'process', severity: 'error', message });
            console.warn(`[MathematicsVerifier] ${message}`);
            for (const result of results) {
              if (result.status !== 'kernel_verified') continue;
              result.status = 'blocked';
              result.cleanupError = message;
              result.error = message;
            }
          }
        }
      }
      if (!added || added.exitCode !== 0) {
        fs.rmSync(temporaryRoot, { recursive: true, force: true });
      }
    }
  }

  // Parallel file completion must not change the public result order.  Keep
  // event timing as observed, but return receipts in caller-supplied order.
  const resultOrder = new Map(preparedItems.map((item, index) => [item.checkId, index]));
  results.sort(
    (left, right) =>
      (resultOrder.get(left.checkId) ?? Number.MAX_SAFE_INTEGER) -
      (resultOrder.get(right.checkId) ?? Number.MAX_SAFE_INTEGER)
  );
  const status = aggregateStatus(results);
  const checkedAt = Date.now();
  emit('session.closed', { status, resultCount: results.length, durationMs: checkedAt - startedAt });
  return {
    schema: 'deepscientist.mathematics.verification-batch/v1',
    sessionId,
    status,
    targetCommit,
    results,
    events,
    startedAt,
    checkedAt,
    durationMs: checkedAt - startedAt,
  };
}

type CachedFormalVerification = {
  expiresAt: number;
  projectRootHash: string;
  result: MathematicsVerifierBatchResult;
  attestation?: {
    algorithm: 'hmac-sha256';
    keyId: string;
    value: string;
  };
};
const formalVerificationCache = new Map<string, CachedFormalVerification>();
type FormalVerificationInFlight = {
  controller: AbortController;
  promise: Promise<MathematicsVerifierBatchResult>;
  subscribers: number;
  settled: boolean;
};
const formalVerificationInFlight = new Map<string, FormalVerificationInFlight>();

const durableFormalVerificationCacheDirectory = (): string =>
  path.join(process.env.DEEPSCIENTIST_CACHE_DIR || os.tmpdir(), 'mathematics', 'formal-verification-v1');

const durableFormalVerificationCachePath = (cacheKey: string): string =>
  path.join(durableFormalVerificationCacheDirectory(), `${cacheKey}.json`);

const durableCachePayload = (cached: Omit<CachedFormalVerification, 'attestation'>): string =>
  JSON.stringify({ expiresAt: cached.expiresAt, projectRootHash: cached.projectRootHash, result: cached.result });

const attestDurableCache = (
  cached: Omit<CachedFormalVerification, 'attestation'>,
  secret = readMathematicsReceiptSecret()
): CachedFormalVerification['attestation'] | undefined => {
  if (!secret) return undefined;
  return {
    algorithm: 'hmac-sha256',
    keyId: crypto.createHash('sha256').update(secret).digest('hex').slice(0, 16),
    value: crypto.createHmac('sha256', secret).update(durableCachePayload(cached), 'utf8').digest('hex'),
  };
};

const isDurableCacheAttested = (cached: CachedFormalVerification, secret?: string): boolean => {
  const expected = attestDurableCache(cached, secret);
  if (
    !expected ||
    !cached.attestation ||
    cached.attestation.algorithm !== expected.algorithm ||
    cached.attestation.keyId !== expected.keyId
  ) {
    return false;
  }
  const actual = Buffer.from(cached.attestation.value, 'hex');
  const wanted = Buffer.from(expected.value, 'hex');
  return actual.length === wanted.length && crypto.timingSafeEqual(actual, wanted);
};

const readDurableFormalVerificationCache = (cacheKey: string): CachedFormalVerification | undefined => {
  try {
    const parsed = JSON.parse(readMathText(durableFormalVerificationCachePath(cacheKey), 64 * 1024 * 1024)) as
      | CachedFormalVerification
      | undefined;
    if (
      !parsed ||
      !Number.isFinite(parsed.expiresAt) ||
      parsed.expiresAt <= Date.now() ||
      !/^[0-9a-f]{64}$/u.test(parsed.projectRootHash) ||
      !parsed.attestation ||
      parsed.result?.schema !== 'deepscientist.mathematics.verification-batch/v1' ||
      parsed.result.status !== 'kernel_verified' ||
      !Array.isArray(parsed.result.results) ||
      parsed.result.results.some((item) => item.status !== 'kernel_verified')
    ) {
      return undefined;
    }
    if (!isDurableCacheAttested(parsed)) return undefined;
    return parsed;
  } catch {
    return undefined;
  }
};

const writeDurableFormalVerificationCache = (cacheKey: string, cached: CachedFormalVerification): void => {
  const directory = durableFormalVerificationCacheDirectory();
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const target = durableFormalVerificationCachePath(cacheKey);
  const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
  fs.writeFileSync(temporary, `${JSON.stringify(cached)}\n`, { encoding: 'utf8', mode: 0o600 });
  fs.renameSync(temporary, target);
  const cacheEntries: fs.Dirent[] = [];
  for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
    if (entry.isFile() && /^[0-9a-f]{64}\.json$/u.test(entry.name)) cacheEntries.push(entry);
  }
  if (cacheEntries.length <= 256) return;
  const entries = cacheEntries.map((entry) => ({
    name: entry.name,
    mtimeMs: fs.statSync(path.join(directory, entry.name)).mtimeMs,
  }));
  entries.sort((left, right) => right.mtimeMs - left.mtimeMs);
  for (let index = 256; index < entries.length; index += 1) {
    fs.rmSync(path.join(directory, entries[index].name), { force: true });
  }
};

function cloneCachedVerification(
  cached: MathematicsVerifierBatchResult,
  onEvent?: (event: MathematicsVerificationEvent) => void
): MathematicsVerifierBatchResult {
  const sessionId = crypto.randomUUID();
  const checkedAt = Date.now();
  const events: MathematicsVerificationEvent[] = [
    {
      schema: EVENT_SCHEMA,
      eventId: crypto.randomUUID(),
      sessionId,
      timestamp: checkedAt,
      kind: 'diagnostic.emitted',
      payload: { source: 'process', severity: 'info', message: 'Formal verification cache hit.' },
    },
  ];
  const results: MathematicsVerifierResult[] = [];
  for (const item of cached.results) {
    events.push({
      schema: EVENT_SCHEMA,
      eventId: crypto.randomUUID(),
      sessionId,
      timestamp: checkedAt,
      kind: 'receipt.published',
      payload: {
        receiptId: item.receiptId,
        checkId: item.checkId,
        proofPath: item.proofPath,
        ...(item.theoremName ? { theoremName: item.theoremName } : {}),
        status: item.status,
      },
    });
    results.push({ ...item });
  }
  events.push({
    schema: EVENT_SCHEMA,
    eventId: crypto.randomUUID(),
    sessionId,
    timestamp: checkedAt,
    kind: 'session.closed',
    payload: { status: cached.status, resultCount: cached.results.length, durationMs: 0 },
  });
  for (const event of events) {
    try {
      onEvent?.(event);
    } catch {
      // Cache observers have the same non-authoritative semantics as live observers.
    }
  }
  return {
    ...cached,
    sessionId,
    startedAt: checkedAt,
    checkedAt,
    durationMs: 0,
    events,
    // Preserve each immutable receipt exactly; a cache lookup is not a new
    // kernel execution and must not rewrite checkedAt/session identity.
    results,
  };
}

const subscribeToFormalVerification = (
  flight: FormalVerificationInFlight,
  options: MathematicsVerifierExecutionOptions
): Promise<MathematicsVerifierBatchResult> =>
  new Promise((resolve, reject) => {
    if (options.signal?.aborted) {
      reject(abortReason(options.signal));
      return;
    }
    flight.subscribers += 1;
    let finished = false;
    const finish = (): void => {
      if (finished) return;
      finished = true;
      flight.subscribers = Math.max(0, flight.subscribers - 1);
      options.signal?.removeEventListener('abort', onAbort);
    };
    const onAbort = (): void => {
      finish();
      // A single cancelled caller must not cancel another caller's Lean run.
      if (!flight.settled && flight.subscribers === 0) flight.controller.abort(options.signal?.reason);
      reject(abortReason(options.signal!));
    };
    options.signal?.addEventListener('abort', onAbort, { once: true });
    flight.promise.then(
      (result) => {
        if (finished) return;
        finish();
        // Preserve the full live event trace for the first/subsequent
        // subscribers; only the observer callback is caller-local.
        for (const event of result.events) {
          try {
            options.onEvent?.(event);
          } catch {
            // An observer must not change verification semantics.
          }
        }
        resolve({ ...result, results: result.results.map((item) => ({ ...item })), events: [...result.events] });
      },
      (error) => {
        if (finished) return;
        finish();
        reject(error);
      }
    );
  });

async function buildFormalVerificationCacheKey(
  request: MathematicsVerifierBatchRequest,
  options: MathematicsVerifierExecutionOptions
): Promise<FormalVerificationCachePreparation | undefined> {
  let projectRoot: string;
  try {
    projectRoot = canonicalProjectRoot(request.projectRoot);
  } catch {
    return undefined;
  }
  if (options.constructionSourcesOnly)
    assertMathConstructionSources(
      projectRoot,
      request.items.map((item) => item.proofPath)
    );
  const head = await readGitHead(projectRoot, options);
  if (!head) return undefined;
  const resolvedTarget = request.targetCommit
    ? await resolveGitCommit(projectRoot, request.targetCommit, options)
    : head;
  if (!resolvedTarget || resolvedTarget !== head) return undefined;
  const status = await readGitStatus(projectRoot, options);
  if (!status.ok || status.output) return undefined;
  let preparedItems: readonly PreparedItem[];
  let proofSources: ReadonlyMap<string, ProofSourceSnapshot>;
  try {
    preparedItems = normalizeItems(projectRoot, request.items);
    const paths = new Map(preparedItems.map(item => [item.relativeProofPath, item.absoluteProofPath]));
    proofSources = new Map(await Promise.all([...paths].map(async ([relativePath, absolutePath]) => {
      const metadata = await proofFileMetadataAsync(absolutePath);
      const source = await fs.promises.readFile(absolutePath, 'utf8');
      // A snapshot can be reused only when its identity belongs to the bytes read.
      if (!metadata || (await proofFileMetadataAsync(absolutePath)) !== metadata)
        throw new Error('formal_verifier_source_changed');
      return [relativePath, { source, hash: crypto.createHash('sha256').update(source).digest('hex'), metadata }] as const;
    })));
  } catch {
    return undefined;
  }
  const fileInputs = preparedItems.map(item => ({
    path: item.relativeProofPath,
    hash: proofSources.get(item.relativeProofPath)!.hash,
    theoremName: item.theoremName,
    statementHash: item.statementHash,
    leanStatementHash: item.leanStatementHash,
    expectedSourceDeclarationHash: item.expectedSourceDeclarationHash,
    claim: item.claim || 'statement',
    id: item.id,
  }));
  const toolchainFiles = ['lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json']
    .map((name) => {
      try {
        return [
          name,
          crypto
            .createHash('sha256')
            .update(fs.readFileSync(path.join(projectRoot, name)))
            .digest('hex'),
        ];
      } catch {
        return undefined;
      }
    })
    .filter((item): item is [string, string] => Boolean(item));
  const dependencyPaths = [
    ['.lake/packages', fingerprintLakePackages(projectRoot)],
    // Lake build output is generated and is deliberately excluded from the
    // sandbox; it cannot affect the cache key for a clean target commit.
    ['.lake/build', 'generated-output-excluded'],
  ];
  const verifierCommand =
    options.verifierCommandPath ||
    (['lakefile.toml', 'lakefile.lean'].some((name) => fs.existsSync(path.join(projectRoot, name))) ? 'lake' : 'lean');
  const verifierExecutablePath = resolveCommandForFingerprint(verifierCommand, options.env);
  const verifierExecutable = [
    verifierCommand,
    verifierExecutablePath || null,
    verifierExecutablePath ? memoizedFingerprintPath(verifierExecutablePath) : null,
  ];
  // Only values that can change Lean/Lake resolution belong in this identity.
  // Credentials, proxies, temporary directories, and runtime metadata
  // must not turn an otherwise identical proof into a cache miss.
  const cacheEnvironmentKeys = [
    'PATH',
    'ELAN_HOME',
    'LEAN_PATH',
    'LAKE_HOME',
    'LANG',
    'LC_ALL',
    'DEEPSCIENTIST_TEST_LEAN_AXIOMS',
  ];
  const optionEnvironment = options.env;
  const environmentEntries: Array<[string, string]> = [];
  for (const key of cacheEnvironmentKeys) {
    const value =
      optionEnvironment && Object.prototype.hasOwnProperty.call(optionEnvironment, key)
        ? optionEnvironment[key]
        : process.env[key];
    if (value !== undefined) environmentEntries.push([key, value]);
  }
  environmentEntries.sort(([left], [right]) => left.localeCompare(right));
  const environment = Object.fromEntries(environmentEntries);
  const cacheKey = crypto
    .createHash('sha256')
    .update(
      JSON.stringify({
        schema: 'deepscientist.formal-verification-cache.v1',
        projectRootHash: crypto.createHash('sha256').update(projectRoot).digest('hex'),
        targetCommit: resolvedTarget,
        verifierCommandPath: options.verifierCommandPath || null,
        prepareLocalDependencies: options.prepareLocalDependencies ?? false,
        expectedDeclarationType: options.expectedDeclarationType ?? null,
        expectedDeclarationTypes: options.expectedDeclarationTypes ?? null,
        forbiddenImportModules: options.forbiddenImportModules ?? [],
        dependencyCandidates: options.dependencyCandidates ?? null,
        collectDeclarationReferences: options.collectDeclarationReferences ?? false,
        verifierExecutable,
        environment,
        toolchainFiles,
        dependencyPaths,
        trustedLakePackages: (options.trustedLakePackagesRoots ?? []).map((root) => [
          root,
          fingerprintLakePackages(projectRoot, root),
        ]),
        items: fileInputs,
      })
    )
    .digest('hex');
  return {
    cacheKey,
    resolvedTargetCommit: resolvedTarget,
    preparedItems,
    proofSources,
  };
}

export async function checkManyFormalVerifications(
  request: MathematicsVerifierBatchRequest,
  options: MathematicsVerifierExecutionOptions = {}
): Promise<MathematicsVerifierBatchResult> {
  // Resolve the pinned mathematics environment once at the public boundary so
  // cache identity, capability checks, and the actual Lean process agree.
  const runtimeOptions: MathematicsVerifierExecutionOptions & { env: NodeJS.ProcessEnv } = {
    ...options,
    env: resolveMathematicsRuntimeEnvironment(options.env || process.env),
  };
  // A successful receipt is immutable for a clean commit, exact proof bytes,
  // theorem declaration, statement hash, and toolchain. Reusing it avoids
  // repeatedly creating worktrees and starting Lean during proof retries.
  if (runtimeOptions.signal?.aborted) {
    return withVerificationSlot(
      () => checkManyFormalVerificationsUnbounded(request, runtimeOptions),
      runtimeOptions.signal
    );
  }
  // Keep cache-key preparation behind the same semaphore as Lean work so a
  // burst of Git queries and proof reads cannot starve actual verification.
  const cachePreparation = await withVerificationSlot(
    () => buildFormalVerificationCacheKey(request, runtimeOptions),
    runtimeOptions.signal
  );
  const cacheKey = cachePreparation?.cacheKey;
  if (cacheKey) {
    const cached = formalVerificationCache.get(cacheKey) ?? readDurableFormalVerificationCache(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      formalVerificationCache.set(cacheKey, cached);
      return cloneCachedVerification(cached.result, runtimeOptions.onEvent);
    }
    if (cached) formalVerificationCache.delete(cacheKey);
    const inFlight = formalVerificationInFlight.get(cacheKey);
    if (inFlight) return subscribeToFormalVerification(inFlight, runtimeOptions);
    const controller = new AbortController();
    const operation = withVerificationSlot(
      () =>
        checkManyFormalVerificationsUnbounded(
          request,
          {
            ...runtimeOptions,
            signal: controller.signal,
            // Subscribers receive an isolated replay of the completed result.
            // Do not let the first caller's observer become the operation's
            // shared callback.
            onEvent: undefined,
          },
          cachePreparation
        ),
      controller.signal
    )
      .then((result) => {
        if (result.status === 'kernel_verified' && result.results.every((item) => item.status === 'kernel_verified')) {
          const cachedResult = {
            expiresAt: Date.now() + 30 * 60_000,
            projectRootHash: crypto
              .createHash('sha256')
              .update(canonicalProjectRoot(request.projectRoot))
              .digest('hex'),
            result,
          };
          formalVerificationCache.set(cacheKey, cachedResult);
          try {
            const attestation = attestDurableCache(cachedResult);
            if (attestation) writeDurableFormalVerificationCache(cacheKey, { ...cachedResult, attestation });
          } catch {
            // A durable cache write is an optimization; the kernel receipt is
            // still valid and remains available in the in-process cache.
          }
          while (formalVerificationCache.size > 256) {
            const oldest = formalVerificationCache.keys().next().value as string | undefined;
            if (!oldest) break;
            formalVerificationCache.delete(oldest);
          }
        }
        return result;
      })
      .finally(() => {
        const current = formalVerificationInFlight.get(cacheKey);
        if (current?.promise === operation) {
          current.settled = true;
          formalVerificationInFlight.delete(cacheKey);
        }
      });
    const flight: FormalVerificationInFlight = { controller, promise: operation, subscribers: 0, settled: false };
    formalVerificationInFlight.set(cacheKey, flight);
    return subscribeToFormalVerification(flight, runtimeOptions);
  }
  return withVerificationSlot(
    () => checkManyFormalVerificationsUnbounded(request, runtimeOptions),
    runtimeOptions.signal
  );
}

export const canonicalMathOfficialManifestPayload = (
  manifest: Omit<MathOfficialProblemManifest, 'manifestHash'> | MathOfficialProblemManifest
): string =>
  JSON.stringify({
    schema: manifest.schema,
    manifestId: manifest.manifestId,
    problemId: manifest.problemId,
    informalStatement: manifest.informalStatement,
    formalStatement: manifest.formalStatement,
    ...(manifest.formalNegationStatement ? { formalNegationStatement: manifest.formalNegationStatement } : {}),
    assumptions: manifest.assumptions,
    statementHash: manifest.statementHash,
    leanStatementHash: manifest.leanStatementHash,
    ...(manifest.leanNegationHash ? { leanNegationHash: manifest.leanNegationHash } : {}),
    officialVerificationCommand: manifest.officialVerificationCommand,
    repositoryUrl: manifest.repositoryUrl,
    baselineCommit: manifest.baselineCommit,
    benchmarkAdapterId: manifest.benchmarkAdapterId,
    benchmarkAdapterVersion: manifest.benchmarkAdapterVersion,
    trackedFiles: manifest.trackedFiles,
    ...(manifest.targetCommit ? { targetCommit: manifest.targetCommit } : {}),
  });

const relativeOfficialManifestPath = (value: string): string => {
  const normalized = value.trim().replaceAll('\\', '/');
  if (!normalized || normalized.includes('\0') || path.isAbsolute(normalized) || normalized.split('/').includes('..')) {
    throw new Error('Official problem manifest path must be relative to the committed project checkout.');
  }
  return normalized.replace(/^\.\//u, '');
};

const normalizedRepositoryUrl = (value: string): string =>
  value
    .trim()
    .replace(/\/+$/u, '')
    .replace(/\.git$/u, '')
    .toLowerCase();

const validateOfficialManifestSource = async (
  repoRoot: string,
  worktreeRoot: string,
  targetCommit: string,
  manifest: MathOfficialProblemManifest,
  options: MathematicsVerifierExecutionOptions,
  manifestPath?: string
): Promise<void> => {
  const [origin, baseline, ancestry] = await Promise.all([
    runGit(repoRoot, ['config', '--get', 'remote.origin.url'], options),
    resolveGitCommit(repoRoot, manifest.baselineCommit, options),
    runGit(repoRoot, ['merge-base', '--is-ancestor', manifest.baselineCommit, targetCommit], options),
  ]);
  if (
    origin.exitCode !== 0 ||
    normalizedRepositoryUrl(origin.stdout) !== normalizedRepositoryUrl(manifest.repositoryUrl)
  ) {
    throw new Error('Official manifest repositoryUrl does not match the bound repository origin.');
  }
  if (!baseline || baseline.toLowerCase() !== manifest.baselineCommit || ancestry.exitCode !== 0) {
    throw new Error('Official manifest baselineCommit is not an ancestor of the comparator target commit.');
  }
  const externallyPinnedHash = (
    options.env?.DEEPSCIENTIST_MATH_OFFICIAL_MANIFEST_HASH || process.env.DEEPSCIENTIST_MATH_OFFICIAL_MANIFEST_HASH
  )
    ?.trim()
    .toLowerCase();
  let hasExternalAnchor = false;
  if (externallyPinnedHash) {
    if (!/^[0-9a-f]{64}$/u.test(externallyPinnedHash) || externallyPinnedHash !== manifest.manifestHash.toLowerCase()) {
      throw new Error('Official manifest does not match the externally pinned benchmark manifest hash.');
    }
    hasExternalAnchor = true;
  }
  // A repository-provided authority file is intentionally outside the
  // detached target checkout.  When present, it prevents a target commit from
  // redefining the benchmark command or statement while retaining the normal
  // self-contained fixture path for legacy repositories.
  const authorityPath = path.join(repoRoot, '.deepscientist', 'math', 'official-manifest.authority.json');
  if (fs.existsSync(authorityPath)) {
    let authority: Record<string, unknown>;
    try {
      authority = JSON.parse(fs.readFileSync(authorityPath, 'utf8')) as Record<string, unknown>;
    } catch (error) {
      throw new Error(
        `Official manifest authority file is invalid: ${error instanceof Error ? error.message : String(error)}`,
        { cause: error }
      );
    }
    const authorityHash = typeof authority.manifestHash === 'string' ? authority.manifestHash.trim().toLowerCase() : '';
    if (!/^[0-9a-f]{64}$/u.test(authorityHash) || authorityHash !== manifest.manifestHash.toLowerCase()) {
      throw new Error('Official manifest does not match the repository authority anchor.');
    }
    for (const [field, actual] of [
      ['manifestId', manifest.manifestId],
      ['problemId', manifest.problemId],
      ['statementHash', manifest.statementHash],
      ['leanStatementHash', manifest.leanStatementHash],
      ['officialVerificationCommand', manifest.officialVerificationCommand],
      ['benchmarkAdapterId', manifest.benchmarkAdapterId],
      ['benchmarkAdapterVersion', manifest.benchmarkAdapterVersion],
    ] as const) {
      if (authority[field] !== undefined && String(authority[field]).trim() !== actual) {
        throw new Error(`Official manifest ${field} does not match the repository authority anchor.`);
      }
    }
    if (
      authority.leanNegationHash !== undefined &&
      String(authority.leanNegationHash).trim() !== manifest.leanNegationHash
    ) {
      throw new Error('Official manifest leanNegationHash does not match the repository authority anchor.');
    }
    if (
      typeof authority.repositoryUrl === 'string' &&
      normalizedRepositoryUrl(authority.repositoryUrl) !== normalizedRepositoryUrl(manifest.repositoryUrl)
    ) {
      throw new Error('Official manifest repositoryUrl does not match the repository authority anchor.');
    }
    if (
      typeof authority.baselineCommit === 'string' &&
      authority.baselineCommit.trim().toLowerCase() !== manifest.baselineCommit
    ) {
      throw new Error('Official manifest baselineCommit does not match the repository authority anchor.');
    }
    if (typeof authority.repositoryUrl !== 'string' || typeof authority.baselineCommit !== 'string') {
      throw new Error('Official manifest authority must include repositoryUrl and baselineCommit.');
    }
    hasExternalAnchor = true;
  }
  if (manifestPath) {
    const baselineManifest = await runGit(repoRoot, ['show', `${manifest.baselineCommit}:${manifestPath}`], options);
    if (baselineManifest.exitCode === 0 && baselineManifest.stdout.trim()) {
      if (manifest.baselineCommit === targetCommit) {
        throw new Error('The official manifest baseline anchor must be a commit distinct from the target commit.');
      }
      try {
        const parsedBaseline = normalizeMathOfficialProblemManifest(JSON.parse(baselineManifest.stdout));
        if (parsedBaseline.manifestHash.toLowerCase() !== manifest.manifestHash.toLowerCase()) {
          throw new Error('Official manifest differs from the immutable baseline manifest anchor.');
        }
      } catch (error) {
        if (error instanceof Error && error.message.includes('differs from the immutable')) throw error;
        throw new Error('The baseline official manifest anchor is malformed.', { cause: error });
      }
      hasExternalAnchor = true;
    }
  }
  if (!hasExternalAnchor) {
    throw new Error(
      'Official comparison requires an external manifest anchor: a pinned hash, a complete authority file, or an immutable baseline manifest.'
    );
  }
  const verifyTrackedFile = async (file: MathOfficialProblemManifest['trackedFiles'][number]): Promise<void> => {
    const absolute = assertNoSymlinkTraversal(
      worktreeRoot,
      path.join(worktreeRoot, file.path),
      `official tracked file ${file.path}`
    );
    let stat: fs.Stats;
    try {
      stat = await fs.promises.stat(absolute);
    } catch (error) {
      throw new Error(`Official tracked file is missing, oversized, or not regular: ${file.path}`, { cause: error });
    }
    if (!stat.isFile() || stat.size > MAX_PROOF_BYTES) {
      throw new Error(`Official tracked file is missing, oversized, or not regular: ${file.path}`);
    }
    const contents = await fs.promises.readFile(absolute);
    const actual = crypto.createHash('sha256').update(contents).digest('hex');
    if (actual !== file.sha256) {
      throw new Error(`Official tracked file hash does not match the manifest: ${file.path}`);
    }
  };
  let nextTrackedFile = 0;
  const trackedFileWorker = async (): Promise<void> => {
    for (;;) {
      const index = nextTrackedFile++;
      if (index >= manifest.trackedFiles.length) return;
      // eslint-disable-next-line no-await-in-loop
      await verifyTrackedFile(manifest.trackedFiles[index]);
    }
  };
  const workerCount = Math.min(configuredVerificationConcurrency(), manifest.trackedFiles.length);
  await Promise.all(Array.from({ length: workerCount }, () => trackedFileWorker()));
};

const readAndValidateOfficialManifest = (
  manifestPath: string,
  expected: Pick<
    MathematicsOfficialComparatorRequest,
    'targetCommit' | 'command' | 'problemId' | 'statementHash' | 'expectedContract'
  >
): MathOfficialProblemManifest => {
  let parsed: unknown;
  try {
    const stat = fs.statSync(manifestPath);
    if (!stat.isFile() || stat.size > MAX_OFFICIAL_MANIFEST_BYTES) {
      throw new Error(`official manifest must be a regular file no larger than ${MAX_OFFICIAL_MANIFEST_BYTES} bytes.`);
    }
    parsed = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
  } catch (error) {
    throw new Error(
      `Official problem manifest could not be read: ${error instanceof Error ? error.message : String(error)}`,
      { cause: error }
    );
  }
  const manifest = normalizeMathOfficialProblemManifest(parsed as MathOfficialProblemManifest);
  const expectedHash = crypto
    .createHash('sha256')
    .update(canonicalMathOfficialManifestPayload(manifest), 'utf8')
    .digest('hex');
  if (manifest.manifestHash.toLowerCase() !== expectedHash) {
    throw new Error('Official problem manifest hash does not match its canonical contents.');
  }
  if (manifest.targetCommit && manifest.targetCommit.toLowerCase() !== expected.targetCommit.toLowerCase()) {
    throw new Error('Official problem manifest targetCommit does not match the comparator target commit.');
  }
  if (manifest.officialVerificationCommand.trim() !== expected.command.trim()) {
    throw new Error('Official comparator command does not match the command frozen in the official problem manifest.');
  }
  if (expected.problemId && manifest.problemId !== expected.problemId.trim()) {
    throw new Error('Official problem manifest problemId does not match the requested problem.');
  }
  if (expected.statementHash && manifest.statementHash !== expected.statementHash.trim()) {
    throw new Error('Official problem manifest statementHash does not match the stored Lean receipt.');
  }
  if (expected.expectedContract) {
    assertMathProblemContractMatchesOfficialManifest(expected.expectedContract, manifest);
  }
  return manifest;
};

async function runOfficialComparatorUnbounded(
  request: MathematicsOfficialComparatorRequest,
  options: MathematicsVerifierExecutionOptions & { env: NodeJS.ProcessEnv }
): Promise<MathematicsOfficialComparatorResult> {
  const runtimeEnvironment = { ...options.env };
  const projectRoot = canonicalProjectRoot(request.projectRoot);
  const command = request.command.trim();
  if (!command || command.includes('\0') || command.length > 8_192) {
    throw new Error('Official comparator command must be a non-empty command of at most 8192 characters.');
  }
  const parsedCommand = parseOfficialCommand(command);
  const requestedCommit = request.targetCommit.trim().toLowerCase();
  if (!/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(requestedCommit)) {
    throw new Error('Official comparator targetCommit must be a full Git object id.');
  }
  const [repoRootResult, resolvedCommit] = await Promise.all([
    runGit(projectRoot, ['rev-parse', '--show-toplevel'], options),
    resolveGitCommit(projectRoot, requestedCommit, options),
  ]);
  const repoRoot = repoRootResult.exitCode === 0 ? repoRootResult.stdout.trim() : '';
  if (!repoRoot || !resolvedCommit || resolvedCommit.toLowerCase() !== requestedCommit) {
    throw new Error('Official comparator could not resolve the exact target commit in the bound repository.');
  }

  const relativeProjectRoot = path.relative(path.resolve(repoRoot), projectRoot);
  if (relativeProjectRoot.startsWith('..') || path.isAbsolute(relativeProjectRoot)) {
    throw new Error('Official comparator projectRoot must remain inside its Git repository.');
  }
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'deepscientist-official-'));
  const worktreeRoot = path.join(temporaryRoot, 'checkout');
  const executionRoot = path.join(temporaryRoot, 'execution');
  const cleanupOptions: MathematicsVerifierExecutionOptions = { ...options, signal: undefined };
  let processResult: ProcessResult | undefined;
  let validatedManifest: MathOfficialProblemManifest | undefined;
  let cleanupFailures: string[] = [];
  let worktreeCreated = false;
  try {
    const added = await runGit(repoRoot, ['worktree', 'add', '--detach', worktreeRoot, requestedCommit], options);
    if (added.exitCode !== 0) {
      throw new Error(
        `Official comparator could not create its detached worktree: ${preview(added.stderr) || 'git failed'}`
      );
    }
    worktreeCreated = true;
    if (request.officialManifestPath) {
      // Manifest paths are repository-relative, while the comparator command
      // itself runs from the requested project subdirectory.
      const manifestPath = assertNoSymlinkTraversal(
        worktreeRoot,
        path.join(worktreeRoot, relativeOfficialManifestPath(request.officialManifestPath)),
        'official manifest path'
      );
      const manifest = readAndValidateOfficialManifest(manifestPath, {
        targetCommit: requestedCommit,
        command,
        problemId: request.problemId,
        statementHash: request.statementHash,
        expectedContract: request.expectedContract,
      });
      validatedManifest = manifest;
      if (request.officialManifest) {
        const suppliedManifest = normalizeMathOfficialProblemManifest(request.officialManifest);
        if (
          suppliedManifest.manifestHash !== manifest.manifestHash ||
          canonicalMathOfficialManifestPayload(suppliedManifest) !== canonicalMathOfficialManifestPayload(manifest)
        ) {
          throw new Error('Caller-supplied official problem manifest differs from the committed manifest.');
        }
      }
    } else if (request.officialManifest) {
      // Direct callers may provide an already-loaded manifest, but still get
      // canonical hash and command/identity checks.  The MCP boundary always
      // supplies officialManifestPath so the bytes come from targetCommit.
      const manifest = normalizeMathOfficialProblemManifest(request.officialManifest);
      validatedManifest = manifest;
      const expectedHash = crypto
        .createHash('sha256')
        .update(canonicalMathOfficialManifestPayload(manifest), 'utf8')
        .digest('hex');
      if (manifest.manifestHash.toLowerCase() !== expectedHash) {
        throw new Error('Official problem manifest hash does not match its canonical contents.');
      }
      if (manifest.officialVerificationCommand.trim() !== command) {
        throw new Error('Official comparator command does not match the supplied official problem manifest.');
      }
      if (manifest.targetCommit && manifest.targetCommit.toLowerCase() !== requestedCommit) {
        throw new Error('Official problem manifest targetCommit does not match the comparator target commit.');
      }
      if (request.problemId && manifest.problemId !== request.problemId.trim()) {
        throw new Error('Official problem manifest problemId does not match the requested problem.');
      }
      if (request.statementHash && manifest.statementHash !== request.statementHash.trim()) {
        throw new Error('Official problem manifest statementHash does not match the stored Lean receipt.');
      }
      if (request.expectedContract) {
        assertMathProblemContractMatchesOfficialManifest(request.expectedContract, manifest);
      }
    }
    if (!validatedManifest) {
      throw new Error('Official comparator requires a committed externally bound problem manifest.');
    }
    await validateOfficialManifestSource(
      repoRoot,
      worktreeRoot,
      requestedCommit,
      validatedManifest,
      { ...options, env: runtimeEnvironment },
      request.officialManifestPath ? relativeOfficialManifestPath(request.officialManifestPath) : undefined
    );
    // Validate every immutable identity before checking host capabilities. A
    // malformed manifest or authority anchor must remain diagnosable even on
    // a host where the secure execution backend is unavailable; no command is
    // run until both checks pass.
    if (resolveSandboxBackends(runtimeEnvironment).length === 0) {
      throw new Error('Secure official comparator execution requires a supported Linux sandbox backend.');
    }
    // Execute a disposable copy so an official command can write build
    // artifacts without mutating the detached Git worktree being validated.
    // Symlinks remain symlinks and are still confined by the chroot below.
    fs.cpSync(worktreeRoot, executionRoot, { recursive: true, dereference: false });
    const executionGitMetadataPath = path.join(executionRoot, '.git');
    if (fs.existsSync(executionGitMetadataPath)) fs.rmSync(executionGitMetadataPath, { recursive: true, force: true });
    // The official comparator must never execute a build or package cache from
    // the caller's current workspace.  It may create fresh outputs below its
    // disposable checkout, but all pre-existing Lake caches are removed.
    const executionCommandRoot = path.join(executionRoot, relativeProjectRoot);
    for (const relativePath of ['.lake/build', '.lake/packages']) {
      const staleCache = path.join(executionCommandRoot, relativePath);
      if (fs.existsSync(staleCache)) fs.rmSync(staleCache, { recursive: true, force: true });
    }
    const lakePackagesPath = seedDetachedLakeCache(projectRoot, executionCommandRoot, runtimeEnvironment,
      options.prepareLocalDependencies);
    processResult = await runLeanSandboxed({
      checkoutRoot: executionRoot,
      projectRelative: relativeProjectRoot.replaceAll(path.sep, '/'),
      command: parsedCommand.executable,
      args: parsedCommand.argv,
      timeoutMs: clampOfficialTimeout(request.timeoutMs),
      signal: options.signal,
      env: runtimeEnvironment,
      ...(lakePackagesPath ? { lakePackagesPath } : {}),
    });
  } finally {
    cleanupFailures = [
      ...cleanupFailures,
      ...(await cleanupVerifierWorktree(repoRoot, worktreeRoot, cleanupOptions, worktreeCreated)),
    ];
    if (cleanupFailures.length > 0) {
      console.warn(`[MathematicsVerifier] Official comparator cleanup incomplete: ${cleanupFailures.join('; ')}`);
    }
    try {
      fs.rmSync(temporaryRoot, { recursive: true, force: true });
    } catch (error) {
      cleanupFailures.push(
        `temporary directory cleanup failed: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  if (!processResult) throw new Error('Official comparator completed without an execution result.');

  const unavailable = isUnavailableProcess(processResult);
  const status =
    processResult.aborted || processResult.timedOut
      ? 'blocked'
      : unavailable
        ? 'unavailable'
        : processResult.exitCode === 0
          ? 'official_verified'
          : 'failed';
  const cleanupError = cleanupFailures.length > 0 ? cleanupFailures.join('; ') : undefined;
  // A comparator that passed but left its disposable checkout behind is not a
  // trustworthy official receipt.  Surface the cleanup failure as a blocked
  // result so callers cannot promote it through the official gate.
  const finalStatus = cleanupError && status === 'official_verified' ? 'blocked' : status;
  const error =
    finalStatus === 'official_verified'
      ? undefined
      : cleanupError && status === 'official_verified'
        ? `Official comparator cleanup failed: ${cleanupError}`
        : processResult.aborted
          ? 'Official comparator was aborted.'
          : processResult.timedOut
            ? 'Official comparator timed out.'
            : processResult.errorMessage
              ? `Official comparator could not be executed: ${processResult.errorMessage}`
              : `Official comparator exited with status ${processResult.exitCode ?? 'unknown'}.`;
  const stdoutPreview = preview(processResult.stdout);
  const stderrPreview = preview(processResult.stderr);
  return Object.freeze({
    status: finalStatus,
    targetCommit: requestedCommit,
    command,
    exitCode: processResult.exitCode,
    signal: processResult.signal,
    timedOut: processResult.timedOut,
    aborted: processResult.aborted,
    stdoutSha256: processResult.stdoutSha256,
    stderrSha256: processResult.stderrSha256,
    ...(stdoutPreview ? { stdoutPreview } : {}),
    ...(stderrPreview ? { stderrPreview } : {}),
    durationMs: processResult.durationMs,
    checkedAt: Date.now(),
    ...(validatedManifest
      ? {
          officialManifestId: validatedManifest.manifestId,
          officialManifestHash: validatedManifest.manifestHash,
          officialManifestProblemId: validatedManifest.problemId,
          officialManifestLeanStatementHash: validatedManifest.leanStatementHash,
          ...(validatedManifest.leanNegationHash
            ? { officialManifestLeanNegationHash: validatedManifest.leanNegationHash }
            : {}),
          officialRepositoryUrl: validatedManifest.repositoryUrl,
          officialBaselineCommit: validatedManifest.baselineCommit,
          benchmarkAdapterId: validatedManifest.benchmarkAdapterId,
          benchmarkAdapterVersion: validatedManifest.benchmarkAdapterVersion,
        }
      : {}),
    ...(cleanupError ? { cleanupError } : {}),
    ...(error ? { error } : {}),
  });
}

export async function runOfficialComparator(
  request: MathematicsOfficialComparatorRequest,
  options: MathematicsVerifierExecutionOptions = {}
): Promise<MathematicsOfficialComparatorResult> {
  const runtimeOptions: MathematicsVerifierExecutionOptions & { env: NodeJS.ProcessEnv } = {
    ...options,
    env: resolveMathematicsRuntimeEnvironment(options.env || process.env),
  };
  return withVerificationSlot(() => runOfficialComparatorUnbounded(request, runtimeOptions), runtimeOptions.signal);
}
