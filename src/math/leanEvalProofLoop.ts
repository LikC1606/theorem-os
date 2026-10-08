import { resolveMathProofEnvironment } from "./mathProofEnvironment";
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import type { LeanEvalProblemAnalysis } from "./leanEvalProblemAnalyzer";
import {
  classifyMathLeanFailure,
  normalizeMathExecutionPolicy,
  normalizeMathProofState,
  type MathProofState,
  type MathExecutionPolicy,
  type MathLeanFailureKind,
} from "../common/types/team/mathematicsTeam";
import { classifyLeanEvalFailure, leanEvalRetryDecision, type LeanEvalFailureCategory } from "./leanEvalFailurePolicy";
import { assertLeanEvalSubmissionComplete, assertLeanEvalSubmissionOwned } from "./leanEvalHoleDag";
import { inspectLeanSource, inspectMathematicsSandboxBackends, runMathematicsSandboxedCommand } from "./verifier";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import { readMathRunHistoryIdentity } from "./mathRunHistory";
import type { MathematicsLeanProofSession, MathematicsLeanSessionSnapshot } from "./leanInteractiveSession";
import {
  generateLeanProofActionCandidates,
  searchLeanProofActions,
  type LeanProofActionCandidate,
} from "./leanProofActionSearch";

export type LeanEvalProofAttemptContext = Readonly<{
  problemId: string;
  wave: number;
  holeNames: readonly string[];
  completedNames: readonly string[];
  workspaceRoot: string;
  previousError?: string;
  /** Structured goal context extracted from the last Lean compiler diagnostic. */
  openGoal?: string;
  openGoalCount?: number;
  proofStateFingerprint?: string;
  signal?: AbortSignal;
  deadlineAt: number;
  remainingMs: number;
  executionPolicy?: MathExecutionPolicy;
  tactic?: string;
  premiseQuery?: string;
  requestedModel?: string;
  selectedModel?: string;
}>;

export type LeanEvalProofAttempt = Readonly<{
  source: string;
  file?: string;
  objective?: string;
  /** Optional tactic provenance supplied by a structured search backend. */
  tactic?: string;
}>;

export type LeanEvalSourceLocation = Readonly<{
  sourceFile: string;
  line: number;
  column: number;
  endLine?: number;
  endColumn?: number;
  /** Character offset in the submitted source, derived from Lean's start position. */
  sourceOffset?: number;
}>;

export type LeanEvalCompilerDiagnostic = Readonly<{
  format: 'lean-json' | 'plain';
  severity: 'error';
  message: string;
  messageKind?: string;
  location?: LeanEvalSourceLocation;
  /** Lean goal context emitted by the first error, without the generic error heading. */
  openGoal?: string;
  openGoalCount?: number;
  /** Stable across source-line movement when the semantic first error and goal are unchanged. */
  proofStateFingerprint: string;
}>;

export type LeanEvalProofLoopOptions = Readonly<{
  workspaceRoot: string;
  analysis: LeanEvalProblemAnalysis;
  /** Runtime-owned canonical project for run-scoped action history. */
  historyProjectRoot?: string;
  /** Stable identity shared by every repair delivery in one solver episode. */
  episodeId?: string;
  /** Compilation already spent establishing the initial session state. */
  initialLeanMs?: number;
  /** Premises returned by the caller's authorized, version-bound retrieval path. */
  premiseCandidates?: readonly Readonly<{ name: string; type: string }>[];
  attempt: (
    context: LeanEvalProofAttemptContext
  ) => Promise<LeanEvalProofAttempt | undefined> | LeanEvalProofAttempt | undefined;
  /** Optional Pantograph/LSP-style candidate source provider. Its output is
   * treated exactly like a model candidate and still passes through the
   * kernel compiler; provider failures fall back to the normal attempt. */
  structuredSearch?: (
    context: LeanEvalProofAttemptContext
  ) => Promise<LeanEvalProofAttempt | undefined> | LeanEvalProofAttempt | undefined;
  /** Optional bounded action candidates evaluated by the source-backed session. */
  actionCandidates?: (
    context: LeanEvalProofAttemptContext
  ) => Promise<readonly LeanProofActionCandidate[] | undefined> | readonly LeanProofActionCandidate[] | undefined;
  timeoutMs?: number;
  /** Number of model/compiler candidates tried synchronously in one delivery. */
  attemptsPerWave?: number;
  signal?: AbortSignal;
  checkpointPath?: string;
  resumeFromCheckpoint?: LeanEvalProofLoopCheckpoint | string;
  /**
   * `restore_checkpoint` is the crash-recovery default. `accept_current_candidate`
   * is reserved for a model that deliberately edited an otherwise-unfinished
   * solver workspace after receiving the previous compiler diagnostic.
   */
  resumeSourcePolicy?: 'restore_checkpoint' | 'accept_current_candidate';
  lakeExecutable?: string;
  /** Trusted read-only Lake package cache mounted into the sandbox. */
  lakePackagesPath?: string;
  /** Use the verifier-owned Linux namespace for construction-time Lean. */
  sandboxed?: boolean;
  /** Upper bound on one candidate source, in bytes. */
  maxSourceBytes?: number;
  /**
   * Optional safety deadline for one in-process proof-loop invocation.
   * Omit this for a resumable episode whose lifetime is controlled by the
   * caller's AbortSignal and durable checkpoint, rather than by a research
   * deadline.
   */
  totalTimeoutMs?: number;
  /** Runtime-derived identity for analysis, toolchain, packages, and sandbox. */
  executionFingerprint?: string;
  /** Runtime-owned tactic/query/model policy. */
  executionPolicy?: MathExecutionPolicy;
  /** Maximum number of solver-owned Lean files in the workspace. */
  maxSubmissionFiles?: number;
  /** Maximum directory depth below Submission/. */
  maxSubmissionDepth?: number;
  /** Maximum aggregate bytes across solver-owned Lean files. */
  maxSubmissionBytes?: number;
  /** Optional source-backed interactive session for the primary proof file. */
  proofSession?: MathematicsLeanProofSession;
}>;

export type LeanEvalProofStep = Readonly<{
  wave: number;
  holeNames: readonly string[];
  attempt: number;
  sourceFile?: string;
  candidateProofHash?: string;
  status: 'compiled' | 'failed' | 'skipped';
  category?: LeanEvalFailureCategory;
  stdout?: string;
  stderr?: string;
  diagnostic?: LeanEvalCompilerDiagnostic;
  durationMs: number;
  repairObjective?: string;
  tactic?: string;
  premiseQuery?: string;
  requestedModel?: string;
  selectedModel?: string;
  sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
}>;

export type LeanEvalProofLoopCheckpoint = Readonly<{
  schema: 'deepscientist.mathematics.lean-eval-proof-checkpoint.v1';
  runIdentity?: string;
  /** Optional for backwards-compatible v1 checkpoints created before episodes. */
  episodeId?: string;
  problemId: string;
  benchmarkCommit: string;
  completedNames: readonly string[];
  activeWave: number;
  sourceHashes: Readonly<Record<string, string>>;
  steps: readonly LeanEvalProofStep[];
  updatedAt: number;
  analysisFingerprint?: string;
  holeScheduleFingerprint?: string;
  workspaceFingerprint?: string;
  executionFingerprint?: string;
  executionPolicy?: MathExecutionPolicy;
  proofState?: MathProofState;
  /** Beam-retained source-backed branches available for cross-checkpoint recovery. */
  proofBranches?: readonly MathematicsLeanSessionSnapshot[];
}>;

export type LeanEvalProofLoopResult = Readonly<{
  status: 'completed' | 'failed' | 'aborted';
  completedNames: readonly string[];
  steps: readonly LeanEvalProofStep[];
  checkpoint: LeanEvalProofLoopCheckpoint;
  failure?: Readonly<{ category: LeanEvalFailureCategory; message: string }>;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const sha256Bytes = (value: Uint8Array): string => crypto.createHash('sha256').update(value).digest('hex');
const MAX_SOURCE_BYTES = 16 * 1024 * 1024;
const MAX_SUBMISSION_FILES = 128;
const MAX_SUBMISSION_DEPTH = 8;
const MAX_SUBMISSION_BYTES = 64 * 1024 * 1024;
const MAX_DIAGNOSTIC_BYTES = 12_000;
const MAX_OPEN_GOAL_BYTES = 4_000;
const proofEnvironmentFiles = Object.freeze(['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean']);
const proofEnvironmentVariables = Object.freeze([
  'PATH',
  'ELAN_HOME',
  'LAKE_HOME',
  'LEAN_PATH',
  'LEAN_SYSROOT',
  'DEEPSCIENTIST_MATH_SANDBOX_BACKEND',
  'DEEPSCIENTIST_MATH_SANDBOX_IMAGE',
]);
const clamp = (value: number, low: number, high: number): number => Math.max(low, Math.min(high, value));

const record = (value: unknown): Record<string, unknown> | undefined =>
  typeof value === 'object' && value !== null && !Array.isArray(value) ? (value as Record<string, unknown>) : undefined;

const boundedDiagnostic = (value: string, limit = MAX_DIAGNOSTIC_BYTES): string =>
  value
    .replaceAll('\r\n', '\n')
    .replaceAll('\r', '\n')
    .split('\n')
    .map((line) => line.trimEnd())
    .join('\n')
    .trim()
    .slice(0, limit);

const sourceOffsetAt = (source: string | undefined, line: number, column: number): number | undefined => {
  if (source === undefined || line < 1 || column < 0) return undefined;
  let offset = 0;
  for (let currentLine = 1; currentLine < line; currentLine += 1) {
    const newline = source.indexOf('\n', offset);
    if (newline < 0) return undefined;
    offset = newline + 1;
  }
  const lineEnd = source.indexOf('\n', offset);
  const lineText = source.slice(offset, lineEnd < 0 ? source.length : lineEnd).replace(/\r$/u, '');
  const prefix = [...lineText].slice(0, column).join('');
  if ([...lineText].length < column) return undefined;
  return offset + prefix.length;
};

const diagnosticLocation = (
  value: Record<string, unknown>,
  fallbackSourceFile: string,
  source?: string
): LeanEvalSourceLocation | undefined => {
  const position = record(value.pos);
  if (!position) return undefined;
  const line = position.line;
  const column = position.column;
  if (!Number.isSafeInteger(line) || Number(line) < 1 || !Number.isSafeInteger(column) || Number(column) < 0) {
    return undefined;
  }
  const reportedFile = typeof value.fileName === 'string' ? value.fileName.trim().replaceAll('\\', '/') : '';
  const sourceFile =
    reportedFile &&
    !path.isAbsolute(reportedFile) &&
    !reportedFile.split('/').includes('..') &&
    !reportedFile.startsWith('<')
      ? reportedFile
      : fallbackSourceFile;
  const end = record(value.endPos);
  const endLine = Number.isSafeInteger(end?.line) && Number(end?.line) >= Number(line) ? Number(end?.line) : undefined;
  const endColumn =
    endLine !== undefined && Number.isSafeInteger(end?.column) && Number(end?.column) >= 0
      ? Number(end?.column)
      : undefined;
  const sourceOffset = sourceOffsetAt(source, Number(line), Number(column));
  return Object.freeze({
    sourceFile,
    line: Number(line),
    column: Number(column),
    ...(endLine !== undefined ? { endLine } : {}),
    ...(endColumn !== undefined ? { endColumn } : {}),
    ...(sourceOffset !== undefined ? { sourceOffset } : {}),
  });
};

const extractOpenGoal = (message: string): Readonly<{ text: string; count: number }> | undefined => {
  const lines = message.split('\n');
  const unsolvedHeader = lines.findIndex((line) => /^unsolved goals?\s*$/iu.test(line.trim()));
  const turnstileCount = lines.filter((line) => /^\s*⊢/u.test(line)).length;
  if (unsolvedHeader >= 0) {
    const text = boundedDiagnostic(lines.slice(unsolvedHeader + 1).join('\n'), MAX_OPEN_GOAL_BYTES);
    return text ? Object.freeze({ text, count: Math.max(1, turnstileCount) }) : undefined;
  }
  const firstTurnstile = lines.findIndex((line) => /^\s*⊢/u.test(line));
  if (firstTurnstile < 0) return undefined;
  let start = firstTurnstile;
  while (start > 0 && lines[start - 1]!.trim()) start -= 1;
  const text = boundedDiagnostic(lines.slice(start).join('\n'), MAX_OPEN_GOAL_BYTES);
  return text ? Object.freeze({ text, count: Math.max(1, turnstileCount) }) : undefined;
};

const proofStateFingerprint = (
  message: string,
  messageKind: string | undefined,
  openGoal: string | undefined
): string =>
  sha256(
    JSON.stringify({
      message: boundedDiagnostic(message)
        .replace(/(?:[\p{L}\p{N}_.-]+\/)*[\p{L}\p{N}_.-]+\.lean(?::\d+(?::\d+)?)?/giu, '<file>')
        .replace(/\bline\s+\d+(?:\s*,\s*column\s+\d+)?\b/giu, 'line <n>'),
      messageKind: messageKind ?? '',
      openGoal: openGoal ?? '',
    })
  );

const plainLeanDiagnostic = (
  stdout: string,
  stderr: string,
  sourceFile: string,
  source?: string
): LeanEvalCompilerDiagnostic | undefined => {
  const raw = boundedDiagnostic([stderr, stdout].filter(Boolean).join('\n'));
  if (!raw) return undefined;
  const lines = raw.split('\n');
  let message = raw;
  let location: LeanEvalSourceLocation | undefined;
  const headerPattern = /^(.*):(\d+):(\d+):\s*error:\s*(.*)$/u;
  const nextDiagnosticPattern = /^.*:\d+:\d+:\s*(?:error|warning|information):/u;
  const headerIndex = lines.findIndex((line) => headerPattern.test(line));
  if (headerIndex >= 0) {
    const header = headerPattern.exec(lines[headerIndex]!)!;
    const following = lines.slice(headerIndex + 1);
    const nextDiagnostic = following.findIndex((line) => nextDiagnosticPattern.test(line));
    message = boundedDiagnostic(
      [header[4]!, ...following.slice(0, nextDiagnostic < 0 ? following.length : nextDiagnostic)].join('\n')
    );
    const line = Number(header[2]);
    const column = Number(header[3]);
    const reportedFile = header[1]!.trim().replaceAll('\\', '/');
    const safeSourceFile =
      reportedFile && !path.isAbsolute(reportedFile) && !reportedFile.split('/').includes('..')
        ? reportedFile
        : sourceFile;
    const sourceOffset = sourceOffsetAt(source, line, column);
    location = Object.freeze({
      sourceFile: safeSourceFile,
      line,
      column,
      ...(sourceOffset !== undefined ? { sourceOffset } : {}),
    });
  }
  const goal = extractOpenGoal(message);
  return Object.freeze({
    format: 'plain',
    severity: 'error',
    message,
    ...(location ? { location } : {}),
    ...(goal ? { openGoal: goal.text, openGoalCount: goal.count } : {}),
    proofStateFingerprint: proofStateFingerprint(message, undefined, goal?.text),
  });
};

/** Parse the first compiler error from Lean's stable JSON-lines CLI protocol. */
export function parseLeanEvalCompilerDiagnostic(
  input: Readonly<{
    stdout: string;
    stderr: string;
    sourceFile: string;
    source?: string;
  }>
): LeanEvalCompilerDiagnostic | undefined {
  for (const output of [input.stdout, input.stderr]) {
    for (const line of output.split('\n')) {
      const trimmed = line.trim();
      if (!trimmed.startsWith('{')) continue;
      let value: Record<string, unknown> | undefined;
      try {
        value = record(JSON.parse(trimmed));
      } catch {
        continue;
      }
      if (value?.severity !== 'error' || typeof value.data !== 'string') continue;
      const message = boundedDiagnostic(value.data);
      if (!message) continue;
      const messageKind = typeof value.kind === 'string' && value.kind.trim() ? value.kind.trim() : undefined;
      const location = diagnosticLocation(value, input.sourceFile, input.source);
      const goal = extractOpenGoal(message);
      return Object.freeze({
        format: 'lean-json',
        severity: 'error',
        message,
        ...(messageKind ? { messageKind } : {}),
        ...(location ? { location } : {}),
        ...(goal ? { openGoal: goal.text, openGoalCount: goal.count } : {}),
        proofStateFingerprint: proofStateFingerprint(message, messageKind, goal?.text),
      });
    }
  }
  return plainLeanDiagnostic(input.stdout, input.stderr, input.sourceFile, input.source);
}
const leanEnvironment = (): NodeJS.ProcessEnv => resolveMathematicsRuntimeEnvironment();
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
    if (stat.isSymbolicLink() || !stat.isDirectory())
      throw new Error(`Proof workspace path is not a directory: ${current}`);
  }
  return resolved;
};

const executableIdentity = (executable: string, env: NodeJS.ProcessEnv): Readonly<Record<string, unknown>> => {
  const candidates = path.isAbsolute(executable)
    ? [executable]
    : (env.PATH || '')
        .split(path.delimiter)
        .filter(Boolean)
        .map((entry) => path.join(entry, executable));
  const selected = candidates.find((candidate) => {
    try {
      return fs.statSync(candidate).isFile();
    } catch {
      return false;
    }
  });
  if (!selected) return Object.freeze({ requested: executable, available: false });
  try {
    const resolved = fs.realpathSync(selected);
    const stat = fs.statSync(resolved);
    return Object.freeze({
      requested: executable,
      available: true,
      resolved,
      size: stat.size,
      modifiedMs: stat.mtimeMs,
      sha256: sha256Bytes(fs.readFileSync(resolved)),
    });
  } catch {
    return Object.freeze({ requested: executable, available: false });
  }
};

const fileIdentity = (root: string, relative: string): readonly [string, string | null] => {
  const file = path.join(root, relative);
  try {
    const stat = fs.lstatSync(file);
    if (stat.isSymbolicLink() || !stat.isFile()) return Object.freeze([relative, null] as const);
    return Object.freeze([relative, sha256Bytes(fs.readFileSync(file))] as const);
  } catch {
    return Object.freeze([relative, null] as const);
  }
};

const packageCacheIdentity = (lakePackagesPath: string | undefined): Readonly<Record<string, unknown>> | undefined => {
  if (!lakePackagesPath) return undefined;
  try {
    const stat = fs.lstatSync(lakePackagesPath);
    if (stat.isSymbolicLink() || !stat.isDirectory()) return Object.freeze({ available: false });
    const resolved = fs.realpathSync(lakePackagesPath);
    const packages = fs
      .readdirSync(resolved, { withFileTypes: true })
      .filter((entry) => entry.isDirectory())
      .map((entry) => {
        const packageRoot = path.join(resolved, entry.name);
        const headFile = path.join(packageRoot, '.git', 'HEAD');
        let head: string | undefined;
        try {
          head = fs.readFileSync(headFile, 'utf8').trim();
          if (head.startsWith('ref: ')) {
            const refFile = path.join(packageRoot, '.git', head.slice('ref: '.length));
            head = `${head}\0${fs.readFileSync(refFile, 'utf8').trim()}`;
          }
        } catch {
          // The project manifest still binds package revisions when Git metadata is unavailable.
        }
        return [entry.name, head ?? null] as const;
      })
      .toSorted(([left], [right]) => left.localeCompare(right));
    return Object.freeze({ available: true, resolved, packages: Object.freeze(packages) });
  } catch {
    return Object.freeze({ available: false });
  }
};

/** Bind reusable proof-loop state to every input that can change elaboration. */
export function createLeanEvalProofExecutionFingerprint(input: {
  workspaceRoot: string;
  analysis: LeanEvalProblemAnalysis;
  lakeExecutable?: string;
  lakePackagesPath?: string;
  sandboxed?: boolean;
  env?: NodeJS.ProcessEnv;
}): string {
  const workspaceRoot = path.resolve(input.workspaceRoot);
  // Fingerprint the same env-file-expanded, secret-free environment that is
  // passed to Lean. Otherwise an env-file change can incorrectly reuse a
  // checkpoint under a different toolchain path or sandbox.
  const env = resolveMathematicsRuntimeEnvironment(input.env ?? process.env);
  const sealed = resolveMathProofEnvironment(workspaceRoot, env);
  if (sealed && input.lakePackagesPath && input.lakePackagesPath !== sealed.packagesRoot)
    throw new Error('Lean proof execution sealed package identity mismatch');
  const sandbox = inspectMathematicsSandboxBackends(env);
  const relevantEnvironment = Object.fromEntries(proofEnvironmentVariables.map((name) => [name, env[name] ?? '']));
  return sha256(
    JSON.stringify({
      schema: 'deepscientist.mathematics.lean-eval-proof-execution.v1',
      platform: process.platform,
      arch: process.arch,
      node: process.version,
      analysis: {
        problemId: input.analysis.problemId,
        benchmarkCommit: input.analysis.benchmarkCommit,
        challengeSha256: input.analysis.challengeSha256,
        holes: input.analysis.holes.map((hole) => [hole.name, hole.basename, hole.kind, hole.dependsOn]),
        schedule: input.analysis.holeSchedule.waves,
      },
      projectFiles: proofEnvironmentFiles.map((file) => fileIdentity(workspaceRoot, file)),
      executables: [executableIdentity(input.lakeExecutable ?? 'lake', env), executableIdentity('lean', env)],
      packageCache: sealed
        ? { available: true, sealedIdentity: sealed.identity }
        : packageCacheIdentity(input.lakePackagesPath),
      sandboxed: input.sandboxed === true,
      sandbox: { available: sandbox.available, preferred: sandbox.preferred ?? null },
      environment: relevantEnvironment,
    })
  );
}

const compileUnsandboxed = (
  workspaceRoot: string,
  file: string,
  timeoutMs: number,
  executable: string,
  signal?: AbortSignal
): Promise<
  Readonly<{ ok: boolean; advanced: boolean; stdout: string; stderr: string; durationMs: number; aborted: boolean }>
> =>
  new Promise((resolve) => {
    const startedAt = Date.now();
    const child = spawn(executable, ['env', 'lean', '--json', '-DmaxErrors=1', file], {
      cwd: workspaceRoot,
      env: { ...leanEnvironment(), CI: '1' },
      detached: process.platform !== 'win32',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    let stdout = '';
    let stderr = '';
    let settled = false;
    let timer: NodeJS.Timeout | undefined;
    const finish = (ok: boolean, aborted = false): void => {
      if (settled) return;
      settled = true;
      if (timer) clearTimeout(timer);
      signal?.removeEventListener('abort', abort);
      resolve(
        Object.freeze({
          ok,
          advanced: false,
          stdout: stdout.slice(0, 16_000),
          stderr: stderr.slice(0, 16_000),
          durationMs: Date.now() - startedAt,
          aborted,
        })
      );
    };
    child.stdout.on('data', (chunk: Buffer | string) => {
      stdout = `${stdout}${chunk}`.slice(0, 32_000);
    });
    child.stderr.on('data', (chunk: Buffer | string) => {
      stderr = `${stderr}${chunk}`.slice(0, 32_000);
    });
    child.once('error', (error) => {
      stderr = `${stderr}${error instanceof Error ? error.message : String(error)}`;
      finish(false);
    });
    child.once('close', (code) => finish(code === 0));
    const stop = (): void => {
      if (process.platform !== 'win32' && child.pid) {
        try {
          process.kill(-child.pid, 'SIGTERM');
        } catch {
          child.kill('SIGTERM');
        }
      } else child.kill('SIGTERM');
    };
    const abort = (): void => {
      stop();
      finish(false, true);
    };
    if (signal?.aborted) return abort();
    signal?.addEventListener('abort', abort, { once: true });
    timer = setTimeout(() => {
      stop();
      stderr = `${stderr}\nLean verification timed out.`.trim();
      // Keep timeouts on the infrastructure-retry path, matching the
      // sandboxed runner's timeout/unavailable handling below.
      finish(false, true);
    }, timeoutMs);
  });

const compile = async (
  workspaceRoot: string,
  file: string,
  timeoutMs: number,
  executable: string,
  signal: AbortSignal | undefined,
  sandboxed: boolean,
  lakePackagesPath: string | undefined
): Promise<
  Readonly<{
    ok: boolean;
    advanced: boolean;
    stdout: string;
    stderr: string;
    durationMs: number;
    aborted: boolean;
    sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
  }>
> => {
  if (!sandboxed) return compileUnsandboxed(workspaceRoot, file, timeoutMs, executable, signal);
  const result = await runMathematicsSandboxedCommand({
    checkoutRoot: workspaceRoot,
    command: executable,
    args: ['env', 'lean', '--json', '-DmaxErrors=1', file],
    timeoutMs,
    signal,
    env: { ...leanEnvironment(), CI: '1' },
    outputCapture: 'head',
    ...(lakePackagesPath ? { lakePackagesPath } : {}),
  });
  return Object.freeze({
    ok: result.started && result.exitCode === 0 && !result.timedOut && !result.aborted,
    advanced: false,
    stdout: result.stdout.slice(0, 16_000),
    stderr: (result.stderr || result.errorMessage || '').slice(0, 16_000),
    durationMs: result.durationMs,
    aborted: result.aborted || result.timedOut || result.errorCode === 'SANDBOX_UNAVAILABLE',
    ...(result.sandboxBackend ? { sandboxBackend: result.sandboxBackend } : {}),
  });
};

/** Run a primary candidate through an already-started source-backed session. */
const compileWithProofSession = async (
  session: MathematicsLeanProofSession,
  source: string,
  tactic: string,
  signal?: AbortSignal,
  timeoutMs?: number
): Promise<
  Readonly<{
    ok: boolean;
    advanced: boolean;
    stdout: string;
    stderr: string;
    durationMs: number;
    aborted: boolean;
    sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
  }>
> => {
  const startedAt = Date.now();
  try {
    const action = await session.runTactic(tactic, source, signal, timeoutMs);
    const runtime = action.action?.runtime;
    return Object.freeze({
      ok: action.status === 'advanced' && action.state?.status === 'closed',
      advanced: action.status === 'advanced',
      stdout: '',
      stderr: action.diagnostics,
      durationMs: runtime?.durationMs ?? 0,
      aborted:
        action.status === 'unavailable' ||
        action.executionDisposition === 'timed_out' ||
        action.executionDisposition === 'aborted' ||
        action.executionDisposition === 'unavailable',
    });
  } catch (error) {
    return Object.freeze({
      ok: false,
      advanced: false,
      stdout: '',
      stderr: error instanceof Error ? error.message : String(error),
      durationMs: Math.max(0, Date.now() - startedAt),
      aborted: Boolean(signal?.aborted),
    });
  }
};

const isAllowedProofFile = (file: string): boolean =>
  file === 'Submission.lean' || (file.startsWith('Submission/') && file.endsWith('.lean'));

const normalizeProofFile = (file: string): string => {
  const normalized = file.replaceAll('\\', '/').replace(/^\.\//u, '');
  const parts = normalized.split('/');
  const depth = normalized === 'Submission.lean' ? 0 : Math.max(0, parts.length - 1);
  if (
    !isAllowedProofFile(normalized) ||
    parts.some((part) => !part || part === '.' || part === '..') ||
    depth > MAX_SUBMISSION_DEPTH
  ) {
    throw new Error('Proof candidate must be Submission.lean or Submission/**/*.lean');
  }
  return normalized;
};

const candidateTacticFields = (candidate: LeanEvalProofAttempt): Readonly<{ tactic?: string }> => {
  const tactic = typeof candidate.tactic === 'string' ? candidate.tactic.trim().slice(0, 256) : '';
  return tactic ? Object.freeze({ tactic }) : Object.freeze({});
};

const analysisFingerprint = (analysis: LeanEvalProblemAnalysis): string =>
  sha256(
    JSON.stringify({
      problemId: analysis.problemId,
      benchmarkCommit: analysis.benchmarkCommit,
      challengeSha256: analysis.challengeSha256,
      holes: analysis.holes.map((hole) => [hole.name, hole.basename, hole.kind, hole.dependsOn]),
      schedule: analysis.holeSchedule.waves,
    })
  );

const workspaceFingerprint = (
  workspaceRoot: string,
  limits: Readonly<{ maxFiles?: number; maxDepth?: number; maxBytes?: number }> = {}
): string => {
  const files: Array<[string, string]> = [];
  let totalBytes = 0;
  const maxFiles = limits.maxFiles ?? MAX_SUBMISSION_FILES;
  const maxDepth = limits.maxDepth ?? MAX_SUBMISSION_DEPTH;
  const maxBytes = limits.maxBytes ?? MAX_SUBMISSION_BYTES;
  const visit = (relative: string): void => {
    const absolute = path.join(workspaceRoot, relative);
    if (!fs.existsSync(absolute)) return;
    const stat = fs.lstatSync(absolute);
    if (stat.isSymbolicLink()) throw new Error(`Proof workspace contains a symlink: ${relative}`);
    if (stat.isDirectory()) {
      const depth = relative === 'Submission' ? 0 : relative.split('/').length - 1;
      if (depth > maxDepth) throw new Error(`Proof workspace exceeds the maximum directory depth of ${maxDepth}`);
      for (const entry of fs.readdirSync(absolute).toSorted()) visit(`${relative}/${entry}`);
      return;
    }
    if (!stat.isFile() || !isAllowedProofFile(relative))
      throw new Error(`Proof workspace file is not allowed: ${relative}`);
    if (files.length >= maxFiles) throw new Error(`Proof workspace exceeds the maximum of ${maxFiles} files`);
    const bytes = fs.readFileSync(absolute);
    totalBytes += bytes.byteLength;
    if (totalBytes > maxBytes) throw new Error(`Proof workspace exceeds the maximum of ${maxBytes} bytes`);
    files.push([relative, sha256Bytes(bytes)]);
  };
  visit('Submission.lean');
  visit('Submission');
  return sha256(JSON.stringify(files));
};

const writePrivateFile = (file: string, contents: string | Uint8Array): void => {
  const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
  const descriptor = fs.openSync(
    file,
    fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_TRUNC | noFollow,
    0o600
  );
  try {
    fs.writeFileSync(descriptor, contents);
    fs.fsyncSync(descriptor);
  } finally {
    fs.closeSync(descriptor);
  }
};

const writeCandidate = (workspaceRoot: string, file: string, source: string): string => {
  const normalizedFile = normalizeProofFile(file);
  if (Buffer.byteLength(source, 'utf8') > MAX_SOURCE_BYTES) {
    throw new Error(`Proof candidate exceeds ${MAX_SOURCE_BYTES} bytes`);
  }
  const resolvedRoot = path.resolve(workspaceRoot);
  const resolved = path.resolve(resolvedRoot, normalizedFile);
  if (resolved !== resolvedRoot && !resolved.startsWith(`${resolvedRoot}${path.sep}`))
    throw new Error('Proof file escaped workspace');
  if (path.extname(resolved).toLowerCase() !== '.lean') throw new Error('Proof candidate must be a Lean file');
  ensureDirectoryNoSymlink(path.dirname(resolved));
  if (fs.existsSync(resolved)) {
    const stat = fs.lstatSync(resolved);
    if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Proof candidate path must be a regular file');
  }
  writePrivateFile(resolved, source);
  return path.relative(resolvedRoot, resolved).replaceAll(path.sep, '/');
};

/** Execute dependency waves with serialized local attempts and durable checkpoints.
 * Cross-turn Worker repairs are intentionally not bounded here; the caller's
 * cancellation/deadline and duplicate-candidate guard remain the termination
 * conditions for a proof episode.
 */
export async function runLeanEvalProofLoop(options: LeanEvalProofLoopOptions): Promise<LeanEvalProofLoopResult> {
  let pendingLeanMs = options.initialLeanMs ?? 0;
  const takePendingLeanMs = () => {
    const value = pendingLeanMs;
    pendingLeanMs = 0;
    return value;
  };
  const resolvedWorkspaceRoot = path.resolve(options.workspaceRoot);
  const workspaceStat = fs.lstatSync(resolvedWorkspaceRoot);
  if (workspaceStat.isSymbolicLink() || !workspaceStat.isDirectory())
    throw new Error('LeanEval proof workspace must be a regular directory');
  const maxAttempts = clamp(Math.floor(options.attemptsPerWave ?? 3), 1, 8);
  const timeoutMs = clamp(Math.floor(options.timeoutMs ?? 60_000), 1_000, 300_000);
  const executable = options.lakeExecutable ?? 'lake';
  const sandboxed = options.sandboxed === true;
  const maxSourceBytes = clamp(Math.floor(options.maxSourceBytes ?? MAX_SOURCE_BYTES), 1_024, MAX_SOURCE_BYTES);
  // A proof episode may legitimately span many repair deliveries.  A default
  // aggregate deadline turns a useful checkpoint into a false terminal result,
  // so only an explicitly supplied finite value enables this process guard.
  const configuredTotalTimeoutMs = options.totalTimeoutMs;
  const totalTimeoutMs =
    configuredTotalTimeoutMs !== undefined && Number.isFinite(configuredTotalTimeoutMs)
      ? clamp(Math.floor(configuredTotalTimeoutMs), 5_000, 1_800_000)
      : undefined;
  const maxSubmissionFiles = clamp(
    Math.floor(options.maxSubmissionFiles ?? MAX_SUBMISSION_FILES),
    1,
    MAX_SUBMISSION_FILES
  );
  const maxSubmissionDepth = clamp(
    Math.floor(options.maxSubmissionDepth ?? MAX_SUBMISSION_DEPTH),
    1,
    MAX_SUBMISSION_DEPTH
  );
  const maxSubmissionBytes = clamp(
    Math.floor(options.maxSubmissionBytes ?? MAX_SUBMISSION_BYTES),
    maxSourceBytes,
    MAX_SUBMISSION_BYTES
  );
  const currentEpisodeId =
    options.episodeId?.trim() ||
    options.proofSession?.episodeId ||
    `${options.analysis.problemId}:${options.analysis.challengeSha256}`;
  const currentRunIdentity = readMathRunHistoryIdentity();
  const checkpointInput =
    typeof options.resumeFromCheckpoint === 'string'
      ? (JSON.parse(fs.readFileSync(path.resolve(options.resumeFromCheckpoint), 'utf8')) as LeanEvalProofLoopCheckpoint)
      : options.resumeFromCheckpoint;
  // Reject foreign history before the crash-recovery sidecar can overwrite source.
  if (
    options.resumeFromCheckpoint &&
    (checkpointInput?.runIdentity !== currentRunIdentity ||
      (currentRunIdentity &&
        (checkpointInput?.problemId !== options.analysis.problemId || checkpointInput?.episodeId !== currentEpisodeId)))
  )
    throw new Error('Lean-Eval proof checkpoint run identity does not match the active run and problem.');
  const deadlineAt = totalTimeoutMs === undefined ? Number.POSITIVE_INFINITY : Date.now() + totalTimeoutMs;
  const loopController = new AbortController();
  const onExternalAbort = (): void => loopController.abort();
  options.signal?.addEventListener('abort', onExternalAbort, { once: true });
  if (options.signal?.aborted) loopController.abort();
  let deadlineExceeded = false;
  const globalDeadlineTimer =
    totalTimeoutMs === undefined
      ? undefined
      : setTimeout(() => {
          deadlineExceeded = true;
          loopController.abort();
        }, totalTimeoutMs);
  globalDeadlineTimer?.unref?.();
  const cleanupLoopSignal = (): void => {
    if (globalDeadlineTimer) clearTimeout(globalDeadlineTimer);
    options.signal?.removeEventListener('abort', onExternalAbort);
  };
  const assertWorkspaceLimits = (): void => {
    workspaceFingerprint(resolvedWorkspaceRoot, {
      maxFiles: maxSubmissionFiles,
      maxDepth: maxSubmissionDepth,
      maxBytes: maxSubmissionBytes,
    });
  };
  assertWorkspaceLimits();
  const completed = new Set<string>();
  const steps: LeanEvalProofStep[] = [];
  let previousError: string | undefined;
  let previousDiagnostic: LeanEvalCompilerDiagnostic | undefined;
  let activeWave = 0;
  const sourceHashes: Record<string, string> = {};
  const stableSources = new Map<string, Buffer | undefined>();
  let checkpointProofState: MathProofState | undefined = options.proofSession?.state;
  const proofBranches = new Map<string, MathematicsLeanSessionSnapshot>();
  let executionPolicy = options.executionPolicy ? normalizeMathExecutionPolicy(options.executionPolicy) : undefined;
  // Set by failure classification so a retry can cross the nominal wave
  // budget only when it selected a genuinely new recovery action.
  let executionPolicyChanged = false;
  const currentAnalysisFingerprint = analysisFingerprint(options.analysis);
  const currentHoleScheduleFingerprint = sha256(JSON.stringify(options.analysis.holeSchedule.waves));
  const currentExecutionFingerprint =
    options.executionFingerprint ??
    createLeanEvalProofExecutionFingerprint({
      workspaceRoot: resolvedWorkspaceRoot,
      analysis: options.analysis,
      lakeExecutable: executable,
      lakePackagesPath: options.lakePackagesPath,
      sandboxed,
    });
  if (typeof options.resumeFromCheckpoint === 'string' && options.resumeSourcePolicy !== 'accept_current_candidate') {
    const checkpointFile = path.resolve(options.resumeFromCheckpoint);
    const backupRoot = `${checkpointFile}.sources`;
    const manifest = path.join(backupRoot, 'manifest.json');
    if (fs.existsSync(manifest)) {
      // Recover a candidate that was written immediately before a process
      // crash.  The sidecar contains only solver-owned files and is verified
      // by content hash before it is copied back.
      ((): void => {
        let entries: Array<{ path: string; hash: string }>;
        try {
          entries = JSON.parse(fs.readFileSync(manifest, 'utf8')) as Array<{ path: string; hash: string }>;
        } catch {
          throw new Error('Lean-Eval proof checkpoint source backup is invalid.');
        }
        const expectedPaths = new Set(entries.map((entry) => normalizeProofFile(entry.path)));
        const currentFiles: string[] = [];
        const collectCurrent = (relative: string): void => {
          const absolute = path.join(resolvedWorkspaceRoot, relative);
          if (!fs.existsSync(absolute)) return;
          const stat = fs.lstatSync(absolute);
          if (stat.isSymbolicLink()) throw new Error(`Proof workspace contains a symlink: ${relative}`);
          if (stat.isDirectory()) {
            for (const entry of fs.readdirSync(absolute).toSorted()) collectCurrent(`${relative}/${entry}`);
          } else if (stat.isFile() && isAllowedProofFile(relative)) currentFiles.push(relative);
        };
        collectCurrent('Submission.lean');
        collectCurrent('Submission');
        for (const relative of currentFiles) {
          if (!expectedPaths.has(relative)) fs.rmSync(path.join(resolvedWorkspaceRoot, relative), { force: true });
        }
        for (const entry of entries) {
          const relative = normalizeProofFile(entry.path);
          if (!/^[0-9a-f]{64}$/u.test(entry.hash))
            throw new Error('Lean-Eval proof checkpoint source hash is invalid.');
          const source = path.join(backupRoot, sha256(relative));
          const destination = path.join(resolvedWorkspaceRoot, relative);
          if (!fs.existsSync(source) || sha256Bytes(fs.readFileSync(source)) !== entry.hash) {
            throw new Error(`Lean-Eval proof checkpoint source backup is corrupt: ${relative}`);
          }
          ensureDirectoryNoSymlink(path.dirname(destination));
          fs.copyFileSync(source, destination);
        }
      })();
    }
  }
  const resume = (() => {
    if (!options.resumeFromCheckpoint) return undefined;
    let value = checkpointInput;
    if (
      !value ||
      value.schema !== 'deepscientist.mathematics.lean-eval-proof-checkpoint.v1' ||
      value.problemId !== options.analysis.problemId ||
      value.benchmarkCommit !== options.analysis.benchmarkCommit
    ) {
      throw new Error('Lean-Eval proof checkpoint identity does not match the active analysis.');
    }
    if (value.proofBranches !== undefined && (!Array.isArray(value.proofBranches) || value.proofBranches.length > 4)) {
      throw new Error('Lean-Eval proof checkpoint contains too many retained proof branches.');
    }
    if (value.episodeId && value.episodeId !== currentEpisodeId) {
      throw new Error('Lean-Eval proof checkpoint episode does not match the active solver episode.');
    }
    if (value.analysisFingerprint && value.analysisFingerprint !== currentAnalysisFingerprint) {
      throw new Error('Lean-Eval proof checkpoint analysis fingerprint does not match the active analysis.');
    }
    if (value.holeScheduleFingerprint && value.holeScheduleFingerprint !== currentHoleScheduleFingerprint) {
      throw new Error('Lean-Eval proof checkpoint hole schedule does not match the active analysis.');
    }
    if (value.executionFingerprint !== currentExecutionFingerprint) {
      throw new Error('Lean-Eval proof checkpoint execution environment does not match the active toolchain.');
    }
    if (options.resumeSourcePolicy === 'accept_current_candidate') {
      const currentWorkspaceFingerprint = workspaceFingerprint(resolvedWorkspaceRoot, {
        maxFiles: maxSubmissionFiles,
        maxDepth: maxSubmissionDepth,
        maxBytes: maxSubmissionBytes,
      });
      const sourcesChanged = value.workspaceFingerprint !== currentWorkspaceFingerprint;
      if (sourcesChanged && value.completedNames.length > 0) {
        throw new Error('Lean-Eval completed proof sources cannot be replaced by an external repair.');
      }
      if (sourcesChanged) {
        // No declaration from this direct whole-candidate wave was accepted, so
        // retain its diagnostic history while making the model's new files the
        // authoritative next candidate. Verified multi-wave sources still fail
        // closed above. The previous source-backed proof state belongs to the
        // old source hash and must not be restored against the repair.
        value = Object.freeze({
          ...value,
          sourceHashes: Object.freeze({}),
          workspaceFingerprint: currentWorkspaceFingerprint,
          proofState: undefined,
          proofBranches: undefined,
        });
      }
    }
    const allowedNames = new Set(options.analysis.holes.map((hole) => hole.name));
    if (value.completedNames.some((name) => !allowedNames.has(name))) {
      throw new Error('Lean-Eval proof checkpoint contains an unknown completed hole.');
    }
    for (const [file, hash] of Object.entries(value.sourceHashes)) {
      if (!isAllowedProofFile(file) || !/^[0-9a-f]{64}$/u.test(hash)) {
        throw new Error('Lean-Eval proof checkpoint contains an invalid source hash.');
      }
      const absolute = path.join(resolvedWorkspaceRoot, file);
      if (fs.existsSync(absolute)) {
        const stat = fs.lstatSync(absolute);
        if (stat.isSymbolicLink() || !stat.isFile() || sha256Bytes(fs.readFileSync(absolute)) !== hash) {
          throw new Error(`Lean-Eval proof workspace does not match checkpoint source: ${file}`);
        }
      } else if (value.completedNames.length > 0) {
        throw new Error(`Lean-Eval proof checkpoint source is missing: ${file}`);
      }
    }
    if (
      value.workspaceFingerprint &&
      value.workspaceFingerprint !==
        workspaceFingerprint(resolvedWorkspaceRoot, {
          maxFiles: maxSubmissionFiles,
          maxDepth: maxSubmissionDepth,
          maxBytes: maxSubmissionBytes,
        })
    ) {
      throw new Error('Lean-Eval proof workspace does not match the checkpoint fingerprint.');
    }
    return value;
  })();
  resume?.completedNames.forEach((name) => completed.add(name));
  if (resume) {
    steps.push(...resume.steps);
    Object.assign(sourceHashes, resume.sourceHashes);
    activeWave = resume.activeWave;
    if (resume.executionPolicy) executionPolicy = normalizeMathExecutionPolicy(resume.executionPolicy);
    if (resume.proofState) {
      const restoredProofState = normalizeMathProofState(resume.proofState);
      if (options.proofSession) {
        let restoredSource: string;
        try {
          restoredSource = fs.readFileSync(
            path.resolve(resolvedWorkspaceRoot, options.proofSession.projectRelative, restoredProofState.sourceFile),
            'utf8'
          );
        } catch (error) {
          throw new Error(
            `Lean-Eval proof checkpoint proof state source is missing: ${restoredProofState.sourceFile}`,
            { cause: error }
          );
        }
        const restored = await options.proofSession.replay(
          { state: restoredProofState, sourceText: restoredSource },
          loopController.signal,
          Math.max(1_000, Math.min(timeoutMs, deadlineAt - Date.now()))
        );
        if (restored.status !== 'restored') {
          throw new Error(`Lean-Eval proof checkpoint proof state cannot be restored: ${restored.diagnostics}`);
        }
        checkpointProofState = restored.state;
      } else {
        checkpointProofState = restoredProofState;
      }
    }
    if (options.proofSession && resume.proofBranches?.length) {
      const activeSnapshot = options.proofSession.snapshot();
      for (const branch of resume.proofBranches.slice(0, 4)) {
        // Replay mutates the same live session, so branches must be serialized.
        // eslint-disable-next-line no-await-in-loop
        const restored = await options.proofSession.replay(
          branch,
          loopController.signal,
          Math.max(1_000, Math.min(timeoutMs, deadlineAt - Date.now()))
        );
        if (restored.status !== 'restored') {
          throw new Error(`Lean-Eval proof checkpoint branch cannot be restored: ${restored.diagnostics}`);
        }
        proofBranches.set(branch.state.stateId, branch);
      }
      const restoredActive = options.proofSession.restore(activeSnapshot);
      if (restoredActive.status === 'invalid') {
        throw new Error(`Lean-Eval proof checkpoint active state cannot be restored: ${restoredActive.diagnostics}`);
      }
    }
  }
  const policyAttemptContext = (): Readonly<{
    policy?: MathExecutionPolicy;
    tactic?: string;
    premiseQuery?: string;
    requestedModel?: string;
    selectedModel?: string;
  }> => {
    if (!executionPolicy) return {};
    const tactic = executionPolicy.tacticLadder[executionPolicy.tacticIndex]?.tactic;
    const premiseQuery = executionPolicy.premiseQueries[executionPolicy.premiseQueryIndex];
    const selectedModel = executionPolicy.modelReceipt?.selected;
    const requestedModel =
      executionPolicy.modelPriority.find((model) => !executionPolicy!.attemptedModels.includes(model)) ?? selectedModel;
    return Object.freeze({
      policy: executionPolicy,
      ...(tactic ? { tactic } : {}),
      ...(premiseQuery ? { premiseQuery } : {}),
      ...(requestedModel ? { requestedModel } : {}),
      ...(selectedModel ? { selectedModel } : {}),
    });
  };
  const advanceExecutionPolicy = (
    category: LeanEvalFailureCategory | MathLeanFailureKind | undefined,
    stateFingerprint?: string
  ): void => {
    if (!executionPolicy) {
      executionPolicyChanged = false;
      return;
    }
    const policyBefore = JSON.stringify(executionPolicy);
    const active = policyAttemptContext();
    let tacticIndex = executionPolicy.tacticIndex;
    let premiseQueryIndex = executionPolicy.premiseQueryIndex;
    if (active.tactic && !executionPolicy.attemptedTactics.includes(active.tactic)) {
      executionPolicy = Object.freeze({
        ...executionPolicy,
        attemptedTactics: Object.freeze([...executionPolicy.attemptedTactics, active.tactic]),
      });
    }
    const premiseFailure =
      category === 'unknown_identifier' ||
      category === 'type_mismatch' ||
      category === 'instance_synthesis_failed' ||
      category === 'unsolved_goals';
    if (
      premiseFailure &&
      active.premiseQuery &&
      !executionPolicy.attemptedPremiseQueries.includes(active.premiseQuery)
    ) {
      executionPolicy = Object.freeze({
        ...executionPolicy,
        attemptedPremiseQueries: Object.freeze([...executionPolicy.attemptedPremiseQueries, active.premiseQuery]),
      });
    }
    if (active.requestedModel && !executionPolicy.attemptedModels.includes(active.requestedModel)) {
      executionPolicy = Object.freeze({
        ...executionPolicy,
        attemptedModels: Object.freeze([...executionPolicy.attemptedModels, active.requestedModel]),
        modelReceipt:
          executionPolicy.modelReceipt ??
          Object.freeze({
            status: 'unavailable' as const,
            requested: active.requestedModel,
            reason: 'Core does not expose dynamic per-dispatch model selection.',
          }),
      });
    }
    const unlabelledProofFailure =
      category === 'unknown' || (category === 'actual_proof_failure' && Boolean(active.tactic) && !premiseFailure);
    if (
      category === 'tactic_failed' ||
      unlabelledProofFailure ||
      (stateFingerprint && stateFingerprint === executionPolicy.lastProofStateFingerprint)
    ) {
      tacticIndex = Math.min(executionPolicy.tacticLadder.length, tacticIndex + 1);
    }
    if (
      category === 'unknown_identifier' ||
      category === 'type_mismatch' ||
      category === 'instance_synthesis_failed' ||
      category === 'unsolved_goals'
    ) {
      premiseQueryIndex = Math.min(executionPolicy.premiseQueries.length, premiseQueryIndex + 1);
    }
    executionPolicy = Object.freeze({
      ...executionPolicy,
      tacticIndex,
      premiseQueryIndex,
      ...(stateFingerprint ? { lastProofStateFingerprint: stateFingerprint } : {}),
    });
    executionPolicyChanged = policyBefore !== JSON.stringify(executionPolicy);
  };
  const checkpoint = (workspaceFingerprintOverride?: string): LeanEvalProofLoopCheckpoint =>
    Object.freeze({
      schema: 'deepscientist.mathematics.lean-eval-proof-checkpoint.v1',
      ...(currentRunIdentity ? { runIdentity: currentRunIdentity } : {}),
      episodeId: currentEpisodeId,
      problemId: options.analysis.problemId,
      benchmarkCommit: options.analysis.benchmarkCommit,
      completedNames: Object.freeze([...completed]),
      activeWave,
      sourceHashes: Object.freeze({ ...sourceHashes }),
      steps: Object.freeze([...steps]),
      updatedAt: Date.now(),
      analysisFingerprint: currentAnalysisFingerprint,
      holeScheduleFingerprint: currentHoleScheduleFingerprint,
      executionFingerprint: currentExecutionFingerprint,
      ...(executionPolicy ? { executionPolicy } : {}),
      ...(options.proofSession
        ? { proofState: options.proofSession.state }
        : checkpointProofState
          ? { proofState: checkpointProofState }
          : {}),
      ...(proofBranches.size > 0 ? { proofBranches: Object.freeze([...proofBranches.values()].slice(-4)) } : {}),
      workspaceFingerprint:
        workspaceFingerprintOverride ??
        workspaceFingerprint(resolvedWorkspaceRoot, {
          maxFiles: maxSubmissionFiles,
          maxDepth: maxSubmissionDepth,
          maxBytes: maxSubmissionBytes,
        }),
    });
  let sourceBackupRoot: string | undefined;
  let sourceBackupEntries: Map<string, string> | undefined;
  let sourceBackupManifestValid = false;
  const sourceBackup = (target: string): string => {
    assertWorkspaceLimits();
    const backupRoot = `${target}.sources`;
    ensureDirectoryNoSymlink(backupRoot);
    if (sourceBackupRoot !== backupRoot) {
      sourceBackupRoot = backupRoot;
      sourceBackupEntries = new Map();
      sourceBackupManifestValid = false;
      const manifest = path.join(backupRoot, 'manifest.json');
      try {
        const manifestStat = fs.lstatSync(manifest);
        if (manifestStat.isSymbolicLink() || !manifestStat.isFile()) throw new Error('invalid manifest file');
        const parsed = JSON.parse(fs.readFileSync(manifest, 'utf8')) as unknown;
        if (Array.isArray(parsed)) {
          sourceBackupManifestValid = true;
          for (const item of parsed) {
            if (!item || typeof item !== 'object') {
              sourceBackupManifestValid = false;
              continue;
            }
            const value = item as Record<string, unknown>;
            if (typeof value.path !== 'string' || typeof value.hash !== 'string') {
              sourceBackupManifestValid = false;
              continue;
            }
            if (!/^[0-9a-f]{64}$/u.test(value.hash)) {
              sourceBackupManifestValid = false;
              continue;
            }
            try {
              const relative = normalizeProofFile(value.path);
              sourceBackupEntries.set(relative, value.hash);
            } catch {
              // Ignore malformed entries and rebuild them from the workspace.
              sourceBackupManifestValid = false;
            }
          }
        }
      } catch {
        // A missing or corrupt sidecar is rebuilt from the current workspace.
      }
    }
    const files: Array<{ path: string; hash: string }> = [];
    const currentPaths = new Set<string>();
    const copy = (relative: string): void => {
      const absolute = path.join(resolvedWorkspaceRoot, relative);
      if (!fs.existsSync(absolute)) return;
      const stat = fs.lstatSync(absolute);
      if (stat.isSymbolicLink()) throw new Error(`Proof workspace contains a symlink: ${relative}`);
      if (stat.isDirectory()) {
        for (const entry of fs.readdirSync(absolute).toSorted()) copy(`${relative}/${entry}`);
        return;
      }
      if (!stat.isFile() || !isAllowedProofFile(relative))
        throw new Error(`Proof workspace file is not allowed: ${relative}`);
      const bytes = fs.readFileSync(absolute);
      const hash = sha256Bytes(bytes);
      const backupPath = path.join(backupRoot, sha256(relative));
      currentPaths.add(relative);
      let reusableBackup = false;
      if (sourceBackupEntries?.get(relative) === hash) {
        try {
          const backupStat = fs.lstatSync(backupPath);
          reusableBackup = backupStat.isFile() && !backupStat.isSymbolicLink();
        } catch {
          reusableBackup = false;
        }
      }
      if (!reusableBackup) {
        writePrivateFile(backupPath, bytes);
      }
      files.push({ path: relative, hash });
    };
    copy('Submission.lean');
    copy('Submission');
    const manifest = path.join(backupRoot, 'manifest.json');
    const previousEntries = sourceBackupEntries ?? new Map<string, string>();
    const manifestChanged =
      previousEntries.size !== files.length ||
      files.some(({ path: filePath, hash }) => previousEntries.get(filePath) !== hash);
    if (manifestChanged || !sourceBackupManifestValid || !fs.existsSync(manifest)) {
      const temporary = `${manifest}.${process.pid}.tmp`;
      writePrivateFile(temporary, `${JSON.stringify(files)}\n`);
      fs.renameSync(temporary, manifest);
      sourceBackupManifestValid = true;
    }
    for (const relative of previousEntries.keys()) {
      if (currentPaths.has(relative)) continue;
      try {
        fs.rmSync(path.join(backupRoot, sha256(relative)), { force: true });
      } catch {
        // Best effort cleanup; the manifest remains authoritative.
      }
    }
    sourceBackupEntries = new Map(files.map(({ path: filePath, hash }) => [filePath, hash]));
    // sourceBackup has already hashed every solver-owned file. Reuse that
    // ordered manifest for the checkpoint fingerprint instead of traversing
    // the same tree a second time during save().
    return sha256(JSON.stringify(files.map(({ path: filePath, hash }) => [filePath, hash])));
  };
  const save = (): void => {
    if (!options.checkpointPath) return;
    const target = path.resolve(options.checkpointPath);
    ensureDirectoryNoSymlink(path.dirname(target));
    const savedWorkspaceFingerprint = sourceBackup(target);
    const temporary = `${target}.${process.pid}.${crypto.randomUUID()}.tmp`;
    const noFollow = typeof fs.constants.O_NOFOLLOW === 'number' ? fs.constants.O_NOFOLLOW : 0;
    const descriptor = fs.openSync(
      temporary,
      fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_EXCL | noFollow,
      0o600
    );
    try {
      fs.writeFileSync(descriptor, `${JSON.stringify(checkpoint(savedWorkspaceFingerprint), null, 2)}\n`, {
        encoding: 'utf8',
      });
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    fs.renameSync(temporary, target);
    try {
      const directory = fs.openSync(path.dirname(target), 'r');
      try {
        fs.fsyncSync(directory);
      } finally {
        fs.closeSync(directory);
      }
    } catch {
      // Directory fsync is not available on every supported filesystem.
    }
  };
  for (
    let waveIndex = Math.min(activeWave, options.analysis.holeSchedule.waves.length);
    waveIndex < options.analysis.holeSchedule.waves.length;
    waveIndex += 1
  ) {
    activeWave = waveIndex;
    const wave = options.analysis.holeSchedule.waves[waveIndex]!;
    let waveSucceeded = false;
    const failedCandidateHashes = new Map<string, Readonly<{ category: LeanEvalFailureCategory; error: string }>>();
    let waveAttemptBudget = maxAttempts;
    let helperAttemptUsed = false;
    const policyHasRecoveryAction = (): boolean => {
      if (!executionPolicy) return false;
      const nextTactic = executionPolicy.tacticLadder[executionPolicy.tacticIndex]?.tactic;
      const nextPremise = executionPolicy.premiseQueries[executionPolicy.premiseQueryIndex];
      return Boolean(
        (nextTactic && !executionPolicy.attemptedTactics.includes(nextTactic)) ||
        (nextPremise && !executionPolicy.attemptedPremiseQueries.includes(nextPremise)) ||
        executionPolicy.modelPriority.some((model) => !executionPolicy!.attemptedModels.includes(model))
      );
    };
    const continueWaveAfterProgress = (attemptIndex: number): void => {
      // attemptsPerWave is a scheduling quantum, not a proof-semantic
      // terminal condition.  A new tactic/premise/model rung or a live-goal
      // transition earns another serialized attempt.  The process deadline
      // (when configured) and caller cancellation remain the hard guards.
      if (executionPolicyChanged) {
        const hasRecoveryAction = policyHasRecoveryAction();
        executionPolicyChanged = false;
        if (hasRecoveryAction) waveAttemptBudget = Math.max(waveAttemptBudget, attemptIndex + 1);
      }
    };
    for (let attemptIndex = 1; attemptIndex <= waveAttemptBudget; attemptIndex += 1) {
      const remainingMs = deadlineAt - Date.now();
      const operationTimeoutMs = Number.isFinite(remainingMs)
        ? Math.max(1, Math.min(timeoutMs, remainingMs))
        : timeoutMs;
      if (loopController.signal.aborted || remainingMs <= 0) {
        if (remainingMs <= 0) {
          deadlineExceeded = true;
          loopController.abort();
        }
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            status: 'skipped',
            durationMs: takePendingLeanMs(),
          })
        );
        save();
        cleanupLoopSignal();
        return Object.freeze({
          status: 'aborted',
          completedNames: Object.freeze([...completed]),
          steps: Object.freeze([...steps]),
          checkpoint: checkpoint(),
        });
      }
      const attemptPolicyContext = policyAttemptContext();
      const policyStepFields = {
        ...(attemptPolicyContext.tactic ? { tactic: attemptPolicyContext.tactic } : {}),
        ...(attemptPolicyContext.premiseQuery ? { premiseQuery: attemptPolicyContext.premiseQuery } : {}),
        ...(attemptPolicyContext.requestedModel ? { requestedModel: attemptPolicyContext.requestedModel } : {}),
        ...(attemptPolicyContext.selectedModel ? { selectedModel: attemptPolicyContext.selectedModel } : {}),
      };
      let candidate: LeanEvalProofAttempt | undefined;
      // Action search executes candidates through the source-backed session.
      // Preserve that kernel result so the stateful action is not compiled a
      // second time below (which would be reported as a duplicate action).
      let precompiledResult: Awaited<ReturnType<typeof compileWithProofSession>> | undefined;
      try {
        // Attempts are intentionally sequential so repairs observe the prior
        // compiler error and never race on solver-owned Submission.lean.
        // eslint-disable-next-line no-await-in-loop
        let timer: NodeJS.Timeout | undefined;
        let rejectAbort: (() => void) | undefined;
        const abortPromise = new Promise<never>((_, reject) => {
          rejectAbort = () => reject(new Error('proof loop was aborted'));
          loopController.signal.addEventListener('abort', rejectAbort, { once: true });
        });
        const attemptGuardMs = operationTimeoutMs;
        const deadlinePromise = new Promise<never>((_, reject) => {
          timer = setTimeout(() => {
            if (Number.isFinite(remainingMs)) deadlineExceeded = true;
            loopController.abort();
            reject(
              new Error(
                Number.isFinite(remainingMs)
                  ? 'proof loop total deadline exceeded'
                  : 'proof attempt safety timeout exceeded'
              )
            );
          }, attemptGuardMs);
        });
        try {
          // eslint-disable-next-line no-await-in-loop
          candidate = await Promise.race([
            Promise.resolve().then(async () => {
              const context: LeanEvalProofAttemptContext = {
                problemId: options.analysis.problemId,
                wave: waveIndex,
                holeNames: wave,
                completedNames: Object.freeze([...completed]),
                workspaceRoot: resolvedWorkspaceRoot,
                signal: loopController.signal,
                deadlineAt,
                remainingMs,
                ...(previousError ? { previousError } : {}),
                ...(previousDiagnostic?.openGoal || options.proofSession?.state.openGoals[0]
                  ? { openGoal: previousDiagnostic?.openGoal ?? options.proofSession?.state.openGoals[0] }
                  : {}),
                ...(previousDiagnostic?.openGoalCount !== undefined
                  ? { openGoalCount: previousDiagnostic.openGoalCount }
                  : {}),
                ...(previousDiagnostic?.proofStateFingerprint || options.proofSession?.state.goalFingerprint
                  ? {
                      proofStateFingerprint:
                        previousDiagnostic?.proofStateFingerprint ?? options.proofSession?.state.goalFingerprint,
                    }
                  : {}),
                ...(attemptPolicyContext.policy ? { executionPolicy: attemptPolicyContext.policy } : {}),
                ...(attemptPolicyContext.tactic ? { tactic: attemptPolicyContext.tactic } : {}),
                ...(attemptPolicyContext.premiseQuery ? { premiseQuery: attemptPolicyContext.premiseQuery } : {}),
                ...(attemptPolicyContext.requestedModel ? { requestedModel: attemptPolicyContext.requestedModel } : {}),
                ...(attemptPolicyContext.selectedModel ? { selectedModel: attemptPolicyContext.selectedModel } : {}),
              };
              if (options.proofSession) {
                try {
                  const candidates = options.actionCandidates
                    ? await options.actionCandidates(context)
                    : options.structuredSearch
                      ? await (async (): Promise<readonly LeanProofActionCandidate[]> => {
                          const discovered: LeanProofActionCandidate[] = [];
                          // The structured provider is a cursor over its cached
                          // state search. Consume a small bounded beam so the
                          // existing provider gains action-level ranking without
                          // changing its public single-candidate contract.
                          for (let index = 0; index < 4; index += 1) {
                            // eslint-disable-next-line no-await-in-loop
                            const searched = await options.structuredSearch!(context);
                            if (!searched) break;
                            discovered.push({
                              kind: searched.tactic ? 'tactic' : 'helper',
                              payload: searched.tactic?.trim() || searched.objective?.trim() || 'candidate',
                              source: searched.source,
                              ...(searched.file ? { file: searched.file } : {}),
                              helperProduced: Boolean(searched.file && searched.file !== 'Submission.lean'),
                            });
                          }
                          return Object.freeze(discovered);
                        })()
                      : (() => {
                          let source = '';
                          try {
                            source = fs.readFileSync(path.join(resolvedWorkspaceRoot, 'Submission.lean'), 'utf8');
                          } catch {
                            return Object.freeze([]);
                          }
                          return generateLeanProofActionCandidates({
                            source,
                            targetLine: previousDiagnostic?.location?.line ?? options.proofSession?.goalLine,
                            ...(context.openGoal ? { openGoal: context.openGoal } : {}),
                            ...(previousError ? { failureCategory: classifyLeanEvalFailure(previousError) } : {}),
                            ...(context.tactic ? { preferredTactic: context.tactic } : {}),
                          });
                        })();
                  if (candidates && candidates.length > 0) {
                    const primaryCandidates = candidates.filter(
                      (actionCandidate) =>
                        !actionCandidate.file || actionCandidate.file === options.proofSession!.sourceFile
                    );
                    const helperCandidates = candidates.filter(
                      (actionCandidate) =>
                        actionCandidate.file && actionCandidate.file !== options.proofSession!.sourceFile
                    );
                    if (primaryCandidates.length > 0) {
                      const searched = await searchLeanProofActions({
                        session: options.proofSession,
                        candidates: primaryCandidates,
                        commitBest: true,
                        signal: loopController.signal,
                        timeoutMs: operationTimeoutMs,
                        performanceRoot: options.historyProjectRoot ?? options.workspaceRoot,
                        episodeId: options.episodeId,
                        problemId: context.problemId,
                        ...(previousError ? { failureCategory: classifyLeanEvalFailure(previousError) } : {}),
                      });
                      pendingLeanMs += searched.durationMs;
                      const best = searched.best;
                      const bestFile = best?.candidate.file ?? options.proofSession.sourceFile;
                      const bestStatus = best?.result.status;
                      if (
                        best &&
                        bestFile === options.proofSession.sourceFile &&
                        (bestStatus === 'advanced' || best?.state?.status === 'closed')
                      ) {
                        for (const branch of searched.branches) {
                          if (
                            !branch.retained ||
                            !branch.state ||
                            branch.state.stateId === best.state?.stateId ||
                            branch.result.status !== 'advanced'
                          )
                            continue;
                          const snapshot = options.proofSession.snapshotState(branch.state.stateId);
                          if (snapshot) proofBranches.set(branch.state.stateId, snapshot);
                        }
                        precompiledResult = Object.freeze({
                          ok: best.state?.status === 'closed',
                          advanced: bestStatus === 'advanced',
                          stdout: '',
                          stderr: best.result.diagnostics,
                          durationMs: 0,
                          aborted: bestStatus === 'unavailable',
                        });
                        return Object.freeze({
                          source: best.candidate.source,
                          ...(best.candidate.file ? { file: best.candidate.file } : {}),
                          tactic: best.candidate.payload,
                          objective: `Apply ${best.candidate.kind} action: ${best.candidate.payload}`,
                        });
                      }
                    }
                    const helper = helperCandidates
                      .toSorted(
                        (left, right) =>
                          Number(right.helperProduced ?? right.kind === 'helper') -
                            Number(left.helperProduced ?? left.kind === 'helper') ||
                          Buffer.byteLength(left.source, 'utf8') - Buffer.byteLength(right.source, 'utf8') ||
                          left.payload.localeCompare(right.payload)
                      )
                      .at(0);
                    if (helper?.file) {
                      return Object.freeze({
                        source: helper.source,
                        file: helper.file,
                        tactic: helper.payload,
                        objective: `Compile helper ${helper.file}: ${helper.payload}`,
                      });
                    }
                  }
                } catch {
                  // Action search is opportunistic; the normal provider remains
                  // authoritative when candidate generation or probing is unavailable.
                }
              }
              if (options.structuredSearch) {
                try {
                  const searched = await options.structuredSearch(context);
                  if (searched) return searched;
                } catch {
                  // Structured search is optional; a provider outage must not
                  // consume the model attempt or alter the formal verdict.
                }
              }
              return options.attempt(context);
            }),
            abortPromise,
            deadlinePromise,
          ]);
        } finally {
          if (timer) clearTimeout(timer);
          if (rejectAbort) loopController.signal.removeEventListener('abort', rejectAbort);
        }
      } catch (error) {
        if (loopController.signal.aborted && (deadlineExceeded || options.signal?.aborted)) {
          steps.push(
            Object.freeze({
              wave: waveIndex,
              holeNames: wave,
              attempt: attemptIndex,
              status: 'skipped',
              durationMs: takePendingLeanMs(),
            })
          );
          save();
          cleanupLoopSignal();
          return Object.freeze({
            status: 'aborted',
            completedNames: Object.freeze([...completed]),
            steps: Object.freeze([...steps]),
            checkpoint: checkpoint(),
          });
        }
        previousError = error instanceof Error ? error.message : String(error);
        previousDiagnostic = undefined;
        const category = classifyLeanEvalFailure(previousError);
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            status: 'failed',
            category,
            stderr: previousError,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
          })
        );
        advanceExecutionPolicy(
          classifyMathLeanFailure(previousError) === 'unknown' ? category : classifyMathLeanFailure(previousError)
        );
        continueWaveAfterProgress(attemptIndex);
        save();
        if (!leanEvalRetryDecision(category).retryable || attemptIndex >= waveAttemptBudget) break;
        continue;
      }
      if (!candidate?.source?.trim()) {
        previousError = 'proof attempt did not provide a candidate source';
        previousDiagnostic = undefined;
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            status: 'failed',
            category: 'actual_proof_failure',
            stderr: previousError,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
          })
        );
        advanceExecutionPolicy('actual_proof_failure');
        continueWaveAfterProgress(attemptIndex);
        save();
        continue;
      }
      if (Buffer.byteLength(candidate.source, 'utf8') > maxSourceBytes) {
        previousError = `proof candidate exceeds ${maxSourceBytes} bytes`;
        previousDiagnostic = undefined;
        const candidateFields = candidateTacticFields(candidate);
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            status: 'failed' as const,
            category: 'actual_proof_failure' as const,
            stderr: previousError,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
            ...candidateFields,
          })
        );
        advanceExecutionPolicy('actual_proof_failure');
        continueWaveAfterProgress(attemptIndex);
        save();
        continue;
      }
      const requestedFile = candidate.file ?? 'Submission.lean';
      const requestedAbsolute = path.resolve(resolvedWorkspaceRoot, requestedFile);
      const resolvedRoot = resolvedWorkspaceRoot;
      if (requestedAbsolute !== resolvedRoot && !requestedAbsolute.startsWith(`${resolvedRoot}${path.sep}`))
        throw new Error('Proof file escaped workspace');
      const existingBeforeWrite = (() => {
        if (!fs.existsSync(requestedAbsolute)) return undefined;
        const stat = fs.lstatSync(requestedAbsolute);
        if (stat.isSymbolicLink() || !stat.isFile()) throw new Error('Proof candidate path must be a regular file');
        return fs.readFileSync(requestedAbsolute);
      })();
      const file = writeCandidate(resolvedWorkspaceRoot, requestedFile, candidate.source);
      assertWorkspaceLimits();
      if (!stableSources.has(file)) stableSources.set(file, existingBeforeWrite);
      const proofHash = sha256(candidate.source);
      const previousSourceHash = sourceHashes[file];
      const candidateFields = candidateTacticFields(candidate);
      try {
        if (file === 'Submission.lean') {
          assertLeanEvalSubmissionComplete(
            options.analysis.holes.map((hole) => hole.name),
            candidate.source
          );
        } else {
          assertLeanEvalSubmissionOwned(candidate.source);
        }
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        const category = classifyLeanEvalFailure(message);
        if (['actual_proof_failure', 'missing_hole', 'submission_namespace_mismatch'].includes(category)) {
          failedCandidateHashes.set(`${candidate.file ?? 'Submission.lean'}\0${sha256(candidate.source)}`, {
            category,
            error: message,
          });
        }
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            sourceFile: file,
            candidateProofHash: proofHash,
            status: 'failed' as const,
            category,
            stderr: message,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
            ...candidateFields,
            ...(candidate.objective ? { repairObjective: candidate.objective } : {}),
          })
        );
        const stable = stableSources.get(file);
        if (stable) writePrivateFile(requestedAbsolute, stable);
        else if (fs.existsSync(requestedAbsolute)) fs.rmSync(requestedAbsolute, { force: true });
        previousError = message;
        previousDiagnostic = undefined;
        if (previousSourceHash) sourceHashes[file] = previousSourceHash;
        else delete sourceHashes[file];
        advanceExecutionPolicy(
          classifyMathLeanFailure(message) === 'unknown' ? category : classifyMathLeanFailure(message)
        );
        continueWaveAfterProgress(attemptIndex);
        save();
        if (!leanEvalRetryDecision(category).retryable || attemptIndex >= waveAttemptBudget) break;
        continue;
      }
      const sourceInspection = inspectLeanSource(candidate.source);
      if (
        sourceInspection.sorryCount > 0 ||
        sourceInspection.admitCount > 0 ||
        sourceInspection.axioms.length > 0 ||
        /\bnative_decide\b/u.test(candidate.source)
      ) {
        const message =
          'candidate contains forbidden proof markers or explicit axioms (sorry/admit/native_decide/axiom)';
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            sourceFile: file,
            candidateProofHash: proofHash,
            status: 'failed' as const,
            category: 'actual_proof_failure' as const,
            stderr: message,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
            ...candidateFields,
            ...(candidate.objective ? { repairObjective: candidate.objective } : {}),
          })
        );
        const stable = stableSources.get(file);
        if (stable) writePrivateFile(requestedAbsolute, stable);
        else if (fs.existsSync(requestedAbsolute)) fs.rmSync(requestedAbsolute, { force: true });
        previousError = message;
        previousDiagnostic = undefined;
        failedCandidateHashes.set(`${file}\0${proofHash}`, {
          category: 'actual_proof_failure',
          error: message,
        });
        if (previousSourceHash) sourceHashes[file] = previousSourceHash;
        else delete sourceHashes[file];
        advanceExecutionPolicy('actual_proof_failure');
        continueWaveAfterProgress(attemptIndex);
        save();
        if (attemptIndex >= waveAttemptBudget) break;
        continue;
      }
      const duplicateFailure = failedCandidateHashes.get(`${file}\0${proofHash}`);
      if (duplicateFailure) {
        const stable = stableSources.get(file);
        if (stable) writePrivateFile(requestedAbsolute, stable);
        else if (fs.existsSync(requestedAbsolute)) fs.rmSync(requestedAbsolute, { force: true });
        if (previousSourceHash) sourceHashes[file] = previousSourceHash;
        else delete sourceHashes[file];
        previousError = duplicateFailure.error;
        previousDiagnostic = undefined;
        steps.push(
          Object.freeze({
            wave: waveIndex,
            holeNames: wave,
            attempt: attemptIndex,
            sourceFile: file,
            candidateProofHash: proofHash,
            status: 'skipped' as const,
            category: duplicateFailure.category,
            stderr: `duplicate candidate skipped: ${duplicateFailure.error}`,
            durationMs: takePendingLeanMs(),
            ...policyStepFields,
            ...candidateFields,
            ...(candidate.objective ? { repairObjective: candidate.objective } : {}),
          })
        );
        const duplicateMathFailure = classifyMathLeanFailure(duplicateFailure.error);
        const policyBefore = executionPolicy ? JSON.stringify(executionPolicy) : undefined;
        advanceExecutionPolicy(duplicateMathFailure === 'unknown' ? duplicateFailure.category : duplicateMathFailure);
        continueWaveAfterProgress(attemptIndex);
        save();
        // Continue only when the runtime policy has a genuinely new tactic,
        // premise, or model action. With no policy progress, another model
        // call would repeat the same deterministic Lean state.
        if (policyBefore === (executionPolicy ? JSON.stringify(executionPolicy) : undefined)) break;
        continue;
      }
      // Compilation is serialized per wave to preserve deterministic repair order.
      // eslint-disable-next-line no-await-in-loop
      const interactiveSession =
        options.proofSession && options.proofSession.sourceFile === file ? options.proofSession : undefined;
      const interactiveSnapshot = interactiveSession?.snapshot();
      let result: Awaited<ReturnType<typeof compile>>;
      if (interactiveSession) {
        if (precompiledResult) {
          result = precompiledResult;
        } else {
          // A session is stateful; actions must remain serialized.
          // eslint-disable-next-line no-await-in-loop
          result = await compileWithProofSession(
            interactiveSession,
            candidate.source,
            candidate.tactic?.trim() || candidate.objective?.trim() || 'candidate',
            loopController.signal,
            operationTimeoutMs
          );
        }
      } else {
        // eslint-disable-next-line no-await-in-loop
        result = await compile(
          resolvedWorkspaceRoot,
          file,
          operationTimeoutMs,
          executable,
          loopController.signal,
          sandboxed,
          options.lakePackagesPath
        );
      }
      if (interactiveSession && !result.ok && !result.advanced && interactiveSnapshot) {
        const restored = interactiveSession.restore(interactiveSnapshot);
        if (restored.status === 'invalid') {
          throw new Error(`Mathematics proof session rollback failed: ${restored.diagnostics}`);
        }
        checkpointProofState = restored.state;
      } else if (interactiveSession) {
        checkpointProofState = interactiveSession.state;
      }
      const rawOutput = `${result.stderr}\n${result.stdout}`.trim();
      const diagnostic = result.ok
        ? undefined
        : parseLeanEvalCompilerDiagnostic({
            stdout: result.stdout,
            stderr: result.stderr,
            sourceFile: file,
            source: candidate.source,
          });
      const output = diagnostic?.message ?? rawOutput;
      const step = Object.freeze({
        wave: waveIndex,
        holeNames: wave,
        attempt: attemptIndex,
        sourceFile: file,
        candidateProofHash: proofHash,
        status: result.ok ? ('compiled' as const) : ('failed' as const),
        ...(result.sandboxBackend ? { sandboxBackend: result.sandboxBackend } : {}),
        ...(result.ok
          ? {}
          : {
              category: result.aborted ? ('landrun_failure' as const) : classifyLeanEvalFailure(output),
              stderr: output,
              ...(diagnostic ? { diagnostic } : {}),
            }),
        stdout: result.stdout,
        durationMs: result.durationMs + takePendingLeanMs(),
        ...policyStepFields,
        ...candidateFields,
        ...(candidate.objective ? { repairObjective: candidate.objective } : {}),
      });
      steps.push(step);
      advanceExecutionPolicy(
        result.ok
          ? undefined
          : step.category === 'actual_proof_failure'
            ? output
              ? classifyMathLeanFailure(output)
              : step.category
            : step.category,
        step.status === 'failed' ? step.diagnostic?.proofStateFingerprint : undefined
      );
      continueWaveAfterProgress(attemptIndex);
      if (
        step.status === 'failed' &&
        step.category &&
        ['actual_proof_failure', 'missing_hole', 'submission_namespace_mismatch'].includes(step.category)
      ) {
        failedCandidateHashes.set(`${file}\0${proofHash}`, {
          category: step.category,
          error: output || 'Lean compilation failed',
        });
      }
      if (result.ok) {
        sourceHashes[file] = proofHash;
        stableSources.set(file, Buffer.from(candidate.source, 'utf8'));
        previousError = undefined;
        previousDiagnostic = undefined;
        save();
        if (file === 'Submission.lean') {
          wave.forEach((name) => completed.add(name));
          waveSucceeded = true;
          save();
          break;
        }
        // A helper can improve the next primary submission, but compiling it
        // does not prove any configured hole by itself. Keep it in the
        // workspace and reserve one extra attempt for the main submission.
        previousError = `compiled helper ${file}; the primary Submission.lean proof remains unverified`;
        if (!helperAttemptUsed) {
          helperAttemptUsed = true;
          // Helper construction is infrastructure progress, not a failed
          // primary proof attempt. This preserves a follow-up slot when the
          // caller requested one attempt per wave.
          waveAttemptBudget = maxAttempts + 1;
        }
        save();
        continue;
      }
      if (interactiveSession && result.advanced) {
        // Keep a valid open-goal transition in the durable workspace. The
        // next candidate must build on this state; restoring the previous
        // source would discard the interactive session's progress.
        sourceHashes[file] = proofHash;
        stableSources.set(file, Buffer.from(candidate.source, 'utf8'));
        previousError = output || 'proof session advanced to a new open goal';
        previousDiagnostic = diagnostic;
        // A valid live-goal transition is proof-state progress even though
        // this individual action did not close the root theorem.
        waveAttemptBudget = Math.max(waveAttemptBudget, attemptIndex + 1);
        save();
        continue;
      }
      const stable = stableSources.get(file);
      const absoluteFile = path.resolve(resolvedWorkspaceRoot, file);
      if (stable) writePrivateFile(absoluteFile, stable);
      else if (fs.existsSync(absoluteFile)) fs.rmSync(absoluteFile, { force: true });
      if (previousSourceHash) sourceHashes[file] = previousSourceHash;
      else delete sourceHashes[file];
      previousError = output || 'Lean compilation failed';
      previousDiagnostic = diagnostic;
      if (interactiveSession && !result.aborted) {
        const alternative = [...proofBranches.values()]
          .toReversed()
          .find(
            (branch) => branch.state.status === 'open' && branch.state.stateId !== interactiveSession.state.stateId
          );
        if (alternative) {
          proofBranches.delete(alternative.state.stateId);
          const restored = interactiveSession.restore(alternative);
          if (restored.status !== 'invalid') {
            writePrivateFile(absoluteFile, Buffer.from(alternative.sourceText, 'utf8'));
            stableSources.set(file, Buffer.from(alternative.sourceText, 'utf8'));
            sourceHashes[file] = sha256(alternative.sourceText);
            checkpointProofState = restored.state;
            previousError = 'The current candidate failed; continue from the retained alternative proof state.';
            previousDiagnostic = undefined;
          }
        }
      }
      save();
      if (result.aborted || !leanEvalRetryDecision(step.category ?? 'actual_proof_failure').retryable) break;
    }
    if (!waveSucceeded) {
      const message = previousError ?? `Lean-Eval proof wave ${waveIndex} failed`;
      save();
      if (deadlineExceeded || options.signal?.aborted) {
        cleanupLoopSignal();
        return Object.freeze({
          status: 'aborted',
          completedNames: Object.freeze([...completed]),
          steps: Object.freeze([...steps]),
          checkpoint: checkpoint(),
        });
      }
      cleanupLoopSignal();
      // The compiler result may carry a structured execution disposition
      // (for example SANDBOX_UNAVAILABLE) that is intentionally represented by
      // the step category. Re-parsing its human diagnostic here can turn the
      // same failure into actual_proof_failure. Only the latest step in this
      // wave is authoritative; an earlier failed wave may already be repaired.
      const lastStep = steps.at(-1);
      const category =
        (lastStep?.wave === waveIndex ? lastStep.category : undefined) ?? classifyLeanEvalFailure(message);
      return Object.freeze({
        status: 'failed',
        completedNames: Object.freeze([...completed]),
        steps: Object.freeze([...steps]),
        checkpoint: checkpoint(),
        failure: Object.freeze({ category, message }),
      });
    }
    activeWave = waveIndex + 1;
    save();
  }
  activeWave = options.analysis.holeSchedule.waves.length;
  save();
  cleanupLoopSignal();
  return Object.freeze({
    status: 'completed',
    completedNames: Object.freeze([...completed]),
    steps: Object.freeze([...steps]),
    checkpoint: checkpoint(),
  });
}
