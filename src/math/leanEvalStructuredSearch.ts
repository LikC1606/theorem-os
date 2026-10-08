/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import type { LeanEvalProofAttempt } from "./leanEvalProofLoop";
import { runMathematicsSandboxedCommand } from "./verifier";

const MAX_GOAL_CHARS = 16_000;
const MAX_REQUEST_BYTES = 64 * 1024;
const MAX_OUTPUT_BYTES = 2 * 1024 * 1024;
const MAX_CANDIDATES = 16;
const MAX_CANDIDATE_SOURCE_BYTES = 16 * 1024 * 1024;
const DEFAULT_TIMEOUT_MS = 30_000;
const MAX_TIMEOUT_MS = 120_000;
const DEFAULT_REQUEST_FLAG = '--request-file';

export type LeanEvalStructuredSearchBackend = 'pantograph' | 'lsp' | 'custom';
export type LeanEvalStructuredSearchTransport = 'request-file' | 'stdin-jsonl';

export type LeanEvalStructuredSearchRequest = Readonly<{
  workspaceRoot: string;
  projectRelative?: string;
  sourceFile?: string;
  /** Goal text supplied by the live Lean diagnostic. */
  goal: string;
  /** Original bounded compiler diagnostic, retained for protocol adapters that
   * need local context in addition to the extracted goal. */
  diagnostic?: string;
  openGoalCount?: number;
  proofStateFingerprint?: string;
  /** Request transport; request-file remains the compatibility default. */
  transport?: LeanEvalStructuredSearchTransport;
  backend?: LeanEvalStructuredSearchBackend;
  /** Executable is resolved from the trusted PATH and staged into the sandbox. */
  executable: string;
  /** Extra fixed arguments understood by the selected backend. */
  args?: readonly string[];
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  requestFileFlag?: string;
}>;

export type LeanEvalStructuredSearchConfig = Readonly<{
  backend: LeanEvalStructuredSearchBackend;
  executable: string;
  transport?: LeanEvalStructuredSearchTransport;
  args?: readonly string[];
  requestFileFlag?: string;
}>;

export type LeanEvalStructuredSearchCandidate = Readonly<LeanEvalProofAttempt & { tactic?: string }>;

export type LeanEvalStructuredSearchResult = Readonly<{
  status: 'passed' | 'failed' | 'unavailable' | 'invalid';
  backend: LeanEvalStructuredSearchBackend;
  candidates: readonly LeanEvalStructuredSearchCandidate[];
  diagnostics: string;
  durationMs: number;
  sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
  error?: string;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

const invalidResult = (
  backend: LeanEvalStructuredSearchBackend,
  error: string,
  diagnostics = ''
): LeanEvalStructuredSearchResult =>
  Object.freeze({ status: 'invalid', backend, candidates: Object.freeze([]), diagnostics, durationMs: 0, error });

const normalizedRelative = (value: string, label: string): string => {
  const normalized = value.trim().replaceAll('\\', '/').replace(/^\.\//u, '');
  if (
    !normalized ||
    normalized.startsWith('/') ||
    /^[A-Za-z]:/u.test(normalized) ||
    normalized.split('/').some((part) => !part || part === '.' || part === '..')
  ) {
    throw new Error(`${label} must be workspace-relative`);
  }
  return normalized;
};

const isSolverOwnedProofFile = (file: string): boolean =>
  file === 'Submission.lean' || (file.startsWith('Submission/') && file.endsWith('.lean'));

const normalizedExecutable = (value: string): string => {
  const executable = value.trim();
  if (!executable || executable !== path.basename(executable) || !/^[A-Za-z0-9._+-]+$/u.test(executable)) {
    throw new Error('Structured search executable must be a PATH-resolved basename');
  }
  return executable;
};

const hasLineBreakOrNul = (value: string): boolean =>
  value.includes('\0') || value.includes('\r') || value.includes('\n');

const boundedArgs = (values: readonly string[] | undefined): readonly string[] => {
  if (!values) return Object.freeze([]);
  if (!Array.isArray(values) || values.length > 32) throw new Error('Structured search args are limited to 32 items');
  const args = values.map((value) => {
    if (typeof value !== 'string' || value.length > 4_000 || hasLineBreakOrNul(value)) {
      throw new Error('Structured search arguments must be single-line strings of at most 4000 characters');
    }
    return value;
  });
  return Object.freeze(args);
};

/** Read an opt-in provider configuration without ever accepting a command
 * line, shell fragment, or absolute executable path. */
export function readLeanEvalStructuredSearchConfig(
  env: NodeJS.ProcessEnv = process.env
): LeanEvalStructuredSearchConfig | undefined {
  const executable = env.DEEPSCIENTIST_LEAN_EVAL_STRUCTURED_SEARCH_EXECUTABLE?.trim();
  if (!executable) return undefined;
  const backendValue = env.DEEPSCIENTIST_LEAN_EVAL_STRUCTURED_SEARCH_BACKEND?.trim() || 'custom';
  if (backendValue !== 'pantograph' && backendValue !== 'lsp' && backendValue !== 'custom') return undefined;
  const transportValue = env.DEEPSCIENTIST_LEAN_EVAL_STRUCTURED_SEARCH_TRANSPORT?.trim() || 'request-file';
  if (transportValue !== 'request-file' && transportValue !== 'stdin-jsonl') return undefined;
  let args: readonly string[] | undefined;
  const encodedArgs = env.DEEPSCIENTIST_LEAN_EVAL_STRUCTURED_SEARCH_ARGS?.trim();
  if (encodedArgs) {
    try {
      const parsed: unknown = JSON.parse(encodedArgs);
      if (!Array.isArray(parsed)) return undefined;
      args = boundedArgs(parsed as string[]);
    } catch {
      return undefined;
    }
  }
  const requestFileFlag = env.DEEPSCIENTIST_LEAN_EVAL_STRUCTURED_SEARCH_REQUEST_FLAG?.trim();
  if (requestFileFlag && !/^--[A-Za-z0-9][A-Za-z0-9-]{0,63}$/u.test(requestFileFlag)) return undefined;
  try {
    normalizedExecutable(executable);
  } catch {
    return undefined;
  }
  return Object.freeze({
    backend: backendValue,
    executable,
    transport: transportValue,
    ...(args ? { args } : {}),
    ...(requestFileFlag ? { requestFileFlag } : {}),
  });
}

const ensurePrivateDirectory = (root: string, relative: string): string => {
  let cursor = path.resolve(root);
  for (const segment of relative.split('/')) {
    cursor = path.join(cursor, segment);
    if (fs.existsSync(cursor)) {
      const stat = fs.lstatSync(cursor);
      if (stat.isSymbolicLink() || !stat.isDirectory()) throw new Error('Structured search metadata path is unsafe');
    } else {
      fs.mkdirSync(cursor, { mode: 0o700 });
    }
  }
  return cursor;
};

const parseCandidates = (value: unknown): readonly LeanEvalStructuredSearchCandidate[] => {
  const root = value && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : {};
  const raw = Array.isArray(root.candidates) ? root.candidates : [];
  const candidates: LeanEvalStructuredSearchCandidate[] = [];
  for (const item of raw.slice(0, MAX_CANDIDATES)) {
    if (!item || typeof item !== 'object' || Array.isArray(item)) continue;
    const candidate = item as Record<string, unknown>;
    if (typeof candidate.source !== 'string' || !candidate.source.trim()) continue;
    if (Buffer.byteLength(candidate.source, 'utf8') > MAX_CANDIDATE_SOURCE_BYTES) continue;
    let file: string | undefined;
    try {
      const candidateFile = candidate.file;
      if (candidateFile === undefined) file = undefined;
      else if (typeof candidateFile !== 'string') continue;
      else file = normalizedRelative(candidateFile, 'Candidate file');
    } catch {
      continue;
    }
    if (file === 'Solution.lean' || file?.endsWith('/Solution.lean')) continue;
    if (file && !isSolverOwnedProofFile(file)) continue;
    const objective = typeof candidate.objective === 'string' ? candidate.objective.slice(0, 4_000) : undefined;
    const tactic = typeof candidate.tactic === 'string' ? candidate.tactic.slice(0, 256) : undefined;
    candidates.push(
      Object.freeze({
        source: candidate.source,
        ...(file ? { file } : {}),
        ...(objective ? { objective } : {}),
        ...(tactic ? { tactic } : {}),
      })
    );
  }
  return Object.freeze(candidates);
};

const parseOutput = (
  output: string
): Readonly<{ candidates: readonly LeanEvalStructuredSearchCandidate[]; diagnostics: string }> => {
  const bounded = output.slice(0, MAX_OUTPUT_BYTES);
  const values: unknown[] = [];
  try {
    values.push(JSON.parse(bounded));
  } catch {
    for (const line of bounded.split(/\r?\n/u).toReversed()) {
      if (!line.trim()) continue;
      try {
        values.push(JSON.parse(line));
        break;
      } catch {
        // Continue to the next JSON-lines record.
      }
    }
  }
  const root =
    values[0] && typeof values[0] === 'object' && !Array.isArray(values[0])
      ? (values[0] as Record<string, unknown>)
      : undefined;
  return Object.freeze({
    candidates: parseCandidates(values[0]),
    diagnostics: typeof root?.diagnostics === 'string' ? root.diagnostics.slice(0, 16_000) : bounded.slice(-16_000),
  });
};

/**
 * Run an optional Pantograph/LSP-style JSON backend in the same sandbox as
 * Lean. The backend reads either a temporary request file or one JSON-lines
 * request on stdin and writes one JSON object to stdout:
 * `{ candidates: [{ source, file?, objective?, tactic? }] }`.
 * Returned source is advisory until the proof loop compiles it.
 */
export async function runLeanEvalStructuredSearch(
  request: LeanEvalStructuredSearchRequest
): Promise<LeanEvalStructuredSearchResult> {
  const backend = request.backend ?? 'custom';
  if (backend !== 'pantograph' && backend !== 'lsp' && backend !== 'custom') {
    return invalidResult('custom', 'Structured search backend is invalid');
  }
  let sourceFile: string;
  let executable: string;
  let args: readonly string[];
  let transport: LeanEvalStructuredSearchTransport;
  try {
    sourceFile = normalizedRelative(request.sourceFile ?? 'Submission.lean', 'Structured search sourceFile');
    if (sourceFile === 'Solution.lean' || sourceFile.endsWith('/Solution.lean')) {
      throw new Error('Protected Solution.lean is not a structured search input');
    }
    executable = normalizedExecutable(request.executable);
    args = boundedArgs(request.args);
    transport = request.transport ?? 'request-file';
    if (transport !== 'request-file' && transport !== 'stdin-jsonl') {
      throw new Error('Structured search transport is invalid');
    }
    if (
      request.requestFileFlag !== undefined &&
      (!/^--[A-Za-z0-9][A-Za-z0-9-]{0,63}$/u.test(request.requestFileFlag) ||
        hasLineBreakOrNul(request.requestFileFlag))
    ) {
      throw new Error('Structured search requestFileFlag must be a simple long option');
    }
    if (!request.goal.trim() || request.goal.length > MAX_GOAL_CHARS || request.goal.includes('\0')) {
      throw new Error(`Structured search goal must be text of at most ${MAX_GOAL_CHARS} characters`);
    }
    if (
      request.diagnostic !== undefined &&
      (!request.diagnostic.trim() || request.diagnostic.length > MAX_GOAL_CHARS || request.diagnostic.includes('\0'))
    ) {
      throw new Error(`Structured search diagnostic must be text of at most ${MAX_GOAL_CHARS} characters`);
    }
    if (
      request.openGoalCount !== undefined &&
      (!Number.isSafeInteger(request.openGoalCount) || request.openGoalCount < 1 || request.openGoalCount > 1024)
    ) {
      throw new Error('Structured search openGoalCount must be an integer between 1 and 1024');
    }
    if (request.proofStateFingerprint !== undefined && !/^[a-f0-9]{64}$/u.test(request.proofStateFingerprint)) {
      throw new Error('Structured search proofStateFingerprint must be a SHA-256 hex digest');
    }
  } catch (error) {
    return invalidResult(backend, error instanceof Error ? error.message : String(error));
  }
  const timeoutMs = Math.max(1_000, Math.min(Math.floor(request.timeoutMs ?? DEFAULT_TIMEOUT_MS), MAX_TIMEOUT_MS));
  const checkoutRoot = path.resolve(request.workspaceRoot);
  const projectRelative = (request.projectRelative ?? '').trim().replaceAll('\\', '/');
  if (
    projectRelative &&
    (projectRelative.startsWith('/') ||
      projectRelative.split('/').some((part) => !part || part === '.' || part === '..'))
  ) {
    return invalidResult(backend, 'Structured search projectRelative must be workspace-relative');
  }
  const projectRoot = path.join(checkoutRoot, projectRelative);
  const requestRelative = `.deepscientist/lean-search/${crypto.randomUUID()}.json`;
  let requestPath: string | undefined;
  try {
    const stat = fs.lstatSync(projectRoot);
    if (stat.isSymbolicLink() || !stat.isDirectory()) throw new Error('Structured search project is not a directory');
    if (fs.realpathSync(projectRoot) !== projectRoot)
      throw new Error('Structured search project contains a symbolic link');
    const sourcePath = path.join(projectRoot, sourceFile);
    if (fs.existsSync(sourcePath)) {
      const sourceStat = fs.lstatSync(sourcePath);
      if (sourceStat.isSymbolicLink() || !sourceStat.isFile())
        throw new Error('Structured search source is not a file');
    }
    const payload = JSON.stringify({
      schema: 'deepscientist.mathematics.lean-structured-search-request.v1',
      backend,
      transport,
      sourceFile,
      goal: request.goal,
      ...(request.diagnostic ? { diagnostic: request.diagnostic } : {}),
      ...(request.openGoalCount !== undefined ? { openGoalCount: request.openGoalCount } : {}),
      ...(request.proofStateFingerprint ? { proofStateFingerprint: request.proofStateFingerprint } : {}),
      ...(request.env?.LEAN_PATH ? { leanPath: request.env.LEAN_PATH } : {}),
    });
    if (Buffer.byteLength(payload, 'utf8') > MAX_REQUEST_BYTES)
      throw new Error('Structured search request is too large');
    if (transport === 'request-file') {
      const requestDirectory = ensurePrivateDirectory(projectRoot, '.deepscientist/lean-search');
      requestPath = path.join(requestDirectory, path.basename(requestRelative));
      fs.writeFileSync(requestPath, `${payload}\n`, { encoding: 'utf8', mode: 0o600 });
    }
    const result = await runMathematicsSandboxedCommand({
      checkoutRoot,
      projectRelative,
      command: executable,
      args:
        transport === 'request-file'
          ? [...args, request.requestFileFlag ?? DEFAULT_REQUEST_FLAG, requestRelative]
          : args,
      ...(transport === 'stdin-jsonl' ? { stdin: `${payload}\n` } : {}),
      timeoutMs,
      signal: request.signal,
      env: request.env,
      ...(request.lakePackagesPath ? { lakePackagesPath: request.lakePackagesPath } : {}),
      outputCapture: 'head',
    });
    const output = `${result.stdout || ''}\n${result.stderr || ''}`;
    const parsed = parseOutput(output);
    const unavailable =
      !result.started ||
      result.errorCode === 'SANDBOX_UNAVAILABLE' ||
      result.errorCode === 'ENOENT' ||
      result.errorCode === 'EACCES';
    return Object.freeze({
      status: unavailable ? 'unavailable' : result.exitCode === 0 ? 'passed' : 'failed',
      backend,
      candidates: parsed.candidates,
      diagnostics: parsed.diagnostics,
      durationMs: result.durationMs,
      ...(result.sandboxBackend ? { sandboxBackend: result.sandboxBackend } : {}),
      ...(result.errorMessage ? { error: result.errorMessage } : {}),
    });
  } catch (error) {
    return invalidResult(backend, error instanceof Error ? error.message : String(error));
  } finally {
    if (requestPath) fs.rmSync(requestPath, { force: true });
  }
}

/** Adapt the command backend to the proof-loop provider contract. A provider
 * is idle on the first attempt, where no compiler goal exists yet. */
export const createLeanEvalStructuredSearchProvider = (
  config: LeanEvalStructuredSearchConfig
): ((context: {
  workspaceRoot: string;
  previousError?: string;
  openGoal?: string;
  openGoalCount?: number;
  proofStateFingerprint?: string;
  signal?: AbortSignal;
  remainingMs: number;
}) => Promise<LeanEvalProofAttempt | undefined>) => {
  type CandidateCacheEntry = {
    candidates: readonly LeanEvalStructuredSearchCandidate[];
    index: number;
  };
  type InFlightSearch = {
    key: string;
    controller: AbortController;
    subscribers: Set<symbol>;
    settled: boolean;
    promise: Promise<readonly LeanEvalStructuredSearchCandidate[]>;
  };
  const candidateCache = new Map<string, CandidateCacheEntry>();
  const inFlightSearches = new Map<string, InFlightSearch>();
  const cacheKeyFor = (workspaceRoot: string, goal: string, proofStateFingerprint?: string): string =>
    `${path.resolve(workspaceRoot)}\0${sha256(`${goal}\0${proofStateFingerprint ?? ''}`)}`;

  const awaitSharedSearch = (
    entry: InFlightSearch,
    signal?: AbortSignal
  ): Promise<readonly LeanEvalStructuredSearchCandidate[]> => {
    if (signal?.aborted) return Promise.reject(signal.reason ?? new Error('Structured search request was cancelled'));
    const subscriber = Symbol('structured-search-subscriber');
    entry.subscribers.add(subscriber);
    return new Promise<readonly LeanEvalStructuredSearchCandidate[]>((resolve, reject) => {
      let settled = false;
      const cleanup = (): void => {
        signal?.removeEventListener('abort', onAbort);
      };
      const finish = (callback: () => void): void => {
        if (settled) return;
        settled = true;
        cleanup();
        callback();
      };
      const onAbort = (): void => {
        finish(() => reject(signal?.reason ?? new Error('Structured search request was cancelled')));
      };
      signal?.addEventListener('abort', onAbort, { once: true });
      entry.promise.then(
        (candidates) => finish(() => resolve(candidates)),
        (error) => finish(() => reject(error))
      );
    }).finally(() => {
      entry.subscribers.delete(subscriber);
      if (!entry.settled && entry.subscribers.size === 0) {
        if (inFlightSearches.get(entry.key) === entry) inFlightSearches.delete(entry.key);
        entry.controller.abort();
      }
    });
  };

  return async (context) => {
    const goal = (context.openGoal ?? context.previousError)?.trim();
    const workspaceKey = `${path.resolve(context.workspaceRoot)}\0`;
    if (!goal) {
      for (const key of candidateCache.keys()) {
        if (key.startsWith(workspaceKey)) candidateCache.delete(key);
      }
      return undefined;
    }
    // The rendered goal alone is not a complete state identity: local
    // hypotheses and elaborator progress can change while the target text
    // remains identical. Never reuse candidates across those states.
    const cacheKey = cacheKeyFor(context.workspaceRoot, goal, context.proofStateFingerprint);
    const cached = candidateCache.get(cacheKey);
    if (cached) {
      if (cached.index >= cached.candidates.length) return undefined;
      const candidate = cached.candidates[cached.index];
      cached.index += 1;
      return candidate;
    }
    let inFlight = inFlightSearches.get(cacheKey);
    if (!inFlight) {
      const controller = new AbortController();
      let entry!: InFlightSearch;
      const promise = runLeanEvalStructuredSearch({
        workspaceRoot: context.workspaceRoot,
        goal,
        ...(context.previousError ? { diagnostic: context.previousError } : {}),
        ...(context.openGoalCount !== undefined ? { openGoalCount: context.openGoalCount } : {}),
        ...(context.proofStateFingerprint ? { proofStateFingerprint: context.proofStateFingerprint } : {}),
        transport: config.transport ?? 'request-file',
        backend: config.backend,
        executable: config.executable,
        ...(config.args ? { args: config.args } : {}),
        ...(config.requestFileFlag ? { requestFileFlag: config.requestFileFlag } : {}),
        // Subscribers enforce their own proof-loop deadlines. The shared
        // process gets the full backend budget so one short-lived caller
        // cannot time out a concurrent caller with a longer deadline.
        timeoutMs: context.signal ? MAX_TIMEOUT_MS : Math.max(1_000, Math.min(context.remainingMs, MAX_TIMEOUT_MS)),
        signal: controller.signal,
      }).then((result) => result.candidates);
      entry = {
        key: cacheKey,
        controller,
        subscribers: new Set(),
        settled: false,
        promise: promise.finally(() => {
          entry.settled = true;
          if (inFlightSearches.get(cacheKey) === entry) inFlightSearches.delete(cacheKey);
        }),
      };
      inFlightSearches.set(cacheKey, entry);
      // A caller may cancel before the backend resolves. Keep the shared
      // promise observed so a later rejection cannot become unhandled.
      void entry.promise.catch(() => {});
      inFlight = entry;
    }
    const candidates = await awaitSharedSearch(inFlight, context.signal);
    const cachedAfterSearch = candidateCache.get(cacheKey);
    if (cachedAfterSearch) {
      if (cachedAfterSearch.index >= cachedAfterSearch.candidates.length) return undefined;
      const candidate = cachedAfterSearch.candidates[cachedAfterSearch.index];
      cachedAfterSearch.index += 1;
      return candidate;
    }
    candidateCache.set(cacheKey, { candidates, index: candidates.length > 0 ? 1 : 0 });
    while (candidateCache.size > 32) candidateCache.delete(candidateCache.keys().next().value as string);
    return candidates[0];
  };
};

export const leanEvalStructuredSearchRequestHash = (request: LeanEvalStructuredSearchRequest): string =>
  sha256(
    JSON.stringify({
      backend: request.backend ?? 'custom',
      executable: request.executable,
      args: request.args ?? [],
      requestFileFlag: request.requestFileFlag ?? DEFAULT_REQUEST_FLAG,
      projectRelative: request.projectRelative ?? '',
      sourceFile: request.sourceFile ?? 'Submission.lean',
      goal: request.goal,
      transport: request.transport ?? 'request-file',
      diagnostic: request.diagnostic ?? '',
      openGoalCount: request.openGoalCount ?? 0,
      proofStateFingerprint: request.proofStateFingerprint ?? '',
    })
  );
