import { resolveMathProofEnvironment } from "./mathProofEnvironment";
/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { classifyLeanEvalFailure } from "./leanEvalFailurePolicy";
import fs from 'node:fs';
import path from 'node:path';
import { runMathematicsSandboxedCommand, resolveMathematicsLakePackagesCache } from "./verifier";
import { resolveMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import type { SharedLeanPackagesLease } from "./leanSharedPackages";
import {
  isLeanDependencyBootstrapTransition,
  readLeanDependencyIdentity,
  type MathematicsLeanLspSession,
  type LeanDependencyIdentity,
} from "./leanLspSession";

export type LeanEvalLeanProbeRequest = Readonly<{
  /** Diagnostic reuse only; independent final verification never opts in. */
  reuseFailedChecks?: boolean;
  workspaceRoot: string;
  projectRelative?: string;
  sourceFile?: string;
  /** Runtime-owned source that must never be persisted as a candidate artifact. */
  sourceText?: string;
  /** Rebuild imports in a disposable snapshot, never in the editable workspace. */
  prepareLocalDependencies?: boolean;
  /** The disposable workspace owns its package copies; do not attach shared caches. */
  useWorkspacePackagesOnly?: boolean;
  /** Host-owned sealed package lease; never accepted from tool arguments. */
  sharedPackages?: SharedLeanPackagesLease;
  mode: 'compile' | 'check' | 'exact' | 'apply' | 'simp';
  expression?: string;
  importModules?: readonly string[];
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  persistentSession?: MathematicsLeanLspSession;
}>;

export type LeanEvalLeanProbeResult = Readonly<{
  status: 'passed' | 'failed' | 'unavailable' | 'invalid';
  cacheHit?: boolean;
  /** Whether the observation is a completed compiler result or an execution interruption. */
  executionDisposition: 'completed' | 'timed_out' | 'aborted' | 'unavailable' | 'invalid';
  mode: LeanEvalLeanProbeRequest['mode'];
  sourceFile: string;
  sourceOffset?: Readonly<{ line: number; column: number }>;
  sourceRange?: Readonly<{ start: { line: number; column: number }; end: { line: number; column: number } }>;
  firstGoal?: string;
  openGoals?: readonly string[];
  goalLocations?: readonly Readonly<{
    localIndex: number;
    line?: number;
    range?: LeanEvalLeanProbeResult['sourceRange'];
  }>[];
  localContextHash?: string;
  diagnostics: string;
  proofStateFingerprint: string;
  durationMs: number;
  /** Environment identity captured before and after this check. */
  environmentFingerprint?: string;
  sandboxBackend?: 'unshare' | 'bwrap' | 'docker' | 'podman';
  error?: string;
  transport?: 'lean-lsp' | 'lean-cli';
  transportFallbackReason?: string;
  hasHardErrors?: boolean;
}>;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');
const failedCheckCache = new Map<string, LeanEvalLeanProbeResult>();
const MAX_FAILED_CHECK_CACHE_ENTRIES = 64;
/** Conservative extra identity for diagnostic reuse, independent of the LSP hot identity.
 * Include build outputs and ignored source directories; uncertainty disables reuse.
 * Values are hashed locally and are never included in tool diagnostics.
 */
const failedCheckEnvironmentIdentity = (request: LeanEvalLeanProbeRequest, projectRoot: string): string | undefined => {
  try {
    const env = { ...process.env, ...resolveMathematicsRuntimeEnvironment(request.env || process.env) };
    const hash = crypto.createHash('sha256');
    hash.update(JSON.stringify(Object.entries(env).sort(([left], [right]) => left.localeCompare(right))));
    let entries = 0;
    const seen = new Set<string>();
    const visit = (file: string): void => {
      if (++entries > 1024) throw new Error('Diagnostic cache identity scan limit');
      let stat: fs.BigIntStats;
      try {
        stat = fs.lstatSync(file, { bigint: true });
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
          hash.update(`missing:${file}`);
          return;
        }
        throw error;
      }
      if (stat.isSymbolicLink()) throw new Error('Diagnostic cache dependency symlink');
      hash.update(file);
      if (stat.isDirectory()) {
        if (seen.has(file)) return;
        seen.add(file);
        for (const name of fs.readdirSync(file).sort()) {
          if (name === '.git' || name === '.deepscientist') continue;
          visit(path.join(file, name));
        }
      } else if (stat.isFile()) {
        hash.update([stat.dev, stat.ino, stat.mode, stat.size, stat.mtimeNs, stat.ctimeNs].join(':'));
      } else throw new Error('Diagnostic cache dependency is not a regular file');
    };
    visit(projectRoot);
    const mountedPackages =
      request.lakePackagesPath ||
      (!request.useWorkspacePackagesOnly ? resolveMathematicsLakePackagesCache(projectRoot, env) : undefined);
    const sealed = resolveMathProofEnvironment(projectRoot, env);
    if (sealed) {
      if (mountedPackages !== sealed.packagesRoot) throw new Error('Diagnostic cache sealed package mismatch');
      hash.update(sealed.identity);
    } else if (mountedPackages) visit(path.resolve(mountedPackages));
    const elanRoots = [
      env.ELAN_HOME || (env.HOME ? path.join(env.HOME, '.elan') : undefined),
      ...(env.DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS ?? '').split(path.delimiter),
    ].filter((root): root is string => Boolean(root));
    let pinnedToolchain = env.ELAN_TOOLCHAIN;
    try {
      pinnedToolchain ||= fs.readFileSync(path.join(projectRoot, 'lean-toolchain'), 'utf8').trim();
    } catch {
      /* Standalone probes can use PATH. */
    }
    const executableIdentity = (file: string): void => {
      try {
        hash.update(file);
        visit(fs.realpathSync(file));
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code === 'ENOENT') hash.update(`missing:${file}`);
        else throw error;
      }
    };
    // Fixed Lean installations are trusted runtime inputs. Bind the selected
    // executable and selector configuration, not unrelated installed versions.
    for (const root of elanRoots) {
      visit(path.join(root, 'settings.toml'));
      for (const command of ['lean', 'lake', 'elan']) executableIdentity(path.join(root, 'bin', command));
      if (pinnedToolchain && /^[A-Za-z0-9_./:+-]+$/u.test(pinnedToolchain) && !pinnedToolchain.includes('..')) {
        const directory = pinnedToolchain.replaceAll('/', '--').replaceAll(':', '---');
        for (const command of ['lean', 'lake'])
          executableIdentity(path.join(root, 'toolchains', directory, 'bin', command));
      }
    }
    for (const command of ['lean', 'lake', 'elan', 'bwrap', 'unshare']) {
      for (const directory of (env.PATH ?? '').split(path.delimiter).filter(Boolean)) {
        const executable = path.resolve(directory, command);
        try {
          if (!fs.statSync(executable).isFile()) continue;
          hash.update(executable);
          visit(fs.realpathSync(executable));
          break;
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
        }
      }
    }
    return hash.digest('hex');
  } catch {
    return undefined;
  }
};

const MAX_PROBE_SOURCE_BYTES = 16 * 1024 * 1024;
const MAX_PROBE_EXPRESSION_CHARS = 12_000;
const safeRelative = (value: string): string => {
  const normalized = value.trim().replaceAll('\\', '/').replace(/^\.\//u, '');
  if (
    !normalized ||
    normalized.includes('\0') ||
    normalized.startsWith('/') ||
    /^[A-Za-z]:/u.test(normalized) ||
    normalized.split('/').some((part) => !part || part === '.' || part === '..')
  ) {
    throw new Error('Lean probe sourceFile must be workspace-relative');
  }
  return normalized;
};

/** Walk a workspace-relative path without following a symlink at any level.
 * The final component may be absent for runtime-owned source text, but every
 * existing parent must still be a real directory. */
const assertNoSymlinkPath = (
  root: string,
  relative: string,
  options: Readonly<{ allowMissingLeaf?: boolean; leafKind?: 'file' | 'directory' }> = {}
): fs.Stats | undefined => {
  let cursor = root;
  const segments = relative ? relative.split('/') : [];
  for (const [index, segment] of segments.entries()) {
    cursor = path.join(cursor, segment);
    let stat: fs.Stats;
    try {
      stat = fs.lstatSync(cursor);
    } catch (error) {
      if (
        options.allowMissingLeaf === true &&
        index === segments.length - 1 &&
        (error as NodeJS.ErrnoException).code === 'ENOENT'
      ) {
        return undefined;
      }
      throw error;
    }
    if (stat.isSymbolicLink()) throw new Error(`Lean probe path contains a symbolic link: ${segment}`);
    if (index < segments.length - 1 && !stat.isDirectory()) {
      throw new Error('Lean probe path contains a non-directory parent');
    }
    if (index === segments.length - 1 && options.leafKind === 'directory' && !stat.isDirectory()) {
      throw new Error('Lean probe project is not a regular directory');
    }
    if (index === segments.length - 1 && options.leafKind === 'file' && !stat.isFile()) {
      throw new Error('Lean probe source is not a regular file');
    }
  }
  return segments.length ? fs.lstatSync(cursor) : fs.lstatSync(root);
};

/** Create runtime metadata directories one component at a time so an existing
 * symlink cannot redirect probe output outside the selected project. */
const ensureNoSymlinkDirectory = (root: string, relative: string): void => {
  let cursor = root;
  for (const segment of relative.split('/')) {
    cursor = path.join(cursor, segment);
    try {
      const stat = fs.lstatSync(cursor);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error('Lean probe runtime metadata directory is not a regular directory');
      }
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
      fs.mkdirSync(cursor, { mode: 0o700 });
      const stat = fs.lstatSync(cursor);
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error('Lean probe runtime metadata directory is not a regular directory', { cause: error });
      }
    }
  }
};

const diagnosticOffset = (output: string): Readonly<{ line: number; column: number }> | undefined => {
  const match = /(?:^|\n)[^\n:]+:(\d+):(\d+):\s*(?:error|warning):/u.exec(output);
  if (!match) return undefined;
  return { line: Number(match[1]), column: Number(match[2]) };
};

/** Keep diagnostic content and source locations while omitting CLI presentation metadata. */
const compactLeanProbeDiagnostics = (output: string): string =>
  output
    .split(/\r?\n/u)
    .map((line) => {
      try {
        const value = JSON.parse(line) as Record<string, unknown>;
        if (
          !value ||
          typeof value.data !== 'string' ||
          !['error', 'warning', 'information'].includes(String(value.severity))
        )
          return line;
        return JSON.stringify({
          severity: value.severity,
          ...(value.fileName !== undefined ? { fileName: value.fileName } : {}),
          ...(value.pos !== undefined ? { pos: value.pos } : {}),
          ...(value.endPos !== undefined ? { endPos: value.endPos } : {}),
          data: value.data,
        });
      } catch {
        return line;
      }
    })
    .join('\n');

/** Decode CLI diagnostics, preserving every reported goal and its local context. */
export function inspectLeanProbeDiagnostics(output: string) {
  const messages: Array<{
    data: string;
    offset?: Readonly<{ line: number; column: number }>;
    range?: LeanEvalLeanProbeResult['sourceRange'];
  }> = [];
  for (const line of output.split(/\r?\n/u)) {
    try {
      const value = JSON.parse(line) as Record<string, unknown>;
      if (value && typeof value.data === 'string' && value.severity === 'error') {
        const pos = value.pos as { line?: unknown; column?: unknown } | undefined;
        const endPos = value.endPos as { line?: unknown; column?: unknown } | undefined;
        const messageOffset =
          typeof pos?.line === 'number' && typeof pos.column === 'number'
            ? { line: pos.line, column: pos.column }
            : undefined;
        const messageRange =
          /^unsolved goals\b/u.test(value.data) &&
          messageOffset &&
          typeof endPos?.line === 'number' &&
          typeof endPos.column === 'number'
            ? {
                start: messageOffset,
                end: { line: endPos.line, column: endPos.column },
              }
            : undefined;
        messages.push({
          data: value.data,
          ...(messageOffset ? { offset: messageOffset } : {}),
          ...(messageRange ? { range: messageRange } : {}),
        });
      }
    } catch {
      // Plain diagnostics remain supported for older Lean and wrapper scripts.
    }
  }
  // Lean can emit independent declarations' diagnostics in either order.
  // Keep goal indices tied to source positions so a selected goal stays stable.
  messages.sort(
    (left, right) =>
      (left.offset?.line ?? Number.POSITIVE_INFINITY) - (right.offset?.line ?? Number.POSITIVE_INFINITY) ||
      (left.offset?.column ?? Number.POSITIVE_INFINITY) - (right.offset?.column ?? Number.POSITIVE_INFINITY)
  );
  const offset = messages.find((message) => message.offset)?.offset;
  const sourceRange = messages.find((message) => message.range)?.range;
  const diagnosticBlocks = messages.length ? messages : [{ data: output }];
  const normalized = diagnosticBlocks
    .map((message) => message.data)
    .join('\n\n')
    .replace(/^.*?:\d+:\d+:\s*(?:error|warning|information):\s*/gmu, '')
    .trim();
  const goals: string[] = [];
  const goalLocations: NonNullable<LeanEvalLeanProbeResult['goalLocations']>[number][] = [];
  const contexts: string[] = [];
  for (const message of diagnosticBlocks) {
    let localIndex = 0;
    const messageText = message.data.replace(/^.*?:\d+:\d+:\s*(?:error|warning|information):\s*/gmu, '').trim();
    for (const block of messageText.split(/\n\s*\n|(?=^case\s)/mu)) {
      const lines = block
        .replace(/^unsolved goals\s*\n?/u, '')
        .trim()
        .split('\n');
      const markers = lines.flatMap((line, index) => (/^\s*(?:⊢|\|-)/u.test(line) ? [index] : []));
      for (const [index, marker] of markers.entries()) {
        const context = lines.slice(0, markers[0]).join('\n').trim();
        const target = lines
          .slice(marker, markers[index + 1] ?? lines.length)
          .join('\n')
          .trim();
        contexts.push(context);
        goals.push([context, target].filter(Boolean).join('\n'));
        goalLocations.push({
          localIndex: localIndex++,
          ...(message.offset ? { line: message.offset.line } : {}),
          ...(message.range ? { range: message.range } : {}),
        });
      }
    }
  }
  return Object.freeze({
    openGoals: Object.freeze(goals),
    goalLocations: Object.freeze(goalLocations),
    localContextHash: sha256(JSON.stringify(contexts)),
    semanticFingerprint: sha256(JSON.stringify({ goals, diagnostics: normalized })),
    hasHardErrors: diagnosticBlocks.some((message) => !/^unsolved goals(?:\s|$)/u.test(message.data.trim())),
    ...((offset ?? diagnosticOffset(output)) ? { sourceOffset: offset ?? diagnosticOffset(output) } : {}),
    ...(sourceRange ? { sourceRange } : {}),
  });
}

const probeSource = (request: LeanEvalLeanProbeRequest, source: string): string => {
  const imports = [
    ...new Set((request.importModules ?? []).filter((item) => /^[A-Za-z][A-Za-z0-9_.]*$/u.test(item))),
  ].slice(0, 16);
  const header = imports.length ? `${imports.map((item) => `import ${item}`).join('\n')}\n` : '';
  const expression = (request.expression ?? '').trim();
  if (request.mode === 'compile') return source;
  if (!expression) throw new Error(`${request.mode} probe requires expression`);
  // Keep declarations and imports from the selected source file in scope so
  // probes test the target project's environment rather than a bare scratch
  // expression. The source remains runtime-owned and is never returned as an
  // artifact.
  const context = source.trimEnd() ? `${source.trimEnd()}\n` : '';
  const prefix = `${header}${context}`;
  if (request.mode === 'check') return `${prefix}#check ${expression}\n`;
  if (request.mode === 'exact') return `${prefix}example : ${expression} := by\n  exact?\n`;
  if (request.mode === 'apply') return `${prefix}example : ${expression} := by\n  apply?\n`;
  return `${prefix}example : ${expression} := by\n  simp?\n`;
};

/** Execute one bounded, runtime-owned Lean probe in the candidate sandbox. */
export async function runLeanEvalLeanProbe(request: LeanEvalLeanProbeRequest): Promise<LeanEvalLeanProbeResult> {
  const mode = request.mode;
  // The probe budget covers source preparation, LSP work, and any CLI fallback.
  // Use the monotonic clock so wall-clock adjustments cannot extend a request.
  const requestStartedAt = performance.now();
  const deadlineAt = requestStartedAt + Math.max(1, Math.floor(request.timeoutMs ?? 120_000));
  const remainingBudgetMs = (): number | undefined =>
    deadlineAt === undefined ? undefined : Math.max(0, deadlineAt - performance.now());
  const requestedSourceFile = request.sourceFile ?? 'Submission.lean';
  let sourceFile: string;
  try {
    sourceFile = safeRelative(requestedSourceFile);
  } catch (error) {
    const displayedSourceFile = requestedSourceFile.trim().replaceAll('\\', '/').slice(0, 1024) || '<invalid>';
    return Object.freeze({
      status: 'invalid',
      executionDisposition: 'invalid',
      mode,
      sourceFile: displayedSourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256(`invalid:source-file:${displayedSourceFile}`),
      durationMs: 0,
      error: error instanceof Error ? error.message : String(error),
    });
  }
  if (sourceFile === 'Solution.lean' || sourceFile.endsWith('/Solution.lean')) {
    return Object.freeze({
      status: 'invalid',
      executionDisposition: 'invalid',
      mode,
      sourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256('invalid:protected-source'),
      durationMs: 0,
      error: 'Protected Solution.lean is not a probe input',
    });
  }
  const checkoutRoot = path.resolve(request.workspaceRoot);
  const projectRelative = (request.projectRelative ?? '').trim().replaceAll('\\', '/');
  if (
    projectRelative.includes('\0') ||
    projectRelative.startsWith('/') ||
    /^[A-Za-z]:/u.test(projectRelative) ||
    (projectRelative && projectRelative.split('/').some((part) => !part || part === '.' || part === '..'))
  ) {
    return Object.freeze({
      status: 'invalid',
      executionDisposition: 'invalid',
      mode,
      sourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256('invalid:path'),
      durationMs: 0,
      error: 'Lean probe project path must be repository-relative',
    });
  }
  const projectRoot = path.join(checkoutRoot, projectRelative);
  const sourcePath = path.join(projectRoot, sourceFile);
  const environmentOptions = {
    workspaceRoot: checkoutRoot,
    ...(projectRelative ? { projectRelative } : {}),
    sourceFile,
    ...(request.env ? { env: request.env } : {}),
    ...(request.lakePackagesPath ? { lakePackagesPath: request.lakePackagesPath } : {}),
  } as const;
  try {
    const checkoutStat = fs.lstatSync(checkoutRoot);
    if (checkoutStat.isSymbolicLink() || !checkoutStat.isDirectory()) {
      throw new Error('Lean probe checkout is not a regular directory');
    }
    assertNoSymlinkPath(checkoutRoot, projectRelative, { leafKind: 'directory' });
    const sourceStat = assertNoSymlinkPath(projectRoot, sourceFile, {
      allowMissingLeaf: request.sourceText !== undefined,
      leafKind: request.sourceText === undefined ? 'file' : undefined,
    });
    if (request.sourceText !== undefined && sourceStat && !sourceStat.isFile()) {
      throw new Error('Lean probe source is not a regular file');
    }
    if (sourceStat && sourceStat.size > MAX_PROBE_SOURCE_BYTES) {
      throw new Error(`Lean probe source exceeds the ${MAX_PROBE_SOURCE_BYTES}-byte limit`);
    }
    if (request.sourceText !== undefined && Buffer.byteLength(request.sourceText, 'utf8') > MAX_PROBE_SOURCE_BYTES) {
      throw new Error(`Lean probe source exceeds the ${MAX_PROBE_SOURCE_BYTES}-byte limit`);
    }
    if (request.mode !== 'compile' && (request.expression ?? '').length > MAX_PROBE_EXPRESSION_CHARS) {
      throw new Error(`Lean probe expression exceeds the ${MAX_PROBE_EXPRESSION_CHARS}-character limit`);
    }
  } catch (error) {
    return Object.freeze({
      status: 'invalid',
      executionDisposition: 'invalid',
      mode,
      sourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256('invalid:missing'),
      durationMs: 0,
      error: error instanceof Error ? error.message : String(error),
    });
  }
  const environmentBefore: LeanDependencyIdentity = readLeanDependencyIdentity(environmentOptions);
  if (environmentBefore.status === 'unavailable') {
    return Object.freeze({
      status: 'unavailable',
      executionDisposition: 'unavailable',
      mode,
      sourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256('environment-unavailable-before-check'),
      durationMs: 0,
      error: `Lean probe dependency environment is unavailable: ${environmentBefore.reason}`,
    });
  }
  const probeRelative = `.deepscientist/lean-probe/${crypto.randomUUID()}.lean`;
  const probePath = path.join(projectRoot, probeRelative);
  const probeDirectory = path.dirname(probePath);
  const metadataDirectory = path.dirname(probeDirectory);
  const probeDirectoryExisted = fs.existsSync(probeDirectory);
  const metadataDirectoryExisted = fs.existsSync(metadataDirectory);
  try {
    ensureNoSymlinkDirectory(projectRoot, '.deepscientist/lean-probe');
    const source = request.sourceText === undefined ? fs.readFileSync(sourcePath, 'utf8') : request.sourceText;
    const compiledSource = probeSource(request, source);
    const reuseEnvironment = request.reuseFailedChecks
      ? failedCheckEnvironmentIdentity(request, projectRoot)
      : undefined;
    const failureCacheKey =
      request.reuseFailedChecks && reuseEnvironment
        ? sha256(
            JSON.stringify([
              checkoutRoot,
              projectRelative,
              sourceFile,
              compiledSource,
              mode,
              environmentBefore.fingerprint,
              reuseEnvironment,
              request.prepareLocalDependencies,
              request.useWorkspacePackagesOnly,
            ])
          )
        : undefined;
    const cachedFailure = failureCacheKey ? failedCheckCache.get(failureCacheKey) : undefined;
    if (
      cachedFailure &&
      !request.signal?.aborted &&
      (request.timeoutMs === undefined ||
        (Number.isFinite(request.timeoutMs) && request.timeoutMs > 0 && remainingBudgetMs()! > 0))
    ) {
      failedCheckCache.delete(failureCacheKey!);
      failedCheckCache.set(failureCacheKey!, cachedFailure);
      return Object.freeze({ ...cachedFailure, cacheHit: true, durationMs: 0 });
    }
    fs.writeFileSync(probePath, compiledSource, { encoding: 'utf8', mode: 0o600 });
    const requestedTimeoutMs = request.timeoutMs;
    const initialRemainingMs = remainingBudgetMs();
    if (requestedTimeoutMs !== undefined && (!Number.isFinite(requestedTimeoutMs) || requestedTimeoutMs <= 0)) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'timed_out',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('timed-out-before-execution'),
        durationMs: 0,
        error: 'Lean probe deadline expired before execution',
      });
    }
    if (initialRemainingMs !== undefined && initialRemainingMs <= 0) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'timed_out',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('timed-out-before-execution'),
        durationMs: Math.max(0, performance.now() - requestStartedAt),
        error: 'Lean probe deadline expired before execution',
      });
    }
    const callTimeoutMs = Math.max(1, Math.min(Math.floor(initialRemainingMs ?? 120_000), 120_000));
    const startedAt = performance.now();
    const persistent =
      request.persistentSession && mode === 'compile'
        ? await request.persistentSession.compile(compiledSource, callTimeoutMs, request.signal)
        : undefined;
    const persistentDurationMs = Math.max(0, performance.now() - startedAt);
    const persistentDisposition = request.persistentSession?.fallbackDisposition;
    if (persistent === undefined && (request.signal?.aborted || persistentDisposition === 'aborted')) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'aborted',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('aborted'),
        durationMs: persistentDurationMs,
        error: 'Lean probe request was aborted before fallback execution',
      });
    }
    const remainingTimeoutMs = remainingBudgetMs() ?? Math.max(0, callTimeoutMs - (performance.now() - startedAt));
    if (persistent === undefined && persistentDisposition === 'timed_out') {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'timed_out',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('timed-out-in-lsp'),
        durationMs: performance.now() - startedAt,
        error: request.persistentSession?.fallbackReason || 'Lean LSP request timed out',
      });
    }
    if (request.persistentSession && persistent?.exitCode === 0 && remainingTimeoutMs === 0) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'timed_out',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('timed-out-before-cli-confirmation'),
        durationMs: performance.now() - startedAt,
        error: 'Lean probe deadline expired before CLI confirmation',
      });
    }
    if (request.persistentSession && persistent === undefined && remainingTimeoutMs === 0) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'timed_out',
        mode,
        sourceFile,
        diagnostics: '',
        proofStateFingerprint: sha256('timed-out-before-cli-fallback'),
        durationMs: performance.now() - startedAt,
        error: 'Lean probe deadline expired before CLI fallback',
      });
    }
    // A server's empty diagnostics are useful construction feedback, but a
    // closed state must also pass the ordinary compiler before being committed.
    const usesCli = !(persistent && persistent.exitCode !== 0);
    const result = usesCli
      ? await runMathematicsSandboxedCommand({
          checkoutRoot,
          projectRelative,
          command: 'lake',
          args: request.prepareLocalDependencies
            ? ['--no-cache', 'lean', probeRelative, '--', '-j', '1', '--json']
            : ['env', 'lean', '-j', '1', '--json', probeRelative],
          timeoutMs: request.persistentSession ? Math.max(1, remainingTimeoutMs) : callTimeoutMs,
          signal: request.signal,
          env: request.env,
          useWorkspacePackagesOnly: request.useWorkspacePackagesOnly,
          sharedPackages: request.sharedPackages,
          ...(request.lakePackagesPath ? { lakePackagesPath: request.lakePackagesPath } : {}),
        })
      : persistent;
    // The transports run sequentially. Preserve the command's measured time,
    // and include any LSP work that happened before CLI fallback/confirmation.
    const executionDurationMs = Math.max(
      performance.now() - startedAt,
      usesCli ? persistentDurationMs + result.durationMs : result.durationMs
    );
    const fullDiagnostics = `${result.stderr || ''}\n${result.stdout || ''}`.trim();
    const diagnostics = compactLeanProbeDiagnostics(fullDiagnostics).slice(-16_000);
    const inspected = inspectLeanProbeDiagnostics(fullDiagnostics);
    const goal = inspected.openGoals[0];
    const offset = inspected.sourceOffset;
    const completed =
      result.started === true &&
      result.exitCode !== null &&
      result.signal == null &&
      result.timedOut !== true &&
      result.aborted !== true &&
      result.errorCode === undefined;
    const unavailable = !completed;
    const executionDisposition = result.timedOut
      ? 'timed_out'
      : result.aborted
        ? 'aborted'
        : unavailable
          ? 'unavailable'
          : 'completed';
    const environmentAfter = readLeanDependencyIdentity(environmentOptions);
    if (environmentAfter.status === 'unavailable') {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'unavailable',
        mode,
        sourceFile,
        diagnostics,
        proofStateFingerprint: sha256('environment-unavailable-after-check'),
        durationMs: executionDurationMs,
        error: `Lean probe dependency environment became unavailable after checking: ${environmentAfter.reason}`,
      });
    }
    if (
      environmentAfter.fingerprint !== environmentBefore.fingerprint &&
      !isLeanDependencyBootstrapTransition(environmentBefore, environmentAfter)
    ) {
      return Object.freeze({
        status: 'unavailable',
        executionDisposition: 'unavailable',
        mode,
        sourceFile,
        diagnostics,
        proofStateFingerprint: sha256('environment-changed-during-check'),
        durationMs: executionDurationMs,
        error: 'Lean probe dependency environment changed during checking',
      });
    }
    const observation: LeanEvalLeanProbeResult = Object.freeze({
      status: unavailable ? 'unavailable' : result.exitCode === 0 ? 'passed' : 'failed',
      executionDisposition,
      transport: persistent && persistent.exitCode !== 0 ? 'lean-lsp' : 'lean-cli',
      ...(request.persistentSession?.fallbackReason
        ? { transportFallbackReason: request.persistentSession.fallbackReason }
        : {}),
      mode,
      sourceFile,
      ...(offset ? { sourceOffset: offset } : {}),
      ...(inspected.sourceRange ? { sourceRange: inspected.sourceRange } : {}),
      ...(goal ? { firstGoal: goal } : {}),
      openGoals: inspected.openGoals,
      goalLocations: inspected.goalLocations,
      localContextHash: inspected.localContextHash,
      hasHardErrors: inspected.hasHardErrors,
      diagnostics,
      proofStateFingerprint: sha256(`${mode}\0${result.exitCode}\0${inspected.semanticFingerprint}`),
      durationMs: executionDurationMs,
      environmentFingerprint: environmentAfter.fingerprint,
      ...(result.sandboxBackend ? { sandboxBackend: result.sandboxBackend } : {}),
      ...(result.errorMessage ? { error: result.errorMessage } : {}),
    });
    if (
      failureCacheKey &&
      reuseEnvironment === failedCheckEnvironmentIdentity(request, projectRoot) &&
      !request.signal?.aborted &&
      observation.status === 'failed' &&
      observation.executionDisposition === 'completed' &&
      Buffer.byteLength(JSON.stringify(observation), 'utf8') <= 128 * 1024 &&
      environmentBefore.fingerprint === environmentAfter.fingerprint &&
      classifyLeanEvalFailure(observation.error || diagnostics) === 'actual_proof_failure' &&
      /unsolved goals|type mismatch|unknown identifier|unexpected token|application type mismatch|tactic.*failed|maximum.*heartbeats|deterministic timeout|maximum recursion depth/iu.test(
        diagnostics
      )
    ) {
      failedCheckCache.set(failureCacheKey, observation);
      while (failedCheckCache.size > MAX_FAILED_CHECK_CACHE_ENTRIES)
        failedCheckCache.delete(failedCheckCache.keys().next().value!);
    }
    return observation;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const aborted = request.signal?.aborted === true;
    return Object.freeze({
      status: 'unavailable',
      executionDisposition: aborted ? 'aborted' : 'unavailable',
      mode,
      sourceFile,
      diagnostics: '',
      proofStateFingerprint: sha256('exception'),
      durationMs: 0,
      error: message,
    });
  } finally {
    fs.rmSync(probePath, { force: true });
    if (!probeDirectoryExisted) {
      try {
        fs.rmdirSync(probeDirectory);
      } catch {
        // Another concurrent probe may still own the directory.
      }
    }
    if (!metadataDirectoryExisted) {
      try {
        fs.rmdirSync(metadataDirectory);
      } catch {
        // Preserve nonempty runtime metadata and concurrent probes.
      }
    }
  }
}
