/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import crypto from 'node:crypto';
import { MathematicsLeanLspSession } from "./leanLspSession";
import { archiveLeanProofActions } from "./leanProofActionArchive";
import {
  inspectLeanDeclarations,
  inspectLeanDeclarationRegions,
  inspectLeanSource,
  stripLeanComments,
} from "./verifier";
import fs from 'node:fs';
import path from 'node:path';
import {
  normalizeMathProofAction,
  normalizeMathProofState,
  type MathProofAction,
  type MathProofActionKind,
  type MathProofState,
} from "../common/types/team/mathematicsTeam";
import { runLeanEvalLeanProbe, type LeanEvalLeanProbeResult } from "./leanEvalLeanProbe";

const MAX_SOURCE_BYTES = 16 * 1024 * 1024;
const MAX_ACTION_PAYLOAD = 16_000;
const ACTION_HISTORY_WINDOW = 512;
const DEFAULT_STATE_CACHE_ENTRIES = 128;
const DEFAULT_STATE_CACHE_BYTES = 32 * 1024 * 1024;
const DEFAULT_ACTION_RESULT_ENTRIES = 128;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value, 'utf8').digest('hex');

const normalizeProjectRelative = (value: string | undefined, field: string): string => {
  const normalized = (value ?? '').trim().replaceAll('\\', '/').replace(/^\.\//u, '');
  if (
    normalized &&
    (normalized.startsWith('/') ||
      /^[A-Za-z]:/u.test(normalized) ||
      normalized.split('/').some((part) => !part || part === '.' || part === '..'))
  ) {
    throw new Error(`Mathematics ${field} must be project-relative`);
  }
  return normalized;
};

const normalizeLeanSourceFile = (value: string | undefined): string => {
  const sourceFile = normalizeProjectRelative(value || 'Submission.lean', 'proof session sourceFile');
  if (!sourceFile || !sourceFile.toLowerCase().endsWith('.lean')) {
    throw new Error('Mathematics proof session sourceFile must be a Lean file');
  }
  if (sourceFile === 'Solution.lean' || sourceFile.endsWith('/Solution.lean')) {
    throw new Error('Protected Solution.lean is not a proof session input');
  }
  return sourceFile;
};

const sourceHash = (source: string): string => sha256(source);

const stateIdFor = (
  episodeId: string,
  source: string,
  goalFingerprint: string,
  parentStateId: string | undefined,
  actionCount: number
): string =>
  sha256(
    JSON.stringify({
      episodeId,
      sourceHash: sourceHash(source),
      goalFingerprint,
      parentStateId: parentStateId ?? null,
      actionCount,
    })
  );

export type MathematicsLeanSessionOptions = Readonly<{
  workspaceRoot: string;
  projectRelative?: string;
  sourceFile?: string;
  sourceText?: string;
  contractSource?: string;
  statementHash: string;
  routeFingerprint: string;
  planId?: string;
  episodeId?: string;
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  cacheLimits?: Readonly<{
    stateEntries?: number;
    stateBytes?: number;
    actionResults?: number;
  }>;
}>;

export type MathematicsLeanSessionSnapshot = Readonly<{
  state: MathProofState;
  sourceText: string;
}>;

export type MathematicsLeanStateFeedback = Readonly<{
  state: MathProofState;
  sourceText: string;
  diagnostics: string | null;
  goalLine: number | null;
  goalRange: LeanEvalLeanProbeResult['sourceRange'] | null;
  goalLocations: LeanEvalLeanProbeResult['goalLocations'] | null;
  environmentFingerprint: string | null;
}>;

export type MathematicsLeanSessionActionResult = Readonly<{
  status: 'advanced' | 'unchanged' | 'failed' | 'unavailable' | 'invalid' | 'duplicate' | 'restored' | 'branched';
  state?: MathProofState;
  action?: MathProofAction;
  branchId?: string;
  diagnostics: string;
  transport?: 'lean-lsp' | 'lean-cli';
  transportFallbackReason?: string;
  goalDisplayTruncated?: boolean;
  durationMs?: number;
  capabilityAdded?: boolean;
  recoveredFromJournal?: boolean;
  cacheHit?: boolean;
  reuseKind?: 'hot' | 'replayed';
  underlyingStatus?: Exclude<MathematicsLeanSessionActionResult['status'], 'duplicate'>;
  executionDisposition?: LeanEvalLeanProbeResult['executionDisposition'];
  environmentFingerprint?: string;
}>;

export type MathematicsLeanSessionCacheMetrics = Readonly<{
  stateEntries: number;
  stateBytes: number;
  actionResults: number;
  pinnedStates: number;
  evictedStates: number;
}>;

export type MathematicsLeanSessionStartResult = Readonly<{
  status: 'started' | 'unavailable' | 'invalid';
  session?: MathematicsLeanProofSession;
  state?: MathProofState;
  diagnostics: string;
  transport?: 'lean-lsp' | 'lean-cli';
  transportFallbackReason?: string;
  goalDisplayTruncated?: boolean;
  durationMs?: number;
  executionDisposition?: LeanEvalLeanProbeResult['executionDisposition'];
  environmentFingerprint?: string;
}>;

const openGoalsFromProbe = (probe: LeanEvalLeanProbeResult): readonly string[] =>
  Object.freeze(
    (probe.openGoals ?? (probe.firstGoal ? [probe.firstGoal] : [])).slice(0, 128).map((goal) => goal.slice(0, 4_000))
  );

const contextHashFromProbe = (probe: LeanEvalLeanProbeResult): string =>
  probe.localContextHash ?? sha256(probe.firstGoal ?? '');

const probeMetadata = (probe: LeanEvalLeanProbeResult) => ({
  durationMs: probe.durationMs,
  ...(probe.cacheHit ? { cacheHit: true } : {}),
  executionDisposition: probe.executionDisposition,
  transport: probe.transport,
  ...(probe.transportFallbackReason ? { transportFallbackReason: probe.transportFallbackReason } : {}),
  goalDisplayTruncated: Boolean(
    probe.openGoals && (probe.openGoals.length > 128 || probe.openGoals.some((goal) => goal.length > 4_000))
  ),
  ...(probe.environmentFingerprint ? { environmentFingerprint: probe.environmentFingerprint } : {}),
});

const deadlineFor = (timeoutMs: number | undefined): number | undefined => {
  if (timeoutMs === undefined) return undefined;
  if (!Number.isFinite(timeoutMs) || timeoutMs <= 0) return performance.now();
  return performance.now() + Math.floor(timeoutMs);
};

const remainingFor = (deadlineAt: number | undefined): number | undefined =>
  deadlineAt === undefined ? undefined : Math.max(0, deadlineAt - performance.now());

const interruptedCall = (
  signal: AbortSignal | undefined,
  deadlineAt: number | undefined
): MathematicsLeanSessionActionResult | undefined => {
  if (signal?.aborted)
    return Object.freeze({
      status: 'unavailable',
      executionDisposition: 'aborted',
      diagnostics: 'Mathematics proof session request was aborted',
      durationMs: 0,
    });
  if (remainingFor(deadlineAt) === 0)
    return Object.freeze({
      status: 'unavailable',
      executionDisposition: 'timed_out',
      diagnostics: 'Mathematics proof session request timed out',
      durationMs: 0,
    });
  return undefined;
};

const stateStatusFromProbe = (probe: LeanEvalLeanProbeResult): MathProofState['status'] => {
  if (probe.status === 'passed') return 'closed';
  if (probe.hasHardErrors) return 'failed';
  if (probe.firstGoal) return 'open';
  return 'failed';
};

const declarationKeys = (source: string): string[] =>
  inspectLeanDeclarations(source).map((declaration) =>
    JSON.stringify([declaration.name, declaration.kind, declaration.declarationType])
  );
const importLines = (source: string): string[] =>
  stripLeanComments(source)
    .split('\n')
    .filter((line) => /^\s*import\s/u.test(line))
    .map((line) => line.trim());

/** Preserve existing obligations while allowing new reusable declarations. */
const candidateContractError = (before: string, after: string): string | undefined => {
  const context = (source: string) => {
    source = stripLeanComments(source);
    let cursor = 0;
    const pieces: string[] = [];
    const declarations: string[] = [];
    const normalize = () =>
      pieces
        .join('\n')
        .split('\n')
        .filter((line) => !/^\s*import\s/u.test(line))
        .join('\n')
        .replace(/\s+/gu, ' ')
        .trim();
    for (const region of inspectLeanDeclarationRegions(source)) {
      if (region.startOffset < cursor) continue;
      pieces.push(source.slice(cursor, region.startOffset));
      declarations.push(JSON.stringify([region.name, region.declarationType, normalize()]));
      cursor = region.endOffset;
    }
    pieces.push(source.slice(cursor));
    return { text: normalize(), declarations };
  };
  const beforeContext = context(before);
  const afterContext = context(after);
  if (
    beforeContext.text !== afterContext.text ||
    beforeContext.declarations.some((entry) => !afterContext.declarations.includes(entry))
  )
    return 'Candidate changed the declaration context (namespace, variables, notation, or other commands).';
  const afterImports = importLines(after);
  if (importLines(before).some((line) => !afterImports.includes(line)))
    return 'Candidate removed or changed an existing import.';
  const afterRegions = inspectLeanDeclarationRegions(after);
  const beforeRegions = inspectLeanDeclarationRegions(before);
  for (const [index, declaration] of inspectLeanDeclarations(before).entries()) {
    if (declaration.kind === 'theorem') continue;
    const oldRegion = beforeRegions[index];
    const newRegion = afterRegions[afterContext.declarations.indexOf(beforeContext.declarations[index]!)];
    if (
      !oldRegion ||
      !newRegion ||
      (!inspectLeanSource(before.slice(oldRegion.bodyOffset, oldRegion.endOffset)).sorryCount &&
        !inspectLeanSource(before.slice(oldRegion.bodyOffset, oldRegion.endOffset)).admitCount &&
        before.slice(oldRegion.bodyOffset, oldRegion.endOffset).trim() !==
          after.slice(newRegion.bodyOffset, newRegion.endOffset).trim())
    )
      return 'Candidate changed an existing definition or instance body used by the original obligation.';
  }
  const remaining = declarationKeys(after);
  for (const declaration of declarationKeys(before)) {
    const index = remaining.indexOf(declaration);
    if (index < 0) return 'Candidate removed or changed an existing declaration; preserve the original obligation.';
    remaining.splice(index, 1);
  }
  for (const [index] of declarationKeys(after).entries()) {
    const region = afterRegions[index];
    if (!region) continue;
    const priorIndex = beforeContext.declarations.indexOf(afterContext.declarations[index]!);
    const priorRegion = priorIndex < 0 ? undefined : beforeRegions[priorIndex];
    const prior = inspectLeanSource(priorRegion ? before.slice(priorRegion.bodyOffset, priorRegion.endOffset) : '');
    const next = inspectLeanSource(after.slice(region.bodyOffset, region.endOffset));
    if (next.sorryCount > prior.sorryCount || next.admitCount > prior.admitCount)
      return 'Candidate introduced a placeholder in an existing or new declaration.';
  }
  const previous = inspectLeanSource(before);
  const next = inspectLeanSource(after);
  if (
    next.sorryCount > previous.sorryCount ||
    next.admitCount > previous.admitCount ||
    next.axioms.some((axiom) => !previous.axioms.includes(axiom))
  )
    return 'Candidate introduced an unproved placeholder or axiom.';
  return undefined;
};

const rejectPlaceholderClosure = (probe: LeanEvalLeanProbeResult, source: string): LeanEvalLeanProbeResult => {
  const inspection = inspectLeanSource(source);
  if (
    probe.status !== 'passed' ||
    (!inspection.sorryCount && !inspection.admitCount && !/declaration uses ['"]sorry['"]/u.test(probe.diagnostics))
  )
    return probe;
  return {
    ...probe,
    status: 'failed',
    hasHardErrors: true,
    diagnostics: `${probe.diagnostics}\nUnproved sorry/admit placeholders remain; compiler success is not proof closure.`,
  };
};

const actionOutcomeFromProbe = (
  probe: LeanEvalLeanProbeResult,
  previous: MathProofState,
  nextGoalFingerprint: string
): MathProofAction['outcome'] => {
  if (probe.status === 'passed') return 'advanced';
  if (probe.hasHardErrors) return 'failed';
  // A valid tactic can replace one open goal with another. Preserve that
  // progress so callers can continue from the new state instead of rolling
  // back to the previous goal.
  if (probe.firstGoal && nextGoalFingerprint !== previous.goalFingerprint) return 'advanced';
  if (JSON.stringify(openGoalsFromProbe(probe)) === JSON.stringify(previous.openGoals)) return 'unchanged';
  if (nextGoalFingerprint === previous.goalFingerprint) return 'unchanged';
  return 'failed';
};

/**
 * A bounded, source-backed Lean session.  It is deliberately implemented on
 * top of the existing sandboxed probe until a Pantograph/LeanDojo transport
 * is available.  Every state transition therefore has a real compiler result;
 * an unavailable tool never produces a synthetic state.
 */
export class MathematicsLeanProofSession {
  readonly sessionId: string;
  readonly episodeId: string;
  readonly sourceFile: string;
  readonly projectRelative: string;

  private readonly options: MathematicsLeanSessionOptions;
  private readonly states = new Map<string, MathProofState>();
  private readonly sources = new Map<string, string>();
  private readonly goalLines = new Map<string, number>();
  private readonly goalRanges = new Map<string, NonNullable<LeanEvalLeanProbeResult['sourceRange']>>();
  private readonly goalLocations = new Map<string, NonNullable<LeanEvalLeanProbeResult['goalLocations']>>();
  private readonly stateDiagnostics = new Map<string, string>();
  private readonly stateEnvironmentFingerprints = new Map<string, string>();
  private readonly completedActions = new Map<string, MathematicsLeanSessionActionResult>();
  private readonly statePins = new Map<string, number>();
  private readonly stateAccess = new Map<string, number>();
  private readonly statePayloads = new Map<
    string,
    Readonly<{ sourceHash: string; stateBytes: number; diagnosticsBytes: number }>
  >();
  private readonly sourcePayloads = new Map<string, { bytes: number; references: number }>();
  private stateAccessClock = 0;
  private cachedStateBytes = 0;
  private evictedStates = 0;
  private current: MathProofState;
  private currentSource: string;
  private readonly obligationSource: string;
  private dependencyFingerprint?: string;
  private closed = false;

  private constructor(
    options: MathematicsLeanSessionOptions,
    sessionId: string,
    episodeId: string,
    sourceFile: string,
    projectRelative: string,
    state: MathProofState,
    sourceText: string,
    diagnostics: string,
    private readonly persistentSession: MathematicsLeanLspSession
  ) {
    // Startup cancellation belongs to its request, not the reused session.
    this.options = { ...options, signal: undefined };
    this.obligationSource = options.contractSource ?? sourceText;
    this.sessionId = sessionId;
    this.episodeId = episodeId;
    this.sourceFile = sourceFile;
    this.projectRelative = projectRelative;
    this.current = state;
    this.currentSource = sourceText;
    this.storeState(state, sourceText, diagnostics);
  }

  private get maxStateEntries(): number {
    return Math.max(1, this.options.cacheLimits?.stateEntries ?? DEFAULT_STATE_CACHE_ENTRIES);
  }

  private get maxStateBytes(): number {
    return Math.max(1, this.options.cacheLimits?.stateBytes ?? DEFAULT_STATE_CACHE_BYTES);
  }

  private get maxActionResults(): number {
    return Math.max(1, this.options.cacheLimits?.actionResults ?? DEFAULT_ACTION_RESULT_ENTRIES);
  }

  private touchState(stateId: string): void {
    this.stateAccess.set(stateId, ++this.stateAccessClock);
  }

  private removeStatePayload(stateId: string): void {
    const payload = this.statePayloads.get(stateId);
    if (!payload) return;
    this.cachedStateBytes -= payload.stateBytes + payload.diagnosticsBytes;
    const source = this.sourcePayloads.get(payload.sourceHash);
    if (source && source.references > 1) {
      source.references -= 1;
    } else if (source) {
      this.cachedStateBytes -= source.bytes;
      this.sourcePayloads.delete(payload.sourceHash);
    }
    this.statePayloads.delete(stateId);
  }

  /**
   * Account the bounded payload once when it enters the hot cache. Sources use
   * the state's existing content hash so metrics and sweeps never re-hash text.
   */
  private storeState(state: MathProofState, sourceText: string, diagnostics: string): void {
    this.removeStatePayload(state.stateId);
    const stateBytes = Buffer.byteLength(JSON.stringify(state), 'utf8');
    const diagnosticsBytes = Buffer.byteLength(diagnostics, 'utf8');
    const source = this.sourcePayloads.get(state.sourceHash);
    if (source) {
      source.references += 1;
    } else {
      const bytes = Buffer.byteLength(sourceText, 'utf8');
      this.sourcePayloads.set(state.sourceHash, { bytes, references: 1 });
      this.cachedStateBytes += bytes;
    }
    this.cachedStateBytes += stateBytes + diagnosticsBytes;
    this.statePayloads.set(state.stateId, { sourceHash: state.sourceHash, stateBytes, diagnosticsBytes });
    this.states.set(state.stateId, state);
    this.sources.set(state.stateId, sourceText);
    this.stateDiagnostics.set(state.stateId, diagnostics);
    this.touchState(state.stateId);
  }

  private clearStateCache(): void {
    this.states.clear();
    this.sources.clear();
    this.goalLines.clear();
    this.goalRanges.clear();
    this.goalLocations.clear();
    this.stateDiagnostics.clear();
    this.stateEnvironmentFingerprints.clear();
    this.statePins.clear();
    this.stateAccess.clear();
    this.statePayloads.clear();
    this.sourcePayloads.clear();
    this.cachedStateBytes = 0;
  }

  private evictState(stateId: string): void {
    this.removeStatePayload(stateId);
    this.states.delete(stateId);
    this.sources.delete(stateId);
    this.goalLines.delete(stateId);
    this.goalRanges.delete(stateId);
    this.goalLocations.delete(stateId);
    this.stateDiagnostics.delete(stateId);
    this.stateEnvironmentFingerprints.delete(stateId);
    this.statePins.delete(stateId);
    this.stateAccess.delete(stateId);
    for (const [key, result] of this.completedActions) {
      if (result.state?.stateId === stateId) this.completedActions.delete(key);
    }
    this.evictedStates += 1;
  }

  private sweepStateCache(): void {
    while (this.states.size > this.maxStateEntries || this.cachedStateBytes > this.maxStateBytes) {
      const candidate = [...this.states.keys()]
        .filter((stateId) => stateId !== this.current.stateId && !(this.statePins.get(stateId) ?? 0))
        .toSorted((left, right) => (this.stateAccess.get(left) ?? 0) - (this.stateAccess.get(right) ?? 0))[0];
      if (!candidate) break;
      this.evictState(candidate);
    }
  }

  /** Keep a state live across a search or adoption operation. */
  retainState(stateId: string): () => void {
    if (!this.states.has(stateId)) return () => undefined;
    this.statePins.set(stateId, (this.statePins.get(stateId) ?? 0) + 1);
    this.touchState(stateId);
    let released = false;
    return () => {
      if (released) return;
      released = true;
      const remaining = (this.statePins.get(stateId) ?? 1) - 1;
      if (remaining > 0) this.statePins.set(stateId, remaining);
      else this.statePins.delete(stateId);
      this.sweepStateCache();
    };
  }

  cacheMetrics(): MathematicsLeanSessionCacheMetrics {
    return Object.freeze({
      stateEntries: this.states.size,
      stateBytes: this.cachedStateBytes,
      actionResults: this.completedActions.size,
      pinnedStates: this.statePins.size,
      evictedStates: this.evictedStates,
    });
  }

  /** Start a session by compiling the initial source in the bound project. */
  static async start(options: MathematicsLeanSessionOptions): Promise<MathematicsLeanSessionStartResult> {
    let sourceFile: string;
    let projectRelative: string;
    try {
      sourceFile = normalizeLeanSourceFile(options.sourceFile);
      projectRelative = normalizeProjectRelative(options.projectRelative, 'proof session projectRelative');
      if (options.sourceText !== undefined && Buffer.byteLength(options.sourceText, 'utf8') > MAX_SOURCE_BYTES) {
        throw new Error(`Mathematics proof session source exceeds ${MAX_SOURCE_BYTES} bytes`);
      }
    } catch (error) {
      return Object.freeze({
        status: 'invalid',
        diagnostics: error instanceof Error ? error.message : String(error),
      });
    }
    const persistentSession = new MathematicsLeanLspSession({
      workspaceRoot: options.workspaceRoot,
      projectRelative,
      sourceFile,
      env: options.env,
      lakePackagesPath: options.lakePackagesPath,
    });
    let probe = await runLeanEvalLeanProbe({
      persistentSession,
      workspaceRoot: options.workspaceRoot,
      ...(projectRelative ? { projectRelative } : {}),
      sourceFile,
      ...(options.sourceText !== undefined ? { sourceText: options.sourceText } : {}),
      mode: 'compile',
      ...(options.timeoutMs !== undefined ? { timeoutMs: options.timeoutMs } : {}),
      ...(options.signal ? { signal: options.signal } : {}),
      ...(options.env ? { env: options.env } : {}),
      ...(options.lakePackagesPath ? { lakePackagesPath: options.lakePackagesPath } : {}),
    });
    if (probe.status === 'unavailable') {
      await persistentSession.close();
      return Object.freeze({
        status: 'unavailable',
        diagnostics: probe.error || probe.diagnostics,
        ...probeMetadata(probe),
      });
    }
    if (probe.status === 'invalid') {
      await persistentSession.close();
      return Object.freeze({
        status: 'invalid',
        diagnostics: probe.error || probe.diagnostics,
        ...probeMetadata(probe),
      });
    }
    if (!probe.environmentFingerprint) {
      await persistentSession.close();
      return Object.freeze({
        status: 'unavailable',
        diagnostics: 'Lean probe did not produce a verified dependency environment',
        ...probeMetadata(probe),
      });
    }
    let sourceText: string;
    try {
      sourceText =
        options.sourceText ??
        fs.readFileSync(path.join(path.resolve(options.workspaceRoot), projectRelative, sourceFile), 'utf8');
    } catch (error) {
      await persistentSession.close();
      return Object.freeze({
        status: 'invalid',
        diagnostics: `Mathematics proof session source cannot be read: ${error instanceof Error ? error.message : String(error)}`,
        ...probeMetadata(probe),
      });
    }
    const contractError = options.contractSource
      ? candidateContractError(options.contractSource, sourceText)
      : undefined;
    if (contractError) {
      await persistentSession.close();
      return { status: 'invalid', diagnostics: contractError, ...probeMetadata(probe) };
    }
    probe = rejectPlaceholderClosure(probe, sourceText);
    const episodeId = options.episodeId?.trim() || `episode-${crypto.randomUUID()}`;
    const state = normalizeMathProofState({
      schema: 'deepscientist.mathematics.proof-state.v1',
      version: 1,
      episodeId,
      stateId: stateIdFor(episodeId, sourceText, probe.proofStateFingerprint, undefined, 0),
      statementHash: options.statementHash,
      routeFingerprint: options.routeFingerprint,
      ...(options.planId ? { planId: options.planId } : {}),
      goalFingerprint: probe.proofStateFingerprint,
      sourceFile,
      sourceHash: sourceHash(sourceText),
      openGoals: openGoalsFromProbe(probe),
      localContextHash: contextHashFromProbe(probe),
      metavariableCount: probe.openGoals?.length ?? (probe.firstGoal ? 1 : 0),
      declarationHashes: [],
      actionHistory: [],
      status: stateStatusFromProbe(probe),
    });
    const session = new MathematicsLeanProofSession(
      options,
      `session-${crypto.randomUUID()}`,
      episodeId,
      sourceFile,
      projectRelative,
      state,
      sourceText,
      probe.diagnostics,
      persistentSession
    );
    if (probe.sourceOffset) session.goalLines.set(state.stateId, probe.sourceOffset.line);
    if (probe.sourceRange) session.goalRanges.set(state.stateId, probe.sourceRange);
    if (probe.goalLocations) session.goalLocations.set(state.stateId, probe.goalLocations);
    if (probe.environmentFingerprint) {
      session.stateEnvironmentFingerprints.set(state.stateId, probe.environmentFingerprint);
      session.dependencyFingerprint = probe.environmentFingerprint;
    }
    return Object.freeze({
      status: 'started',
      session,
      state,
      diagnostics: probe.diagnostics,
      ...probeMetadata(probe),
    });
  }

  get state(): MathProofState {
    return this.current;
  }

  get environmentFingerprint(): string | undefined {
    return this.persistentSession.dependencyFingerprint;
  }

  get goalLine(): number | undefined {
    return this.goalLines.get(this.current.stateId);
  }
  get goalRange(): LeanEvalLeanProbeResult['sourceRange'] {
    return this.goalRanges.get(this.current.stateId);
  }

  get diagnostics(): string {
    return this.stateDiagnostics.get(this.current.stateId) ?? '';
  }

  goalLocation(index: number) {
    return this.goalLocations.get(this.current.stateId)?.[index];
  }

  /** Adopt an externally edited candidate only after re-elaboration, retaining the Lean process. */
  async synchronizeSource(
    sourceText: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    const deadlineAt = deadlineFor(timeoutMs ?? this.options.timeoutMs);
    const interruption = interruptedCall(signal, deadlineAt);
    if (interruption) return interruption;
    if (this.closed) return { status: 'invalid', diagnostics: 'Mathematics proof session is closed' };
    if (Buffer.byteLength(sourceText, 'utf8') > MAX_SOURCE_BYTES)
      return { status: 'invalid', diagnostics: 'Mathematics proof source exceeds supported size' };
    const contractError = candidateContractError(this.obligationSource, sourceText);
    if (contractError) return { status: 'invalid', diagnostics: contractError };
    const dependency = this.persistentSession.dependencyFingerprint;
    if (
      dependency !== undefined &&
      dependency === this.dependencyFingerprint &&
      sourceHash(sourceText) === this.current.sourceHash
    )
      return { status: 'restored', state: this.current, diagnostics: '' };
    const probe = rejectPlaceholderClosure(
      await runLeanEvalLeanProbe({
        reuseFailedChecks: true,
        workspaceRoot: this.options.workspaceRoot,
        projectRelative: this.projectRelative,
        sourceFile: this.sourceFile,
        sourceText,
        mode: 'compile',
        persistentSession: this.persistentSession,
        timeoutMs: remainingFor(deadlineAt),
        signal,
        env: this.options.env,
        lakePackagesPath: this.options.lakePackagesPath,
      }),
      sourceText
    );
    const postProbeInterruption = interruptedCall(signal, deadlineAt);
    if (postProbeInterruption)
      return Object.freeze({
        ...postProbeInterruption,
        state: this.current,
        durationMs: probe.durationMs,
      });
    if (this.closed) return { status: 'invalid', diagnostics: 'Mathematics proof session is closed' };
    if (probe.status === 'invalid' || probe.status === 'unavailable')
      return { status: probe.status, diagnostics: probe.error ?? probe.diagnostics, ...probeMetadata(probe) };
    if (!probe.environmentFingerprint)
      return {
        status: 'unavailable',
        diagnostics: 'Lean probe did not produce a verified dependency environment',
        ...probeMetadata(probe),
      };
    const synchronizedEnvironment = this.persistentSession.dependencyFingerprint;
    if (!synchronizedEnvironment || synchronizedEnvironment !== probe.environmentFingerprint)
      return {
        status: 'unavailable',
        diagnostics: 'Lean dependency environment changed after source synchronization',
        ...probeMetadata(probe),
      };
    try {
      archiveLeanProofActions(this.options.workspaceRoot, this.actionHistoryRef, this.current.actionHistory);
    } catch (error) {
      return {
        status: 'unavailable',
        diagnostics: `Proof history could not be archived: ${error instanceof Error ? error.message : String(error)}`,
        ...probeMetadata(probe),
      };
    }
    const state = normalizeMathProofState({
      ...this.current,
      stateId: stateIdFor(this.episodeId, sourceText, probe.proofStateFingerprint, undefined, 0),
      parentStateId: undefined,
      sourceHash: sourceHash(sourceText),
      goalFingerprint: probe.proofStateFingerprint,
      openGoals: openGoalsFromProbe(probe),
      localContextHash: contextHashFromProbe(probe),
      metavariableCount: probe.openGoals?.length ?? (probe.firstGoal ? 1 : 0),
      actionHistory: [],
      actionHistoryOffset: undefined,
      actionHistoryRef: undefined,
      status: stateStatusFromProbe(probe),
    });
    this.clearStateCache();
    this.completedActions.clear();
    this.storeState(state, sourceText, probe.diagnostics);
    if (probe.sourceOffset) this.goalLines.set(state.stateId, probe.sourceOffset.line);
    if (probe.sourceRange) this.goalRanges.set(state.stateId, probe.sourceRange);
    if (probe.goalLocations) this.goalLocations.set(state.stateId, probe.goalLocations);
    this.stateEnvironmentFingerprints.set(state.stateId, probe.environmentFingerprint);
    this.current = state;
    this.currentSource = sourceText;
    this.dependencyFingerprint = probe.environmentFingerprint;
    return { status: 'restored', state, diagnostics: probe.diagnostics, ...probeMetadata(probe) };
  }

  /** Check a source without replacing current; adoption happens through restoreState. */
  async checkCandidateSource(
    sourceText: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    const deadlineAt = deadlineFor(timeoutMs ?? this.options.timeoutMs);
    const interruption = interruptedCall(signal, deadlineAt);
    if (interruption) return interruption;
    if (this.closed) return { status: 'invalid', diagnostics: 'Mathematics proof session is closed' };
    if (Buffer.byteLength(sourceText, 'utf8') > MAX_SOURCE_BYTES)
      return { status: 'invalid', diagnostics: 'Mathematics proof source exceeds supported size' };
    const contractError = candidateContractError(this.obligationSource, sourceText);
    if (contractError) return { status: 'invalid', diagnostics: contractError };
    const probe = rejectPlaceholderClosure(
      await runLeanEvalLeanProbe({
        reuseFailedChecks: true,
        workspaceRoot: this.options.workspaceRoot,
        projectRelative: this.projectRelative,
        sourceFile: this.sourceFile,
        sourceText,
        mode: 'compile',
        persistentSession: this.persistentSession,
        timeoutMs: remainingFor(deadlineAt),
        signal,
        env: this.options.env,
        lakePackagesPath: this.options.lakePackagesPath,
      }),
      sourceText
    );
    const postProbeInterruption = interruptedCall(signal, deadlineAt);
    if (postProbeInterruption)
      return Object.freeze({ ...postProbeInterruption, state: this.current, durationMs: probe.durationMs });
    if (this.closed) return { status: 'invalid', diagnostics: 'Mathematics proof session is closed' };
    if (probe.status === 'invalid' || probe.status === 'unavailable')
      return Object.freeze({
        status: probe.status,
        diagnostics: probe.error ?? probe.diagnostics,
        ...probeMetadata(probe),
      });
    if (!probe.environmentFingerprint)
      return Object.freeze({
        status: 'unavailable',
        diagnostics: 'Lean probe did not produce a verified dependency environment',
        ...probeMetadata(probe),
      });
    const candidateEnvironment = this.persistentSession.dependencyFingerprint;
    if (!candidateEnvironment || candidateEnvironment !== probe.environmentFingerprint)
      return Object.freeze({
        status: 'unavailable',
        diagnostics: 'Lean dependency environment changed after candidate checking',
        ...probeMetadata(probe),
      });
    const state = normalizeMathProofState({
      ...this.current,
      stateId: stateIdFor(this.episodeId, sourceText, probe.proofStateFingerprint, undefined, 0),
      parentStateId: undefined,
      sourceHash: sourceHash(sourceText),
      goalFingerprint: probe.proofStateFingerprint,
      openGoals: openGoalsFromProbe(probe),
      localContextHash: contextHashFromProbe(probe),
      metavariableCount: probe.openGoals?.length ?? (probe.firstGoal ? 1 : 0),
      actionHistory: [],
      actionHistoryOffset: undefined,
      actionHistoryRef: undefined,
      status: stateStatusFromProbe(probe),
    });
    this.storeState(state, sourceText, probe.diagnostics);
    if (probe.sourceOffset) this.goalLines.set(state.stateId, probe.sourceOffset.line);
    if (probe.sourceRange) this.goalRanges.set(state.stateId, probe.sourceRange);
    if (probe.goalLocations) this.goalLocations.set(state.stateId, probe.goalLocations);
    this.stateEnvironmentFingerprints.set(state.stateId, probe.environmentFingerprint);
    const status =
      state.status === 'failed'
        ? 'failed'
        : state.status === 'closed' || state.goalFingerprint !== this.current.goalFingerprint
          ? 'advanced'
          : 'unchanged';
    return Object.freeze({ status, state, diagnostics: probe.error || probe.diagnostics, ...probeMetadata(probe) });
  }

  snapshot(): MathematicsLeanSessionSnapshot {
    return Object.freeze({ state: this.current, sourceText: this.currentSource });
  }

  /** Read a retained branch without changing the active session state. */
  snapshotState(stateId: string): MathematicsLeanSessionSnapshot | undefined {
    const state = this.states.get(stateId);
    const sourceText = state ? this.sources.get(stateId) : undefined;
    if (state && sourceText !== undefined) this.touchState(stateId);
    return state && sourceText !== undefined ? Object.freeze({ state, sourceText }) : undefined;
  }

  /** Read feedback captured when a state was checked without changing or recompiling the live state. */
  readStateFeedback(stateId: string): MathematicsLeanStateFeedback | undefined {
    const state = this.states.get(stateId);
    const sourceText = state ? this.sources.get(stateId) : undefined;
    if (!state || sourceText === undefined) return undefined;
    this.touchState(stateId);
    return Object.freeze({
      state,
      sourceText,
      diagnostics: this.stateDiagnostics.get(stateId) ?? null,
      goalLine: this.goalLines.get(stateId) ?? null,
      goalRange: this.goalRanges.get(stateId) ?? null,
      goalLocations: this.goalLocations.get(stateId) ?? null,
      environmentFingerprint: this.stateEnvironmentFingerprints.get(stateId) ?? null,
    });
  }

  async runTactic(
    tactic: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('tactic', tactic, candidateSource, signal, timeoutMs);
  }

  async applyPremise(
    premise: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('premise', premise, candidateSource, signal, timeoutMs);
  }

  async rewrite(
    rewrite: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('rewrite', rewrite, candidateSource, signal, timeoutMs);
  }

  async construct(
    constructor: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('constructor', constructor, candidateSource, signal, timeoutMs);
  }

  async cases(
    expression: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('cases', expression, candidateSource, signal, timeoutMs);
  }

  async induction(
    expression: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('induction', expression, candidateSource, signal, timeoutMs);
  }

  async helper(
    declaration: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('helper', declaration, candidateSource, signal, timeoutMs);
  }

  async importModule(
    moduleName: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    return this.execute('import', moduleName, candidateSource, signal, timeoutMs);
  }

  undo(stateId?: string): MathematicsLeanSessionActionResult {
    if (this.closed) return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session is closed' });
    const targetId = stateId ?? this.current.parentStateId;
    const target = targetId ? this.states.get(targetId) : undefined;
    if (!target)
      return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session checkpoint is unknown' });
    this.current = target;
    this.currentSource = this.sources.get(target.stateId)!;
    this.touchState(target.stateId);
    return Object.freeze({ status: 'restored', state: target, diagnostics: '' });
  }

  /** Restore a state together with the exact source retained for that state. */
  restoreState(stateId: string): MathematicsLeanSessionActionResult {
    if (this.closed) return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session is closed' });
    const state = this.states.get(stateId);
    const sourceText = state ? this.sources.get(stateId) : undefined;
    if (!state || sourceText === undefined) {
      return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session checkpoint is unknown' });
    }
    const environment = this.persistentSession.dependencyFingerprint;
    const checkedEnvironment = this.stateEnvironmentFingerprints.get(stateId);
    if (!environment || !checkedEnvironment || environment !== checkedEnvironment) {
      return Object.freeze({
        status: 'invalid',
        diagnostics: 'Proof checkpoint environment is stale; replay is required',
      });
    }
    this.current = state;
    this.currentSource = sourceText;
    this.touchState(stateId);
    return Object.freeze({ status: 'restored', state, diagnostics: '' });
  }

  branch(): MathematicsLeanSessionActionResult {
    if (this.closed) return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session is closed' });
    const branchId = `branch-${crypto.randomUUID()}`;
    return Object.freeze({
      status: 'branched',
      state: this.current,
      branchId,
      diagnostics: '',
    });
  }

  restore(snapshot: MathematicsLeanSessionSnapshot): MathematicsLeanSessionActionResult {
    const validated = this.validateSnapshot(snapshot);
    if (!validated.state) return validated;
    const state = validated.state;
    const retained = this.states.get(state.stateId);
    if (!retained || JSON.stringify(retained) !== JSON.stringify(state)) {
      return Object.freeze({ status: 'invalid', diagnostics: 'Unknown proof snapshot requires source replay' });
    }
    this.current = retained;
    this.currentSource = snapshot.sourceText;
    this.touchState(retained.stateId);
    return Object.freeze({ status: 'restored', state: retained, diagnostics: '' });
  }

  /** Recompile a durable snapshot, optionally reusing matching live compiler feedback. */
  async replay(
    snapshot: MathematicsLeanSessionSnapshot,
    signal?: AbortSignal,
    timeoutMs?: number,
    options?: Readonly<{ reuseCurrentSource?: boolean }>
  ): Promise<MathematicsLeanSessionActionResult> {
    const deadlineAt = deadlineFor(timeoutMs ?? this.options.timeoutMs);
    const interruption = interruptedCall(signal, deadlineAt);
    if (interruption) return interruption;
    const validated = this.validateSnapshot(snapshot);
    if (!validated.state) return validated;
    const contractError = candidateContractError(this.obligationSource, snapshot.sourceText);
    if (contractError) return { status: 'invalid', diagnostics: contractError };
    const state = validated.state;
    const sourceText = snapshot.sourceText;
    const previousStateId = this.current.stateId;
    // Cold recovery has already compiled this exact source during session startup.
    // Reuse its feedback only while the checked dependency identity remains live.
    if (options?.reuseCurrentSource && sourceText === this.currentSource) {
      const feedback = this.readStateFeedback(previousStateId);
      const environment = this.persistentSession.dependencyFingerprint;
      if (
        feedback &&
        feedback.diagnostics !== null &&
        feedback.environmentFingerprint &&
        feedback.environmentFingerprint === environment &&
        environment === this.dependencyFingerprint
      ) {
        if (
          state.goalFingerprint !== feedback.state.goalFingerprint ||
          state.status !== feedback.state.status ||
          state.localContextHash !== feedback.state.localContextHash ||
          JSON.stringify(state.openGoals) !== JSON.stringify(feedback.state.openGoals) ||
          state.metavariableCount !== feedback.state.metavariableCount ||
          state.declarationHashes.length !== 0
        ) {
          return Object.freeze({
            status: 'invalid',
            diagnostics: 'Proof snapshot does not match current source replay',
          });
        }
        this.storeState(state, sourceText, feedback.diagnostics);
        if (feedback.goalLine !== null) this.goalLines.set(state.stateId, feedback.goalLine);
        if (feedback.goalRange) this.goalRanges.set(state.stateId, feedback.goalRange);
        if (feedback.goalLocations) this.goalLocations.set(state.stateId, feedback.goalLocations);
        this.stateEnvironmentFingerprints.set(state.stateId, environment);
        this.current = state;
        this.sweepStateCache();
        return Object.freeze({
          status: 'restored',
          state,
          diagnostics: feedback.diagnostics,
          durationMs: 0,
          cacheHit: true,
          reuseKind: 'hot',
          environmentFingerprint: environment,
        });
      }
    }
    const probe = rejectPlaceholderClosure(
      await runLeanEvalLeanProbe({
        persistentSession: this.persistentSession,
        workspaceRoot: this.options.workspaceRoot,
        ...(this.projectRelative ? { projectRelative: this.projectRelative } : {}),
        sourceFile: this.sourceFile,
        sourceText,
        mode: 'compile',
        ...(remainingFor(deadlineAt) !== undefined ? { timeoutMs: remainingFor(deadlineAt) } : {}),
        ...(signal ? { signal } : this.options.signal ? { signal: this.options.signal } : {}),
        ...(this.options.env ? { env: this.options.env } : {}),
        ...(this.options.lakePackagesPath ? { lakePackagesPath: this.options.lakePackagesPath } : {}),
      }),
      sourceText
    );
    const postProbeInterruption = interruptedCall(signal, deadlineAt);
    if (postProbeInterruption)
      return Object.freeze({
        ...postProbeInterruption,
        state: this.current,
        durationMs: probe.durationMs,
      });
    if (probe.status === 'unavailable' || probe.status === 'invalid') {
      return Object.freeze({
        status: probe.status,
        diagnostics: probe.error || probe.diagnostics,
        ...probeMetadata(probe),
      });
    }
    if (!probe.environmentFingerprint) {
      return Object.freeze({
        status: 'unavailable',
        diagnostics: 'Lean probe did not produce a verified dependency environment',
        ...probeMetadata(probe),
      });
    }
    const replayEnvironment = this.persistentSession.dependencyFingerprint;
    if (!replayEnvironment || replayEnvironment !== probe.environmentFingerprint) {
      return Object.freeze({
        status: 'unavailable',
        diagnostics: 'Proof snapshot environment changed after replay',
        ...probeMetadata(probe),
      });
    }
    if (
      this.closed ||
      this.current.stateId !== previousStateId ||
      state.goalFingerprint !== probe.proofStateFingerprint ||
      state.status !== stateStatusFromProbe(probe) ||
      state.localContextHash !== contextHashFromProbe(probe) ||
      JSON.stringify(state.openGoals) !== JSON.stringify(openGoalsFromProbe(probe)) ||
      state.metavariableCount !== (probe.openGoals?.length ?? (probe.firstGoal ? 1 : 0)) ||
      state.declarationHashes.length !== 0
    ) {
      return Object.freeze({
        status: 'invalid',
        diagnostics: 'Proof snapshot does not match current source replay',
        ...probeMetadata(probe),
      });
    }
    this.storeState(state, sourceText, probe.diagnostics);
    if (probe.sourceOffset) this.goalLines.set(state.stateId, probe.sourceOffset.line);
    if (probe.sourceRange) this.goalRanges.set(state.stateId, probe.sourceRange);
    if (probe.goalLocations) this.goalLocations.set(state.stateId, probe.goalLocations);
    this.stateEnvironmentFingerprints.set(state.stateId, probe.environmentFingerprint);
    this.current = state;
    this.currentSource = sourceText;
    this.dependencyFingerprint = probe.environmentFingerprint;
    this.sweepStateCache();
    return Object.freeze({ status: 'restored', state, diagnostics: probe.diagnostics, ...probeMetadata(probe) });
  }

  private validateSnapshot(snapshot: MathematicsLeanSessionSnapshot): MathematicsLeanSessionActionResult {
    if (this.closed) return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session is closed' });
    if (typeof snapshot.sourceText !== 'string' || Buffer.byteLength(snapshot.sourceText, 'utf8') > MAX_SOURCE_BYTES) {
      return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session snapshot source is invalid' });
    }
    let state: MathProofState;
    try {
      state = normalizeMathProofState(snapshot.state);
    } catch (error) {
      return Object.freeze({ status: 'invalid', diagnostics: error instanceof Error ? error.message : String(error) });
    }
    if (
      state.episodeId !== this.episodeId ||
      state.planId !== this.current.planId ||
      state.stateId !==
        stateIdFor(
          this.episodeId,
          snapshot.sourceText,
          state.goalFingerprint,
          state.parentStateId,
          (state.actionHistoryOffset ?? 0) + state.actionHistory.length
        ) ||
      state.statementHash !== this.current.statementHash ||
      state.routeFingerprint !== this.current.routeFingerprint ||
      state.sourceFile !== this.sourceFile ||
      (state.actionHistoryRef !== undefined && state.actionHistoryRef !== this.actionHistoryRef) ||
      state.sourceHash !== sourceHash(snapshot.sourceText)
    ) {
      return Object.freeze({
        status: 'invalid',
        diagnostics: 'Mathematics proof session snapshot identity does not match',
      });
    }
    return Object.freeze({ status: 'restored', state, diagnostics: '' });
  }

  close(): Promise<void> {
    this.closed = true;
    return this.persistentSession.close();
  }

  private get actionHistoryRef(): string {
    return `.deepscientist/math/proof-actions/${sha256(JSON.stringify([this.episodeId, this.sourceFile, this.current.statementHash]))}.jsonl`;
  }

  private async execute(
    kind: MathProofActionKind,
    payload: string,
    candidateSource: string,
    signal?: AbortSignal,
    timeoutMs?: number
  ): Promise<MathematicsLeanSessionActionResult> {
    const deadlineAt = deadlineFor(timeoutMs ?? this.options.timeoutMs);
    const interruption = interruptedCall(signal, deadlineAt);
    if (interruption) return Object.freeze({ ...interruption, state: this.current });
    if (this.closed) return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session is closed' });
    const normalizedPayload = payload.trim();
    if (!normalizedPayload || normalizedPayload.length > MAX_ACTION_PAYLOAD) {
      return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session action payload is invalid' });
    }
    if (typeof candidateSource !== 'string' || Buffer.byteLength(candidateSource, 'utf8') > MAX_SOURCE_BYTES) {
      return Object.freeze({ status: 'invalid', diagnostics: 'Mathematics proof session candidate source is invalid' });
    }
    const contractError = candidateContractError(this.obligationSource, candidateSource);
    if (contractError) return Object.freeze({ status: 'invalid', diagnostics: contractError });
    let refreshMs = 0;
    const observedDependency = this.persistentSession.dependencyFingerprint;
    if (!observedDependency || observedDependency !== this.dependencyFingerprint) {
      const refreshed = await this.synchronizeSource(this.currentSource, signal, remainingFor(deadlineAt));
      refreshMs = refreshed.durationMs ?? 0;
      if (refreshed.status === 'invalid' || refreshed.status === 'unavailable') return refreshed;
    }
    const postRefreshInterruption = interruptedCall(signal, deadlineAt);
    if (postRefreshInterruption) return Object.freeze({ ...postRefreshInterruption, state: this.current });
    const dependency = this.dependencyFingerprint;
    if (!dependency)
      return Object.freeze({
        status: 'unavailable',
        state: this.current,
        diagnostics: 'Lean dependency environment is unavailable',
      });
    const actionKey = `${dependency ?? 'environment-unreported'}\0${this.current.sourceHash}\0${this.current.goalFingerprint}\0${kind}\0${normalizedPayload}\0${sourceHash(candidateSource)}`;
    const completed = this.completedActions.get(actionKey);
    if (completed?.state) {
      const feedback = this.readStateFeedback(completed.state.stateId);
      if (
        feedback &&
        feedback.sourceText === candidateSource &&
        feedback.state.sourceHash === sourceHash(candidateSource) &&
        feedback.environmentFingerprint === (this.persistentSession.dependencyFingerprint ?? null) &&
        this.restoreState(completed.state.stateId).status === 'restored'
      ) {
        this.completedActions.delete(actionKey);
        this.completedActions.set(actionKey, completed);
        return Object.freeze({
          ...completed,
          status: 'duplicate',
          underlyingStatus: completed.status === 'duplicate' ? completed.underlyingStatus : completed.status,
          cacheHit: true,
          reuseKind: 'hot',
          durationMs: 0,
        });
      }
      this.completedActions.delete(actionKey);
    }
    const probe = rejectPlaceholderClosure(
      await runLeanEvalLeanProbe({
        reuseFailedChecks: true,
        persistentSession: this.persistentSession,
        workspaceRoot: this.options.workspaceRoot,
        ...(this.projectRelative ? { projectRelative: this.projectRelative } : {}),
        sourceFile: this.sourceFile,
        sourceText: candidateSource,
        mode: 'compile',
        ...(remainingFor(deadlineAt) !== undefined ? { timeoutMs: remainingFor(deadlineAt) } : {}),
        ...(signal ? { signal } : this.options.signal ? { signal: this.options.signal } : {}),
        ...(this.options.env ? { env: this.options.env } : {}),
        ...(this.options.lakePackagesPath ? { lakePackagesPath: this.options.lakePackagesPath } : {}),
      }),
      candidateSource
    );
    const postProbeInterruption = interruptedCall(signal, deadlineAt);
    if (postProbeInterruption)
      return Object.freeze({
        ...postProbeInterruption,
        state: this.current,
        durationMs: refreshMs + probe.durationMs,
      });
    if (probe.status === 'unavailable' || probe.status === 'invalid') {
      return Object.freeze({
        status: probe.status,
        state: this.current,
        diagnostics: probe.error || probe.diagnostics,
        ...probeMetadata(probe),
        durationMs: refreshMs + probe.durationMs,
      });
    }
    if (!probe.environmentFingerprint || probe.environmentFingerprint !== dependency) {
      return Object.freeze({
        status: 'unavailable',
        state: this.current,
        diagnostics: 'Lean dependency environment changed during candidate checking',
        ...probeMetadata(probe),
        durationMs: refreshMs + probe.durationMs,
      });
    }
    const nextGoalFingerprint = probe.proofStateFingerprint;
    const nextStateId = stateIdFor(
      this.episodeId,
      candidateSource,
      nextGoalFingerprint,
      this.current.stateId,
      (this.current.actionHistoryOffset ?? 0) + this.current.actionHistory.length + 1
    );
    const action = normalizeMathProofAction({
      schema: 'deepscientist.mathematics.proof-action.v1',
      version: 1,
      actionId: `action-${nextStateId.slice(0, 24)}`,
      kind,
      payload: normalizedPayload,
      preconditionStateId: this.current.stateId,
      resultStateId: nextStateId,
      runtime: {
        durationMs: Math.max(0, Math.round(refreshMs + probe.durationMs)),
        exitCode: probe.status === 'passed' ? 0 : 1,
        ...(probe.diagnostics ? { diagnosticHash: sha256(probe.diagnostics) } : {}),
      },
      outcome: actionOutcomeFromProbe(probe, this.current, nextGoalFingerprint),
    });
    const fullHistory = [...this.current.actionHistory, action];
    const archived = fullHistory.slice(0, Math.max(0, fullHistory.length - ACTION_HISTORY_WINDOW));
    try {
      archiveLeanProofActions(this.options.workspaceRoot, this.actionHistoryRef, archived);
    } catch (error) {
      return Object.freeze({
        status: 'unavailable',
        state: this.current,
        diagnostics: `Proof history could not be archived: ${error instanceof Error ? error.message : String(error)}`,
        ...probeMetadata(probe),
        durationMs: refreshMs + probe.durationMs,
      });
    }
    const nextState = normalizeMathProofState({
      schema: 'deepscientist.mathematics.proof-state.v1',
      version: 1,
      episodeId: this.episodeId,
      stateId: nextStateId,
      parentStateId: this.current.stateId,
      statementHash: this.current.statementHash,
      routeFingerprint: this.current.routeFingerprint,
      ...(this.current.planId ? { planId: this.current.planId } : {}),
      goalFingerprint: nextGoalFingerprint,
      sourceFile: this.sourceFile,
      sourceHash: sourceHash(candidateSource),
      openGoals: openGoalsFromProbe(probe),
      localContextHash: contextHashFromProbe(probe),
      metavariableCount: probe.openGoals?.length ?? (probe.firstGoal ? 1 : 0),
      declarationHashes: this.current.declarationHashes,
      actionHistory: fullHistory.slice(-ACTION_HISTORY_WINDOW),
      actionHistoryOffset: (this.current.actionHistoryOffset ?? 0) + archived.length,
      ...((this.current.actionHistoryOffset ?? 0) + archived.length > 0
        ? { actionHistoryRef: this.actionHistoryRef }
        : {}),
      status: stateStatusFromProbe(probe),
    });
    this.storeState(nextState, candidateSource, probe.diagnostics);
    if (probe.sourceOffset) this.goalLines.set(nextState.stateId, probe.sourceOffset.line);
    if (probe.sourceRange) this.goalRanges.set(nextState.stateId, probe.sourceRange);
    if (probe.goalLocations) this.goalLocations.set(nextState.stateId, probe.goalLocations);
    this.stateEnvironmentFingerprints.set(nextState.stateId, probe.environmentFingerprint);
    this.current = nextState;
    this.currentSource = candidateSource;
    this.dependencyFingerprint = probe.environmentFingerprint;
    const result: MathematicsLeanSessionActionResult = Object.freeze({
      status: action.outcome === 'advanced' ? 'advanced' : action.outcome === 'unchanged' ? 'unchanged' : 'failed',
      capabilityAdded:
        action.outcome === 'unchanged' &&
        (kind === 'helper'
          ? declarationKeys(candidateSource).length >
            declarationKeys(this.sources.get(action.preconditionStateId) ?? '').length
          : kind === 'import' &&
            importLines(candidateSource).some(
              (line) => !importLines(this.sources.get(action.preconditionStateId) ?? '').includes(line)
            )),
      state: nextState,
      action,
      diagnostics: probe.error || probe.diagnostics,
      ...probeMetadata(probe),
    });
    this.completedActions.set(actionKey, result);
    while (this.completedActions.size > this.maxActionResults) {
      const oldest = this.completedActions.keys().next().value as string | undefined;
      if (!oldest) break;
      this.completedActions.delete(oldest);
    }
    this.sweepStateCache();
    return result;
  }
}

export const startMathematicsLeanSession = (
  options: MathematicsLeanSessionOptions
): Promise<MathematicsLeanSessionStartResult> => MathematicsLeanProofSession.start(options);
