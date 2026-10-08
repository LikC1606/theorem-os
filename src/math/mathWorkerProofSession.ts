import { isRoutineMathClosureAction, runMathLocalClosure } from "./mathLocalClosure";
import { type CheckedMathProofBlock } from "./mathProofBlocks";
import { buildMathDiscoveryCandidates } from "./mathDiscoveryFrontier";
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import {
  startMathematicsLeanSession,
  type MathematicsLeanProofSession,
  type MathematicsLeanSessionActionResult,
  type MathematicsLeanSessionSnapshot,
} from "./leanInteractiveSession";
import {
  classifyLeanProofDiagnostic,
  generateLeanProofActionCandidates,
  generateLeanPremiseActionCandidates,
  isUsableCandidateResult,
  searchLeanProofActions,
  type LeanProofActionCandidate,
  type LeanProofRecoveredAttempt,
} from "./leanProofActionSearch";
import { canonicalMathJson, readMathJson, withMathRuntimeLease, writeMathJsonDurable } from "./mathRuntimeIo";
import { archiveLeanProofActions } from "./leanProofActionArchive";
import { isAllowedMathProofSource } from "./mathProofSourcePolicy";
import { writeMathTextAtomicallyWithStatus } from "./mathSourceArtifact";
import { readMathRunHistoryIdentity } from "./mathRunHistory";
import { isMathPlanningSafetyError } from "./mathPlanningContext";
import { z } from 'zod';
import { recordMathProofImpactAdoption } from "./mathProofImpact";

export type MathWorkerProofActionRequest = Readonly<{
  workspaceRoot: string;
  projectRelative?: string;
  sourceFile: string;
  statementHash: string;
  /** Host-frozen original contract; never derive required declarations from an edited candidate. */
  contractSource?: string;
  routeFingerprint: string;
  initialRouteFingerprint?: string;
  routeRevision?: number;
  acceptedRouteFingerprints?: readonly string[];
  /** Final adoption guard. It must be a synchronous snapshot, never a model or I/O promise. */
  validateActiveRoute?: () => boolean;
  episodeId: string;
  expectedSourceHash: string;
  action: 'probe' | 'search' | 'branches' | 'checkout';
  problemId?: string;
  historyProjectRoot?: string;
  branchId?: string;
  branchOffset?: number;
  branchPageSize?: number;
  branchGeneration?: string;
  /** Host-only: omit default branch metadata for ordinary probes; explicit branch controls take precedence. */
  includeBranchMetadata?: boolean;
  goalIndex?: number;
  candidateOffset?: number;
  candidateBatchSize?: number;
  candidateSetHash?: string;
  searchMode?: MathSearchMode;
  lookahead?: boolean;
  premiseQuery?: string;
  premiseCandidates?: readonly MathPremiseCandidate[];
  premiseProvider?: (
    view: MathValidatedGoalView,
    context?: Readonly<{ signal?: AbortSignal; remainingTimeoutMs?: number }>
  ) => Promise<readonly MathPremiseCandidate[]>;
  /** Host-only, authorized frozen blocks; never accepted from public tool arguments. */
  checkedProofBlocks?: (
    view: MathValidatedGoalView,
    context: Readonly<{ signal?: AbortSignal; remainingTimeoutMs?: number }>
  ) => Promise<readonly CheckedMathProofBlock[]>;
  candidates?: readonly Pick<LeanProofActionCandidate, 'kind' | 'payload' | 'source'>[];
  applyBest?: boolean;
  timeoutMs?: number;
  signal?: AbortSignal;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
  cacheLimits?: Readonly<{
    liveSessions?: number;
    stateEntries?: number;
    stateBytes?: number;
    actionResults?: number;
  }>;
}>;

export type MathPremiseCandidate = Readonly<{
  name: string;
  type: string;
  packageName?: string;
  packageRevision?: string;
  sourceModule?: string;
  sourceFile?: string;
  providerRank?: number;
  corpusDigest?: string;
}>;

export type MathSearchMode = 'auto' | 'provided' | 'premises' | 'generic';

export type ResolvedMathSearchPlan = Readonly<{
  mode: Exclude<MathSearchMode, 'auto'>;
  retrieve: boolean;
  generateGeneric: boolean;
  preserveOrder: boolean;
  lookahead: boolean;
}>;

export type MathValidatedGoalView = Readonly<{
  stateId: string;
  sourceHash: string;
  environmentFingerprint: string | null;
  proofStateFingerprint: string;
  goalIndex: number;
  goal: string;
  location: ReturnType<MathematicsLeanProofSession['goalLocation']> | null;
}>;

export type MathProofFeedbackView = Readonly<{
  stateId: string;
  sourceHash: string;
  environmentFingerprint: string | null;
  proofStateFingerprint: string;
  status: 'open' | 'closed' | 'failed' | 'timeout';
  goals: readonly string[];
  diagnostics: string;
  feedbackAvailable: boolean;
  location: ReturnType<MathematicsLeanProofSession['goalLocation']> | null;
  goalLocations: NonNullable<ReturnType<MathematicsLeanProofSession['readStateFeedback']>>['goalLocations'];
  truncated: boolean;
}>;

const mathProofFeedbackLocation = (
  feedback: NonNullable<ReturnType<MathematicsLeanProofSession['readStateFeedback']>>,
  targetIndex: number,
  targetGoal: string | undefined,
  baselineGoalCount: number
): MathProofFeedbackView['location'] => {
  const exactGoalIndexes = targetGoal
    ? feedback.state.openGoals.flatMap((goal, index) => (goal === targetGoal ? [index] : []))
    : [];
  if (exactGoalIndexes.length === 1) return feedback.goalLocations?.[exactGoalIndexes[0]!] ?? null;
  if (targetGoal || feedback.state.openGoals.length < baselineGoalCount) return null;
  return (
    feedback.goalLocations?.[targetIndex] ??
    (targetIndex === 0 && (feedback.goalLine !== null || feedback.goalRange !== null)
      ? {
          ...(feedback.goalLine !== null ? { line: feedback.goalLine } : {}),
          ...(feedback.goalRange !== null ? { range: feedback.goalRange } : {}),
          localIndex: 0,
        }
      : null)
  );
};

export type MathCandidateApplicability =
  | 'incomplete'
  | 'candidate_failed'
  | 'not_checked'
  | 'checked_closed'
  | 'checked_with_goals';

/** Classify only evidence produced for this candidate; a baseline state never proves candidate applicability. */
export function classifyMathCandidateApplicability(
  result: MathematicsLeanSessionActionResult
): Readonly<{ applicability: MathCandidateApplicability; reason: string }> {
  const outcome = result.underlyingStatus ?? result.status;
  if (
    result.executionDisposition === 'timed_out' ||
    result.executionDisposition === 'aborted' ||
    result.executionDisposition === 'unavailable' ||
    outcome === 'unavailable'
  )
    return Object.freeze({ applicability: 'incomplete', reason: result.executionDisposition ?? 'unavailable' });
  if (outcome === 'invalid' || outcome === 'failed' || result.state?.status === 'failed')
    return Object.freeze({ applicability: 'candidate_failed', reason: outcome });
  if (result.status === 'duplicate' && !result.cacheHit)
    return Object.freeze({ applicability: 'not_checked', reason: 'duplicate_without_candidate_evidence' });
  if (!result.state) return Object.freeze({ applicability: 'not_checked', reason: 'candidate_state_missing' });
  if (result.state.status === 'closed' && result.state.openGoals.length === 0)
    return Object.freeze({ applicability: 'checked_closed', reason: 'candidate_checked_closed' });
  if (result.state.status === 'open' && result.state.openGoals.length > 0)
    return Object.freeze({ applicability: 'checked_with_goals', reason: 'candidate_checked_with_goals' });
  return Object.freeze({ applicability: 'not_checked', reason: 'candidate_evidence_incomplete' });
}

export function resolveMathSearchPlan(
  input: Readonly<{
    searchMode?: MathSearchMode;
    candidateCount: number;
    premiseQuery?: string;
    lookahead?: boolean;
  }>
): ResolvedMathSearchPlan {
  if (!Number.isSafeInteger(input.candidateCount) || input.candidateCount < 0)
    throw new Error('math_search_candidate_count_invalid');
  const hasCandidates = input.candidateCount > 0;
  const hasQuery = Boolean(input.premiseQuery?.trim());
  const requested = input.searchMode ?? 'auto';
  if (hasCandidates && hasQuery) throw new Error('math_search_mode_conflict');
  const mode = requested === 'auto' ? (hasCandidates ? 'provided' : hasQuery ? 'premises' : 'generic') : requested;
  if (mode === 'provided' && !hasCandidates) throw new Error('math_search_candidates_required');
  if (mode !== 'provided' && hasCandidates) throw new Error('math_search_mode_conflict');
  if (mode === 'generic' && hasQuery) throw new Error('math_search_mode_conflict');
  if (mode === 'premises' && !hasQuery) throw new Error('math_search_premise_query_required');
  if (mode === 'provided' && input.lookahead === true) throw new Error('math_search_lookahead_conflict');
  return Object.freeze({
    mode,
    retrieve: mode === 'premises',
    generateGeneric: mode === 'generic',
    preserveOrder: mode === 'provided',
    lookahead: mode !== 'provided' && input.lookahead === true,
  });
}

const digest = (value: string): string => crypto.createHash('sha256').update(value).digest('hex');
const MAX_RECOVERED_ATTEMPTS = 128;
const WAL_READ_CHUNK_BYTES = 64 * 1024;
const MAX_WAL_RECORD_BYTES = 4 * 1024 * 1024;

function readMathJsonLines(file: string, visit: (value: unknown) => void): number {
  const descriptor = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
  const chunk = Buffer.allocUnsafe(WAL_READ_CHUNK_BYTES);
  const decoder = new TextDecoder('utf-8', { fatal: true });
  let pending: Buffer[] = [];
  let pendingBytes = 0;
  let skippingOversizedRecord = false;
  let skippedRecords = 0;
  const finishRecord = () => {
    if (skippingOversizedRecord) skippedRecords += 1;
    if (!skippingOversizedRecord && pendingBytes) {
      try {
        const line = decoder.decode(Buffer.concat(pending, pendingBytes));
        if (line.trim()) visit(JSON.parse(line));
      } catch {
        // Corrupt UTF-8, interrupted JSON, and invalid records are local to this line.
        skippedRecords += 1;
      }
    }
    pending = [];
    pendingBytes = 0;
    skippingOversizedRecord = false;
  };
  try {
    while (true) {
      const bytesRead = fs.readSync(descriptor, chunk, 0, chunk.length, null);
      if (!bytesRead) break;
      let offset = 0;
      while (offset < bytesRead) {
        const newline = chunk.subarray(0, bytesRead).indexOf(10, offset);
        const end = newline < 0 ? bytesRead : newline;
        if (!skippingOversizedRecord) {
          if (pendingBytes + end - offset > MAX_WAL_RECORD_BYTES) {
            // Drop the entire oversized line, including its later chunks, until LF.
            pending = [];
            pendingBytes = 0;
            skippingOversizedRecord = true;
          } else if (end > offset) {
            pending.push(Buffer.from(chunk.subarray(offset, end)));
            pendingBytes += end - offset;
          }
        }
        if (newline >= 0) finishRecord();
        offset = end + 1;
      }
    }
    // Preserve complete records without a trailing LF; incomplete tails are ignored.
    finishRecord();
  } finally {
    fs.closeSync(descriptor);
  }
  return skippedRecords;
}

function retainNewestRecoveredAttempt(attempts: LeanProofRecoveredAttempt[], attempt: LeanProofRecoveredAttempt): void {
  attempts.push(attempt);
  if (attempts.length > MAX_RECOVERED_ATTEMPTS) attempts.splice(0, attempts.length - MAX_RECOVERED_ATTEMPTS);
}
const sessions = new Map<string, MathematicsLeanProofSession>();
// Retain only the identity of a successfully synced file; checkpoint contents stay on disk.
const durableCheckpointIdentities = new WeakMap<MathematicsLeanProofSession, string>();
const checkpointFileIdentity = (file: string): string => {
  const stat = fs.lstatSync(file, { bigint: true });
  return [stat.dev, stat.ino, stat.size, stat.mtimeNs, stat.ctimeNs].join(':');
};
const sessionPins = new Map<string, number>();
let evictedSessionCount = 0;
const draftSearches = new Map<
  string,
  { fingerprint: string; result: Awaited<ReturnType<typeof searchLeanProofActions>> }
>();
const queues = new Map<string, Promise<unknown>>();
const recoveredJournals = new Map<
  string,
  { sessionId: string; environment: string; attempts: LeanProofRecoveredAttempt[] }
>();

async function retireMathWorkerProofSession(key: string): Promise<void> {
  const retired = sessions.get(key);
  sessions.delete(key);
  draftSearches.delete(key);
  recoveredJournals.delete(key);
  if (retired) {
    evictedSessionCount += 1;
    await retired.close();
  }
}

async function sweepMathWorkerProofSessions(limit: number): Promise<void> {
  while (sessions.size > limit) {
    // Successful access moves the session to the end; this map is the LRU order.
    const oldest = [...sessions.keys()].find((key) => !(sessionPins.get(key) ?? 0));
    if (!oldest) break;
    // eslint-disable-next-line no-await-in-loop -- each transport is closed before selecting the next victim.
    await retireMathWorkerProofSession(oldest);
  }
}

export function readMathWorkerProofRuntimeMetrics() {
  return Object.freeze({
    liveSessions: sessions.size,
    pinnedSessions: sessionPins.size,
    evictedSessions: evictedSessionCount,
    evictedBranchProjections: evictedBranchProjectionCount,
    sessions: Object.freeze(
      [...sessions.entries()].map(([key, session]) => Object.freeze({ key, ...session.cacheMetrics() }))
    ),
    branchStores: Object.freeze(
      [...branchProjections.values()].map((projection) =>
        Object.freeze({
          key: projection.key,
          directoryScans: projection.directoryScans,
          fullSnapshotReads: projection.fullSnapshotReads,
          fullSnapshotReadBytes: projection.fullSnapshotReadBytes,
          snapshotHashCount: projection.snapshotHashCount,
          metadataComparisons: projection.metadataComparisons,
          invalidBranches: projection.invalidBranches.size,
          snapshotWrites: projection.snapshotWrites,
          indexWrites: projection.indexWrites,
          indexRepairs: projection.indexRepairs,
        })
      )
    ),
  });
}
const suppliedCandidate = z
  .object({
    kind: z.enum(['tactic', 'premise', 'rewrite', 'constructor', 'cases', 'induction', 'helper', 'import']),
    payload: z.string().trim().min(1),
    source: z.string().min(1),
  })
  .strict();
const branchMetadata = z.object({
  branchId: z.string().regex(/^[a-f0-9]{64}$/u),
  stateId: z.string(),
  sourceHash: z.string(),
  routeFingerprint: z.string().optional(),
  goalFingerprint: z.string(),
  openGoalCount: z.number().int().nonnegative(),
  status: z.enum(['open', 'closed', 'failed', 'timeout']),
  capabilityAdded: z.boolean().optional(),
});
type ProofBranchMetadata = z.infer<typeof branchMetadata>;
type ProofBranchProjection = {
  root: string;
  key: string;
  branches: Map<string, ProofBranchMetadata>;
  stamps: Map<string, Readonly<{ size: number; mtimeMs: number }>>;
  invalidBranches: Map<string, string>;
  loaded: boolean;
  dirty: boolean;
  generation: number;
  sortedGeneration: number;
  sortedBranches: readonly ProofBranchMetadata[];
  lastAccess: number;
  checkpointSize: number;
  directoryScans: number;
  fullSnapshotReads: number;
  fullSnapshotReadBytes: number;
  snapshotHashCount: number;
  metadataComparisons: number;
  snapshotWrites: number;
  indexWrites: number;
  indexRepairs: number;
};
const branchProjections = new Map<string, ProofBranchProjection>();
const writableBranchProjections = new Set<string>();
const MAX_BRANCH_PROJECTIONS = 64;
const MAX_BRANCH_WARNINGS = 8;
let branchProjectionClock = 0;
let evictedBranchProjectionCount = 0;

const touchBranchProjection = (projection: ProofBranchProjection): void => {
  projection.lastAccess = ++branchProjectionClock;
};

const markBranchProjectionChanged = (projection: ProofBranchProjection): void => {
  projection.generation += 1;
  projection.sortedGeneration = -1;
  projection.dirty = true;
};

const sortedProofBranches = (projection: ProofBranchProjection): readonly ProofBranchMetadata[] => {
  touchBranchProjection(projection);
  if (projection.sortedGeneration !== projection.generation) {
    projection.sortedBranches = Object.freeze(
      [...projection.branches.values()].toSorted((left, right) => {
        projection.metadataComparisons += 1;
        return left.branchId.localeCompare(right.branchId);
      })
    );
    projection.sortedGeneration = projection.generation;
  }
  return projection.sortedBranches;
};

const branchProjection = (root: string, key: string): ProofBranchProjection => {
  const cacheKey = `${root}\0${key}`;
  let projection = branchProjections.get(cacheKey);
  if (!projection) {
    projection = {
      root,
      key,
      branches: new Map(),
      stamps: new Map(),
      invalidBranches: new Map(),
      loaded: false,
      dirty: false,
      generation: 0,
      sortedGeneration: -1,
      sortedBranches: Object.freeze([]),
      lastAccess: ++branchProjectionClock,
      checkpointSize: 0,
      directoryScans: 0,
      fullSnapshotReads: 0,
      fullSnapshotReadBytes: 0,
      snapshotHashCount: 0,
      metadataComparisons: 0,
      snapshotWrites: 0,
      indexWrites: 0,
      indexRepairs: 0,
    };
    branchProjections.set(cacheKey, projection);
    while (branchProjections.size > MAX_BRANCH_PROJECTIONS) {
      const victim = [...branchProjections.entries()]
        .filter(([candidate]) => candidate !== cacheKey)
        .toSorted((left, right) => left[1].lastAccess - right[1].lastAccess)[0];
      if (!victim) break;
      if (victim[1].dirty && writableBranchProjections.has(victim[0])) {
        try {
          flushProofBranchProjection(victim[1]);
        } catch {
          // Snapshot files remain authoritative; the derived index is rebuilt on demand.
        }
      }
      branchProjections.delete(victim[0]);
      writableBranchProjections.delete(victim[0]);
      evictedBranchProjectionCount += 1;
    }
  }
  touchBranchProjection(projection);
  return projection;
};

function regularPath(root: string, relative: string, createParents = false): string {
  const parts = relative.replaceAll('\\', '/').split('/');
  if (
    parts.some((part) => !part || part === '.' || part === '..') ||
    /^[A-Za-z]:/u.test(relative) ||
    path.isAbsolute(relative)
  )
    throw new Error('Proof session requires a project-relative path');
  let current = root;
  for (let index = 0; index < parts.length; index += 1) {
    current = path.join(current, parts[index]!);
    if (createParents && index < parts.length - 1 && !fs.existsSync(current)) fs.mkdirSync(current, { mode: 0o700 });
    if (!fs.existsSync(current) && createParents && index === parts.length - 1) break;
    const stat = fs.lstatSync(current);
    if (stat.isSymbolicLink() || (index < parts.length - 1 ? !stat.isDirectory() : !stat.isFile()))
      throw new Error('Proof session path is not regular');
  }
  return current;
}

type StoredProofBranch = Readonly<{
  snapshot: MathematicsLeanSessionSnapshot;
  preconditionSourceHash?: string;
}>;

function existingWorkerProofDirectory(root: string): string | undefined {
  let current = root;
  for (const part of ['.deepscientist', 'math', 'worker-proof']) {
    current = path.join(current, part);
    if (!fs.existsSync(current)) return undefined;
    const stat = fs.lstatSync(current);
    if (!stat.isDirectory() || stat.isSymbolicLink()) throw new Error('Proof branch directory is not regular');
  }
  return current;
}

function readProofBranch(root: string, key: string, id: string): StoredProofBranch {
  if (!/^[a-f0-9]{64}$/u.test(id)) throw new Error('Invalid proof branch identity');
  const branchPrefix = `${key}.branch-`;
  const file = regularPath(root, `.deepscientist/math/worker-proof/${branchPrefix}${id}.json`);
  const projection = branchProjection(root, key);
  projection.fullSnapshotReads += 1;
  projection.fullSnapshotReadBytes += fs.statSync(file).size;
  const value = readMathJson(file) as {
    key: string;
    id: string;
    digest: string;
    snapshot: MathematicsLeanSessionSnapshot;
    preconditionSourceHash?: string;
  };
  projection.snapshotHashCount += 1;
  if (
    value.key !== key ||
    value.id !== id ||
    value.digest !== digest(canonicalMathJson(value.snapshot)) ||
    id !== value.digest ||
    value.snapshot?.state?.sourceHash !== digest(value.snapshot?.sourceText ?? '')
  )
    throw new Error('Proof branch identity mismatch');
  return Object.freeze({
    snapshot: value.snapshot,
    ...(typeof value.preconditionSourceHash === 'string'
      ? { preconditionSourceHash: value.preconditionSourceHash }
      : {}),
  });
}

function invalidateProofBranch(root: string, key: string, id: string, reason: string): void {
  const projection = branchProjection(root, key);
  const existed = projection.branches.delete(id);
  projection.stamps.delete(id);
  projection.invalidBranches.set(id, reason);
  if (existed) markBranchProjectionChanged(projection);
}

function proofBranchMetadata(
  snapshot: MathematicsLeanSessionSnapshot,
  branchId: string
): z.infer<typeof branchMetadata> {
  return branchMetadata.parse({
    branchId,
    stateId: snapshot.state.stateId,
    sourceHash: snapshot.state.sourceHash,
    routeFingerprint: snapshot.state.routeFingerprint,
    goalFingerprint: snapshot.state.goalFingerprint,
    openGoalCount: snapshot.state.openGoals.length,
    status: snapshot.state.status,
    capabilityAdded:
      snapshot.state.actionHistory.at(-1)?.outcome === 'unchanged' &&
      ['helper', 'import'].includes(snapshot.state.actionHistory.at(-1)?.kind ?? ''),
  });
}

function flushProofBranchProjection(projection: ProofBranchProjection): void {
  if (!projection.dirty) return;
  const indexPath = regularPath(
    projection.root,
    `.deepscientist/math/worker-proof/${projection.key}.branches.index.json`,
    true
  );
  const branches = sortedProofBranches(projection);
  writeMathJsonDurable(indexPath, {
    schema: 'deepscientist.mathematics.worker-proof-branches.v2',
    version: 2,
    key: projection.key,
    branches,
  });
  projection.dirty = false;
  projection.checkpointSize = branches.length;
  projection.indexWrites += 1;
}

function readStoredProofBranches(
  root: string,
  key: string,
  reconcile = false,
  allowIndexWrite = true
): readonly ProofBranchMetadata[] {
  const projection = branchProjection(root, key);
  if (!projection.loaded) {
    const indexPath = path.join(root, '.deepscientist', 'math', 'worker-proof', `${key}.branches.index.json`);
    if (fs.existsSync(indexPath)) {
      try {
        const index = readMathJson(indexPath) as {
          schema?: unknown;
          version?: unknown;
          key?: unknown;
          branches?: unknown;
        };
        const declaresVersion = index.schema !== undefined || index.version !== undefined;
        if (
          (declaresVersion &&
            (index.schema !== 'deepscientist.mathematics.worker-proof-branches.v2' || index.version !== 2)) ||
          index.key !== key ||
          !Array.isArray(index.branches)
        )
          throw new Error('invalid branch index');
        for (const item of index.branches) {
          const parsed = branchMetadata.safeParse(item);
          if (parsed.success) projection.branches.set(parsed.data.branchId, parsed.data);
        }
        if (projection.branches.size) {
          projection.generation += 1;
          projection.sortedGeneration = -1;
        }
        projection.checkpointSize = projection.branches.size;
      } catch {
        projection.branches.clear();
        projection.stamps.clear();
        projection.invalidBranches.clear();
        projection.indexRepairs += 1;
        markBranchProjectionChanged(projection);
      }
    } else {
      projection.indexRepairs += 1;
      markBranchProjectionChanged(projection);
    }
    projection.loaded = true;
    reconcile = true;
  }
  if (!reconcile) return sortedProofBranches(projection);
  const directory = existingWorkerProofDirectory(root);
  if (!directory) return Object.freeze([]);
  projection.directoryScans += 1;
  const branchPrefix = `${key}.branch-`;
  const files = fs
    .readdirSync(directory)
    .filter((file) => file.startsWith(branchPrefix) && file.endsWith('.json'))
    .toSorted();
  const ids = new Set(files.map((file) => file.slice(branchPrefix.length, -5)));
  for (const existing of projection.branches.keys()) {
    if (!ids.has(existing)) {
      projection.branches.delete(existing);
      projection.stamps.delete(existing);
      projection.invalidBranches.set(existing, 'Proof branch snapshot is missing');
      markBranchProjectionChanged(projection);
    }
  }
  for (const id of ids) {
    const file = path.join(directory, `${branchPrefix}${id}.json`);
    let stamp: Readonly<{ size: number; mtimeMs: number }>;
    try {
      const stat = fs.statSync(file);
      stamp = Object.freeze({ size: stat.size, mtimeMs: stat.mtimeMs });
    } catch (error) {
      projection.branches.delete(id);
      projection.stamps.delete(id);
      projection.invalidBranches.set(id, error instanceof Error ? error.message : String(error));
      markBranchProjectionChanged(projection);
      continue;
    }
    const previousStamp = projection.stamps.get(id);
    if (projection.branches.has(id) && previousStamp?.size === stamp.size && previousStamp.mtimeMs === stamp.mtimeMs)
      continue;
    try {
      projection.branches.set(id, proofBranchMetadata(readProofBranch(root, key, id).snapshot, id));
      projection.stamps.set(id, stamp);
      projection.invalidBranches.delete(id);
      markBranchProjectionChanged(projection);
    } catch (error) {
      projection.branches.delete(id);
      projection.stamps.delete(id);
      projection.invalidBranches.set(id, error instanceof Error ? error.message : String(error));
      markBranchProjectionChanged(projection);
    }
  }
  if (allowIndexWrite && projection.dirty && projection.checkpointSize === 0) flushProofBranchProjection(projection);
  return sortedProofBranches(projection);
}

function persistProofBranch(
  root: string,
  key: string,
  snapshot: MathematicsLeanSessionSnapshot,
  preconditionSourceHash?: string
): string {
  writableBranchProjections.add(`${root}\0${key}`);
  const projection = branchProjection(root, key);
  if (!projection.loaded) readStoredProofBranches(root, key);
  const id = digest(canonicalMathJson(snapshot));
  const file = regularPath(root, `.deepscientist/math/worker-proof/${key}.branch-${id}.json`, true);
  if (!fs.existsSync(file)) {
    writeMathJsonDurable(file, {
      key,
      id,
      digest: id,
      snapshot,
      ...(preconditionSourceHash ? { preconditionSourceHash } : {}),
    });
    projection.snapshotWrites += 1;
  }
  const stat = fs.statSync(file);
  projection.stamps.set(id, Object.freeze({ size: stat.size, mtimeMs: stat.mtimeMs }));
  projection.invalidBranches.delete(id);
  if (!projection.branches.has(id)) {
    projection.branches.set(id, proofBranchMetadata(snapshot, id));
    markBranchProjectionChanged(projection);
  }
  if (projection.branches.size >= 64 && projection.branches.size >= Math.max(64, projection.checkpointSize * 2))
    flushProofBranchProjection(projection);
  return id;
}

/** Worker construction feedback. Only the independent verifier grants proof authority. */
export async function runMathWorkerProofAction(request: MathWorkerProofActionRequest) {
  if (request.timeoutMs !== undefined && (!Number.isFinite(request.timeoutMs) || request.timeoutMs <= 0))
    throw new Error('Proof session timeoutMs must be a positive finite number');
  const deadlineAt =
    request.timeoutMs === undefined ? undefined : performance.now() + Math.max(1, Math.floor(request.timeoutMs));
  const remainingTimeoutMs = (): number | undefined =>
    deadlineAt === undefined ? undefined : Math.max(0, deadlineAt - performance.now());
  const root = fs.realpathSync(request.workspaceRoot);
  const sourceFile = request.sourceFile.replaceAll('\\', '/');
  if (!isAllowedMathProofSource([request.projectRelative, sourceFile].filter(Boolean).join('/')))
    throw new Error('Proof session source is not an allowed Lean candidate');
  const projectRoot = request.projectRelative
    ? path.dirname(regularPath(root, `${request.projectRelative}/lean-toolchain`))
    : root;
  const sourcePath = regularPath(projectRoot, sourceFile);
  const runIdentity = readMathRunHistoryIdentity(request.env);
  const proofScopeKey = digest(
    JSON.stringify([
      root,
      request.projectRelative ?? '',
      sourceFile,
      request.statementHash,
      request.episodeId,
      runIdentity ?? null,
    ])
  );
  const key = digest(JSON.stringify([proofScopeKey, request.routeFingerprint, request.routeRevision ?? 0]));
  const initialRouteFingerprint =
    request.initialRouteFingerprint ?? request.acceptedRouteFingerprints?.[0] ?? request.routeFingerprint;
  const acceptedRoutes = [
    ...new Set([initialRouteFingerprint, request.routeFingerprint, ...(request.acceptedRouteFingerprints ?? [])]),
  ];
  const legacyStores = acceptedRoutes.map((routeFingerprint) => ({
    routeFingerprint,
    key: digest(
      JSON.stringify([
        root,
        request.projectRelative ?? '',
        sourceFile,
        request.statementHash,
        routeFingerprint,
        request.episodeId,
        runIdentity ?? null,
      ])
    ),
  }));
  const legacyStoreKeys = legacyStores.map(({ key: legacyKey }) => legacyKey);
  const branchStorageKeys = [proofScopeKey, ...legacyStoreKeys.filter((candidate) => candidate !== proofScopeKey)];
  const queueKey = sourcePath;
  const operationStateReleases: Array<() => void> = [];
  let operationSession: MathematicsLeanProofSession | undefined;
  const retainForOperation = (stateId: string): void => {
    if (operationSession) operationStateReleases.push(operationSession.retainState(stateId));
  };
  sessionPins.set(key, (sessionPins.get(key) ?? 0) + 1);
  const operation = (queues.get(queueKey) ?? Promise.resolve())
    .catch((): undefined => undefined)
    .then(async () => {
      if (request.signal?.aborted)
        return {
          status: 'unavailable' as const,
          executionDisposition: 'aborted' as const,
          diagnostics: 'Proof session request was aborted before execution',
          durationMs: 0,
          authority: 'lean-process' as const,
          solverReady: false as const,
        };
      if (remainingTimeoutMs() === 0)
        return {
          status: 'unavailable' as const,
          executionDisposition: 'timed_out' as const,
          diagnostics: 'Proof session request timed out while queued',
          durationMs: 0,
          authority: 'lean-process' as const,
          solverReady: false as const,
        };
      const source = fs.readFileSync(sourcePath, 'utf8');
      if (digest(source) !== request.expectedSourceHash)
        throw new Error('Proof session source changed; refresh its source hash before retrying');
      const branchOffset = request.branchOffset ?? 0;
      const branchPageSize = request.branchPageSize ?? 32;
      if (
        !Number.isSafeInteger(branchOffset) ||
        branchOffset < 0 ||
        !Number.isSafeInteger(branchPageSize) ||
        branchPageSize < 1
      )
        throw new Error('Proof branch pagination is invalid');
      const branchPage = (reconcile = false) => {
        const merged = new Map<string, ProofBranchMetadata>();
        const conflicted = new Set<string>();
        const warnings: string[] = [];
        let invalidBranchCount = 0;
        for (const storageKey of branchStorageKeys) {
          const stored = readStoredProofBranches(root, storageKey, reconcile, storageKey === proofScopeKey);
          const projection = branchProjection(root, storageKey);
          invalidBranchCount += projection.invalidBranches.size;
          for (const [branchId, reason] of projection.invalidBranches) {
            if (warnings.length >= MAX_BRANCH_WARNINGS) break;
            warnings.push(`${storageKey}:${branchId}: ${reason}`);
          }
          for (const branch of stored) {
            if (conflicted.has(branch.branchId)) continue;
            const prior = merged.get(branch.branchId);
            if (!prior) {
              merged.set(branch.branchId, branch);
              continue;
            }
            projection.metadataComparisons += 1;
            if (canonicalMathJson(prior) === canonicalMathJson(branch)) continue;
            merged.delete(branch.branchId);
            conflicted.add(branch.branchId);
            invalidBranchCount += 1;
            if (warnings.length < MAX_BRANCH_WARNINGS)
              warnings.push(`${branch.branchId}: conflicting metadata across accepted branch stores`);
          }
        }
        const branches = [...merged.values()];
        const branchGeneration = digest(
          canonicalMathJson(
            branchStorageKeys.map((storageKey) => {
              const projection = branchProjection(root, storageKey);
              return [storageKey, projection.generation, projection.branches.size, projection.invalidBranches.size];
            })
          )
        );
        if (request.branchGeneration && request.branchGeneration !== branchGeneration)
          throw new Error('math_proof_branch_cursor_stale');
        return {
          branches: branches.slice(branchOffset, branchOffset + branchPageSize),
          branchTotal: branches.length,
          nextBranchOffset: branchOffset + branchPageSize < branches.length ? branchOffset + branchPageSize : null,
          branchGeneration,
          invalidBranchCount,
          branchWarnings: Object.freeze(warnings),
        };
      };
      if (request.action === 'branches')
        return {
          status: 'listed' as const,
          executionDisposition: 'completed' as const,
          authority: 'lean-process' as const,
          solverReady: false as const,
          sourceHash: request.expectedSourceHash,
          ...branchPage(true),
          durationMs: 0,
        };
      const checkpointPath = regularPath(root, `.deepscientist/math/worker-proof/${key}.json`, true);
      const identityPath = regularPath(root, `.deepscientist/math/worker-proof/${proofScopeKey}.identity.json`, true);
      const legacyIdentities = legacyStores.flatMap(({ key: legacyKey, routeFingerprint }) => {
        try {
          const identity = regularPath(root, `.deepscientist/math/worker-proof/${legacyKey}.identity.json`);
          return fs.existsSync(identity) ? [{ path: identity, legacyKey, routeFingerprint }] : [];
        } catch {
          return [];
        }
      });
      if (!fs.existsSync(identityPath)) {
        const relativeSourcePath = path.relative(root, sourcePath).replaceAll(path.sep, '/');
        const recoveredIdentities = legacyIdentities.map(({ path: legacyPath, legacyKey, routeFingerprint }) => {
          const identity = readMathJson(legacyPath) as Record<string, unknown>;
          if (
            identity.sessionKey !== legacyKey ||
            identity.workspaceRoot !== root ||
            identity.statementHash !== request.statementHash ||
            identity.sourceFile !== relativeSourcePath ||
            identity.runIdentity !== runIdentity ||
            typeof identity.contractSource !== 'string' ||
            identity.contractSourceHash !== digest(identity.contractSource)
          )
            throw new Error('math_proof_contract_recovery_required');
          return { identity, routeFingerprint };
        });
        const initialIdentity = recoveredIdentities.find(
          (candidate) => candidate.routeFingerprint === initialRouteFingerprint
        );
        const recoveredHashes = new Set(recoveredIdentities.map(({ identity }) => identity.contractSourceHash));
        if (!initialIdentity && recoveredHashes.size > 1) throw new Error('math_proof_contract_recovery_required');
        const recoveredIdentity = initialIdentity?.identity ?? recoveredIdentities[0]?.identity;
        const historyDirectory = existingWorkerProofDirectory(root);
        const historyKeys = new Set([proofScopeKey, key, ...legacyStoreKeys]);
        const hasExistingHistory = Boolean(
          historyDirectory &&
          fs
            .readdirSync(historyDirectory)
            .some((entry) =>
              [...historyKeys].some(
                (historyKey) =>
                  entry === `${historyKey}.json` ||
                  entry === `${historyKey}.attempts.jsonl` ||
                  entry === `${historyKey}.actions.jsonl` ||
                  entry.startsWith(`${historyKey}.branch-`)
              )
            )
        );
        if (!recoveredIdentity && hasExistingHistory) throw new Error('math_proof_contract_recovery_required');
        writeMathJsonDurable(identityPath, {
          ...recoveredIdentity,
          schema: 'deepscientist.mathematics.worker-proof-identity.v1',
          sessionKey: proofScopeKey,
          workspaceRoot: root,
          ...(runIdentity ? { runIdentity } : {}),
          problemId: request.problemId ?? request.statementHash,
          statementHash: request.statementHash,
          sourceFile: relativeSourcePath,
          createdAt: new Date().toISOString(),
          contractSource:
            typeof recoveredIdentity?.contractSource === 'string'
              ? recoveredIdentity.contractSource
              : (request.contractSource ?? source),
          contractSourceHash:
            typeof recoveredIdentity?.contractSourceHash === 'string'
              ? recoveredIdentity.contractSourceHash
              : digest(request.contractSource ?? source),
        });
      }
      const identity = readMathJson(identityPath) as Record<string, unknown>;
      const expectedIdentitySourceFile = path.relative(root, sourcePath).replaceAll(path.sep, '/');
      if (
        identity.sessionKey !== proofScopeKey ||
        identity.workspaceRoot !== root ||
        identity.runIdentity !== runIdentity ||
        identity.statementHash !== request.statementHash ||
        identity.sourceFile !== expectedIdentitySourceFile ||
        typeof identity.contractSource !== 'string' ||
        digest(identity.contractSource) !== identity.contractSourceHash ||
        (request.contractSource !== undefined && identity.contractSource !== request.contractSource)
      )
        throw new Error('math_proof_contract_recovery_required');
      const contractSource = identity.contractSource;
      const traceRef = `.deepscientist/math/worker-proof/${proofScopeKey}.attempts.jsonl`;
      const recordAttempt = (attempt: {
        operation: string;
        sourceHash: string;
        outcome: string;
        durationMs?: number;
        diagnostics?: string;
        [field: string]: unknown;
      }) => {
        const file = regularPath(root, traceRef, true);
        const descriptor = fs.openSync(
          file,
          fs.constants.O_APPEND | fs.constants.O_CREAT | fs.constants.O_WRONLY | fs.constants.O_NOFOLLOW,
          0o600
        );
        try {
          fs.writeFileSync(
            descriptor,
            `${JSON.stringify({
              schema: 'deepscientist.mathematics.worker-proof-attempt.v1',
              attemptId: crypto.randomUUID(),
              sessionKey: proofScopeKey,
              executionKey: key,
              workspaceRoot: root,
              ...(runIdentity ? { runIdentity } : {}),
              problemId: request.problemId ?? request.statementHash,
              statementHash: request.statementHash,
              sourceFile: path.relative(root, sourcePath).replaceAll(path.sep, '/'),
              recordedAt: new Date().toISOString(),
              ...attempt,
              durationMs: attempt.durationMs ?? 0,
            })}\n`
          );
          fs.fsyncSync(descriptor);
        } finally {
          fs.closeSync(descriptor);
        }
      };
      let session = sessions.get(key);
      let durationMs = 0;
      const recoveryDiagnostics: string[] = [];
      // Preserve the last checked source before an ordinary file edit replaces it.
      // Existing branch checkout replays Lean and retains all adoption guards.
      let priorEditSnapshot = session?.snapshot();
      let priorEditDiagnostics = session?.diagnostics;
      if (!priorEditSnapshot && fs.existsSync(checkpointPath)) {
        try {
          const stored = readMathJson(checkpointPath) as MathematicsLeanSessionSnapshot & { diagnostics?: string };
          if (
            stored.state?.statementHash === request.statementHash &&
            stored.state?.sourceHash === digest(stored.sourceText)
          ) {
            priorEditSnapshot = stored;
            if (typeof stored.diagnostics === 'string') priorEditDiagnostics = stored.diagnostics;
          }
        } catch {
          // The normal cold recovery path reports unreadable checkpoints below.
        }
      }
      let previousSourceBranchId: string | undefined;
      if (priorEditSnapshot && priorEditSnapshot.sourceText !== source && priorEditSnapshot.state.status !== 'failed') {
        try {
          previousSourceBranchId = persistProofBranch(root, proofScopeKey, priorEditSnapshot);
        } catch {
          recoveryDiagnostics.push('Previous checked source could not be archived as a recovery branch.');
        }
      }
      if (!session) {
        const attemptedAt = performance.now();
        const started = await startMathematicsLeanSession({
          ...request,
          sourceText: source,
          contractSource,
          timeoutMs: remainingTimeoutMs(),
        }).catch((error: unknown) => {
          recordAttempt({
            operation: 'probe',
            sourceHash: request.expectedSourceHash,
            outcome: 'unavailable',
            durationMs: performance.now() - attemptedAt,
            diagnostics: String(error),
          });
          throw error;
        });
        recordAttempt({
          operation: 'probe',
          sourceHash: request.expectedSourceHash,
          outcome: started.state?.status ?? started.status,
          durationMs: started.durationMs,
          diagnostics: started.diagnostics,
        });
        durationMs += started.durationMs ?? 0;
        if (!started.session)
          return {
            status: started.status,
            diagnostics: started.diagnostics,
            durationMs,
            ...(started.executionDisposition ? { executionDisposition: started.executionDisposition } : {}),
            authority: 'lean-process' as const,
            solverReady: false as const,
            traceRef,
          };
        session = started.session;
        sessions.set(key, session);
        if (fs.existsSync(checkpointPath)) {
          try {
            const snapshot = readMathJson(checkpointPath) as MathematicsLeanSessionSnapshot;
            if (snapshot?.sourceText === source) {
              const replayed = await session.replay(snapshot, request.signal, remainingTimeoutMs(), {
                reuseCurrentSource: true,
              });
              recordAttempt({
                operation: 'replay',
                sourceHash: snapshot.state.sourceHash,
                outcome: replayed.status,
                durationMs: replayed.durationMs,
                diagnostics: replayed.diagnostics,
              });
              durationMs += replayed.durationMs ?? 0;
              // A stale dependency may invalidate replay; the newly compiled live state remains usable.
              if (replayed.status !== 'restored' && request.signal?.aborted)
                return {
                  status: 'unavailable' as const,
                  diagnostics: replayed.diagnostics,
                  durationMs,
                  authority: 'lean-process' as const,
                  solverReady: false as const,
                };
            }
          } catch {
            recoveryDiagnostics.push('Stored proof snapshot could not be replayed; rebuilt state from current source.');
          }
        }
      } else {
        const synchronized = await session.synchronizeSource(source, request.signal, remainingTimeoutMs());
        if (synchronized.durationMs !== undefined)
          recordAttempt({
            operation: 'probe',
            sourceHash: request.expectedSourceHash,
            outcome: synchronized.status,
            durationMs: synchronized.durationMs,
            diagnostics: synchronized.diagnostics,
          });
        durationMs += synchronized.durationMs ?? 0;
        if (synchronized.status === 'invalid' || synchronized.status === 'unavailable')
          return {
            status: synchronized.status,
            diagnostics: synchronized.diagnostics,
            durationMs,
            ...(synchronized.executionDisposition ? { executionDisposition: synchronized.executionDisposition } : {}),
            authority: 'lean-process' as const,
            solverReady: false as const,
          };
      }
      sessions.delete(key);
      sessions.set(key, session);
      await sweepMathWorkerProofSessions(Math.max(1, request.cacheLimits?.liveSessions ?? 16));
      operationSession = session;
      const baseline = session.snapshot();
      retainForOperation(baseline.state.stateId);
      const restoreBaseline = (): void => {
        const restored = session!.restore(baseline);
        if (restored.status === 'invalid') throw new Error('math_proof_recovery_required');
      };
      let checkout: MathematicsLeanSessionSnapshot | undefined;
      let checkoutResult: MathematicsLeanSessionActionResult | undefined;
      if (request.action === 'checkout') {
        if (!request.branchId) throw new Error('Proof checkout requires branchId');
        let stored: StoredProofBranch | undefined;
        for (const storageKey of branchStorageKeys) {
          try {
            stored = readProofBranch(root, storageKey, request.branchId);
            break;
          } catch (error) {
            const projection = branchProjection(root, storageKey);
            const branchFile = path.join(
              root,
              '.deepscientist',
              'math',
              'worker-proof',
              `${storageKey}.branch-${request.branchId}.json`
            );
            if (projection.branches.has(request.branchId) || fs.existsSync(branchFile))
              invalidateProofBranch(
                root,
                storageKey,
                request.branchId,
                error instanceof Error ? error.message : String(error)
              );
            // Continue through accepted legacy route stores before rejecting this branch.
          }
        }
        if (!stored)
          return {
            status: 'invalid' as const,
            executionDisposition: 'invalid' as const,
            diagnostics: 'math_proof_branch_missing_or_corrupt',
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
        try {
          persistProofBranch(root, proofScopeKey, baseline);
        } catch {
          throw new Error('Current proof source could not be preserved before historical checkout');
        }
        checkout = stored.snapshot;
        if (
          checkout.state.episodeId !== request.episodeId ||
          checkout.state.statementHash !== request.statementHash ||
          checkout.state.sourceFile !== sourceFile ||
          checkout.state.sourceHash !== digest(checkout.sourceText) ||
          !checkout.state.routeFingerprint ||
          !acceptedRoutes.includes(checkout.state.routeFingerprint)
        ) {
          throw new Error('math_proof_branch_contract_mismatch');
        }
        const restored = await session.checkCandidateSource(checkout.sourceText, request.signal, remainingTimeoutMs());
        recordAttempt({
          operation: 'replay',
          sourceHash: checkout.state.sourceHash,
          outcome: restored.status,
          durationMs: restored.durationMs,
          diagnostics: restored.diagnostics,
        });
        durationMs += restored.durationMs ?? 0;
        checkoutResult = restored;
        const historicalGoalCompatible =
          stored.snapshot.state.status === 'closed' ||
          restored.state?.goalFingerprint === stored.snapshot.state.goalFingerprint;
        if (
          !historicalGoalCompatible ||
          !restored.state ||
          !isUsableCandidateResult(
            session,
            baseline.state,
            {
              source: checkout.sourceText,
              kind: 'tactic',
              payload: `checkout ${request.branchId}`,
            },
            restored
          )
        ) {
          const rolledBack = session.restore(baseline);
          if (rolledBack.status === 'invalid') throw new Error('math_proof_recovery_required');
          return {
            status: 'unavailable' as const,
            executionDisposition:
              restored.executionDisposition ?? (restored.status === 'invalid' ? 'invalid' : 'unavailable'),
            diagnostics: `Proof branch replay failed: ${restored.diagnostics}`,
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
        }
        retainForOperation(restored.state.stateId);
      }
      const goalIndex = request.goalIndex ?? 0;
      const offset = request.candidateOffset ?? 0;
      const suppliedCandidates = z
        .array(suppliedCandidate)
        .parse(request.candidates ?? []) as LeanProofActionCandidate[];
      const searchPlan =
        request.action === 'search'
          ? resolveMathSearchPlan({
              searchMode: request.searchMode,
              candidateCount: suppliedCandidates.length,
              premiseQuery: request.premiseQuery,
              lookahead: request.lookahead,
            })
          : undefined;
      const batchSize = request.candidateBatchSize ?? (searchPlan?.mode === 'provided' ? 12 : 4);
      if (![goalIndex, offset, batchSize].every(Number.isSafeInteger) || goalIndex < 0 || offset < 0 || batchSize < 1)
        throw new Error('Proof search pagination and goal index must be nonnegative integers');
      if (request.action === 'search' && goalIndex >= session.state.openGoals.length && session.state.openGoals.length)
        throw new Error('Selected proof goal does not exist');
      const location = session.goalLocation(goalIndex);
      if (request.action === 'search' && goalIndex > 0 && !location?.range && !location?.line)
        throw new Error('Selected proof goal lacks a compiler source location; refresh with structured diagnostics');
      const diagnostics = session.diagnostics;
      const failureCategory = classifyLeanProofDiagnostic(diagnostics);
      const recoveryEnvironment = request.action === 'search' ? session.environmentFingerprint : undefined;
      const cachedJournal = recoveredJournals.get(key);
      const journalCached =
        cachedJournal?.sessionId === session.sessionId && cachedJournal?.environment === recoveryEnvironment;
      const recoveredAttempts: LeanProofRecoveredAttempt[] = journalCached ? cachedJournal.attempts : [];
      if (request.action === 'search' && recoveryEnvironment) {
        try {
          const tracePaths = [proofScopeKey, ...legacyStoreKeys]
            .map((storageKey) => {
              try {
                return regularPath(root, `.deepscientist/math/worker-proof/${storageKey}.attempts.jsonl`);
              } catch {
                return undefined;
              }
            })
            .filter((candidate): candidate is string => Boolean(candidate && fs.existsSync(candidate)));
          const parseRecoveredAttempt = (value: unknown): LeanProofRecoveredAttempt | undefined => {
            try {
              const attempt = value as Record<string, unknown>;
              if (
                typeof attempt.sessionKey !== 'string' ||
                ![proofScopeKey, ...legacyStoreKeys].includes(attempt.sessionKey) ||
                attempt.workspaceRoot !== root ||
                attempt.runIdentity !== runIdentity ||
                attempt.statementHash !== request.statementHash ||
                attempt.environmentFingerprint !== recoveryEnvironment ||
                attempt.operation !== 'search' ||
                typeof attempt.preconditionSourceHash !== 'string' ||
                typeof attempt.preconditionGoalFingerprint !== 'string' ||
                typeof attempt.outcome !== 'string'
              )
                return undefined;
              if (
                ['failed', 'invalid'].includes(attempt.outcome) &&
                (typeof attempt.executionKey !== 'string' || attempt.executionKey !== key)
              )
                return undefined;
              const candidate = suppliedCandidate.parse({
                kind: attempt.kind,
                payload: attempt.payload,
                source: attempt.candidateSource,
              });
              if (digest(candidate.source) !== attempt.sourceHash) return undefined;
              return {
                candidate: { kind: candidate.kind!, payload: candidate.payload!, source: candidate.source! },
                preconditionSourceHash: attempt.preconditionSourceHash,
                preconditionGoalFingerprint: attempt.preconditionGoalFingerprint,
                outcome: attempt.outcome,
                ...(attempt.snapshot ? { snapshot: attempt.snapshot as MathematicsLeanSessionSnapshot } : {}),
                capabilityAdded: attempt.capabilityAdded === true,
              };
            } catch {
              return undefined;
            }
          };
          const recoveryKey = (attempt: LeanProofRecoveredAttempt): string =>
            canonicalMathJson([
              attempt.preconditionSourceHash,
              attempt.preconditionGoalFingerprint,
              attempt.candidate.kind,
              attempt.candidate.payload,
              digest(attempt.candidate.source),
            ]);
          const readRecoveryTrace = (tracePath: string, visit: (value: unknown) => void): void => {
            const skipped = readMathJsonLines(tracePath, visit);
            if (skipped) {
              recoveryDiagnostics.push(
                `Attempt history is partial: skipped ${skipped} malformed or oversized record(s) in ${path.basename(tracePath)}.`
              );
            }
          };
          if (!journalCached) {
            for (const tracePath of tracePaths) {
              readRecoveryTrace(tracePath, (value) => {
                const attempt = parseRecoveredAttempt(value);
                if (attempt) retainNewestRecoveredAttempt(recoveredAttempts, attempt);
              });
            }
          } else if (suppliedCandidates.length) {
            const hotKeys = new Set(recoveredAttempts.map(recoveryKey));
            const wantedKeys = new Set(
              suppliedCandidates.map((candidate) =>
                recoveryKey({
                  candidate,
                  preconditionSourceHash: baseline.state.sourceHash,
                  preconditionGoalFingerprint: baseline.state.goalFingerprint,
                  outcome: '',
                })
              )
            );
            for (const hotKey of hotKeys) wantedKeys.delete(hotKey);
            if (wantedKeys.size) {
              const recoveredMisses = new Map<string, LeanProofRecoveredAttempt>();
              for (const tracePath of tracePaths) {
                readRecoveryTrace(tracePath, (value) => {
                  const attempt = parseRecoveredAttempt(value);
                  if (!attempt) return;
                  const attemptKey = recoveryKey(attempt);
                  if (wantedKeys.has(attemptKey)) recoveredMisses.set(attemptKey, attempt);
                });
              }
              for (const attempt of recoveredMisses.values()) retainNewestRecoveredAttempt(recoveredAttempts, attempt);
            }
          }
        } catch {
          /* Legacy runs and unavailable journals continue with live search. */
        }
        recoveredJournals.set(key, {
          sessionId: session.sessionId,
          environment: recoveryEnvironment,
          attempts: recoveredAttempts,
        });
      }
      let retrievedPremises = request.premiseCandidates ?? [];
      if (request.action === 'search' && searchPlan?.retrieve) {
        if (!request.premiseProvider && !request.premiseCandidates)
          throw new Error('math_search_premise_provider_required');
        if (request.signal?.aborted || remainingTimeoutMs() === 0)
          return {
            status: 'unavailable' as const,
            executionDisposition: request.signal?.aborted ? ('aborted' as const) : ('timed_out' as const),
            diagnostics: request.signal?.aborted ? 'math_search_aborted' : 'math_search_timed_out',
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
        const selectedGoal = session.state.openGoals[goalIndex];
        if (!selectedGoal) throw new Error('math_search_selected_goal_unavailable');
        const retrievalEnvironment = session.environmentFingerprint ?? null;
        const beforeRetrieval = {
          sourceHash: digest(fs.readFileSync(sourcePath, 'utf8')),
          environmentFingerprint: retrievalEnvironment,
        };
        try {
          retrievedPremises = request.premiseProvider
            ? await request.premiseProvider(
                {
                  stateId: session.state.stateId,
                  sourceHash: session.state.sourceHash,
                  environmentFingerprint: retrievalEnvironment,
                  proofStateFingerprint: session.state.goalFingerprint,
                  goalIndex,
                  goal: selectedGoal,
                  location: location ?? null,
                },
                { signal: request.signal, remainingTimeoutMs: remainingTimeoutMs() }
              )
            : retrievedPremises;
        } catch (error) {
          const disposition = request.signal?.aborted
            ? ('aborted' as const)
            : remainingTimeoutMs() === 0
              ? ('timed_out' as const)
              : ('unavailable' as const);
          return {
            status: 'unavailable' as const,
            executionDisposition: disposition,
            diagnostics:
              disposition === 'aborted'
                ? 'math_search_aborted'
                : disposition === 'timed_out'
                  ? 'math_search_timed_out'
                  : `math_search_provider_unavailable: ${error instanceof Error ? error.message : String(error)}`,
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
        }
        const sourceChanged =
          beforeRetrieval.sourceHash !== request.expectedSourceHash ||
          digest(fs.readFileSync(sourcePath, 'utf8')) !== request.expectedSourceHash;
        const environmentChanged = beforeRetrieval.environmentFingerprint !== (session.environmentFingerprint ?? null);
        const disposition = request.signal?.aborted
          ? ('aborted' as const)
          : sourceChanged || environmentChanged
            ? ('invalid' as const)
            : remainingTimeoutMs() === 0
              ? ('timed_out' as const)
              : undefined;
        if (disposition)
          return {
            status: disposition === 'invalid' ? ('invalid' as const) : ('unavailable' as const),
            executionDisposition: disposition,
            diagnostics:
              disposition === 'aborted'
                ? 'math_search_aborted'
                : disposition === 'timed_out'
                  ? 'math_search_timed_out'
                  : 'math_search_context_stale',
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
      }
      let blockProviderDisposition: 'aborted' | 'timed_out' | 'unavailable' | undefined;
      let blockProviderDiagnostic: string | undefined;
      let checkedBlocks: readonly CheckedMathProofBlock[] = [];
      if (request.action === 'search' && searchPlan?.mode === 'generic' && request.checkedProofBlocks) {
        const blockEnvironmentBefore = session.environmentFingerprint;
        const controller = new AbortController();
        let timer: ReturnType<typeof setTimeout> | undefined;
        let interrupt: (() => void) | undefined;
        const interrupted = new Promise<readonly CheckedMathProofBlock[]>((resolve) => {
          interrupt = () => {
            controller.abort();
            resolve([]);
          };
        });
        const onAbort = () => {
          blockProviderDisposition = 'aborted';
          interrupt?.();
        };
        request.signal?.addEventListener('abort', onAbort, { once: true });
        const budget = remainingTimeoutMs();
        if (request.signal?.aborted) onAbort();
        else if (budget === 0) {
          blockProviderDisposition = 'timed_out';
          interrupt?.();
        } else if (budget !== undefined)
          timer = setTimeout(() => {
            blockProviderDisposition = 'timed_out';
            interrupt?.();
          }, budget);
        try {
          if (!blockProviderDisposition)
            checkedBlocks = await Promise.race([
              request.checkedProofBlocks(
                {
                  stateId: session.state.stateId,
                  sourceHash: session.state.sourceHash,
                  environmentFingerprint: blockEnvironmentBefore ?? null,
                  proofStateFingerprint: session.state.goalFingerprint,
                  goalIndex,
                  goal: session.state.openGoals[goalIndex] ?? '',
                  location: location ?? null,
                },
                { signal: controller.signal, remainingTimeoutMs: remainingTimeoutMs() }
              ),
              interrupted,
            ]);
        } catch (error) {
          if (!controller.signal.aborted && isMathPlanningSafetyError(error)) throw error;
          blockProviderDisposition = request.signal?.aborted
            ? 'aborted'
            : remainingTimeoutMs() === 0
              ? 'timed_out'
              : 'unavailable';
          blockProviderDiagnostic = error instanceof Error ? error.message : String(error);
        } finally {
          if (timer !== undefined) clearTimeout(timer);
          request.signal?.removeEventListener('abort', onAbort);
        }
        const disposition =
          blockProviderDisposition ??
          (request.signal?.aborted
            ? ('aborted' as const)
            : remainingTimeoutMs() === 0
              ? ('timed_out' as const)
              : digest(fs.readFileSync(sourcePath, 'utf8')) !== request.expectedSourceHash ||
                  session.environmentFingerprint !== blockEnvironmentBefore
                ? ('invalid' as const)
                : undefined);
        if (disposition)
          return {
            status: disposition === 'invalid' ? ('invalid' as const) : ('unavailable' as const),
            executionDisposition: disposition,
            diagnostics: blockProviderDiagnostic ?? `math_block_provider_${disposition}`,
            authority: 'lean-process' as const,
            solverReady: false as const,
            sourceHash: request.expectedSourceHash,
            durationMs,
            ...branchPage(),
          };
      }
      const blockCandidates = checkedBlocks.length
        ? buildMathDiscoveryCandidates(
            {
              source,
              targetLine: location?.line ?? session.goalLine,
              targetRange: location?.range ?? session.goalRange,
              goalIndex: location?.localIndex ?? 0,
              openGoal: session.state.openGoals[goalIndex],
              premises: [],
              diagnostics,
            },
            checkedBlocks
          )
        : [];
      const candidatePool =
        request.action !== 'search' || !searchPlan
          ? []
          : searchPlan.mode === 'provided'
            ? suppliedCandidates
            : searchPlan.mode === 'premises'
              ? generateLeanPremiseActionCandidates({
                  source,
                  targetLine: location?.line ?? session.goalLine,
                  targetRange: location?.range ?? session.goalRange,
                  goalIndex: location?.localIndex ?? 0,
                  openGoal: session.state.openGoals[goalIndex],
                  premises: retrievedPremises,
                  diagnostics,
                })
              : [
                  ...blockCandidates,
                  ...generateLeanProofActionCandidates({
                    source,
                    targetLine: location?.line ?? session.goalLine,
                    targetRange: location?.range ?? session.goalRange,
                    goalIndex: location?.localIndex ?? 0,
                    openGoal: session.state.openGoals[goalIndex],
                    failureCategory,
                    diagnostics,
                  }).filter((candidate) =>
                    isRoutineMathClosureAction(candidate, session.state.openGoals[goalIndex] ?? '')
                  ),
                ];
      const searchEnvironmentFingerprint = request.action === 'search' ? session.environmentFingerprint : undefined;
      const candidateSetHash =
        request.action === 'search'
          ? digest(
              canonicalMathJson({
                version: 'math-search-plan-v2',
                sourceHash: request.expectedSourceHash,
                environmentFingerprint: searchEnvironmentFingerprint ?? null,
                goalIndex,
                goalFingerprint: session.state.goalFingerprint,
                mode: searchPlan?.mode ?? null,
                candidates: candidatePool.map(({ kind, payload, source: candidateSource, provenance }) => ({
                  kind,
                  payload,
                  sourceHash: digest(candidateSource),
                  provenance,
                })),
              })
            )
          : undefined;
      if (request.action === 'search' && offset > 0 && request.candidateSetHash !== candidateSetHash)
        throw new Error('math_search_cursor_stale');
      const candidates = candidatePool.slice(offset, offset + batchSize);
      const searchFingerprint =
        request.action === 'search'
          ? digest(
              JSON.stringify([
                request.expectedSourceHash,
                searchEnvironmentFingerprint,
                digest(session.diagnostics),
                candidateSetHash,
                goalIndex,
                offset,
                batchSize,
                searchPlan?.lookahead ?? false,
                searchPlan?.preserveOrder ?? false,
              ])
            )
          : undefined;
      const priorSearch = draftSearches.get(key);
      const cachedCandidate = priorSearch?.result.best;
      const cachedCandidateReusable =
        request.action === 'search' &&
        priorSearch?.fingerprint === searchFingerprint &&
        Boolean(
          (cachedCandidate?.state &&
            session.snapshotState(cachedCandidate.state.stateId) &&
            isUsableCandidateResult(session, baseline.state, cachedCandidate.candidate, cachedCandidate.result)) ||
          (!cachedCandidate && priorSearch?.result.localClosure)
        );
      const cachedSearch = cachedCandidateReusable ? priorSearch!.result : undefined;
      const searched =
        cachedSearch ??
        (request.action === 'search'
          ? await (searchPlan?.mode === 'generic' ? runMathLocalClosure : searchLeanProofActions)({
              session,
              candidates,
              signal: request.signal,
              timeoutMs: remainingTimeoutMs(),
              commitBest: true,
              performanceRoot: request.historyProjectRoot ?? root,
              episodeId: request.episodeId,
              problemId: request.problemId ?? request.statementHash,
              failureCategory,
              goalIndex,
              lookahead: searchPlan?.lookahead ?? false,
              preserveOrder: searchPlan?.preserveOrder ?? false,
              recoveredAttempts,
              retainForOperation,
              onAttempt: (attempt) => {
                const completedSnapshot =
                  (attempt.result.status === 'advanced' || attempt.result.capabilityAdded) && attempt.result.state
                    ? session.snapshotState(attempt.result.state.stateId)
                    : undefined;
                recordAttempt({
                  operation: 'search',
                  startedAt: attempt.startedAt,
                  recordedAt: attempt.recordedAt,
                  sourceHash: digest(attempt.candidate.source),
                  candidateSource: attempt.candidate.source,
                  kind: attempt.candidate.kind,
                  payload: attempt.candidate.payload,
                  goalIndex: attempt.goalIndex,
                  goalFingerprint: attempt.goalFingerprint,
                  preconditionSourceHash: attempt.baseState.sourceHash,
                  preconditionGoalFingerprint: attempt.baseState.goalFingerprint,
                  environmentFingerprint: session.environmentFingerprint,
                  capabilityAdded: Boolean(attempt.result.capabilityAdded),
                  recoveredFromJournal: Boolean(attempt.result.recoveredFromJournal),
                  ...(completedSnapshot ? { snapshot: completedSnapshot } : {}),
                  outcome: attempt.result.underlyingStatus ?? attempt.result.status,
                  diagnostics: attempt.result.diagnostics,
                  durationMs:
                    attempt.result.reuseKind === 'hot'
                      ? 0
                      : (attempt.result.action?.runtime.durationMs ?? attempt.result.durationMs),
                });
                retainNewestRecoveredAttempt(recoveredAttempts, {
                  candidate: attempt.candidate,
                  preconditionSourceHash: attempt.baseState.sourceHash,
                  preconditionGoalFingerprint: attempt.baseState.goalFingerprint,
                  outcome: attempt.result.underlyingStatus ?? attempt.result.status,
                  ...(completedSnapshot ? { snapshot: completedSnapshot } : {}),
                  capabilityAdded: Boolean(attempt.result.capabilityAdded),
                });
                if (completedSnapshot) {
                  try {
                    persistProofBranch(root, proofScopeKey, completedSnapshot, attempt.baseState.sourceHash);
                  } catch {
                    recoveryDiagnostics.push(
                      'A completed branch remains in the attempt journal but its snapshot file could not be saved.'
                    );
                  }
                }
              },
            }).catch((error: unknown) => {
              restoreBaseline();
              throw error;
            })
          : undefined);
      durationMs += cachedSearch ? 0 : (searched?.durationMs ?? 0);
      const historyRef = `.deepscientist/math/worker-proof/${proofScopeKey}.actions.jsonl`;
      try {
        archiveLeanProofActions(
          root,
          historyRef,
          cachedSearch
            ? []
            : (searched?.executedAttempts.flatMap(
                (attempt) =>
                  attempt.result.state?.actionHistory ?? (attempt.result.action ? [attempt.result.action] : [])
              ) ?? [])
        );
      } catch (error) {
        restoreBaseline();
        throw error;
      }
      for (const branch of searched?.branches ?? []) {
        if (
          !branch.state ||
          ['failed', 'unavailable', 'invalid', 'duplicate'].includes(branch.result.status) ||
          (branch.result.status === 'unchanged' && branch.state.sourceHash === baseline.state.sourceHash)
        )
          continue;
        const snapshot = session.snapshotState(branch.state.stateId);
        if (!snapshot) continue;
        try {
          persistProofBranch(root, proofScopeKey, snapshot, baseline.state.sourceHash);
        } catch {
          recoveryDiagnostics.push('A proof branch could not be persisted; the current draft remains available.');
        }
      }
      const best = searched?.best;
      const selected = checkout
        ? checkoutResult?.state
          ? {
              candidate: { source: checkout.sourceText, kind: 'tactic', payload: `checkout ${request.branchId}` },
              state: checkoutResult.state,
              result: checkoutResult,
            }
          : undefined
        : best && isUsableCandidateResult(session, baseline.state, best.candidate, best.result)
          ? best
          : undefined;
      const selectedFeedback = selected?.state ? session.readStateFeedback(selected.state.stateId) : undefined;
      const selectedSnapshot = selected?.state ? session.snapshotState(selected.state.stateId) : undefined;
      const selectedBranchId =
        request.action === 'checkout'
          ? request.branchId
          : selectedSnapshot
            ? digest(canonicalMathJson(selectedSnapshot))
            : undefined;
      let applied = false;
      let commitOutcome: 'not_requested' | 'not_replaced' | 'replaced_durable' | 'replaced_uncertain' =
        request.applyBest ? 'not_replaced' : 'not_requested';
      let operationDisposition = searched?.executionDisposition ?? 'completed';
      if (checkoutResult && (checkoutResult.status === 'failed' || checkoutResult.status === 'invalid'))
        operationDisposition = 'unavailable';
      if (operationDisposition === 'completed') {
        if (request.signal?.aborted) operationDisposition = 'aborted';
        else if (remainingTimeoutMs() === 0) operationDisposition = 'timed_out';
      }
      if (
        selected &&
        request.applyBest &&
        operationDisposition === 'completed' &&
        !request.signal?.aborted &&
        remainingTimeoutMs() !== 0
      ) {
        regularPath(projectRoot, sourceFile);
        const selectedSourceHash = digest(selected.candidate.source);
        const selectedState = selected.state;
        const selectedEnvironment = session.environmentFingerprint;
        if (
          !selectedState ||
          selectedState.sourceHash !== selectedSourceHash ||
          !selectedFeedback ||
          selectedFeedback.sourceText !== selected.candidate.source ||
          selectedFeedback.state.sourceHash !== selectedSourceHash ||
          selectedFeedback.state.stateId !== selectedState.stateId ||
          !selectedFeedback.environmentFingerprint ||
          !selectedEnvironment ||
          selectedFeedback.environmentFingerprint !== selectedEnvironment
        ) {
          restoreBaseline();
          throw new Error('Proof candidate evidence or active route changed; candidate was not applied');
        }
        if (digest(fs.readFileSync(sourcePath, 'utf8')) !== request.expectedSourceHash) {
          restoreBaseline();
          throw new Error('Proof source changed during search; candidate was not applied');
        }
        const restored = session.restoreState(selectedState.stateId);
        if (restored.status !== 'restored' || restored.state?.stateId !== selectedState.stateId) {
          restoreBaseline();
          throw new Error('Proof candidate state could not be restored; candidate was not applied');
        }
        let activeRouteValid: boolean | undefined;
        try {
          const routeResult: unknown = request.validateActiveRoute?.();
          if (routeResult !== undefined && typeof routeResult !== 'boolean') {
            // A thenable may reject after this call. Observe it before rejecting
            // so a caller cannot turn a contract error into an unhandled rejection.
            if (routeResult && typeof (routeResult as unknown as { catch?: unknown }).catch === 'function') {
              void (routeResult as unknown as Promise<unknown>).catch((): undefined => undefined);
            }
            throw new Error('math_proof_final_route_guard_must_be_synchronous');
          }
          activeRouteValid = routeResult as boolean | undefined;
        } catch (error) {
          restoreBaseline();
          throw error;
        }
        if (activeRouteValid === false) {
          restoreBaseline();
          throw new Error('Proof active route changed during search; candidate was not applied');
        }
        const assertFinalAdoptionContext = (): void => {
          if (request.signal?.aborted) throw new Error('math_proof_adoption_aborted');
          if (remainingTimeoutMs() === 0) throw new Error('math_proof_adoption_timed_out');
          regularPath(projectRoot, sourceFile);
          if (digest(fs.readFileSync(sourcePath, 'utf8')) !== request.expectedSourceHash)
            throw new Error('math_proof_source_changed_before_rename');
          const environmentFingerprint = session.environmentFingerprint;
          if (!environmentFingerprint || environmentFingerprint !== selectedFeedback.environmentFingerprint)
            throw new Error('math_proof_environment_changed_before_rename');
          const finalRouteStatus: unknown = request.validateActiveRoute?.();
          if (
            finalRouteStatus !== undefined &&
            typeof finalRouteStatus !== 'boolean' &&
            finalRouteStatus &&
            typeof (finalRouteStatus as { catch?: unknown }).catch === 'function'
          ) {
            void (finalRouteStatus as Promise<unknown>).catch((): undefined => undefined);
          }
          if (finalRouteStatus !== undefined && typeof finalRouteStatus !== 'boolean')
            throw new Error('math_proof_final_route_guard_must_be_synchronous');
          if (finalRouteStatus === false) throw new Error('math_proof_active_route_changed_before_rename');
        };
        try {
          const commit = async (assertLeaseHeld: () => void): Promise<void> => {
            assertLeaseHeld();
            assertFinalAdoptionContext();
            const writeResult = writeMathTextAtomicallyWithStatus(sourcePath, selected.candidate.source, {
              beforeRename: () => {
                assertFinalAdoptionContext();
                assertLeaseHeld();
              },
            });
            commitOutcome = writeResult.status;
            applied = true;
            if (writeResult.status === 'replaced_uncertain')
              recoveryDiagnostics.push(
                'Proof source was replaced, but directory durability confirmation failed; the visible candidate remains current.'
              );
            const visibleSourceHash = digest(fs.readFileSync(sourcePath, 'utf8'));
            if (visibleSourceHash !== selectedSourceHash)
              throw new Error(`math_proof_source_changed_after_commit:${visibleSourceHash}`);
          };
          if (process.platform === 'linux') {
            const lockPath = regularPath(
              root,
              `.deepscientist/math/worker-proof/source-${digest(sourcePath)}.lock`,
              true
            );
            await withMathRuntimeLease(
              { lockPath, flockExecutable: 'flock', ...(request.signal ? { signal: request.signal } : {}) },
              async (lease) => commit(lease.assertHeld)
            );
          } else {
            await commit(() => {
              if (request.signal?.aborted) throw new Error('math_proof_adoption_aborted');
            });
          }
        } catch (error) {
          if (!applied) {
            commitOutcome = 'not_replaced';
            restoreBaseline();
          }
          throw error;
        }
        if (baseline.state.goalFingerprint !== selectedState.goalFingerprint) {
          const observation = {
            schema: 'deepscientist.mathematics.worker-proof-observation.v1',
            sessionKey: proofScopeKey,
            executionKey: key,
            workspaceRoot: root,
            ...(runIdentity ? { runIdentity } : {}),
            eventId: digest(
              JSON.stringify([
                proofScopeKey,
                key,
                request.expectedSourceHash,
                selectedState.sourceHash,
                selectedState.goalFingerprint,
              ])
            ),
            problemId: request.problemId ?? request.statementHash,
            statementHash: request.statementHash,
            recordedAt: new Date().toISOString(),
            kind: 'goal_transition',
            sourceHash: selectedState.sourceHash,
            sourceFile: path.relative(root, sourcePath).replaceAll(path.sep, '/'),
            previousSourceHash: request.expectedSourceHash,
            beforeGoalFingerprint: baseline.state.goalFingerprint,
            afterGoalFingerprint: selectedState.goalFingerprint,
            openGoalsBefore: baseline.state.openGoals.length,
            openGoalsAfter: selected.state.openGoals.length,
            closed: selectedState.status === 'closed',
            applied: true,
            authority: 'lean-process',
          };
          try {
            const file = regularPath(
              root,
              `.deepscientist/math/worker-proof/${proofScopeKey}.observations.jsonl`,
              true
            );
            fs.appendFileSync(file, `${JSON.stringify(observation)}\n`, { mode: 0o600 });
          } catch {
            recoveryDiagnostics.push('Applied proof transition could not be recorded in optional observations.');
          }
        }
        recordMathProofImpactAdoption({
          env: request.env,
          consumerAssignmentId: request.episodeId,
          previousSource: source,
          source: selectedSnapshot!.sourceText,
          openGoalsBefore: baseline.state.openGoals.length,
          openGoalsAfter: selectedState.openGoals.length,
        });
      } else restoreBaseline();
      if (
        searchFingerprint &&
        searched?.batchComplete &&
        operationDisposition === 'completed' &&
        (selected || searched.localClosure) &&
        !applied
      )
        draftSearches.set(key, { fingerprint: searchFingerprint, result: searched });
      // Observation alone must not discard a checked draft; search revalidates its source and environment.
      else if (request.action !== 'probe') draftSearches.delete(key);
      let checkpointSaved = true;
      try {
        const checkpoint = { ...session.snapshot(), diagnostics: session.diagnostics };
        let checkpointUnchanged = false;
        if (request.action === 'probe' && durableCheckpointIdentities.has(session) && fs.existsSync(checkpointPath)) {
          try {
            checkpointUnchanged =
              checkpointFileIdentity(checkpointPath) === durableCheckpointIdentities.get(session) &&
              canonicalMathJson(readMathJson(checkpointPath)) === canonicalMathJson(checkpoint);
          } catch {
            // Rebuild a missing or damaged disk record from the checked live state.
          }
        }
        if (!checkpointUnchanged) {
          writeMathJsonDurable(checkpointPath, checkpoint);
          durableCheckpointIdentities.set(session, checkpointFileIdentity(checkpointPath));
        }
      } catch {
        durableCheckpointIdentities.delete(session);
        checkpointSaved = false;
        recoveryDiagnostics.push(
          'Proof snapshot could not be persisted; current draft result is available and the next call can rebuild from source.'
        );
      }
      const baselineGoal = baseline.state.openGoals[goalIndex];
      const currentFeedback = session.readStateFeedback(session.state.stateId);
      if (!currentFeedback) throw new Error('Current proof state feedback is unavailable');
      const currentLocation = mathProofFeedbackLocation(
        currentFeedback,
        goalIndex,
        baselineGoal,
        baseline.state.openGoals.length
      );
      const current: MathProofFeedbackView = Object.freeze({
        stateId: currentFeedback.state.stateId,
        sourceHash: currentFeedback.state.sourceHash,
        environmentFingerprint: currentFeedback.environmentFingerprint,
        proofStateFingerprint: currentFeedback.state.goalFingerprint,
        status: currentFeedback.state.status,
        goals: Object.freeze([...currentFeedback.state.openGoals]),
        diagnostics: currentFeedback.diagnostics ?? '',
        feedbackAvailable: currentFeedback.diagnostics !== null,
        location: currentLocation,
        goalLocations: currentFeedback.goalLocations,
        truncated:
          currentFeedback.state.openGoals.length >= 128 ||
          currentFeedback.state.openGoals.some((goal) => goal.length >= 4_000),
      });
      const candidate:
        | (MathProofFeedbackView & {
            branchId?: string;
            source: string;
            reason: string;
            state: MathematicsLeanSessionSnapshot['state'];
          })
        | undefined =
        selected?.state && selectedFeedback
          ? Object.freeze({
              stateId: selectedFeedback.state.stateId,
              sourceHash: selectedFeedback.state.sourceHash,
              environmentFingerprint: selectedFeedback.environmentFingerprint,
              proofStateFingerprint: selectedFeedback.state.goalFingerprint,
              status: selectedFeedback.state.status,
              goals: Object.freeze([...selectedFeedback.state.openGoals]),
              diagnostics: selectedFeedback.diagnostics ?? '',
              feedbackAvailable: selectedFeedback.diagnostics !== null,
              location: mathProofFeedbackLocation(
                selectedFeedback,
                goalIndex,
                baselineGoal,
                baseline.state.openGoals.length
              ),
              goalLocations: selectedFeedback.goalLocations,
              truncated:
                selectedFeedback.state.openGoals.length >= 128 ||
                selectedFeedback.state.openGoals.some((goal) => goal.length >= 4_000),
              ...(selectedBranchId ? { branchId: selectedBranchId } : {}),
              source: selected.candidate.source,
              reason: `${selected.candidate.kind}: ${selected.candidate.payload}`,
              state: selectedFeedback.state,
            })
          : undefined;
      const includeBranchMetadata =
        request.action !== 'probe' ||
        request.includeBranchMetadata !== false ||
        request.branchGeneration !== undefined ||
        request.branchOffset !== undefined ||
        request.branchPageSize !== undefined;
      const persistedBranches = includeBranchMetadata ? branchPage() : undefined;
      const projectionMetrics = (includeBranchMetadata ? branchStorageKeys : []).map((storageKey) => {
        const projection = branchProjection(root, storageKey);
        return {
          key: storageKey,
          directoryScans: projection.directoryScans,
          fullSnapshotReads: projection.fullSnapshotReads,
          fullSnapshotReadBytes: projection.fullSnapshotReadBytes,
          snapshotHashCount: projection.snapshotHashCount,
          metadataComparisons: projection.metadataComparisons,
          invalidBranches: projection.invalidBranches.size,
          snapshotWrites: projection.snapshotWrites,
          indexWrites: projection.indexWrites,
          indexRepairs: projection.indexRepairs,
        };
      });
      return {
        status: searched?.status ?? (checkoutResult && !selected ? 'unavailable' : checkout ? 'restored' : 'probed'),
        authority: 'lean-process' as const,
        solverReady: false as const,
        applied,
        commitOutcome,
        capabilityAdded: Boolean(best?.result.capabilityAdded),
        checkpointSaved,
        previousSourceBranchId,
        diagnosticDelta:
          priorEditSnapshot && priorEditSnapshot.sourceText !== source
            ? (() => {
                const before = new Set(
                  (priorEditDiagnostics ?? '')
                    .split('\n')
                    .map((line) => line.trim())
                    .filter(Boolean)
                );
                const after = new Set(
                  current.diagnostics
                    .split('\n')
                    .map((line) => line.trim())
                    .filter(Boolean)
                );
                return {
                  previousSourceHash: priorEditSnapshot?.state.sourceHash,
                  currentSourceHash: current.sourceHash,
                  available: priorEditDiagnostics !== undefined,
                  added:
                    priorEditDiagnostics === undefined
                      ? []
                      : [...after]
                          .filter((line) => !before.has(line))
                          .slice(0, 40)
                          .map((line) => line.slice(0, 500)),
                  removed:
                    priorEditDiagnostics === undefined
                      ? []
                      : [...before]
                          .filter((line) => !after.has(line))
                          .slice(0, 40)
                          .map((line) => line.slice(0, 500)),
                  truncated:
                    before.size > 40 || after.size > 40 || [...before, ...after].some((line) => line.length > 500),
                  authority: 'compiler-diagnostic-lines' as const,
                };
              })()
            : undefined,
        recoveryDiagnostics,
        proofScopeKey,
        executionKey: key,
        runtimeMetrics: {
          session: session.cacheMetrics(),
          branch: projectionMetrics,
        },
        cachedSearch: Boolean(cachedSearch),
        searchMode: searchPlan?.mode,
        ...(searched?.localClosure ? { localClosure: searched.localClosure } : {}),
        candidateSetHash,
        candidateTotal: candidatePool.length,
        nextCandidateOffset: searched
          ? searched.batchComplete
            ? offset + candidates.length < candidatePool.length
              ? offset + candidates.length
              : null
            : searchPlan?.preserveOrder
              ? offset + searched.nextCandidateIndex
              : offset
          : null,
        goalIndex,
        ...persistedBranches,
        sourceHash: current.sourceHash,
        historyRef,
        traceRef,
        diagnostics: current.diagnostics,
        location: current.location,
        failureCategory: classifyLeanProofDiagnostic(current.diagnostics),
        executionDisposition: operationDisposition,
        durationMs,
        state: session.state,
        remainingGoals: current.goals,
        current,
        candidate,
        attempts:
          searched?.executedAttempts.map((attempt) => ({
            action: attempt.candidate.payload,
            kind: attempt.candidate.kind,
            sourceHash: digest(attempt.candidate.source),
            goalFingerprint: attempt.goalFingerprint,
            goalIndex: attempt.goalIndex,
            status: attempt.result.status,
            ...classifyMathCandidateApplicability(attempt.result),
            executionDisposition: attempt.result.executionDisposition ?? 'completed',
            provenance: attempt.candidate.provenance,
            recoveredFromJournal: Boolean(attempt.result.recoveredFromJournal),
            capabilityAdded: Boolean(attempt.result.capabilityAdded),
            diagnostics: attempt.result.diagnostics,
            durationMs:
              attempt.result.reuseKind === 'hot'
                ? 0
                : (attempt.result.action?.runtime.durationMs ?? attempt.result.durationMs ?? 0),
          })) ?? [],
        testedPremises: retrievedPremises
          .filter((premise) =>
            searched?.branches.some(
              (branch) =>
                branch.candidate.payload === `exact ${premise.name}` ||
                branch.candidate.payload === `apply ${premise.name}`
            )
          )
          .map((premise) => premise.name),
        ...(searchPlan?.mode === 'premises'
          ? {
              retrieval: {
                scope: 'frozen-corpus' as const,
                query: request.premiseQuery?.trim() ?? '',
                resultCount: retrievedPremises.length,
                testedCount: searched?.executedAttempts.filter((attempt) => attempt.candidate.provenance).length ?? 0,
              },
            }
          : {}),
      };
    });
  queues.set(queueKey, operation);
  try {
    return await operation;
  } finally {
    if (queues.get(queueKey) === operation) queues.delete(queueKey);
    for (const release of operationStateReleases.splice(0)) release();
    operationSession = undefined;
    const remainingPins = (sessionPins.get(key) ?? 1) - 1;
    if (remainingPins > 0) sessionPins.set(key, remainingPins);
    else sessionPins.delete(key);
    await sweepMathWorkerProofSessions(Math.max(1, request.cacheLimits?.liveSessions ?? 16));
  }
}

export async function closeMathWorkerProofSessions(): Promise<void> {
  await Promise.allSettled(queues.values());
  for (const [cacheKey, projection] of branchProjections) {
    if (!writableBranchProjections.has(cacheKey)) continue;
    try {
      flushProofBranchProjection(projection);
    } catch {
      // The branch snapshots remain authoritative when a derived index cannot be flushed.
    }
  }
  const active = [...sessions.values()];
  sessions.clear();
  sessionPins.clear();
  draftSearches.clear();
  recoveredJournals.clear();
  branchProjections.clear();
  writableBranchProjections.clear();
  branchProjectionClock = 0;
  evictedSessionCount = 0;
  evictedBranchProjectionCount = 0;
  await Promise.allSettled(active.map((session) => session.close()));
}
