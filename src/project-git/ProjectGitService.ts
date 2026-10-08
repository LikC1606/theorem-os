/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type {
  ProjectGitCheckpointArtifactRef,
  ProjectGitChangedEvent,
  ProjectGitBlobRequest,
  ProjectGitBlobResult,
  ProjectGitBindConversationRequest,
  ProjectGitBindConversationResult,
  ProjectGitActivateResearchBranchRequest,
  ProjectGitActivateResearchBranchResult,
  ProjectGitCommitRequest,
  ProjectGitCommitResult,
  ProjectGitCommitSummary,
  ProjectGitCloneRequest,
  ProjectGitCloneResult,
  ProjectGitCompareResearchBranchesRequest,
  ProjectGitCompareResearchBranchesResult,
  ProjectGitDiffRequest,
  ProjectGitDiffResult,
  ProjectGitDiscoverRequest,
  ProjectGitDiscoverResult,
  ProjectGitDomain,
  ProjectGitGraphRequest,
  ProjectGitGraphResult,
  ProjectGitMetricComparison,
  ProjectGitMetricContext,
  ProjectGitPreflightRequest,
  ProjectGitPreflightResult,
  ProjectGitPrepareManagedRequest,
  ProjectGitPrepareManagedResult,
  ProjectGitPrepareResearchBranchRequest,
  ProjectGitPrepareResearchBranchResult,
  ProjectGitPrepareWorkspaceRequest,
  ProjectGitPrepareWorkspaceResult,
  ProjectGitPerformanceMetric,
  ProjectGitRepository,
  ProjectGitResearchBranch,
  ProjectGitAgentWorktreeState,
  ProjectGitResearchBranchAgent,
  ProjectGitResearchBranchStatus,
  ProjectGitResearchFrontierRequest,
  ProjectGitResearchFrontierResult,
  ProjectGitResearchStageReceipt,
  ProjectGitTreeEntry,
  ProjectGitTreeRequest,
  ProjectGitTreeResult,
  ProjectGitWorkingDiffRequest,
  ProjectGitWorkingDiffResult,
  ProjectGitWorkingTreeResult,
  ProjectGitWorkspaceBinding,
  ProjectWorkspaceDeletionKind,
  ProjectWorkspaceDeletionRequest,
} from "../common/types/office/preview";
import type { TargetDiscoveryProgressSummary } from "../common/chat/targetDiscovery";
import {
  formatResearchCommitSubject,
  normalizeProjectGitDirectionDecision,
  normalizeResearchStrategy,
  parseResearchCommitSubject,
  type ProjectGitDirectionDecision,
  type ResearchStrategy,
} from "../common/chat/researchStrategy";
import {
  normalizeMathLocalGateReceipt,
  normalizeMathHelperReceipt,
  normalizeMathNodeProofReceipt,
  normalizeMathDurableProgressCheckpoint,
  isMathFoundationalLeanAxiom,
  type MathLocalGateReceipt,
  type MathHelperReceipt,
  type MathNodeProofReceipt,
  type MathSolverReadyReceipt,
  type MathDurableProgressCheckpoint,
} from "../common/types/team/mathematicsTeam";
import fs from 'node:fs';
import crypto from 'node:crypto';
import path from 'node:path';
import { createResearchTeamTransportKey } from "../common/types/team/researchTeamIdentity";
import { decodeMathAssignmentJournal, isRuntimeMathAssignment } from "../math/mathAssignmentJournal";
import { isMathWorkerProofRuntimeRecordPath, readMathJson } from "../math/mathRuntimeIo";
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { Worker, parentPort } from 'node:worker_threads';
import { isDeepStrictEqual } from 'node:util';
import {
  parseGitLog,
  parseLogNumstats,
  parseNameStatus,
  parseNumstat,
  parsePorcelainStatus,
  PROJECT_GIT_LOG_FORMAT,
  summarizeNumstat,
} from "./projectGitParsers";
import { createProjectId, mergeProjectManifest } from "./projectManifest";
import { lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";

const MAX_TEXT_BYTES = 5 * 1024 * 1024;
const MAX_BINARY_BYTES = 20 * 1024 * 1024;
const MAX_GIT_BUFFER = 24 * 1024 * 1024;
const DEFAULT_GIT_TIMEOUT_MS = 15_000;
export const DEFAULT_AGENT_WORKTREE_GIT_TIMEOUT_MS = 10 * 60_000;
const EMPTY_TREE_SHA = '4b825dc642cb6eb9a060e54bf8d69288fbee4904';
const PATH_LOG_RECORD_SEPARATOR = '\x1e';
const PATH_LOG_METADATA_SEPARATOR = '\x1d';
const PATH_LOG_FIELD_SEPARATOR = '\x1f';
const PATH_LOG_FORMAT = ['%H', '%h', '%s', '%aI'].join('%x1f');

const writeFileAtomicDurable = (filePath: string, content: string): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  const temporaryPath = `${filePath}.${process.pid}.${Date.now()}.${crypto.randomUUID()}.tmp`;
  try {
    const descriptor = fs.openSync(temporaryPath, 'w', 0o600);
    try {
      fs.writeFileSync(descriptor, content, 'utf8');
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    fs.renameSync(temporaryPath, filePath);
    try {
      const directory = fs.openSync(path.dirname(filePath), fs.constants.O_RDONLY);
      fs.fsyncSync(directory);
      fs.closeSync(directory);
    } catch {
      // Directory fsync is not available on every supported platform.
    }
  } finally {
    if (fs.existsSync(temporaryPath)) fs.rmSync(temporaryPath, { force: true });
  }
};

type ProjectGitChangedListener = (event: ProjectGitChangedEvent) => void;

const projectGitChangedListeners = new Set<ProjectGitChangedListener>();

export const onProjectGitChanged = (listener: ProjectGitChangedListener): (() => void) => {
  projectGitChangedListeners.add(listener);
  return () => projectGitChangedListeners.delete(listener);
};

export const notifyProjectGitChanged = (event: ProjectGitChangedEvent): void => {
  projectGitReadCache.clear();
  // Utility-thread operations relay change notifications to their owner
  // process; the main-process bridge subscribes there and forwards them over
  // IPC.  Local MCP/CLI callers still receive the in-process notification.
  parentPort?.postMessage({ type: 'project-git-changed', event });
  projectGitChangedListeners.forEach((listener) => {
    try {
      listener(event);
    } catch (error) {
      console.warn('[ProjectGitService] Project Git change listener failed:', error);
    }
  });
};

/** Operations exposed by the Electron main-process Project Git bridge. */
export type ProjectGitWorkerOperation =
  | 'inspectProjectGitWorkspace'
  | 'prepareProjectWorkspace'
  | 'cloneProjectGit'
  | 'bindManagedProjectConversation'
  | 'prepareManagedProject'
  | 'discoverProjectGit'
  | 'listProjectGitGraph'
  | 'listProjectGitResearchFrontier'
  | 'prepareProjectGitResearchBranch'
  | 'activateProjectGitResearchBranch'
  | 'compareProjectGitResearchBranches'
  | 'getProjectGitCommit'
  | 'getProjectGitDiff'
  | 'getProjectGitTree'
  | 'getProjectGitBlob'
  | 'getProjectGitWorkingTree'
  | 'getProjectGitWorkingDiff';

/**
 * Execute a Project Git operation in a utility thread.  The legacy service
 * functions intentionally remain synchronous for MCP/CLI callers, but the
 * Electron bridge must never run those functions on the main event loop: a
 * clone or worktree operation can legitimately take minutes.
 */
const PROJECT_GIT_READ_CACHE_MS = 250;
const PROJECT_GIT_CACHEABLE_OPERATIONS = new Set<ProjectGitWorkerOperation>([
  'inspectProjectGitWorkspace',
  'listProjectGitGraph',
  'listProjectGitResearchFrontier',
  'getProjectGitCommit',
  'getProjectGitTree',
  'getProjectGitWorkingTree',
]);
const MAX_PROJECT_GIT_READ_CACHE_ENTRIES = 64;
const projectGitReadCache = new Map<string, { expiresAt: number; result: unknown }>();
const projectGitReadInFlight = new Map<string, Promise<unknown>>();

const runProjectGitOperationInWorkerUncached = <T>(
  operation: ProjectGitWorkerOperation,
  request: unknown,
  onChanged?: (event: ProjectGitChangedEvent) => void
): Promise<T> =>
  new Promise<T>((resolve, reject) => {
    // electron-vite bundles this service into `out/main/chunks`, while the
    // worker entrypoint is emitted at `out/main/projectGitWorker.js`.  A
    // module-relative URL would therefore incorrectly resolve to
    // `out/main/chunks/projectGitWorker.js` in packaged builds.  Resolve the
    // sibling of the compiled main entry first and keep the module URL as a
    // development/source fallback.
    const compiledWorkerCandidates = [
      // electron-builder may unpack the worker (and its shared chunk) so
      // worker_threads receives a real filesystem path instead of an asar
      // virtual path. Prefer that copy when it exists.
      path.resolve(
        __dirname.replace(`${path.sep}app.asar${path.sep}`, `${path.sep}app.asar.unpacked${path.sep}`),
        '../projectGitWorker.js'
      ),
      path.resolve(__dirname, '../projectGitWorker.js'),
    ];
    const compiledWorkerPath = compiledWorkerCandidates.find((candidate) => fs.existsSync(candidate));
    const workerUrl = compiledWorkerPath
      ? pathToFileURL(compiledWorkerPath)
      : new URL('./projectGitWorker.js', import.meta.url);
    const worker = new Worker(workerUrl, {
      workerData: { operation, request },
    });
    let settled = false;
    const finish = (callback: () => void): void => {
      if (settled) return;
      settled = true;
      callback();
      void worker.terminate();
    };
    worker.on(
      'message',
      (message: { type?: string; event?: ProjectGitChangedEvent; ok?: boolean; result?: T; error?: string }) => {
        if (message.type === 'project-git-changed' && message.event) {
          try {
            onChanged?.(message.event);
          } catch (error) {
            // Event forwarding is observational and must never turn a completed
            // Git operation into an IPC/worker failure (nor crash Electron's
            // main process when a renderer listener is already disposed).
            console.warn('[ProjectGit] worker change listener failed:', error);
          }
          return;
        }
        finish(() => {
          if (message.ok) resolve(message.result as T);
          else reject(new Error(message.error || `Project Git worker operation ${operation} failed.`));
        });
      }
    );
    worker.once('error', (error) => finish(() => reject(error)));
    worker.once('exit', (code) => {
      if (code !== 0) finish(() => reject(new Error(`Project Git worker exited with status ${code}.`)));
      else if (!settled)
        finish(() => reject(new Error(`Project Git worker exited without a result for ${operation}.`)));
    });
  });

export const runProjectGitOperationInWorker = <T>(
  operation: ProjectGitWorkerOperation,
  request: unknown,
  onChanged?: (event: ProjectGitChangedEvent) => void
): Promise<T> => {
  if (!PROJECT_GIT_CACHEABLE_OPERATIONS.has(operation)) {
    return runProjectGitOperationInWorkerUncached<T>(operation, request, onChanged);
  }
  let key: string;
  try {
    key = `${operation}:${JSON.stringify(request)}`;
  } catch {
    return runProjectGitOperationInWorkerUncached<T>(operation, request, onChanged);
  }
  const now = Date.now();
  const cached = projectGitReadCache.get(key);
  if (cached && cached.expiresAt > now) return Promise.resolve(cached.result as T);
  const existing = projectGitReadInFlight.get(key);
  if (existing) return existing as Promise<T>;
  const requestPromise = runProjectGitOperationInWorkerUncached<T>(operation, request, onChanged)
    .then((result) => {
      projectGitReadCache.set(key, { expiresAt: Date.now() + PROJECT_GIT_READ_CACHE_MS, result });
      while (projectGitReadCache.size > MAX_PROJECT_GIT_READ_CACHE_ENTRIES) {
        const oldest = projectGitReadCache.keys().next().value as string | undefined;
        if (oldest === undefined) break;
        projectGitReadCache.delete(oldest);
      }
      return result;
    })
    .finally(() => {
      projectGitReadInFlight.delete(key);
    });
  projectGitReadInFlight.set(key, requestPromise);
  return requestPromise;
};

type GitResult = {
  status: number;
  stdout: Buffer;
  stderr: string;
};

type ResearchBranchMetadata = {
  name: string;
  parentRef?: string;
  baseCommit?: string;
  goalId?: string;
  routeNodeId?: string;
  objective?: string;
  agent?: ProjectGitResearchBranchAgent;
  worktreePath?: string;
  mergedInto?: string;
  mergedAt?: string;
  status?: Exclude<ProjectGitResearchBranchStatus, 'active'>;
  createdAt?: string;
  updatedAt?: string;
};

type ResearchBranchMetadataStore = {
  schema: 'deepscientist.research_branches.v1';
  branches: ResearchBranchMetadata[];
};

export type ProjectGitCheckpointRequest = {
  workspace: string;
  message: string;
  includePaths: string[];
  stage?: string;
  researchStrategy?: ResearchStrategy;
  routeNodeId?: string;
  repairsNodeId?: string;
  verification?: string[];
  metrics?: ProjectGitPerformanceMetric[];
  metricContext?: ProjectGitMetricContext;
  goalId?: string;
  runId?: string;
  conversationId?: string;
  domain?: ProjectGitDomain;
  artifactRef?: ProjectGitCheckpointArtifactRef;
  targetSummary?: TargetDiscoveryProgressSummary;
  researchStage?: ProjectGitResearchStageReceipt;
  directionDecision?: ProjectGitDirectionDecision;
};

export type ProjectGitCheckpointResult = {
  ok: boolean;
  repository?: ProjectGitRepository;
  commit?: string;
  shortCommit?: string;
  subject?: string;
  changedFiles: string[];
  stage?: string;
  researchStrategy?: ResearchStrategy;
  routeNodeId?: string;
  repairsNodeId?: string;
  verification?: string[];
  metrics?: ProjectGitPerformanceMetric[];
  metricContext?: ProjectGitMetricContext;
  goalId?: string;
  domain?: ProjectGitDomain;
  artifactRef?: ProjectGitCheckpointArtifactRef;
  targetSummary?: TargetDiscoveryProgressSummary;
  researchStage?: ProjectGitResearchStageReceipt;
  directionDecision?: ProjectGitDirectionDecision;
  error?: string;
};

export type ProjectGitPrepareAgentWorktreeRequest = {
  workspace: string;
  teamId: string;
  slotId: string;
  roleId: string;
  strategyLane?: string;
  assignmentId: string;
  /** Omitted for the legacy Challenge branch/worktree layout. */
  orchestrationNamespace?: string;
  workflowId?: string;
  objective?: string;
  from?: string;
};

export type ProjectGitPrepareAgentWorktreeResult = {
  ok: boolean;
  repository?: ProjectGitRepository;
  branch?: ProjectGitResearchBranch;
  workspace?: string;
  error?: string;
};

export type ProjectGitDiscardAgentWorktreeRequest = Readonly<{
  workspace: string;
  teamId: string;
  slotId: string;
  assignmentId: string;
  branch?: string;
  worktreePath?: string;
  /** Keep the prepared WAL entry for the caller to transition to a terminal state. */
  preserveReceipt?: boolean;
}>;

export type ProjectGitDiscardAgentWorktreeResult = Readonly<{
  ok: boolean;
  discarded: boolean;
  preserved?: boolean;
  error?: string;
}>;

export type ProjectGitResolveCommitRequest = Readonly<{
  workspace: string;
  reference: string;
}>;

export type ProjectGitCommitAncestorRequest = Readonly<{
  workspace: string;
  ancestor: string;
  descendant?: string;
}>;

/** Durable, Git-metadata-only identity for a dispatched Research Team assignment. */
export type ProjectGitResearchTeamAssignmentIntegration = Readonly<{
  executionMode: 'advisory' | 'artifact';
  branch?: string;
  headCommit?: string;
  mergedCommit?: string;
  /** The solver episode ended without a merge because its proof is incomplete. */
  retainedWithoutMerge?: boolean;
  /** A no-ff merge changed the proof identity and requires fresh certification. */
  reverificationRequired?: boolean;
  /** Receipts produced by Lead-side certification of the merged commit. */
  reverifiedReceipts?: Readonly<{
    localGateReceipt?: MathLocalGateReceipt;
    mathNodeReceipt?: MathNodeProofReceipt;
    mathHelperReceipt?: MathHelperReceipt;
  }>;
  sourceVerificationReceipts?: readonly ProjectGitMathSourceVerificationReceipt[];
  /** Last host verification outcome; pending/integrity outcomes never authorize a successor. */
  verification?: ProjectGitMathVerificationEvidence;
  solverReadyReceipt?: MathSolverReadyReceipt;
}>;

export type ProjectGitMathSourceVerificationReceipt = Readonly<{
  schema: 'deepscientist.math.source-verification.v1';
  receiptId: string;
  targetCommit: string;
  sourcePath: string;
  contentSha256: string;
  proofHash: string;
  theoremName: string;
  statementHash: string;
  leanStatementHash?: string;
  sourceDeclarationHash: string;
  verifier: 'lean-kernel';
  goalsRemaining: 0;
  sorryCount: 0;
  admitCount: 0;
  axioms: readonly string[];
  checkedAt: number;
}>;

/** Host-owned evidence describing why a frozen mathematics candidate may or may not resume. */
export type ProjectGitMathVerificationEvidence = Readonly<{
  schema: 'deepscientist.math.source-verification-evidence.v1';
  disposition: 'candidate_rejected' | 'pending' | 'integrity_error';
  targetCommit: string;
  checkedAt: number;
  itemIds: readonly string[];
  sourceHashes: readonly string[];
  diagnostics?: string;
}>;

export type ProjectGitResearchTeamUsageBaseline = Readonly<{
  measurement: 'token_totals' | 'context_window';
  inputTokens: number;
  cachedInputTokens: number;
  outputTokens: number;
  reasoningOutputTokens: number;
  totalTokens: number;
  contextWindowSize?: number;
  cost?: number;
}>;

export type ProjectGitResearchTeamAssignmentSupersession = Readonly<{
  winnerAssignmentId: string;
  reason: string;
}>;

export type ProjectGitResearchTeamDelivery = Readonly<{
  deliveryId: string;
  /** Bounded key used only at the Core HTTP boundary. */
  transportIdempotencyKey?: string;
  /** Semantic hash of the delivered result, independent of envelope sizing. */
  payloadHash?: string;
  result: unknown;
  deliveredAt: string;
  resultPayloadBytes: number;
  leadPayloadBytes: number;
}>;

export type ProjectGitResearchTeamPreparedGit = Readonly<{
  branch?: string;
  worktreePath?: string;
  /** Canonical assignment base. */
  baseCommit?: string;
  /** Initial commit of a private solver repository. */
  actualBaseCommit?: string;
  /** Private solver HEAD when this assignment started. */
  progressBaseCommit?: string;
  /** Project directory inside the private solver repository. */
  solverProjectRoot?: string;
}>;

export type ProjectGitResearchTeamAssignmentReceipt = Readonly<{
  schema: 'deepscientist.research_team_assignment.v1' | 'deepscientist.research_team_assignment.v2';
  teamId: string;
  slotId: string;
  assignmentId: string;
  state: 'prepared' | 'accepted' | 'integrated' | 'superseded';
  assignment: unknown;
  /** Durable budget clock and accepted execution-attempt count. */
  startedAt?: string;
  attemptStartedAt?: string;
  attemptCount?: number;
  /** Core run identity needed to cancel or recover an accepted turn after Lead restart. */
  teamRunId?: string;
  /** Prepared branch/worktree identity retained separately from the immutable assignment. */
  preparedGit?: ProjectGitResearchTeamPreparedGit;
  usageBaseline?: ProjectGitResearchTeamUsageBaseline;
  integration?: ProjectGitResearchTeamAssignmentIntegration;
  supersession?: ProjectGitResearchTeamAssignmentSupersession;
  /** A competing accepted assignment that still needs durable supersession. */
  supersessionPending?: ProjectGitResearchTeamAssignmentSupersession;
  /** Durable state for budget cancellation retries across Lead restarts. */
  budgetCancellation?: Readonly<{
    status: 'pending' | 'failed' | 'succeeded';
    teamRunId: string;
    requestedAt: string;
    lastAttemptAt?: string;
    attemptCount: number;
    nextRetryAt?: string;
    error?: string;
  }>;
  delivery?: ProjectGitResearchTeamDelivery;
  /** Durable Mathematics scheduler state, updated atomically at integration. */
  mathProgress?: MathDurableProgressCheckpoint;
  updatedAt: string;
}>;

export type ProjectGitResearchTeamAssignmentRequest = Readonly<{
  schema?: ProjectGitResearchTeamAssignmentReceipt['schema'];
  workspace: string;
  teamId: string;
  slotId: string;
  assignmentId: string;
  assignment?: unknown;
  usageBaseline?: ProjectGitResearchTeamUsageBaseline;
  teamRunId?: string;
  preparedGit?: ProjectGitResearchTeamPreparedGit;
  state?: 'prepared' | 'accepted';
  integration?: ProjectGitResearchTeamAssignmentIntegration;
  supersession?: ProjectGitResearchTeamAssignmentSupersession;
  supersessionPending?: ProjectGitResearchTeamAssignmentSupersession;
  budgetCancellation?: Readonly<{
    status: 'pending' | 'failed' | 'succeeded';
    teamRunId: string;
    requestedAt?: string;
    lastAttemptAt?: string;
    nextRetryAt?: string;
    error?: string;
  }>;
  mathProgress?: MathDurableProgressCheckpoint;
}>;

export type ProjectGitResearchTeamDeliveryRequest = Readonly<{
  workspace: string;
  teamId: string;
  slotId: string;
  assignmentId: string;
  result: unknown;
  leadPayloadBytes: number;
}>;

export type ProjectGitIntegrateAgentBranchRequest = {
  workspace: string;
  teamId: string;
  slotId: string;
  branch: string;
  assignmentId?: string;
  orchestrationNamespace?: string;
  expectedHead?: string;
  summary?: string;
};

export type ProjectGitResearchTeamAssignmentListRequest = Readonly<{
  strict?: boolean;
  workspace: string;
  teamId: string;
  states?: readonly ProjectGitResearchTeamAssignmentReceipt['state'][];
}>;

export type ProjectGitIntegrateAgentBranchResult = {
  ok: boolean;
  repository?: ProjectGitRepository;
  branch?: ProjectGitResearchBranch;
  mergedCommit?: string;
  alreadyIntegrated?: boolean;
  error?: string;
};

export const resolveAgentWorktreeGitTimeoutMs = (
  value = process.env.DEEPSCIENTIST_PROJECT_GIT_WORKTREE_TIMEOUT_MS
): number => {
  const parsed = Number(value);
  return value?.trim() && Number.isSafeInteger(parsed) && parsed >= DEFAULT_GIT_TIMEOUT_MS
    ? parsed
    : DEFAULT_AGENT_WORKTREE_GIT_TIMEOUT_MS;
};

const runGit = (
  cwd: string,
  args: string[],
  maxBuffer = MAX_GIT_BUFFER,
  timeout = DEFAULT_GIT_TIMEOUT_MS
): GitResult => {
  const result = spawnSync('git', ['-C', cwd, ...args], {
    encoding: 'buffer',
    maxBuffer,
    timeout,
    windowsHide: true,
  });
  return {
    status: result.status ?? 1,
    stdout: Buffer.isBuffer(result.stdout) ? result.stdout : Buffer.from(result.stdout || ''),
    stderr: Buffer.isBuffer(result.stderr) ? result.stderr.toString('utf8').trim() : String(result.stderr || '').trim(),
  };
};

const initializeMainRepository = (workspace: string): void => {
  const initialized = runGit(workspace, ['init']);
  if (initialized.status !== 0) {
    throw new Error(errorMessage(initialized, 'Unable to initialize the Git repository.'));
  }
  const selectedMain = runGit(workspace, ['symbolic-ref', 'HEAD', 'refs/heads/main']);
  if (selectedMain.status !== 0) {
    throw new Error(errorMessage(selectedMain, 'Unable to select the main Git branch.'));
  }
};

const runStandaloneGit = (args: string[], cwd?: string, timeout = 120_000, maxBuffer = MAX_GIT_BUFFER): GitResult => {
  const result = spawnSync('git', args, {
    ...(cwd ? { cwd } : {}),
    encoding: 'buffer',
    maxBuffer,
    timeout,
    windowsHide: true,
  });
  return {
    status: result.status ?? 1,
    stdout: Buffer.isBuffer(result.stdout) ? result.stdout : Buffer.from(result.stdout || ''),
    stderr: Buffer.isBuffer(result.stderr) ? result.stderr.toString('utf8').trim() : String(result.stderr || '').trim(),
  };
};

const textOutput = (result: GitResult): string => result.stdout.toString('utf8').trim();

const porcelainOutput = (result: GitResult): string => result.stdout.toString('utf8').replace(/\r?\n$/u, '');

const errorMessage = (result: GitResult, fallback: string): string => result.stderr || fallback;

const resolveWorkspace = (workspace: string): string => {
  const requested = String(workspace || '').trim();
  if (!requested) throw new Error('A project workspace is required.');
  const resolved = fs.realpathSync(requested);
  if (!fs.statSync(resolved).isDirectory()) throw new Error('The project workspace must be a directory.');
  return resolved;
};

const normalizeRelativePath = (value?: string): string | undefined => {
  if (value === undefined || value === '') return undefined;
  if (value.includes('\0') || path.isAbsolute(value)) throw new Error('Git paths must be project-relative.');
  const normalized = value.replace(/\\/gu, '/').replace(/^\.\//u, '');
  if (!normalized || normalized.split('/').some((segment) => segment === '..')) {
    throw new Error('Git path escapes the project workspace.');
  }
  return normalized;
};

const validateRef = (value: string): string => {
  const ref = String(value || '').trim();
  if (!ref || ref.startsWith('-') || ref.includes('\0') || /[\s:\\]/u.test(ref)) {
    throw new Error('Invalid Git revision.');
  }
  return ref;
};

const validateCloneRemote = (value: string): string => {
  const remote = String(value || '').trim();
  if (!remote || remote.includes('\0') || /[\r\n]/u.test(remote)) {
    throw new Error('A Git remote URL is required.');
  }
  const isHttps = /^https:\/\//iu.test(remote);
  const isLoopbackHttp = /^http:\/\/(?:localhost|127\.0\.0\.1|\[::1\])(?::\d+)?(?:\/|$)/iu.test(remote);
  const isSsh = /^(?:ssh:\/\/|git@[^:]+:)/iu.test(remote);
  if (!isHttps && !isLoopbackHttp && !isSsh) {
    throw new Error('Only HTTPS, SSH, or loopback HTTP Git remotes can be cloned here.');
  }
  if (isHttps || isLoopbackHttp) {
    const parsed = new URL(remote);
    if (parsed.username || parsed.password) {
      throw new Error('Use the system Git credential manager or SSH instead of placing credentials in the URL.');
    }
  }
  return remote;
};

const redactedCloneRemote = (remote: string): string => {
  if (!/^https?:\/\//iu.test(remote)) return remote;
  try {
    const parsed = new URL(remote);
    parsed.username = '';
    parsed.password = '';
    parsed.search = '';
    parsed.hash = '';
    return parsed.toString().replace(/\/$/u, '');
  } catch {
    return remote.replace(/\/\/[^/@]+@/u, '//');
  }
};

const cloneDirectoryName = (remote: string): string => {
  const name = remote
    .replace(/[?#].*$/u, '')
    .replace(/[\\/]$/u, '')
    .split(/[\\/]/u)
    .at(-1)
    ?.replace(/\.git$/iu, '')
    .trim();
  if (!name || name === '.' || name === '..' || !/^[a-z0-9._-]+$/iu.test(name)) {
    throw new Error('The remote name cannot be used as a local project folder. Choose a destination explicitly.');
  }
  return name;
};

const validateBranchName = (repoRoot: string, value: string): string => {
  const branch = String(value || '').trim();
  if (!branch || branch.length > 180 || branch.startsWith('-') || branch.includes('\0')) {
    throw new Error('Invalid research branch name.');
  }
  const result = runGit(repoRoot, ['check-ref-format', '--branch', branch]);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Invalid research branch name.'));
  return branch;
};

const gitCommonDir = (repoRoot: string): string => {
  const result = runGit(repoRoot, ['rev-parse', '--git-common-dir']);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to locate Git metadata.'));
  const commonDir = textOutput(result);
  return path.isAbsolute(commonDir) ? commonDir : path.resolve(repoRoot, commonDir);
};

const researchBranchStorePath = (repoRoot: string): string =>
  path.join(gitCommonDir(repoRoot), 'deepscientist', 'research-branches.json');

const researchTeamAssignmentStoreDirectory = (repoRoot: string): string =>
  path.join(gitCommonDir(repoRoot), 'deepscientist', 'research-team-assignments');

const cloneDirectoryWithCopyOnWrite = (source: string, destination: string): void => {
  fs.mkdirSync(destination, { recursive: true });
  for (const entry of fs.readdirSync(source, { withFileTypes: true })) {
    const from = path.join(source, entry.name);
    const to = path.join(destination, entry.name);
    if (entry.isDirectory()) cloneDirectoryWithCopyOnWrite(from, to);
    else if (entry.isFile()) fs.copyFileSync(from, to, fs.constants.COPYFILE_FICLONE);
    // Lake caches do not require symlink entries. Skipping them avoids copying
    // a cache link that could escape the assigned worktree.
  }
};

const hydrateAgentLakeCache = (sourceWorkspace: string, assignedWorkspace: string): void => {
  const sourceRoot = path.resolve(sourceWorkspace);
  const targetRoot = path.resolve(assignedWorkspace);
  if (sourceRoot === targetRoot) return;

  // A repository may contain one or more nested Lean projects. The IMO
  // adapter deliberately keeps its Git root above generated/<problem>, so
  // looking only for <workspace>/.lake leaves Worker worktrees without the
  // pinned Mathlib cache and causes `lake` to attempt a network clone.
  const projectRelatives: string[] = [];
  const visit = (directory: string, relative: string, depth: number): void => {
    if (depth > 8) return;
    const lake = path.join(directory, '.lake');
    const toolchain = path.join(directory, 'lean-toolchain');
    try {
      if (fs.lstatSync(toolchain).isFile() && fs.lstatSync(lake).isDirectory()) {
        projectRelatives.push(relative);
        return;
      }
    } catch {
      // This directory is not a Lean project; continue looking below it.
    }
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(directory, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      if (
        !entry.isDirectory() ||
        entry.isSymbolicLink() ||
        ['.git', '.lake', '.deepscientist', 'node_modules'].includes(entry.name)
      )
        continue;
      visit(path.join(directory, entry.name), relative ? path.join(relative, entry.name) : entry.name, depth + 1);
    }
  };
  visit(sourceRoot, '', 0);
  for (const relative of projectRelatives) {
    const sourceLake = path.join(sourceRoot, relative, '.lake');
    const targetLake = path.join(targetRoot, relative, '.lake');
    fs.mkdirSync(targetLake, { recursive: true });
    const sourcePackages = path.join(sourceLake, 'packages');
    const targetPackages = path.join(targetLake, 'packages');
    if (fs.existsSync(sourcePackages) && fs.statSync(sourcePackages).isDirectory() && !fs.existsSync(targetPackages)) {
      fs.symlinkSync(sourcePackages, targetPackages, process.platform === 'win32' ? 'junction' : 'dir');
    }
    const sourceBuild = path.join(sourceLake, 'build');
    const targetBuild = path.join(targetLake, 'build');
    if (fs.existsSync(sourceBuild) && fs.statSync(sourceBuild).isDirectory() && !fs.existsSync(targetBuild)) {
      cloneDirectoryWithCopyOnWrite(sourceBuild, targetBuild);
    }
  }
};

const researchTeamAssignmentReceiptPath = (repoRoot: string, teamId: string, assignmentId: string): string => {
  const key = crypto.createHash('sha256').update(`${teamId}\0${assignmentId}`, 'utf8').digest('hex');
  return path.join(researchTeamAssignmentStoreDirectory(repoRoot), `${key}.json`);
};

const normalizeResearchTeamReceiptIdentity = (value: string, field: string): string => {
  const normalized = String(value || '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new Error(`Research Team assignment receipt ${field} is invalid.`);
  }
  return normalized;
};

const normalizeLegacyResearchTeamAssignmentReceipt = (value: unknown): unknown => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return value;
  const receipt = value as Record<string, unknown>;
  const integration = receipt.integration;
  if (!integration || typeof integration !== 'object' || Array.isArray(integration)) return value;
  const integrationRecord = integration as Record<string, unknown>;
  const receipts = integrationRecord.reverifiedReceipts;
  if (!receipts || typeof receipts !== 'object' || Array.isArray(receipts) || Object.keys(receipts).length !== 0) {
    return value;
  }
  const { reverifiedReceipts: _legacyEmptyReceipts, ...normalizedIntegration } = integrationRecord;
  return {
    ...receipt,
    integration: normalizedIntegration,
  };
};

const isProjectGitResearchTeamAssignmentReceipt = (
  value: unknown
): value is ProjectGitResearchTeamAssignmentReceipt => {
  if (!value || typeof value !== 'object') return false;
  const receipt = value as Partial<ProjectGitResearchTeamAssignmentReceipt>;
  const integration = receipt.integration;
  const supersession = receipt.supersession;
  const supersessionPending = receipt.supersessionPending;
  const budgetCancellation = receipt.budgetCancellation;
  const delivery = receipt.delivery;
  const usageBaseline = receipt.usageBaseline;
  const preparedGit = receipt.preparedGit;
  const usageBaselineValid =
    usageBaseline === undefined ||
    ((usageBaseline.measurement === 'token_totals' || usageBaseline.measurement === 'context_window') &&
      [
        usageBaseline.inputTokens,
        usageBaseline.cachedInputTokens,
        usageBaseline.outputTokens,
        usageBaseline.reasoningOutputTokens,
        usageBaseline.totalTokens,
      ].every((item) => Number.isFinite(item) && item >= 0) &&
      (usageBaseline.contextWindowSize === undefined ||
        (Number.isFinite(usageBaseline.contextWindowSize) && usageBaseline.contextWindowSize >= 0)) &&
      (usageBaseline.cost === undefined || (Number.isFinite(usageBaseline.cost) && usageBaseline.cost >= 0)));
  const integrationValid =
    integration !== undefined &&
    (integration.executionMode === 'advisory' || integration.executionMode === 'artifact') &&
    (integration.branch === undefined || typeof integration.branch === 'string') &&
    (integration.headCommit === undefined || /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(integration.headCommit)) &&
    (integration.mergedCommit === undefined || /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(integration.mergedCommit)) &&
    (integration.retainedWithoutMerge === undefined || typeof integration.retainedWithoutMerge === 'boolean') &&
    (integration.executionMode === 'artifact'
      ? Boolean(integration.branch && integration.headCommit) &&
        (integration.retainedWithoutMerge === true
          ? integration.mergedCommit === undefined &&
            integration.reverificationRequired === undefined &&
            integration.reverifiedReceipts === undefined
          : Boolean(integration.mergedCommit))
      : integration.branch === undefined &&
        integration.headCommit === undefined &&
        integration.mergedCommit === undefined &&
        integration.retainedWithoutMerge === undefined) &&
    (integration.reverificationRequired === undefined || typeof integration.reverificationRequired === 'boolean') &&
    (integration.solverReadyReceipt === undefined ||
      (integration.solverReadyReceipt.schema === 'deepscientist.mathematics.solver-ready.v1' &&
        integration.solverReadyReceipt.targetCommit === integration.mergedCommit &&
        typeof integration.solverReadyReceipt.attestation === 'object')) &&
    (() => {
      const receipts = integration.reverifiedReceipts;
      if (receipts === undefined) return true;
      if (!receipts || typeof receipts !== 'object') return false;
      if (!receipts.localGateReceipt && !receipts.mathNodeReceipt && !receipts.mathHelperReceipt) return false;
      if (integration.reverificationRequired === true || !integration.mergedCommit) return false;
      try {
        const normalized = [
          receipts.localGateReceipt ? normalizeMathLocalGateReceipt(receipts.localGateReceipt) : undefined,
          receipts.mathNodeReceipt ? normalizeMathNodeProofReceipt(receipts.mathNodeReceipt) : undefined,
          receipts.mathHelperReceipt ? normalizeMathHelperReceipt(receipts.mathHelperReceipt) : undefined,
        ].filter((item): item is NonNullable<typeof item> => Boolean(item));
        return normalized.every((item) => item.targetCommit === integration.mergedCommit);
      } catch {
        return false;
      }
    })() &&
    (() => {
      const receipts = integration.sourceVerificationReceipts;
      if (receipts === undefined) return true;
      if (!Array.isArray(receipts) || receipts.length === 0 || integration.reverificationRequired === true)
        return false;
      try {
        const normalized = receipts.map((receipt) =>
          normalizeMathSourceVerificationReceipt(receipt, integration.mergedCommit)
        );
        return (
          new Set(normalized.map((receipt) => `${receipt.sourcePath}\u0000${receipt.theoremName}`)).size ===
            normalized.length && new Set(normalized.map((receipt) => receipt.receiptId)).size === normalized.length
        );
      } catch {
        return false;
      }
    })() &&
    (() => {
      const evidence = integration.verification;
      if (evidence === undefined) return true;
      try {
        const normalized = normalizeMathVerificationEvidence(
          evidence,
          integration.mergedCommit ?? integration.headCommit
        );
        return normalized.disposition !== 'pending'
          ? true
          : integration.retainedWithoutMerge === true
            ? integration.reverificationRequired === undefined
            : integration.reverificationRequired === true;
      } catch {
        return false;
      }
    })();
  const supersessionValid =
    supersession !== undefined &&
    typeof supersession.winnerAssignmentId === 'string' &&
    /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(supersession.winnerAssignmentId) &&
    supersession.winnerAssignmentId !== receipt.assignmentId &&
    typeof supersession.reason === 'string' &&
    Boolean(supersession.reason.trim()) &&
    supersession.reason.length <= 500;
  const supersessionPendingValid =
    supersessionPending !== undefined &&
    typeof supersessionPending.winnerAssignmentId === 'string' &&
    /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(supersessionPending.winnerAssignmentId) &&
    supersessionPending.winnerAssignmentId !== receipt.assignmentId &&
    typeof supersessionPending.reason === 'string' &&
    Boolean(supersessionPending.reason.trim()) &&
    supersessionPending.reason.length <= 500;
  const budgetCancellationValid =
    budgetCancellation === undefined ||
    (budgetCancellation !== null &&
      (budgetCancellation.status === 'pending' ||
        budgetCancellation.status === 'failed' ||
        budgetCancellation.status === 'succeeded') &&
      typeof budgetCancellation.teamRunId === 'string' &&
      /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(budgetCancellation.teamRunId) &&
      typeof budgetCancellation.requestedAt === 'string' &&
      Number.isFinite(Date.parse(budgetCancellation.requestedAt)) &&
      (budgetCancellation.lastAttemptAt === undefined ||
        (typeof budgetCancellation.lastAttemptAt === 'string' &&
          Number.isFinite(Date.parse(budgetCancellation.lastAttemptAt)))) &&
      (budgetCancellation.nextRetryAt === undefined ||
        (typeof budgetCancellation.nextRetryAt === 'string' &&
          Number.isFinite(Date.parse(budgetCancellation.nextRetryAt)))) &&
      Number.isSafeInteger(budgetCancellation.attemptCount) &&
      budgetCancellation.attemptCount >= 0 &&
      (budgetCancellation.error === undefined ||
        (typeof budgetCancellation.error === 'string' && budgetCancellation.error.length <= 2_000)));
  let mathProgressValid = receipt.mathProgress === undefined;
  if (receipt.mathProgress !== undefined) {
    try {
      const normalized = normalizeMathDurableProgressCheckpoint(receipt.mathProgress);
      mathProgressValid = normalized.statementHash.length > 0 && normalized.routeFingerprint.length > 0;
    } catch {
      mathProgressValid = false;
    }
  }
  const expectedDeliveryId = `${receipt.teamId}:${receipt.slotId}:${receipt.assignmentId}`;
  const deliveryValid =
    delivery === undefined ||
    (delivery.deliveryId === expectedDeliveryId &&
      delivery.result !== undefined &&
      typeof delivery.deliveredAt === 'string' &&
      Number.isFinite(Date.parse(delivery.deliveredAt)) &&
      Number.isSafeInteger(delivery.resultPayloadBytes) &&
      delivery.resultPayloadBytes >= 0 &&
      delivery.resultPayloadBytes === Buffer.byteLength(JSON.stringify(delivery.result), 'utf8') &&
      Number.isSafeInteger(delivery.leadPayloadBytes) &&
      delivery.leadPayloadBytes >= 0);
  return (
    (receipt.schema === 'deepscientist.research_team_assignment.v1' ||
      (receipt.schema === 'deepscientist.research_team_assignment.v2' &&
        isRuntimeMathAssignment(receipt.assignment) &&
        receipt.assignment.assignmentId === receipt.assignmentId &&
        receipt.assignment.request.targetSlotId === receipt.slotId)) &&
    typeof receipt.teamId === 'string' &&
    typeof receipt.slotId === 'string' &&
    typeof receipt.assignmentId === 'string' &&
    (receipt.state === 'prepared' ||
      receipt.state === 'accepted' ||
      receipt.state === 'integrated' ||
      receipt.state === 'superseded') &&
    receipt.assignment !== undefined &&
    (receipt.startedAt === undefined ||
      (typeof receipt.startedAt === 'string' && Number.isFinite(Date.parse(receipt.startedAt)))) &&
    (receipt.attemptStartedAt === undefined ||
      (typeof receipt.attemptStartedAt === 'string' && Number.isFinite(Date.parse(receipt.attemptStartedAt)))) &&
    (receipt.attemptCount === undefined || (Number.isSafeInteger(receipt.attemptCount) && receipt.attemptCount > 0)) &&
    (receipt.teamRunId === undefined ||
      (typeof receipt.teamRunId === 'string' && /^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(receipt.teamRunId))) &&
    (preparedGit === undefined ||
      (preparedGit !== null &&
        (preparedGit.branch === undefined ||
          (typeof preparedGit.branch === 'string' && preparedGit.branch.length <= 512)) &&
        (preparedGit.worktreePath === undefined ||
          (typeof preparedGit.worktreePath === 'string' && path.isAbsolute(preparedGit.worktreePath))) &&
        (preparedGit.baseCommit === undefined || /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(preparedGit.baseCommit)) &&
        (preparedGit.actualBaseCommit === undefined ||
          /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(preparedGit.actualBaseCommit)) &&
        (preparedGit.progressBaseCommit === undefined ||
          /^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(preparedGit.progressBaseCommit)) &&
        (preparedGit.solverProjectRoot === undefined ||
          (typeof preparedGit.solverProjectRoot === 'string' && path.isAbsolute(preparedGit.solverProjectRoot))) &&
        (preparedGit.actualBaseCommit === undefined) === (preparedGit.progressBaseCommit === undefined) &&
        (preparedGit.actualBaseCommit === undefined) === (preparedGit.solverProjectRoot === undefined) &&
        (preparedGit.actualBaseCommit === undefined ||
          (preparedGit.worktreePath !== undefined &&
            (() => {
              const relative = path.relative(preparedGit.worktreePath!, preparedGit.solverProjectRoot!);
              return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
            })())))) &&
    (receipt.state === 'integrated'
      ? integrationValid && supersession === undefined && supersessionPending === undefined
      : receipt.state === 'superseded'
        ? supersessionValid && (integration === undefined || integrationValid) && supersessionPending === undefined
        : receipt.state === 'accepted'
          ? (integration === undefined || integrationValid) &&
            supersession === undefined &&
            (supersessionPending === undefined || supersessionPendingValid)
          : integration === undefined &&
            supersession === undefined &&
            (supersessionPending === undefined || supersessionPendingValid)) &&
    mathProgressValid &&
    usageBaselineValid &&
    budgetCancellationValid &&
    deliveryValid &&
    (receipt.state !== 'prepared' || delivery === undefined) &&
    typeof receipt.updatedAt === 'string'
  );
};

const normalizeResearchTeamMathProgress = (
  value: MathDurableProgressCheckpoint | undefined
): MathDurableProgressCheckpoint | undefined => (value ? normalizeMathDurableProgressCheckpoint(value) : undefined);

const readResearchTeamAssignmentReceipt = (
  repoRoot: string,
  teamId: string,
  assignmentId: string
): ProjectGitResearchTeamAssignmentReceipt | undefined => {
  const receiptPath = researchTeamAssignmentReceiptPath(repoRoot, teamId, assignmentId);
  if (!fs.existsSync(receiptPath)) return undefined;
  try {
    const parsed = normalizeLegacyResearchTeamAssignmentReceipt(JSON.parse(fs.readFileSync(receiptPath, 'utf8')));
    decodeMathAssignmentJournal(parsed);
    if (!isProjectGitResearchTeamAssignmentReceipt(parsed)) {
      throw new Error('invalid receipt shape');
    }
    if (parsed.teamId !== teamId || parsed.assignmentId !== assignmentId) {
      throw new Error('receipt identity does not match its lookup key');
    }
    return Object.freeze(parsed);
  } catch {
    throw new Error('Research Team assignment receipt metadata is unreadable; refuse to trust Worker results.');
  }
};

const writeResearchTeamAssignmentReceipt = (
  repoRoot: string,
  receipt: ProjectGitResearchTeamAssignmentReceipt
): void => {
  const receiptPath = researchTeamAssignmentReceiptPath(repoRoot, receipt.teamId, receipt.assignmentId);
  writeFileAtomicDurable(receiptPath, `${JSON.stringify(receipt, null, 2)}\n`);
};

/**
 * A lock written inside an isolated MCP records a PID from that sandbox's own
 * PID namespace. Checked from another namespace it names an unrelated live
 * process (pid 2 is always alive), so a killed MCP left the repository lock
 * held forever and every Worker worktree preparation failed as "busy" (run 23).
 * Only a PID from the same namespace is probed; otherwise the age check decides.
 */
const projectGitLockOwner = lockOwnerRecord;
// A legacy or foreign-namespace owner is not alive here; the age check decides.
export const isProjectGitLockOwnerAlive = (value: unknown): boolean => lockOwnerState(value) === 'alive';

const withResearchTeamAssignmentLock = <T>(
  repoRoot: string,
  teamId: string,
  assignmentId: string,
  operation: () => T
): T => {
  const receiptPath = researchTeamAssignmentReceiptPath(repoRoot, teamId, assignmentId);
  const lockPath = `${receiptPath}.lock`;
  fs.mkdirSync(path.dirname(receiptPath), { recursive: true });
  const token = crypto.randomUUID();
  let descriptor: number | undefined;
  while (descriptor === undefined) {
    try {
      descriptor = fs.openSync(lockPath, 'wx', 0o600);
      fs.writeFileSync(descriptor, `${JSON.stringify({ ...projectGitLockOwner(), token, createdAt: Date.now() })}\n`);
    } catch (error) {
      // openSync may succeed while writing the lock metadata fails (for
      // example, a full filesystem). Do not leak that descriptor before
      // surfacing the real failure or retrying an EEXIST race.
      if (descriptor !== undefined) {
        try {
          fs.closeSync(descriptor);
        } catch {
          // Preserve the original lock/write error.
        }
        try {
          fs.unlinkSync(lockPath);
        } catch {
          // Preserve the original lock/write error.
        }
        descriptor = undefined;
      }
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
      try {
        const stale = Date.now() - fs.statSync(lockPath).mtimeMs > 30_000;
        let ownerAlive = false;
        try {
          ownerAlive = isProjectGitLockOwnerAlive(JSON.parse(fs.readFileSync(lockPath, 'utf8')));
        } catch {
          // Invalid lock metadata is recovered by the age check.
        }
        if (stale && !ownerAlive) {
          try {
            fs.unlinkSync(lockPath);
          } catch (unlinkError) {
            if ((unlinkError as NodeJS.ErrnoException).code !== 'ENOENT') throw unlinkError;
          }
          continue;
        }
      } catch (statError) {
        if ((statError as NodeJS.ErrnoException).code === 'ENOENT') continue;
        throw statError;
      }
      // This service is called from Electron's process/IPC path.  A
      // synchronous sleep here would freeze the main process while another
      // worker owns the lock.  Surface contention immediately; callers can
      // retry through their existing async orchestration instead.
      throw new Error('Research Team assignment receipt is busy in another process; retry asynchronously.', {
        cause: error,
      });
    }
  }
  try {
    return operation();
  } finally {
    fs.closeSync(descriptor);
    try {
      const owner = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as { token?: string };
      if (owner.token === token) fs.unlinkSync(lockPath);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT' && !(error instanceof SyntaxError)) {
        console.warn('[ProjectGit] failed to release assignment receipt lock', error);
      }
    }
  }
};

/**
 * A prepared receipt is only a write-ahead reservation. Once Core accepts a
 * newer assignment for the same Worker slot, the older reservation can never
 * become the active turn and must not remain in the pending WAL projection.
 * Mark it terminal while retaining the immutable assignment for audit and
 * route-history inspection.
 */
const supersedePreparedAssignmentsForAcceptedSlot = (
  repoRoot: string,
  teamId: string,
  slotId: string,
  winnerAssignmentId: string
): void => {
  let prepared: readonly ProjectGitResearchTeamAssignmentReceipt[];
  try {
    prepared = listProjectGitResearchTeamAssignments({
      workspace: repoRoot,
      teamId,
      states: ['prepared'],
    });
  } catch {
    // The accepted receipt is authoritative. A later reconciliation can
    // retry cleanup if a malformed or concurrently locked record is present.
    return;
  }
  for (const candidate of prepared) {
    if (candidate.slotId !== slotId || candidate.assignmentId === winnerAssignmentId) continue;
    try {
      withResearchTeamAssignmentLock(repoRoot, teamId, candidate.assignmentId, () => {
        const current = readResearchTeamAssignmentReceipt(repoRoot, teamId, candidate.assignmentId);
        if (!current || current.state !== 'prepared' || current.slotId !== slotId) return;
        const superseded: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
          ...current,
          state: 'superseded',
          supersession: Object.freeze({
            winnerAssignmentId,
            reason: 'A newer assignment was accepted for the same Worker slot before this reservation was accepted.',
          }),
          supersessionPending: undefined,
          budgetCancellation: undefined,
          updatedAt: new Date().toISOString(),
        });
        writeResearchTeamAssignmentReceipt(repoRoot, superseded);
      });
    } catch {
      // Do not turn an already accepted Core dispatch into a retryable error.
      // The next status/recovery pass will revisit this prepared reservation.
    }
  }
};

const normalizeMathSourceVerificationReceipt = (
  value: ProjectGitMathSourceVerificationReceipt,
  mergedCommit: string | undefined
): ProjectGitMathSourceVerificationReceipt => {
  if (!value || typeof value !== 'object' || value.schema !== 'deepscientist.math.source-verification.v1') {
    throw new Error('Research Team source verification receipt schema is invalid.');
  }
  const sourcePath = normalizeRelativePath(value.sourcePath);
  const receiptId = String(value.receiptId || '').trim();
  const theoremName = String(value.theoremName || '').trim();
  const commit = String(value.targetCommit || '')
    .trim()
    .toLowerCase();
  const digestValues = [
    value.contentSha256,
    value.proofHash,
    value.statementHash,
    value.sourceDeclarationHash,
    ...(value.leanStatementHash ? [value.leanStatementHash] : []),
  ];
  if (
    !receiptId ||
    receiptId.length > 256 ||
    !sourcePath ||
    !theoremName ||
    theoremName.length > 512 ||
    !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(commit) ||
    commit !== mergedCommit ||
    digestValues.some((digest) => !/^[a-f0-9]{64}$/u.test(digest)) ||
    value.proofHash !== value.contentSha256 ||
    value.verifier !== 'lean-kernel' ||
    value.goalsRemaining !== 0 ||
    value.sorryCount !== 0 ||
    value.admitCount !== 0 ||
    !Array.isArray(value.axioms) ||
    value.axioms.some((axiom) => typeof axiom !== 'string' || !isMathFoundationalLeanAxiom(axiom)) ||
    !Number.isSafeInteger(value.checkedAt) ||
    value.checkedAt <= 0
  ) {
    throw new Error('Research Team source verification receipt is invalid.');
  }
  return Object.freeze({
    schema: value.schema,
    receiptId,
    targetCommit: commit,
    sourcePath,
    contentSha256: value.contentSha256,
    proofHash: value.proofHash,
    theoremName,
    statementHash: value.statementHash,
    ...(value.leanStatementHash ? { leanStatementHash: value.leanStatementHash } : {}),
    sourceDeclarationHash: value.sourceDeclarationHash,
    verifier: 'lean-kernel',
    goalsRemaining: 0,
    sorryCount: 0,
    admitCount: 0,
    axioms: Object.freeze([...value.axioms]),
    checkedAt: value.checkedAt,
  });
};

const normalizeMathVerificationEvidence = (
  value: ProjectGitMathVerificationEvidence,
  targetCommit: string | undefined
): ProjectGitMathVerificationEvidence => {
  if (
    !value ||
    value.schema !== 'deepscientist.math.source-verification-evidence.v1' ||
    !['candidate_rejected', 'pending', 'integrity_error'].includes(value.disposition) ||
    typeof value.targetCommit !== 'string' ||
    !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(value.targetCommit) ||
    value.targetCommit !== targetCommit ||
    !Number.isSafeInteger(value.checkedAt) ||
    value.checkedAt <= 0 ||
    !Array.isArray(value.itemIds) ||
    value.itemIds.some((item) => typeof item !== 'string' || item.length === 0 || item.length > 512) ||
    !Array.isArray(value.sourceHashes) ||
    value.sourceHashes.some((hash) => typeof hash !== 'string' || !/^[a-f0-9]{64}$/u.test(hash)) ||
    value.itemIds.length !== value.sourceHashes.length ||
    (value.diagnostics !== undefined && (typeof value.diagnostics !== 'string' || value.diagnostics.length > 12_000))
  ) {
    throw new Error('Research Team verification evidence is invalid.');
  }
  return Object.freeze({
    schema: value.schema,
    disposition: value.disposition,
    targetCommit: value.targetCommit,
    checkedAt: value.checkedAt,
    itemIds: Object.freeze([...value.itemIds]),
    sourceHashes: Object.freeze([...value.sourceHashes]),
    ...(value.diagnostics ? { diagnostics: value.diagnostics } : {}),
  });
};

const normalizeResearchTeamAssignmentIntegration = (
  value: ProjectGitResearchTeamAssignmentIntegration | undefined
): ProjectGitResearchTeamAssignmentIntegration => {
  if (!value || (value.executionMode !== 'advisory' && value.executionMode !== 'artifact')) {
    throw new Error('Research Team integrated receipt requires exact delivery integration identity.');
  }
  const branch = value.branch?.trim();
  const headCommit = value.headCommit?.trim().toLowerCase();
  const mergedCommit = value.mergedCommit?.trim().toLowerCase();
  const retainedWithoutMerge = value.retainedWithoutMerge;
  if (retainedWithoutMerge !== undefined && typeof retainedWithoutMerge !== 'boolean') {
    throw new Error('Research Team integration retainedWithoutMerge must be boolean.');
  }
  const reverificationRequired = value.reverificationRequired;
  if (reverificationRequired !== undefined && typeof reverificationRequired !== 'boolean') {
    throw new Error('Research Team integration reverificationRequired must be boolean.');
  }
  if (value.executionMode === 'advisory') {
    if (
      branch ||
      headCommit ||
      mergedCommit ||
      retainedWithoutMerge ||
      value.reverifiedReceipts ||
      value.sourceVerificationReceipts ||
      value.verification ||
      value.solverReadyReceipt
    ) {
      throw new Error('Research Team advisory integration identity cannot contain Git delivery fields.');
    }
    return Object.freeze({
      executionMode: 'advisory',
      ...(reverificationRequired ? { reverificationRequired: true } : {}),
    });
  }
  if (!branch || !headCommit || (!retainedWithoutMerge && !mergedCommit)) {
    throw new Error(
      'Research Team artifact integration identity requires branch, headCommit, and either mergedCommit or retainedWithoutMerge.'
    );
  }
  if (
    !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(headCommit) ||
    (mergedCommit !== undefined && !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(mergedCommit))
  ) {
    throw new Error('Research Team artifact integration identity requires full Git object ids.');
  }
  if (retainedWithoutMerge && mergedCommit) {
    throw new Error('Research Team retained artifact integration cannot contain a mergedCommit.');
  }
  if (
    retainedWithoutMerge &&
    (reverificationRequired || value.reverifiedReceipts || value.sourceVerificationReceipts || value.solverReadyReceipt)
  ) {
    throw new Error('Research Team retained artifact integration cannot carry merged-commit verification state.');
  }
  const normalizedReceipts = value.reverifiedReceipts
    ? Object.freeze({
        ...(value.reverifiedReceipts.localGateReceipt
          ? { localGateReceipt: normalizeMathLocalGateReceipt(value.reverifiedReceipts.localGateReceipt) }
          : {}),
        ...(value.reverifiedReceipts.mathNodeReceipt
          ? { mathNodeReceipt: normalizeMathNodeProofReceipt(value.reverifiedReceipts.mathNodeReceipt) }
          : {}),
        ...(value.reverifiedReceipts.mathHelperReceipt
          ? { mathHelperReceipt: normalizeMathHelperReceipt(value.reverifiedReceipts.mathHelperReceipt) }
          : {}),
      })
    : undefined;
  const reverifiedReceipts =
    normalizedReceipts?.localGateReceipt || normalizedReceipts?.mathNodeReceipt || normalizedReceipts?.mathHelperReceipt
      ? normalizedReceipts
      : undefined;
  if (
    reverifiedReceipts &&
    [
      reverifiedReceipts.localGateReceipt?.targetCommit,
      reverifiedReceipts.mathNodeReceipt?.targetCommit,
      reverifiedReceipts.mathHelperReceipt?.targetCommit,
    ]
      .filter(Boolean)
      .some((commit) => commit !== mergedCommit)
  ) {
    throw new Error('Research Team merged receipts must target the recorded merged commit.');
  }
  if (reverifiedReceipts && reverificationRequired === true) {
    throw new Error('Research Team integration cannot require reverification while carrying merged receipts.');
  }
  const sourceVerificationReceipts = value.sourceVerificationReceipts
    ? Object.freeze(
        value.sourceVerificationReceipts.map((receipt) => normalizeMathSourceVerificationReceipt(receipt, mergedCommit))
      )
    : undefined;
  if (sourceVerificationReceipts && (!sourceVerificationReceipts.length || reverificationRequired === true)) {
    throw new Error('Research Team source verification receipts conflict with pending reverification.');
  }
  if (
    sourceVerificationReceipts &&
    (new Set(sourceVerificationReceipts.map((receipt) => `${receipt.sourcePath}\u0000${receipt.theoremName}`)).size !==
      sourceVerificationReceipts.length ||
      new Set(sourceVerificationReceipts.map((receipt) => receipt.receiptId)).size !==
        sourceVerificationReceipts.length)
  ) {
    throw new Error('Research Team source verification receipts must have unique source and receipt identities.');
  }
  const verification = value.verification
    ? normalizeMathVerificationEvidence(value.verification, mergedCommit ?? headCommit)
    : undefined;
  if (
    verification?.disposition === 'pending' &&
    ((retainedWithoutMerge && reverificationRequired === true) ||
      (!retainedWithoutMerge && reverificationRequired !== true))
  ) {
    throw new Error(
      retainedWithoutMerge
        ? 'Research Team private pending verification cannot carry canonical reverification state.'
        : 'Research Team canonical pending verification must retain reverificationRequired.'
    );
  }
  if (value.solverReadyReceipt) {
    if (value.solverReadyReceipt.schema !== 'deepscientist.mathematics.solver-ready.v1') {
      throw new Error('Research Team solver-ready receipt schema is invalid.');
    }
    if (value.solverReadyReceipt.targetCommit !== mergedCommit) {
      throw new Error('Research Team solver-ready receipt must target the recorded merged commit.');
    }
  }
  return Object.freeze({
    executionMode: 'artifact',
    branch,
    headCommit,
    ...(mergedCommit ? { mergedCommit } : {}),
    ...(retainedWithoutMerge ? { retainedWithoutMerge: true } : {}),
    ...(reverificationRequired ? { reverificationRequired: true } : {}),
    ...(reverifiedReceipts ? { reverifiedReceipts } : {}),
    ...(sourceVerificationReceipts ? { sourceVerificationReceipts } : {}),
    ...(verification ? { verification } : {}),
    ...(value.solverReadyReceipt ? { solverReadyReceipt: value.solverReadyReceipt } : {}),
  });
};

// The registry records a successor reservation before retiring its predecessor.
// A crash between these writes is recoverable, but must never permit two
// accepted owners. Enforce the handoff at both ACK and delivery promotion.
const assertMathAssignmentPredecessorRetired = (repoRoot: string, teamId: string, value: unknown): void => {
  if (!isRuntimeMathAssignment(value) || !value.request.predecessorAssignmentId) return;
  const predecessor = readResearchTeamAssignmentReceipt(repoRoot, teamId, value.request.predecessorAssignmentId);
  if (
    !predecessor ||
    !isRuntimeMathAssignment(predecessor.assignment) ||
    predecessor.assignment.runId !== value.runId ||
    predecessor.assignment.bindingDigest !== value.bindingDigest ||
    predecessor.assignment.scopeId !== value.scopeId ||
    (predecessor.state !== 'integrated' &&
      !(predecessor.state === 'superseded' && predecessor.supersession?.winnerAssignmentId === value.assignmentId))
  ) {
    throw new Error('math_assignment_predecessor_not_retired');
  }
};

export const recordProjectGitResearchTeamAssignment = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  if (request.assignment === undefined)
    throw new Error('Research Team assignment receipt requires the full assignment.');
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  const requestedState = request.state ?? 'accepted';
  const requestedSchema = request.schema ?? 'deepscientist.research_team_assignment.v1';
  if (
    !['deepscientist.research_team_assignment.v1', 'deepscientist.research_team_assignment.v2'].includes(
      requestedSchema
    )
  ) {
    throw new Error('math_assignment_wal_schema_unsupported');
  }
  if (requestedSchema === 'deepscientist.research_team_assignment.v2') {
    decodeMathAssignmentJournal({
      schema: requestedSchema,
      teamId,
      slotId,
      assignmentId,
      state: requestedState,
      assignment: request.assignment,
    });
  } else if (
    request.assignment &&
    typeof request.assignment === 'object' &&
    'schema' in request.assignment &&
    request.assignment.schema === 'deepscientist.math.assignment.v2'
  ) {
    throw new Error('math_assignment_wal_schema_unsupported');
  }
  const integration = request.integration ? normalizeResearchTeamAssignmentIntegration(request.integration) : undefined;
  if (requestedState !== 'prepared' && requestedState !== 'accepted') {
    throw new Error('Research Team assignment receipt state is invalid.');
  }
  if (request.preparedGit) {
    if (
      request.preparedGit.branch !== undefined &&
      (request.preparedGit.branch.length === 0 || request.preparedGit.branch.length > 512)
    ) {
      throw new Error('Research Team prepared branch identity is invalid.');
    }
    if (request.preparedGit.worktreePath !== undefined && !path.isAbsolute(request.preparedGit.worktreePath)) {
      throw new Error('Research Team prepared worktree identity must be absolute.');
    }
    if (
      request.preparedGit.baseCommit !== undefined &&
      !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(request.preparedGit.baseCommit)
    ) {
      throw new Error('Research Team prepared baseCommit must be a full Git object id.');
    }
    const extendedIdentity = [
      request.preparedGit.actualBaseCommit,
      request.preparedGit.progressBaseCommit,
      request.preparedGit.solverProjectRoot,
    ];
    if (
      extendedIdentity.some((value) => value !== undefined) &&
      extendedIdentity.some((value) => value === undefined)
    ) {
      throw new Error('Research Team private solver Git identity must be complete.');
    }
    for (const [label, commit] of [
      ['actualBaseCommit', request.preparedGit.actualBaseCommit],
      ['progressBaseCommit', request.preparedGit.progressBaseCommit],
    ] as const) {
      if (commit !== undefined && !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(commit)) {
        throw new Error(`Research Team prepared ${label} must be a full Git object id.`);
      }
    }
    if (request.preparedGit.solverProjectRoot !== undefined) {
      if (!path.isAbsolute(request.preparedGit.solverProjectRoot)) {
        throw new Error('Research Team prepared solverProjectRoot must be absolute.');
      }
      if (!request.preparedGit.worktreePath) {
        throw new Error('Research Team private solver Git identity requires worktreePath.');
      }
      const relative = path.relative(request.preparedGit.worktreePath, request.preparedGit.solverProjectRoot);
      if (relative.startsWith('..') || path.isAbsolute(relative)) {
        throw new Error('Research Team prepared solverProjectRoot must be inside worktreePath.');
      }
    }
  }
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    if (requestedState === 'accepted') assertMathAssignmentPredecessorRetired(repoRoot, teamId, request.assignment);
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (existing) {
      if (
        existing.schema !== requestedSchema ||
        existing.slotId !== slotId ||
        !isDeepStrictEqual(existing.assignment, request.assignment)
      ) {
        throw new Error('Research Team assignment receipt conflicts with an existing assignment identity.');
      }
      if (existing.state === 'integrated' || existing.state === 'superseded') {
        throw new Error('Research Team assignment is already terminal and cannot be redispatched.');
      }
      if (
        existing.usageBaseline &&
        request.usageBaseline &&
        !isDeepStrictEqual(existing.usageBaseline, request.usageBaseline)
      ) {
        throw new Error('Research Team assignment usage baseline conflicts with the prepared assignment.');
      }
      const usageBaseline = existing.usageBaseline ?? request.usageBaseline;
      if (existing.state === 'accepted' && requestedState === 'accepted') {
        if (integration || request.mathProgress) {
          const enriched: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
            ...existing,
            ...(integration ? { integration } : {}),
            ...(request.mathProgress ? { mathProgress: request.mathProgress } : {}),
            updatedAt: new Date().toISOString(),
          });
          writeResearchTeamAssignmentReceipt(repoRoot, enriched);
          supersedePreparedAssignmentsForAcceptedSlot(repoRoot, teamId, slotId, assignmentId);
          return enriched;
        }
        const attemptCount = (existing.attemptCount ?? 1) + 1;
        if (!Number.isSafeInteger(attemptCount) || attemptCount <= 0) {
          throw new Error('Research Team assignment attempt counter overflowed.');
        }
        const retried: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
          ...existing,
          attemptCount,
          attemptStartedAt: new Date().toISOString(),
          ...(request.teamRunId
            ? { teamRunId: normalizeResearchTeamReceiptIdentity(request.teamRunId, 'teamRunId') }
            : {}),
          ...(usageBaseline ? { usageBaseline } : {}),
          ...(request.preparedGit ? { preparedGit: request.preparedGit } : {}),
          ...(integration ? { integration } : {}),
          ...(request.mathProgress ? { mathProgress: request.mathProgress } : {}),
          updatedAt: new Date().toISOString(),
        });
        writeResearchTeamAssignmentReceipt(repoRoot, retried);
        supersedePreparedAssignmentsForAcceptedSlot(repoRoot, teamId, slotId, assignmentId);
        return retried;
      }
      if (existing.state === 'accepted' || requestedState === 'prepared') {
        if (usageBaseline === existing.usageBaseline && !request.preparedGit) return existing;
        const backfilled: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
          ...existing,
          ...(usageBaseline ? { usageBaseline } : {}),
          ...(request.preparedGit ? { preparedGit: request.preparedGit } : {}),
          ...(integration ? { integration } : {}),
          ...(request.mathProgress ? { mathProgress: request.mathProgress } : {}),
          updatedAt: new Date().toISOString(),
        });
        writeResearchTeamAssignmentReceipt(repoRoot, backfilled);
        return backfilled;
      }
      const accepted: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
        ...existing,
        state: 'accepted',
        attemptStartedAt: new Date().toISOString(),
        ...(request.teamRunId
          ? { teamRunId: normalizeResearchTeamReceiptIdentity(request.teamRunId, 'teamRunId') }
          : {}),
        ...(usageBaseline ? { usageBaseline } : {}),
        ...(request.preparedGit ? { preparedGit: request.preparedGit } : {}),
        ...(integration ? { integration } : {}),
        ...(request.mathProgress ? { mathProgress: request.mathProgress } : {}),
        updatedAt: new Date().toISOString(),
      });
      writeResearchTeamAssignmentReceipt(repoRoot, accepted);
      supersedePreparedAssignmentsForAcceptedSlot(repoRoot, teamId, slotId, assignmentId);
      return accepted;
    }
    const receipt: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      schema: requestedSchema,
      teamId,
      slotId,
      assignmentId,
      state: requestedState,
      assignment: request.assignment,
      startedAt: new Date().toISOString(),
      ...(requestedState === 'accepted' ? { attemptStartedAt: new Date().toISOString() } : {}),
      attemptCount: 1,
      ...(request.teamRunId ? { teamRunId: normalizeResearchTeamReceiptIdentity(request.teamRunId, 'teamRunId') } : {}),
      ...(request.preparedGit ? { preparedGit: request.preparedGit } : {}),
      ...(request.usageBaseline ? { usageBaseline: request.usageBaseline } : {}),
      ...(integration ? { integration } : {}),
      ...(request.mathProgress ? { mathProgress: request.mathProgress } : {}),
      updatedAt: new Date().toISOString(),
    });
    writeResearchTeamAssignmentReceipt(repoRoot, receipt);
    if (requestedState === 'accepted') {
      supersedePreparedAssignmentsForAcceptedSlot(repoRoot, teamId, slotId, assignmentId);
    }
    return receipt;
  });
};

export const readProjectGitResearchTeamAssignment = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt | undefined => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  const receipt = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
  if (receipt && receipt.slotId !== slotId) {
    throw new Error('Research Team assignment receipt slot does not match the requested Worker slot.');
  }
  return receipt;
};

export const listProjectGitResearchTeamAssignments = (
  request: ProjectGitResearchTeamAssignmentListRequest
): readonly ProjectGitResearchTeamAssignmentReceipt[] => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const states = request.states ? new Set(request.states) : undefined;
  const directory = researchTeamAssignmentStoreDirectory(repoRoot);
  if (!fs.existsSync(directory)) return Object.freeze([]);
  const receipts: Array<Readonly<{ receipt: ProjectGitResearchTeamAssignmentReceipt; startedAt: number }>> = [];
  for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
    if (!entry.name.endsWith('.json')) continue;
    if (!entry.isFile()) {
      if (request.strict) throw new Error('math_assignment_wal_integrity');
      continue;
    }
    try {
      const parsed = normalizeLegacyResearchTeamAssignmentReceipt(
        request.strict
          ? readMathJson(path.join(directory, entry.name))
          : JSON.parse(fs.readFileSync(path.join(directory, entry.name), 'utf8'))
      );
      if (request.strict) {
        const identity = parsed && typeof parsed === 'object' ? (parsed as Record<string, unknown>).teamId : undefined;
        if (typeof identity === 'string' && identity !== teamId) continue;
        decodeMathAssignmentJournal(parsed);
        if (
          !isProjectGitResearchTeamAssignmentReceipt(parsed) ||
          path.basename(researchTeamAssignmentReceiptPath(repoRoot, parsed.teamId, parsed.assignmentId)) !== entry.name
        ) {
          throw new Error('math_assignment_wal_integrity');
        }
      }
      if (
        isProjectGitResearchTeamAssignmentReceipt(parsed) &&
        parsed.teamId === teamId &&
        (!states || states.has(parsed.state))
      ) {
        receipts.push(
          Object.freeze({
            receipt: Object.freeze(parsed),
            startedAt: Date.parse(parsed.startedAt || parsed.updatedAt),
          })
        );
      }
    } catch {
      if (request.strict) throw new Error('math_assignment_wal_integrity');
      // A corrupt unrelated receipt cannot make every healthy assignment
      // undiscoverable. Direct lookup of that receipt still fails closed.
    }
  }
  receipts.sort((left, right) => left.startedAt - right.startedAt);
  return Object.freeze(receipts.map(({ receipt }) => receipt));
};

export const createProjectGitResearchTeamDeliveryId = (teamId: string, slotId: string, assignmentId: string): string =>
  `${teamId}:${slotId}:${assignmentId}`;

/**
 * Core accepts at most 128 characters for idempotency keys. Keep the readable
 * delivery identity for local receipts, but use a deterministic bounded key
 * across the transport boundary and on retries.
 */
export const createProjectGitResearchTeamTransportIdempotencyKey = (deliveryId: string): string =>
  createResearchTeamTransportKey(deliveryId);

const canonicalResearchTeamPayload = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(canonicalResearchTeamPayload);
  if (value && typeof value === 'object') {
    return Object.fromEntries(
      Object.entries(value as Record<string, unknown>)
        .sort(([left], [right]) => left.localeCompare(right))
        .map(([key, entry]) => [key, canonicalResearchTeamPayload(entry)])
    );
  }
  return value;
};

export const createProjectGitResearchTeamPayloadHash = (value: unknown): string =>
  crypto
    .createHash('sha256')
    .update(JSON.stringify(canonicalResearchTeamPayload(value)), 'utf8')
    .digest('hex');

export const recordProjectGitResearchTeamDelivery = (
  request: ProjectGitResearchTeamDeliveryRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  if (request.result === undefined) throw new Error('Research Team delivery receipt requires the full result.');
  if (!Number.isSafeInteger(request.leadPayloadBytes) || request.leadPayloadBytes < 0) {
    throw new Error('Research Team delivery receipt requires a nonnegative Lead payload byte count.');
  }
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (!existing) {
      throw new Error('Research Team assignment receipt is missing; refuse to persist an untracked delivery.');
    }
    if (existing.slotId !== slotId) {
      throw new Error('Research Team assignment receipt slot does not match the delivering Worker slot.');
    }
    if (existing.state === 'prepared') assertMathAssignmentPredecessorRetired(repoRoot, teamId, existing.assignment);
    const resultPayloadBytes = Buffer.byteLength(JSON.stringify(request.result), 'utf8');
    const deliveryId = createProjectGitResearchTeamDeliveryId(teamId, slotId, assignmentId);
    const transportIdempotencyKey = createProjectGitResearchTeamTransportIdempotencyKey(deliveryId);
    const payloadHash = createProjectGitResearchTeamPayloadHash(request.result);
    if (existing.delivery) {
      if (
        existing.delivery.deliveryId !== deliveryId ||
        (existing.delivery.payloadHash && existing.delivery.payloadHash !== payloadHash) ||
        !isDeepStrictEqual(existing.delivery.result, request.result)
      ) {
        throw new Error('Research Team delivery receipt conflicts with the previously persisted result.');
      }
      return existing;
    }
    const delivery: ProjectGitResearchTeamDelivery = Object.freeze({
      deliveryId,
      transportIdempotencyKey,
      payloadHash,
      result: request.result,
      deliveredAt: new Date().toISOString(),
      resultPayloadBytes,
      leadPayloadBytes: request.leadPayloadBytes,
    });
    const { budgetCancellation: _budgetCancellation, ...withoutBudgetCancellation } = existing;
    const receipt: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      ...withoutBudgetCancellation,
      ...(existing.state === 'prepared' ? { state: 'accepted' as const } : {}),
      delivery,
      updatedAt: existing.state === 'prepared' ? new Date().toISOString() : existing.updatedAt,
    });
    writeResearchTeamAssignmentReceipt(repoRoot, receipt);
    return receipt;
  });
};

export const recordProjectGitResearchTeamBudgetCancellation = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  const cancellation = request.budgetCancellation;
  if (!cancellation) throw new Error('Research Team budget cancellation metadata is required.');
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (!existing) {
      if (request.assignment === undefined) {
        throw new Error(
          'Research Team assignment receipt is missing; cancellation recovery requires the full assignment.'
        );
      }
      const now = new Date().toISOString();
      const teamRunId = normalizeResearchTeamReceiptIdentity(cancellation.teamRunId, 'budgetCancellation.teamRunId');
      const prepared: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
        schema: 'deepscientist.research_team_assignment.v1',
        teamId,
        slotId,
        assignmentId,
        state: 'prepared',
        assignment: request.assignment,
        startedAt: now,
        attemptCount: 1,
        teamRunId,
        ...(request.usageBaseline ? { usageBaseline: request.usageBaseline } : {}),
        budgetCancellation: Object.freeze({
          status: cancellation.status,
          teamRunId,
          requestedAt: cancellation.requestedAt || now,
          ...(cancellation.status !== 'pending' ? { lastAttemptAt: cancellation.lastAttemptAt || now } : {}),
          attemptCount: cancellation.status === 'pending' ? 0 : 1,
          ...(cancellation.nextRetryAt ? { nextRetryAt: cancellation.nextRetryAt } : {}),
          ...(cancellation.error ? { error: cancellation.error.slice(0, 2_000) } : {}),
        }),
        updatedAt: now,
      });
      writeResearchTeamAssignmentReceipt(repoRoot, prepared);
      return prepared;
    }
    if (existing.slotId !== slotId) {
      throw new Error('Research Team assignment receipt slot does not match the cancellation request.');
    }
    if (existing.state === 'integrated' || existing.state === 'superseded') return existing;
    const teamRunId = normalizeResearchTeamReceiptIdentity(cancellation.teamRunId, 'budgetCancellation.teamRunId');
    const now = new Date().toISOString();
    const previous = existing.budgetCancellation;
    const attemptCount = Math.max(0, previous?.attemptCount ?? 0) + (cancellation.status === 'pending' ? 0 : 1);
    const next: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      ...existing,
      teamRunId,
      budgetCancellation: Object.freeze({
        status: cancellation.status,
        teamRunId,
        requestedAt: previous?.requestedAt || cancellation.requestedAt || now,
        ...(cancellation.status !== 'pending' ? { lastAttemptAt: cancellation.lastAttemptAt || now } : {}),
        attemptCount: cancellation.status === 'pending' ? (previous?.attemptCount ?? 0) : attemptCount,
        ...(cancellation.nextRetryAt ? { nextRetryAt: cancellation.nextRetryAt } : {}),
        ...(cancellation.error ? { error: cancellation.error.slice(0, 2_000) } : {}),
      }),
      updatedAt: now,
    });
    writeResearchTeamAssignmentReceipt(repoRoot, next);
    return next;
  });
};

export const recordProjectGitResearchTeamSupersessionPending = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  const pending = request.supersessionPending;
  if (!pending) throw new Error('Research Team supersession pending metadata is required.');
  const winnerAssignmentId = normalizeResearchTeamReceiptIdentity(
    pending.winnerAssignmentId,
    'supersessionPending.winnerAssignmentId'
  );
  const reason = String(pending.reason || '').trim();
  if (winnerAssignmentId === assignmentId || !reason || reason.length > 500) {
    throw new Error('Research Team supersession pending metadata is invalid.');
  }
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (!existing) throw new Error('Research Team assignment receipt is missing; refuse to record supersession.');
    if (existing.slotId !== slotId) {
      throw new Error('Research Team assignment receipt slot does not match the supersession request.');
    }
    if (existing.state !== 'accepted') {
      return existing;
    }
    const normalized = Object.freeze({ winnerAssignmentId, reason });
    if (
      existing.supersessionPending?.winnerAssignmentId === winnerAssignmentId &&
      existing.supersessionPending.reason === reason
    ) {
      return existing;
    }
    const next: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      ...existing,
      supersessionPending: normalized,
      updatedAt: new Date().toISOString(),
    });
    writeResearchTeamAssignmentReceipt(repoRoot, next);
    return next;
  });
};

export const completeProjectGitResearchTeamAssignment = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (!existing) {
      throw new Error('Research Team assignment receipt is missing; refuse to mark an untracked result integrated.');
    }
    if (existing.slotId !== slotId) {
      throw new Error('Research Team assignment receipt slot does not match the requested Worker slot.');
    }
    if (existing.state === 'prepared') {
      throw new Error('Research Team assignment was prepared but Core acceptance was never confirmed.');
    }
    if (existing.state === 'superseded') {
      throw new Error('Research Team assignment was superseded and cannot be integrated.');
    }
    if (existing.supersessionPending) {
      throw new Error('Research Team assignment has a pending supersession and cannot be integrated.');
    }
    const integration = normalizeResearchTeamAssignmentIntegration(request.integration);
    const mathProgress = normalizeResearchTeamMathProgress(request.mathProgress);
    if (
      existing.mathProgress &&
      mathProgress &&
      existing.mathProgress.statementHash === mathProgress.statementHash &&
      existing.mathProgress.routeFingerprint === mathProgress.routeFingerprint &&
      mathProgress.consecutiveStalls < existing.mathProgress.consecutiveStalls &&
      mathProgress.outcome === 'stalled'
    ) {
      throw new Error('Research Team Mathematics progress checkpoint cannot move a stalled counter backwards.');
    }
    const sameIntegrationIdentity =
      existing.integration?.executionMode === integration.executionMode &&
      existing.integration.branch === integration.branch &&
      existing.integration.headCommit === integration.headCommit &&
      existing.integration.mergedCommit === integration.mergedCommit &&
      existing.integration.retainedWithoutMerge === integration.retainedWithoutMerge;
    const clearingPendingReverification =
      sameIntegrationIdentity &&
      existing.integration?.reverificationRequired === true &&
      integration.reverificationRequired !== true;
    if (
      existing.state === 'integrated' &&
      (!sameIntegrationIdentity ||
        (!clearingPendingReverification &&
          existing.integration?.reverificationRequired !== integration.reverificationRequired))
    ) {
      throw new Error('Research Team integrated receipt does not match the repeated delivery identity.');
    }
    if (existing.state === 'integrated') {
      if (clearingPendingReverification) {
        const cleared = Object.freeze({ ...existing, integration, updatedAt: new Date().toISOString() });
        writeResearchTeamAssignmentReceipt(repoRoot, cleared);
        return cleared;
      }
      if (mathProgress && existing.mathProgress && !sameMathProgressCheckpoint(existing.mathProgress, mathProgress)) {
        throw new Error('Research Team integrated receipt Mathematics progress conflicts with the repeated delivery.');
      }
      const backfillMathProgress = mathProgress && !existing.mathProgress;
      if (backfillMathProgress) {
        const backfilled = Object.freeze({
          ...existing,
          ...(backfillMathProgress ? { mathProgress } : {}),
          updatedAt: new Date().toISOString(),
        });
        writeResearchTeamAssignmentReceipt(repoRoot, backfilled);
        return backfilled;
      }
      return existing;
    }
    const {
      supersessionPending: _supersessionPending,
      budgetCancellation: _budgetCancellation,
      ...withoutPendingSupersession
    } = existing;
    const receipt: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      ...withoutPendingSupersession,
      state: 'integrated',
      integration,
      ...(mathProgress ? { mathProgress } : {}),
      updatedAt: new Date().toISOString(),
    });
    writeResearchTeamAssignmentReceipt(repoRoot, receipt);
    return receipt;
  });
};

const withoutMathProgressTimestamp = (
  value: MathDurableProgressCheckpoint
): Omit<MathDurableProgressCheckpoint, 'updatedAt'> => {
  const { updatedAt: _updatedAt, ...rest } = value;
  return rest;
};

const sameMathProgressCheckpoint = (
  left: MathDurableProgressCheckpoint,
  right: MathDurableProgressCheckpoint
): boolean => isDeepStrictEqual(withoutMathProgressTimestamp(left), withoutMathProgressTimestamp(right));

export const supersedeProjectGitResearchTeamAssignment = (
  request: ProjectGitResearchTeamAssignmentRequest
): ProjectGitResearchTeamAssignmentReceipt => {
  const repoRoot = resolveWorkspace(request.workspace);
  const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
  const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
  const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
  return withResearchTeamAssignmentLock(repoRoot, teamId, assignmentId, () => {
    const existing = readResearchTeamAssignmentReceipt(repoRoot, teamId, assignmentId);
    if (!existing) {
      throw new Error('Research Team assignment receipt is missing; refuse to supersede an untracked result.');
    }
    if (existing.slotId !== slotId) {
      throw new Error('Research Team assignment receipt slot does not match the requested Worker slot.');
    }
    if (existing.state === 'integrated' && existing.integration?.verification?.disposition !== 'candidate_rejected') {
      throw new Error('Research Team assignment is already integrated and cannot be superseded.');
    }
    const winnerAssignmentId = normalizeResearchTeamReceiptIdentity(
      request.supersession?.winnerAssignmentId || '',
      'supersession.winnerAssignmentId'
    );
    const reason = String(request.supersession?.reason || '').trim();
    if (winnerAssignmentId === assignmentId) {
      throw new Error('Research Team assignment cannot supersede itself.');
    }
    if (!reason || reason.length > 500) {
      throw new Error('Research Team assignment supersession requires a bounded reason.');
    }
    const supersession = Object.freeze({ winnerAssignmentId, reason });
    if (existing.state === 'superseded') {
      if (
        existing.supersession?.winnerAssignmentId !== supersession.winnerAssignmentId ||
        existing.supersession.reason !== supersession.reason
      ) {
        throw new Error('Research Team superseded receipt conflicts with the repeated selection.');
      }
      return existing;
    }
    const {
      supersessionPending: _supersessionPending,
      budgetCancellation: _budgetCancellation,
      ...withoutPendingSupersession
    } = existing;
    const receipt: ProjectGitResearchTeamAssignmentReceipt = Object.freeze({
      ...withoutPendingSupersession,
      state: 'superseded',
      supersession,
      updatedAt: new Date().toISOString(),
    });
    writeResearchTeamAssignmentReceipt(repoRoot, receipt);
    return receipt;
  });
};

const readResearchBranchMetadata = (repoRoot: string): ResearchBranchMetadataStore => {
  const storePath = researchBranchStorePath(repoRoot);
  if (!fs.existsSync(storePath)) return { schema: 'deepscientist.research_branches.v1', branches: [] };
  try {
    const parsed = JSON.parse(fs.readFileSync(storePath, 'utf8')) as Partial<ResearchBranchMetadataStore>;
    if (parsed.schema !== 'deepscientist.research_branches.v1' || !Array.isArray(parsed.branches)) {
      throw new Error('invalid research branch metadata schema');
    }
    return {
      schema: 'deepscientist.research_branches.v1',
      branches: parsed.branches.filter((branch): branch is ResearchBranchMetadata => Boolean(branch?.name)),
    };
  } catch (error) {
    throw new Error('Research branch metadata is unreadable; refuse to reconcile Agent worktrees.', { cause: error });
  }
};

const writeResearchBranchMetadata = (repoRoot: string, store: ResearchBranchMetadataStore): void => {
  const storePath = researchBranchStorePath(repoRoot);
  writeFileAtomicDurable(storePath, `${JSON.stringify(store, null, 2)}\n`);
};

const heldProjectGitLocks = new Set<string>();

const withProjectGitFileLock = <T>(lockPath: string, busyMessage: string, operation: () => T): T => {
  // Nested calls in one service invocation (for example prepare → reconcile →
  // metadata update) already hold the same repository lock. Keep the lock
  // re-entrant in-process while the lock file still serializes other workers
  // and other Electron/MCP processes.
  if (heldProjectGitLocks.has(lockPath)) return operation();
  fs.mkdirSync(path.dirname(lockPath), { recursive: true });
  const lockToken = crypto.randomUUID();
  const lockContents = JSON.stringify({ ...projectGitLockOwner(), token: lockToken, createdAt: Date.now() });
  let descriptor: number | undefined;
  while (descriptor === undefined) {
    try {
      descriptor = fs.openSync(lockPath, 'wx', 0o600);
      fs.writeFileSync(descriptor, `${lockContents}\n`);
    } catch (error) {
      if (descriptor !== undefined) {
        try {
          fs.closeSync(descriptor);
        } catch {
          // Preserve the original lock/write error.
        }
        try {
          fs.unlinkSync(lockPath);
        } catch {
          // Preserve the original lock/write error.
        }
        descriptor = undefined;
      }
      if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
      try {
        const staleByAge = Date.now() - fs.statSync(lockPath).mtimeMs > 30_000;
        const observedContents = fs.readFileSync(lockPath, 'utf8');
        let ownerAlive = false;
        try {
          ownerAlive = isProjectGitLockOwnerAlive(JSON.parse(observedContents));
        } catch {
          // Invalid lock metadata is eligible for age-based stale recovery.
        }
        if (staleByAge && !ownerAlive) {
          if (fs.readFileSync(lockPath, 'utf8') === observedContents) fs.unlinkSync(lockPath);
          continue;
        }
      } catch (statError) {
        if ((statError as NodeJS.ErrnoException).code === 'ENOENT') continue;
        throw statError;
      }
      // Never block Electron's process event loop waiting on a filesystem
      // lock.  The operation is intentionally fail-fast and can be retried by
      // the caller without holding the UI/IPC thread hostage.
      throw new Error(busyMessage, { cause: error });
    }
  }
  heldProjectGitLocks.add(lockPath);
  try {
    return operation();
  } finally {
    heldProjectGitLocks.delete(lockPath);
    if (descriptor !== undefined) fs.closeSync(descriptor);
    try {
      const current = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as { token?: unknown };
      if (current.token === lockToken) fs.unlinkSync(lockPath);
    } catch (error) {
      // Cleanup must never replace an error raised by the protected operation.
      // A missing, malformed, or concurrently replaced lock is safe to leave
      // for the stale-lock recovery path on the next writer.
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT' && !(error instanceof SyntaxError)) {
        console.warn('[ProjectGit] failed to release project Git lock', error);
      }
    }
  }
};

const withResearchBranchMetadataLock = <T>(repoRoot: string, operation: () => T): T =>
  withProjectGitFileLock(
    `${researchBranchStorePath(repoRoot)}.lock`,
    'Research branch metadata is busy in another process; retry asynchronously.',
    operation
  );

const projectGitRepositoryLockPath = (repoRoot: string): string =>
  path.join(gitCommonDir(repoRoot), 'deepscientist', 'git-operations.lock');

const withProjectGitRepositoryLock = <T>(repoRoot: string, operation: () => T): T =>
  withProjectGitFileLock(
    projectGitRepositoryLockPath(repoRoot),
    'Project Git repository is busy in another process; retry asynchronously.',
    operation
  );

/** Run a custom canonical Git mutation under the same lock as ProjectGit operations. */
export const runProjectGitRepositoryMutation = <T>(workspace: string, operation: () => T): T => {
  const repository = discoverRepository(workspace);
  assertRepositoryRootWriteScope(repository, 'Mutating a Project Git repository');
  return withProjectGitRepositoryLock(repository.repoRoot, operation);
};

/**
 * Serialize mutations that happen before a repository exists (managed project
 * creation, cloning, or initializing a selected non-Git directory).  Once a
 * repository exists callers should use withProjectGitRepositoryLock so all
 * worktrees sharing the same Git common directory coordinate on one lock.
 */
const withProjectGitPathLock = <T>(targetPath: string, operation: () => T): T =>
  (() => {
    const resolvedTarget = path.resolve(targetPath);
    const lockDirectory =
      fs.existsSync(resolvedTarget) && fs.statSync(resolvedTarget).isDirectory()
        ? resolvedTarget
        : path.dirname(resolvedTarget);
    const lockKey = crypto.createHash('sha256').update(resolvedTarget).digest('hex').slice(0, 24);
    return withProjectGitFileLock(
      path.join(lockDirectory, `.deepscientist-operation-${lockKey}.lock`),
      'Project workspace is busy in another process; retry asynchronously.',
      operation
    );
  })();

const upsertResearchBranchMetadata = (repoRoot: string, metadata: ResearchBranchMetadata): void => {
  withResearchBranchMetadataLock(repoRoot, () => {
    const store = readResearchBranchMetadata(repoRoot);
    const current = store.branches.find((branch) => branch.name === metadata.name);
    store.branches = [
      ...store.branches.filter((branch) => branch.name !== metadata.name),
      { ...current, ...metadata, updatedAt: new Date().toISOString() },
    ];
    writeResearchBranchMetadata(repoRoot, store);
  });
};

const stableGitSegment = (value: string, fallback: string): string => {
  const normalized = String(value || '')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 36);
  return normalized || fallback;
};

const agentBranchIdentity = (
  request: ProjectGitPrepareAgentWorktreeRequest
): { branch: string; worktreeSegments: string[]; legacyChallengeLayout: boolean; namespace: string } => {
  const legacyChallengeLayout = !request.orchestrationNamespace;
  const namespace = stableGitSegment(request.orchestrationNamespace || 'challenge', 'challenge');
  const team = stableGitSegment(request.teamId, 'team');
  const role = stableGitSegment(request.roleId, stableGitSegment(request.slotId, 'worker'));
  const assignment = stableGitSegment(request.assignmentId, 'assignment');
  const digest = crypto
    .createHash('sha256')
    .update(`${namespace}\0${request.teamId}\0${request.slotId}\0${request.assignmentId}`)
    .digest('hex')
    .slice(0, 10);
  const leaf = `${assignment.slice(0, 28)}-${digest}`;
  return {
    branch: legacyChallengeLayout
      ? `deepscientist/challenge/${team}/${role}/${leaf}`
      : `deepscientist/agents/${namespace}/${team}/${role}/${leaf}`,
    worktreeSegments: legacyChallengeLayout ? [team, role, leaf] : [namespace, team, role, leaf],
    legacyChallengeLayout,
    namespace,
  };
};

const LOCAL_AGENT_RUNTIME_EXCLUDE_RULES = [
  '/.deepscientist/challenge-worktrees/',
  '/.deepscientist/agent-worktrees/',
  '/.agents/skills/',
  '/.codex/skills/',
  '/active-problem.json',
  '**/.lake/',
  '**/.lake.incomplete/',
];

/**
 * The IMO adapter keeps evaluator-only inputs in the controller workspace so
 * the outer verifier can certify the submitted commit.  A Worker receives a
 * linked Git worktree, therefore those tracked files would otherwise be
 * readable by the model even though its role contract denies them.  Sparse
 * checkout removes them from the Worker filesystem without staging deletions
 * or changing the branch commit.
 */
const BLIND_WORKER_MARKER = path.join('.humanize', 'imo2026-blind-worker');
const BLIND_WORKER_SPARSE_PATTERNS = [
  '/*',
  '!/ComparatorChallenge.lean',
  '!/comparator.json',
  '!/docs/humanize/math-contract.json',
] as const;

const applyBlindWorkerSparseCheckout = (canonicalWorkspace: string, assignedWorkspace: string): void => {
  if (!fs.existsSync(path.join(canonicalWorkspace, BLIND_WORKER_MARKER))) return;
  const sparse = runGit(
    assignedWorkspace,
    ['sparse-checkout', 'set', '--no-cone', ...BLIND_WORKER_SPARSE_PATTERNS],
    MAX_GIT_BUFFER,
    resolveAgentWorktreeGitTimeoutMs()
  );
  if (sparse.status !== 0) {
    throw new Error(errorMessage(sparse, 'Unable to apply the blind Worker worktree policy.'));
  }
};

const ensureLocalAgentWorktreeExcludes = (repoRoot: string): void => {
  const excludePath = path.join(gitCommonDir(repoRoot), 'info', 'exclude');
  fs.mkdirSync(path.dirname(excludePath), { recursive: true });
  let current = fs.existsSync(excludePath) ? fs.readFileSync(excludePath, 'utf8') : '';
  const existing = new Set(current.split(/\r?\n/u));
  const missing = LOCAL_AGENT_RUNTIME_EXCLUDE_RULES.filter((rule) => !existing.has(rule));
  if (!missing.length) return;
  current = `${current}${current && !current.endsWith('\n') ? '\n' : ''}${missing.join('\n')}\n`;
  fs.writeFileSync(excludePath, current, { encoding: 'utf8', mode: 0o600 });
};

/**
 * lean_workspace calls ensureScienceProject on the Team root, which creates an
 * untracked .deepscientist/project.json and .gitignore. They are not Lead work
 * and a Worker branches from a commit, so they never reach the worktree; but
 * as untracked files they blocked every later Worker worktree (run 23).
 * Managed projects track these files, so they are tolerated here rather than
 * excluded globally.
 *
 * lean_workspace certification also projects its Lean trace into the Team
 * root (`mathematics/verification-trace.json` and a content-addressed copy
 * under `mathematics/report-traces/`). The mathematics verifier already
 * ignores exactly these paths, but integration did not: in run 23 attempt 15
 * a kernel-verified original-target proof was refused four times with
 * "clean the project before integration" because of that projection alone.
 */
const SCIENCE_RUNTIME_MANIFEST_PATHS = new Set(['.deepscientist/project.json', '.deepscientist/.gitignore']);
const MATHEMATICS_TRACE_PROJECTION_PATH = 'mathematics/verification-trace.json';
const MATHEMATICS_REPORT_TRACE_PATTERN = /^mathematics\/report-traces\/verification-[a-f0-9]{20}\.json$/u;
export const isUntrackedScienceRuntimeRecordPath = (pathRelative: string): boolean =>
  SCIENCE_RUNTIME_MANIFEST_PATHS.has(pathRelative) ||
  pathRelative === MATHEMATICS_TRACE_PROJECTION_PATH ||
  MATHEMATICS_REPORT_TRACE_PATTERN.test(pathRelative) ||
  isMathWorkerProofRuntimeRecordPath(pathRelative);
const onlyUntrackedScienceRuntimeManifest = (repoRoot: string): boolean => {
  const status = runGit(repoRoot, ['status', '--porcelain=v1', '-z', '--untracked-files=all']);
  if (status.status !== 0) return false;
  const entries = status.stdout.toString('utf8').split('\0').filter(Boolean);
  return (
    entries.length > 0 &&
    entries.every((entry) => entry.startsWith('?? ') && isUntrackedScienceRuntimeRecordPath(entry.slice(3)))
  );
};

const listedWorktreeForBranch = (repoRoot: string, branch: string): string | undefined => {
  const result = runGit(repoRoot, ['worktree', 'list', '--porcelain']);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to inspect Git worktrees.'));
  const targetRef = `refs/heads/${branch}`;
  return result.stdout
    .toString('utf8')
    .split(/\r?\n\r?\n/u)
    .map((block) => ({
      worktree: /^worktree (.+)$/mu.exec(block)?.[1],
      ref: /^branch (.+)$/mu.exec(block)?.[1],
    }))
    .find((item) => item.ref === targetRef)?.worktree;
};

const listedWorktreesByRef = (repoRoot: string): Map<string, string> => {
  const result = runGit(repoRoot, ['worktree', 'list', '--porcelain']);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to inspect Git worktrees.'));
  return new Map(
    result.stdout
      .toString('utf8')
      .split(/\r?\n\r?\n/u)
      .flatMap((block) => {
        const worktree = /^worktree (.+)$/mu.exec(block)?.[1];
        const ref = /^branch (.+)$/mu.exec(block)?.[1];
        return worktree && ref ? [[ref, worktree] as const] : [];
      })
  );
};

/**
 * Reconcile clean Agent worktrees left behind by a Core/desktop crash.  Dirty
 * worktrees are deliberately preserved as evidence; only worktrees below the
 * DeepScientist Agent directory whose branch has no durable assignment
 * metadata are eligible for automatic reclamation.
 */
export const reconcileProjectGitAgentWorktrees = (workspace: string): { reclaimed: number; preserved: number } => {
  const repository = discoverRepository(workspace);
  assertRepositoryRootWriteScope(repository, 'Reconciling Agent worktrees');
  return withProjectGitRepositoryLock(repository.repoRoot, () => {
    const metadataNames = new Set(
      readResearchBranchMetadata(repository.repoRoot).branches.map((branch) => branch.name)
    );
    const agentRoot = path.resolve(repository.repoRoot, '.deepscientist', 'agent-worktrees');
    let reclaimed = 0;
    let preserved = 0;
    for (const [ref, worktree] of listedWorktreesByRef(repository.repoRoot)) {
      if (!ref.startsWith('refs/heads/')) continue;
      const resolvedWorktree = path.resolve(worktree);
      if (
        resolvedWorktree === path.resolve(repository.repoRoot) ||
        !resolvedWorktree.startsWith(`${agentRoot}${path.sep}`)
      ) {
        continue;
      }
      const branch = ref.slice('refs/heads/'.length);
      if (metadataNames.has(branch)) continue;
      const status = inspectAgentWorktree(resolvedWorktree, resolvedWorktree);
      if (status.state === 'dirty') {
        preserved += 1;
        continue;
      }
      const removed = runGit(repository.repoRoot, ['worktree', 'remove', '--force', resolvedWorktree]);
      if (removed.status !== 0) {
        preserved += 1;
        continue;
      }
      const deleted = runGit(repository.repoRoot, ['branch', '-D', '--', branch]);
      if (deleted.status === 0 || deleted.status === 1) reclaimed += 1;
      else preserved += 1;
    }
    return { reclaimed, preserved };
  });
};

const inspectAgentWorktree = (
  worktreePath: string | undefined,
  registeredRoot: string | undefined
): { state?: ProjectGitAgentWorktreeState; dirtyFileCount?: number } => {
  if (!worktreePath) return {};
  const resolvedPath = path.resolve(worktreePath);
  const resolvedRoot = registeredRoot ? path.resolve(registeredRoot) : undefined;
  const belongsToRegisteredWorktree =
    resolvedRoot && (resolvedPath === resolvedRoot || resolvedPath.startsWith(`${resolvedRoot}${path.sep}`));
  if (!fs.existsSync(resolvedPath) || !belongsToRegisteredWorktree) return { state: 'missing' };
  const status = runGit(resolvedPath, ['status', '--porcelain=v1', '--untracked-files=normal']);
  if (status.status !== 0) return { state: 'missing' };
  const dirtyFileCount = status.stdout.toString('utf8').split(/\r?\n/u).filter(Boolean).length;
  return dirtyFileCount ? { state: 'dirty', dirtyFileCount } : { state: 'clean', dirtyFileCount: 0 };
};

const CHECKPOINT_IGNORED_SEGMENTS = new Set([
  'node_modules',
  'out',
  'dist',
  'build',
  'coverage',
  '.cache',
  '__pycache__',
  '.pytest_cache',
  '.mypy_cache',
  '.ruff_cache',
  '.tox',
  '.venv',
]);

const PROJECT_GIT_DOMAINS = new Set<ProjectGitDomain>([
  'general',
  'research',
  'medical_evidence',
  'knowledge_deposition',
  'financial',
  'financial_factor',
  'target_discovery',
  'mathematics',
  'challenge',
]);

const isSensitiveCheckpointPath = (value: string): boolean => {
  const normalized = value.replace(/\\/gu, '/').toLowerCase();
  const basename = normalized.split('/').at(-1) || normalized;
  if (
    normalized === '.deepscientist/artifact-repo' ||
    normalized.startsWith('.deepscientist/artifact-repo/') ||
    normalized === '.deepscientist/science-artifacts' ||
    normalized.startsWith('.deepscientist/science-artifacts/') ||
    normalized === '.deepscientist/exports' ||
    normalized.startsWith('.deepscientist/exports/') ||
    normalized === '.deepscientist/factor-search' ||
    normalized.startsWith('.deepscientist/factor-search/') ||
    normalized.includes('/.deepscientist/artifact-repo/') ||
    normalized.endsWith('/.deepscientist/artifact-repo') ||
    normalized.includes('/.deepscientist/science-artifacts/') ||
    normalized.endsWith('/.deepscientist/science-artifacts') ||
    normalized.includes('/.deepscientist/exports/') ||
    normalized.endsWith('/.deepscientist/exports') ||
    normalized.includes('/.deepscientist/factor-search/') ||
    normalized.endsWith('/.deepscientist/factor-search')
  ) {
    return true;
  }
  if ([...CHECKPOINT_IGNORED_SEGMENTS].some((segment) => normalized.split('/').includes(segment))) return true;
  return (
    /^\.env(?:\.|$)/u.test(basename) ||
    /(?:^|[._-])(?:credential|credentials|secret|secrets|token|tokens)(?:[._-]|$)/u.test(basename) ||
    /\.(?:pem|key|p12|pfx)$/u.test(basename) ||
    /^(?:id_rsa|id_ed25519|authorized_keys)$/u.test(basename)
  );
};

const resolveCommit = (repoRoot: string, value: string): string => {
  const ref = validateRef(value);
  const result = runGit(repoRoot, ['rev-parse', '--verify', `${ref}^{commit}`]);
  const sha = textOutput(result);
  if (result.status !== 0 || !/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/u.test(sha))
    throw new Error(errorMessage(result, 'Git revision not found.'));
  return sha;
};

export const resolveProjectGitCommit = (request: ProjectGitResolveCommitRequest): string =>
  resolveCommit(resolveWorkspace(request.workspace), request.reference);

/** Return whether an exact commit is present in the canonical descendant history. */
export const isProjectGitCommitAncestor = (request: ProjectGitCommitAncestorRequest): boolean => {
  const repoRoot = resolveWorkspace(request.workspace);
  const ancestor = resolveCommit(repoRoot, request.ancestor);
  const descendant = resolveCommit(repoRoot, request.descendant ?? 'HEAD');
  return runGit(repoRoot, ['merge-base', '--is-ancestor', ancestor, descendant]).status === 0;
};

const getStatusCounts = (
  value: string
): Pick<ProjectGitRepository, 'dirty' | 'stagedCount' | 'modifiedCount' | 'untrackedCount' | 'dirtyFileCount'> => {
  let stagedCount = 0;
  let modifiedCount = 0;
  let untrackedCount = 0;
  const dirtyFiles = new Set<string>();
  value
    .split(/\r?\n/u)
    .filter(Boolean)
    .forEach((line) => {
      const index = line.charAt(0);
      const worktree = line.charAt(1);
      const rawPath = line.slice(3).trim();
      dirtyFiles.add(rawPath.split(' -> ').at(-1) || rawPath);
      if (index === '?' && worktree === '?') untrackedCount += 1;
      else {
        if (index && index !== ' ') stagedCount += 1;
        if (worktree && worktree !== ' ') modifiedCount += 1;
      }
    });
  return {
    dirty: stagedCount + modifiedCount + untrackedCount > 0,
    stagedCount,
    modifiedCount,
    untrackedCount,
    dirtyFileCount: dirtyFiles.size,
  };
};

const discoverRepository = (workspace: string): ProjectGitRepository => {
  const workspaceRoot = resolveWorkspace(workspace);
  const rootResult = runGit(workspaceRoot, ['rev-parse', '--show-toplevel']);
  if (rootResult.status !== 0)
    throw new Error(errorMessage(rootResult, 'The selected project is not a Git repository.'));
  const repoRoot = fs.realpathSync(textOutput(rootResult));
  const relative = path.relative(repoRoot, workspaceRoot).replace(/\\/gu, '/');
  if (relative.startsWith('..') || path.isAbsolute(relative))
    throw new Error('The workspace is outside the Git repository.');
  const branchResult = runGit(repoRoot, ['symbolic-ref', '--quiet', '--short', 'HEAD']);
  const headResult = runGit(repoRoot, ['rev-parse', '--verify', 'HEAD']);
  const bare = textOutput(runGit(repoRoot, ['rev-parse', '--is-bare-repository'])) === 'true';
  const statusText = porcelainOutput(runGit(repoRoot, ['status', '--porcelain=v1', '--untracked-files=normal']));
  return {
    workspaceRoot,
    repoRoot,
    workspacePrefix: relative || undefined,
    branch: branchResult.status === 0 ? textOutput(branchResult) : undefined,
    head: headResult.status === 0 ? textOutput(headResult) : undefined,
    detached: branchResult.status !== 0 && headResult.status === 0,
    bare,
    ...getStatusCounts(statusText),
  };
};

const withRepository = <T extends ProjectGitDiscoverResult>(
  request: ProjectGitDiscoverRequest,
  fallback: Partial<T>,
  handler: (repository: ProjectGitRepository) => T
): T => {
  try {
    return handler(discoverRepository(request.workspace));
  } catch (error) {
    return {
      ...fallback,
      ok: false,
      error: error instanceof Error ? error.message : String(error),
    } as T;
  }
};

const scopePathspec = (repository: ProjectGitRepository, requestedPath?: string): string[] => {
  const relativePath = normalizeRelativePath(requestedPath);
  const scopedPath = [repository.workspacePrefix, relativePath].filter(Boolean).join('/');
  return scopedPath ? ['--', scopedPath] : [];
};

const assertRepositoryRootWriteScope = (repository: ProjectGitRepository, operation: string): void => {
  if (!repository.workspacePrefix) return;
  throw new Error(
    `${operation} requires the bound project workspace to be the Git repository root. ` +
      'A subdirectory workspace cannot authorize repository-wide Git mutations.'
  );
};

const toWorkspacePath = (repository: ProjectGitRepository, repoPath?: string): string | undefined => {
  if (!repoPath || !repository.workspacePrefix) return repoPath;
  const prefix = `${repository.workspacePrefix}/`;
  return repoPath.startsWith(prefix) ? repoPath.slice(prefix.length) : repoPath;
};

const getCommitSummary = (repoRoot: string, sha: string) => {
  const result = runGit(repoRoot, ['show', '-s', `--format=${PROJECT_GIT_LOG_FORMAT}`, sha]);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to read Git commit.'));
  const commit = parseGitLog(result.stdout.toString('utf8'))[0];
  if (!commit) throw new Error('Unable to parse Git commit.');
  return commit;
};

const getPathCommitSummaries = (
  repository: ProjectGitRepository,
  sha: string,
  relativePath: string,
  entryNames: string[]
): Map<string, NonNullable<ProjectGitTreeEntry['lastCommit']>> => {
  const summaries = new Map<string, NonNullable<ProjectGitTreeEntry['lastCommit']>>();
  if (!entryNames.length) return summaries;
  const targetNames = new Set(entryNames);
  const repoPath = [repository.workspacePrefix, relativePath].filter(Boolean).join('/');
  const result = runGit(repository.repoRoot, [
    '-c',
    'core.quotepath=false',
    'log',
    '--date=iso-strict',
    `--format=%x1e${PATH_LOG_FORMAT}%x1d`,
    '--name-only',
    sha,
    ...(repoPath ? ['--', repoPath] : []),
  ]);
  if (result.status !== 0) return summaries;
  result.stdout
    .toString('utf8')
    .split(PATH_LOG_RECORD_SEPARATOR)
    .filter(Boolean)
    .forEach((record) => {
      const metadataEnd = record.indexOf(PATH_LOG_METADATA_SEPARATOR);
      if (metadataEnd < 0) return;
      const [commitSha, shortSha, subject, authoredAt] = record
        .slice(0, metadataEnd)
        .trim()
        .split(PATH_LOG_FIELD_SEPARATOR);
      if (!commitSha || !shortSha) return;
      record
        .slice(metadataEnd + 1)
        .split(/\r?\n/u)
        .map((item) => item.trim())
        .filter(Boolean)
        .forEach((changedRepoPath) => {
          const workspacePath = toWorkspacePath(repository, changedRepoPath);
          if (!workspacePath) return;
          const currentPrefix = relativePath ? `${relativePath}/` : '';
          if (currentPrefix && !workspacePath.startsWith(currentPrefix)) return;
          const entryName = workspacePath.slice(currentPrefix.length).split('/')[0];
          if (!targetNames.has(entryName) || summaries.has(entryName)) return;
          summaries.set(entryName, { sha: commitSha, shortSha, subject, authoredAt: authoredAt || undefined });
        });
    });
  return summaries;
};

const getCommitBase = (repoRoot: string, sha: string, requestedParent?: string): string => {
  if (requestedParent) {
    const parent = resolveCommit(repoRoot, requestedParent);
    const parents = getCommitSummary(repoRoot, sha).parents;
    if (!parents.includes(parent)) throw new Error('The selected comparison base is not a parent of this commit.');
    return parent;
  }
  return getCommitSummary(repoRoot, sha).parents[0] || EMPTY_TREE_SHA;
};

export const discoverProjectGit = (request: ProjectGitDiscoverRequest): ProjectGitDiscoverResult =>
  withRepository<ProjectGitDiscoverResult>(request, {}, (repository) => ({ ok: true, repository }));

export const inspectProjectGitWorkspace = (request: ProjectGitPreflightRequest): ProjectGitPreflightResult => {
  try {
    const workspace = resolveWorkspace(request.workspace);
    const rootResult = runGit(workspace, ['rev-parse', '--show-toplevel']);
    if (rootResult.status !== 0) return { ok: true, kind: 'non-git', canIsolate: false };
    const repository = discoverRepository(workspace);
    return {
      ok: true,
      kind: 'git',
      repository,
      canIsolate: Boolean(repository.head && !repository.bare && !repository.workspacePrefix),
    };
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const listProjectGitGraph = (request: ProjectGitGraphRequest): ProjectGitGraphResult =>
  withRepository<ProjectGitGraphResult>(request, { commits: [], hasMore: false }, (repository) => {
    const limit = Math.max(1, Math.min(request.limit || 100, 200));
    const skip = Math.max(0, request.skip || 0);
    const ref = request.ref ? resolveCommit(repository.repoRoot, request.ref) : repository.head;
    if (!ref && !request.allRefs) return { ok: true, repository, commits: [], hasMore: false };
    const revisionArgs = request.ref ? [ref!] : request.allRefs ? ['--all', '--topo-order'] : [ref!];
    const pathspec = scopePathspec(repository);
    const logResult = runGit(repository.repoRoot, [
      'log',
      `--max-count=${limit + 1}`,
      `--skip=${skip}`,
      '--date=iso-strict',
      `--format=${PROJECT_GIT_LOG_FORMAT}`,
      ...revisionArgs,
      ...pathspec,
    ]);
    if (logResult.status !== 0) throw new Error(errorMessage(logResult, 'Unable to read Git history.'));
    const parsed = parseGitLog(logResult.stdout.toString('utf8'));
    const hasMore = parsed.length > limit;
    const statsResult = runGit(repository.repoRoot, [
      'log',
      `--max-count=${limit}`,
      `--skip=${skip}`,
      '--format=%x1e%H',
      '--find-renames',
      '--no-merges',
      '--numstat',
      ...revisionArgs,
      ...pathspec,
    ]);
    const statsByCommit = parseLogNumstats(statsResult.stdout.toString('utf8'));
    const commits = parsed.slice(0, limit).map((commit) =>
      Object.assign(
        {},
        commit,
        statsByCommit.get(commit.sha) || {
          changedFileCount: 0,
          additions: 0,
          deletions: 0,
        }
      )
    );
    return {
      ok: true,
      repository,
      commits,
      hasMore,
      nextSkip: hasMore ? skip + limit : undefined,
    };
  });

const latestCheckpointForRef = (repoRoot: string, ref: string): ReturnType<typeof getCommitSummary> | undefined => {
  const result = runGit(repoRoot, [
    'log',
    '--max-count=200',
    '--date=iso-strict',
    `--format=${PROJECT_GIT_LOG_FORMAT}`,
    ref,
  ]);
  if (result.status !== 0) return undefined;
  return parseGitLog(result.stdout.toString('utf8')).find((commit) => Boolean(commit.checkpoint));
};

const listResearchBranches = (repository: ProjectGitRepository, goalId?: string): ProjectGitResearchBranch[] => {
  const result = runGit(repository.repoRoot, [
    'for-each-ref',
    '--sort=-committerdate',
    '--format=%(refname:short)%00%(refname)%00%(objectname)%00%(committerdate:iso-strict)',
    'refs/heads',
  ]);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to list research branches.'));
  const metadataByName = new Map(
    readResearchBranchMetadata(repository.repoRoot).branches.map((item) => [item.name, item])
  );
  const worktreesByRef = listedWorktreesByRef(repository.repoRoot);
  return result.stdout
    .toString('utf8')
    .split(/\r?\n/u)
    .filter(Boolean)
    .map((line): ProjectGitResearchBranch | undefined => {
      const [name, ref, head, updatedAt] = line.split('\0');
      if (!name || !ref || !head) return undefined;
      const metadata = metadataByName.get(name);
      const latestCheckpoint = latestCheckpointForRef(repository.repoRoot, ref);
      const belongsToGoal = !goalId || metadata?.goalId === goalId || latestCheckpoint?.checkpoint?.goalId === goalId;
      if (!belongsToGoal) return undefined;
      const active = repository.branch === name;
      const worktree = inspectAgentWorktree(metadata?.worktreePath, worktreesByRef.get(ref));
      const branch: ProjectGitResearchBranch & { routeNodeId?: string } = {
        name,
        ref,
        head,
        shortHead: head.slice(0, 7),
        active,
        status: active ? 'active' : metadata?.status || 'candidate',
        parentRef: metadata?.parentRef,
        baseCommit: metadata?.baseCommit,
        goalId: metadata?.goalId || latestCheckpoint?.checkpoint?.goalId,
        routeNodeId: metadata?.routeNodeId || latestCheckpoint?.checkpoint?.routeNodeId,
        objective: metadata?.objective,
        agent: metadata?.agent,
        worktreePath: metadata?.worktreePath,
        worktreeState: worktree.state,
        worktreeDirtyFileCount: worktree.dirtyFileCount,
        mergedInto: metadata?.mergedInto,
        mergedAt: metadata?.mergedAt,
        updatedAt: metadata?.updatedAt || updatedAt || latestCheckpoint?.authoredAt,
        latestCheckpoint,
      };
      return branch;
    })
    .filter((branch): branch is ProjectGitResearchBranch => Boolean(branch))
    .toSorted(
      (left, right) =>
        Number(right.active) - Number(left.active) || String(right.updatedAt).localeCompare(String(left.updatedAt))
    );
};

export const listProjectGitResearchFrontier = (
  request: ProjectGitResearchFrontierRequest
): ProjectGitResearchFrontierResult =>
  withRepository<ProjectGitResearchFrontierResult>(request, { branches: [] }, (repository) => {
    const branches = listResearchBranches(repository, request.goalId);
    return {
      ok: true,
      repository,
      activeBranch: request.goalId ? branches.find((branch) => branch.active)?.name : repository.branch,
      branches,
    };
  });

const assertCleanResearchSwitch = (repository: ProjectGitRepository): void => {
  if (repository.bare) throw new Error('Research branches cannot be switched in a bare Git repository.');
  if (repository.dirty) {
    throw new Error(
      'The working tree must be clean before switching research branches. Create a checkpoint or resolve the changes first.'
    );
  }
};

const assertBranchNotCheckedOutElsewhere = (repository: ProjectGitRepository, branch: string): void => {
  const result = runGit(repository.repoRoot, ['worktree', 'list', '--porcelain']);
  if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to inspect Git worktrees.'));
  const targetRef = `refs/heads/${branch}`;
  const occupied = result.stdout
    .toString('utf8')
    .split(/\r?\n\r?\n/u)
    .map((block) => {
      const worktree = /^worktree (.+)$/mu.exec(block)?.[1];
      const ref = /^branch (.+)$/mu.exec(block)?.[1];
      return { worktree, ref };
    })
    .find(
      (item) =>
        item.ref === targetRef && item.worktree && path.resolve(item.worktree) !== path.resolve(repository.repoRoot)
    );
  if (occupied?.worktree)
    throw new Error(`Research branch ${branch} is already active in another worktree: ${occupied.worktree}`);
};

export const prepareProjectGitResearchBranch = (
  request: ProjectGitPrepareResearchBranchRequest
): ProjectGitPrepareResearchBranchResult => {
  try {
    const repository = discoverRepository(request.workspace);
    assertRepositoryRootWriteScope(repository, 'Preparing a research branch');
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      // Re-read all mutable repository state after acquiring the cross-process
      // lock; the pre-lock discovery only identifies the common Git directory.
      const lockedRepository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(lockedRepository, 'Preparing a research branch');
      assertCleanResearchSwitch(lockedRepository);
      const branch = validateBranchName(lockedRepository.repoRoot, request.branch);
      if (runGit(lockedRepository.repoRoot, ['show-ref', '--verify', '--quiet', `refs/heads/${branch}`]).status === 0) {
        throw new Error(`Research branch already exists: ${branch}`);
      }
      const from = resolveCommit(lockedRepository.repoRoot, request.from);
      const parentRef = request.parentRef ? validateRef(request.parentRef) : lockedRepository.branch;
      if (parentRef) resolveCommit(lockedRepository.repoRoot, parentRef);
      const switched = runGit(lockedRepository.repoRoot, ['switch', '-c', branch, from]);
      if (switched.status !== 0) throw new Error(errorMessage(switched, 'Unable to create the research branch.'));
      const timestamp = new Date().toISOString();
      upsertResearchBranchMetadata(lockedRepository.repoRoot, {
        name: branch,
        parentRef,
        baseCommit: from,
        goalId: normalizeTrailerValue(request.goalId, 120),
        routeNodeId: normalizeTrailerValue(request.routeNodeId, 120),
        objective: normalizeTrailerValue(request.objective, 240),
        status: 'candidate',
        createdAt: timestamp,
        updatedAt: timestamp,
      });
      const nextRepository = discoverRepository(request.workspace);
      const response: ProjectGitPrepareResearchBranchResult = {
        ok: true,
        repository: nextRepository,
        branch: listResearchBranches(nextRepository, request.goalId).find((item) => item.name === branch),
      };
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: nextRepository.repoRoot,
        reason: 'branch-changed',
        branch,
        head: nextRepository.head,
      });
      return response;
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const prepareProjectGitAgentWorktree = (
  request: ProjectGitPrepareAgentWorktreeRequest
): ProjectGitPrepareAgentWorktreeResult => {
  try {
    let repository = discoverRepository(request.workspace);
    assertRepositoryRootWriteScope(repository, 'Preparing an Agent worktree');
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      repository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(repository, 'Preparing an Agent worktree');
      if (repository.bare || !repository.head)
        throw new Error('Agent worktrees require a non-bare repository with a commit.');
      ensureLocalAgentWorktreeExcludes(repository.repoRoot);
      reconcileProjectGitAgentWorktrees(repository.repoRoot);
      repository = discoverRepository(request.workspace);
      if (repository.dirty && !onlyUntrackedScienceRuntimeManifest(repository.repoRoot)) {
        throw new Error('Create a Lead checkpoint or clean the project before dispatching an Agent worktree.');
      }

      const identity = agentBranchIdentity(request);
      const branch = validateBranchName(repository.repoRoot, identity.branch);
      const from = resolveCommit(repository.repoRoot, request.from || repository.head);
      const metadata = readResearchBranchMetadata(repository.repoRoot).branches.find((item) => item.name === branch);
      if (
        metadata?.agent &&
        (metadata.agent.teamId !== request.teamId ||
          metadata.agent.slotId !== request.slotId ||
          metadata.agent.assignmentId !== request.assignmentId)
      ) {
        throw new Error('The deterministic Agent branch is already owned by another assignment.');
      }

      const worktreeRoot = path.join(
        repository.repoRoot,
        '.deepscientist',
        identity.legacyChallengeLayout ? 'challenge-worktrees' : 'agent-worktrees',
        ...identity.worktreeSegments
      );
      const branchExists =
        runGit(repository.repoRoot, ['show-ref', '--verify', '--quiet', `refs/heads/${branch}`]).status === 0;
      if (branchExists && !metadata?.agent) {
        throw new Error('The deterministic Agent branch already exists without registered assignment ownership.');
      }
      const listedWorktree = listedWorktreeForBranch(repository.repoRoot, branch);
      if (listedWorktree && path.resolve(listedWorktree) !== path.resolve(worktreeRoot)) {
        throw new Error(`Agent branch is already checked out in another worktree: ${listedWorktree}`);
      }
      if (!listedWorktree) {
        fs.mkdirSync(path.dirname(worktreeRoot), { recursive: true });
        const worktreeTimeout = resolveAgentWorktreeGitTimeoutMs();
        const added = branchExists
          ? runGit(repository.repoRoot, ['worktree', 'add', worktreeRoot, branch], MAX_GIT_BUFFER, worktreeTimeout)
          : runGit(
              repository.repoRoot,
              ['worktree', 'add', '-b', branch, worktreeRoot, from],
              MAX_GIT_BUFFER,
              worktreeTimeout
            );
        if (added.status !== 0) throw new Error(errorMessage(added, 'Unable to create the Agent worktree.'));
      }

      const assignedWorkspace = repository.workspacePrefix
        ? path.join(worktreeRoot, repository.workspacePrefix)
        : worktreeRoot;
      if (!fs.existsSync(assignedWorkspace)) throw new Error('The Agent workspace was not created.');
      applyBlindWorkerSparseCheckout(path.resolve(request.workspace), assignedWorkspace);
      hydrateAgentLakeCache(path.resolve(request.workspace), assignedWorkspace);
      const timestamp = new Date().toISOString();
      upsertResearchBranchMetadata(repository.repoRoot, {
        name: branch,
        parentRef: repository.branch,
        baseCommit: metadata?.baseCommit || from,
        objective: normalizeTrailerValue(request.objective, 240),
        status: metadata?.status || 'candidate',
        agent: {
          teamId: request.teamId,
          slotId: request.slotId,
          roleId: request.roleId,
          ...(request.strategyLane ? { strategyLane: request.strategyLane } : {}),
          assignmentId: request.assignmentId,
          ...(!identity.legacyChallengeLayout ? { orchestrationNamespace: identity.namespace } : {}),
          ...(request.workflowId ? { workflowId: request.workflowId } : {}),
        },
        worktreePath: assignedWorkspace,
        createdAt: metadata?.createdAt || timestamp,
        updatedAt: timestamp,
      });
      const refreshed = discoverRepository(request.workspace);
      const response: ProjectGitPrepareAgentWorktreeResult = {
        ok: true,
        repository: refreshed,
        branch: listResearchBranches(refreshed).find((item) => item.name === branch),
        workspace: assignedWorkspace,
      };
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: refreshed.repoRoot,
        reason: 'worktree-prepared',
        branch,
        head: response.branch?.head,
      });
      return response;
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

/** Remove an unstarted Agent worktree/branch after a dispatch failure.  Dirty
 * worktrees are preserved deliberately so a failed cleanup cannot destroy
 * Worker evidence; callers can surface them as orphaned resources. */
export const discardProjectGitAgentWorktree = (
  request: ProjectGitDiscardAgentWorktreeRequest
): ProjectGitDiscardAgentWorktreeResult => {
  try {
    let repository = discoverRepository(request.workspace);
    assertRepositoryRootWriteScope(repository, 'Discarding an Agent worktree');
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      repository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(repository, 'Discarding an Agent worktree');
      const teamId = normalizeResearchTeamReceiptIdentity(request.teamId, 'teamId');
      const slotId = normalizeResearchTeamReceiptIdentity(request.slotId, 'slotId');
      const assignmentId = normalizeResearchTeamReceiptIdentity(request.assignmentId, 'assignmentId');
      let branch = request.branch?.trim();
      const worktreePath = request.worktreePath?.trim();
      const receipt = readResearchTeamAssignmentReceipt(repository.repoRoot, teamId, assignmentId);
      const cancelledPreparedReceipt = Boolean(
        receipt?.state === 'prepared' &&
        !receipt.delivery &&
        receipt.slotId === slotId &&
        receipt.budgetCancellation?.status === 'succeeded'
      );
      if (!branch && !worktreePath) {
        // Advisory assignments have no Git identity. Once Core cancellation
        // has succeeded, their prepared WAL is safe to remove so a retry can
        // reuse the assignment id. Keep artifact receipts that still point at
        // a worktree until the caller supplies that identity for cleanup.
        if (!cancelledPreparedReceipt || receipt?.preparedGit?.branch || receipt?.preparedGit?.worktreePath) {
          return { ok: true, discarded: false };
        }
        withResearchTeamAssignmentLock(repository.repoRoot, teamId, assignmentId, () => {
          const current = readResearchTeamAssignmentReceipt(repository.repoRoot, teamId, assignmentId);
          if (
            current?.state === 'prepared' &&
            !current.delivery &&
            current.slotId === slotId &&
            current.budgetCancellation?.status === 'succeeded'
          ) {
            const receiptPath = researchTeamAssignmentReceiptPath(repository.repoRoot, teamId, assignmentId);
            try {
              fs.unlinkSync(receiptPath);
            } catch (error) {
              if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
            }
          }
        });
        return { ok: true, discarded: true };
      }

      const metadataStore = readResearchBranchMetadata(repository.repoRoot);
      const metadataForBranch = branch ? metadataStore.branches.find((item) => item.name === branch) : undefined;
      const canonicalExistingPath = (candidate: string): string | undefined => {
        try {
          return fs.realpathSync(candidate);
        } catch {
          return path.resolve(candidate);
        }
      };
      const agentRoots = [
        path.resolve(repository.repoRoot, '.deepscientist', 'agent-worktrees'),
        path.resolve(repository.repoRoot, '.deepscientist', 'challenge-worktrees'),
      ];
      const isUnder = (candidate: string, root: string): boolean =>
        candidate === root || candidate.startsWith(`${root}${path.sep}`);
      const resolvedWorktreePath = worktreePath ? canonicalExistingPath(worktreePath) : undefined;
      if (resolvedWorktreePath && !agentRoots.some((root) => isUnder(resolvedWorktreePath, root))) {
        throw new Error('Agent worktree cleanup path must remain inside a managed Agent worktree root.');
      }
      if (metadataForBranch) {
        const owner = metadataForBranch.agent;
        if (!owner || owner.teamId !== teamId || owner.slotId !== slotId || owner.assignmentId !== assignmentId) {
          throw new Error('The Agent worktree is owned by a different Team assignment.');
        }
        if (worktreePath && metadataForBranch.worktreePath) {
          const recordedPath = canonicalExistingPath(metadataForBranch.worktreePath);
          if (resolvedWorktreePath !== recordedPath) {
            throw new Error('The Agent worktree path does not match its registered assignment metadata.');
          }
        }
      } else if (branch) {
        throw new Error('The Agent branch has no registered assignment ownership; preserve it for manual recovery.');
      } else if (resolvedWorktreePath) {
        const matching = metadataStore.branches.find((item) => {
          if (!item.worktreePath || !item.agent) return false;
          return (
            item.agent.teamId === teamId &&
            item.agent.slotId === slotId &&
            item.agent.assignmentId === assignmentId &&
            canonicalExistingPath(item.worktreePath) === resolvedWorktreePath
          );
        });
        if (!matching) {
          throw new Error('The Agent worktree has no matching registered assignment; preserve it for manual recovery.');
        }
        branch = matching.name;
      }
      if (worktreePath && fs.existsSync(worktreePath)) {
        const status = runGit(worktreePath, ['status', '--porcelain=v1', '--untracked-files=normal']);
        if (status.status === 0 && status.stdout.toString('utf8').trim()) {
          return {
            ok: true,
            discarded: false,
            preserved: true,
            error: 'Agent worktree contains uncommitted evidence.',
          };
        }
        const removed = runGit(repository.repoRoot, ['worktree', 'remove', '--force', worktreePath]);
        if (removed.status !== 0) throw new Error(errorMessage(removed, 'Unable to remove the Agent worktree.'));
      }
      if (branch) {
        const listed = listedWorktreeForBranch(repository.repoRoot, branch);
        if (listed) {
          const removed = runGit(repository.repoRoot, ['worktree', 'remove', '--force', listed]);
          if (removed.status !== 0) throw new Error(errorMessage(removed, 'Unable to remove the Agent worktree.'));
        }
        const deleted = runGit(repository.repoRoot, ['branch', '-D', '--', branch]);
        if (deleted.status !== 0 && deleted.status !== 1) {
          throw new Error(errorMessage(deleted, 'Unable to remove the Agent branch.'));
        }
        withResearchBranchMetadataLock(repository.repoRoot, () => {
          const store = readResearchBranchMetadata(repository.repoRoot);
          writeResearchBranchMetadata(repository.repoRoot, {
            ...store,
            branches: store.branches.filter((item) => item.name !== branch),
          });
        });
      }
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: repository.repoRoot,
        reason: 'worktree-discarded',
        ...(branch ? { branch } : {}),
      });
      // Keep the prepared WAL entry when reconciliation needs to record a
      // terminal supersession. Dispatch compensation retains the historical
      // deletion behavior unless it explicitly opts into this handoff.
      if (!request.preserveReceipt) {
        try {
          withResearchTeamAssignmentLock(repository.repoRoot, teamId, assignmentId, () => {
            const currentReceipt = readResearchTeamAssignmentReceipt(repository.repoRoot, teamId, assignmentId);
            if (
              currentReceipt?.state === 'prepared' &&
              !currentReceipt.delivery &&
              currentReceipt.slotId === slotId &&
              (!branch || !currentReceipt.preparedGit?.branch || currentReceipt.preparedGit.branch === branch) &&
              (!worktreePath ||
                !currentReceipt.preparedGit?.worktreePath ||
                currentReceipt.preparedGit.worktreePath === worktreePath)
            ) {
              const receiptPath = researchTeamAssignmentReceiptPath(repository.repoRoot, teamId, assignmentId);
              try {
                fs.unlinkSync(receiptPath);
              } catch (error) {
                if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
              }
            }
          });
        } catch {
          // Worktree cleanup remains successful even if receipt deletion races
          // with a recovery reader; the next status pass can reconcile it.
        }
      }
      return { ok: true, discarded: true };
    });
  } catch (error) {
    return { ok: false, discarded: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const integrateProjectGitAgentBranch = (
  request: ProjectGitIntegrateAgentBranchRequest
): ProjectGitIntegrateAgentBranchResult => {
  try {
    let repository = discoverRepository(request.workspace);
    assertRepositoryRootWriteScope(repository, 'Integrating an Agent branch');
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      repository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(repository, 'Integrating an Agent branch');
      if (repository.bare || !repository.head || !repository.branch) {
        throw new Error('Agent integration requires an active Lead branch.');
      }
      // Untracked host projections are not Lead work; the Agent branch never
      // contains them, so the merge cannot overwrite or conflict with them.
      if (repository.dirty && !onlyUntrackedScienceRuntimeManifest(repository.repoRoot))
        throw new Error('Create a Lead checkpoint or clean the project before integration.');
      const branch = validateBranchName(repository.repoRoot, request.branch);
      const metadata = readResearchBranchMetadata(repository.repoRoot).branches.find((item) => item.name === branch);
      if (!metadata?.agent) throw new Error('The selected branch is not a registered research Agent branch.');
      if (metadata.agent.teamId !== request.teamId || metadata.agent.slotId !== request.slotId) {
        throw new Error('The Agent branch owner does not match the requested Team slot.');
      }
      if (request.assignmentId && metadata.agent.assignmentId !== request.assignmentId) {
        throw new Error('The Agent branch owner does not match the requested assignment.');
      }
      if (
        request.orchestrationNamespace &&
        metadata.agent.orchestrationNamespace !== stableGitSegment(request.orchestrationNamespace, 'research')
      ) {
        throw new Error('The Agent branch owner does not match the requested orchestration namespace.');
      }
      const branchHead = resolveCommit(repository.repoRoot, branch);
      if (request.expectedHead && resolveCommit(repository.repoRoot, request.expectedHead) !== branchHead) {
        throw new Error('The delivered commit is not the current head of the Agent branch.');
      }
      if (metadata.worktreePath && fs.existsSync(metadata.worktreePath)) {
        const workerStatus = porcelainOutput(
          runGit(metadata.worktreePath, ['status', '--porcelain=v1', '--untracked-files=all'])
        );
        const noteOnly = workerStatus
          .split('\n')
          .filter(Boolean)
          .every((entry) => {
            const relative = entry.slice(3).trim().replaceAll(path.sep, '/');
            return (
              relative === 'RESEARCH.md' ||
              relative.endsWith('/RESEARCH.md') ||
              (entry.startsWith('?? ') && isMathWorkerProofRuntimeRecordPath(relative))
            );
          });
        if (workerStatus && !noteOnly) throw new Error('The Agent worktree still has uncommitted changes.');
      }

      const alreadyIntegrated =
        runGit(repository.repoRoot, ['merge-base', '--is-ancestor', branchHead, repository.head]).status === 0;
      if (!alreadyIntegrated) {
        const summary = normalizeTrailerValue(request.summary, 160) || metadata.objective || metadata.agent.roleId;
        const merged = runGit(repository.repoRoot, [
          'merge',
          '--no-ff',
          '--no-edit',
          '-m',
          `Research Agent integrate ${metadata.agent.roleId}: ${summary}`,
          branch,
        ]);
        if (merged.status !== 0) {
          runGit(repository.repoRoot, ['merge', '--abort']);
          throw new Error(errorMessage(merged, 'Unable to integrate the Agent branch without conflicts.'));
        }
      }

      const timestamp = new Date().toISOString();
      upsertResearchBranchMetadata(repository.repoRoot, {
        name: branch,
        status: 'promoted',
        mergedInto: repository.branch,
        mergedAt: timestamp,
      });
      const refreshed = discoverRepository(request.workspace);
      const response: ProjectGitIntegrateAgentBranchResult = {
        ok: true,
        repository: refreshed,
        branch: listResearchBranches(refreshed).find((item) => item.name === branch),
        mergedCommit: refreshed.head,
        alreadyIntegrated,
      };
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: refreshed.repoRoot,
        reason: 'branch-integrated',
        branch,
        head: refreshed.head,
      });
      return response;
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const activateProjectGitResearchBranch = (
  request: ProjectGitActivateResearchBranchRequest
): ProjectGitActivateResearchBranchResult => {
  try {
    let repository = discoverRepository(request.workspace);
    assertRepositoryRootWriteScope(repository, 'Activating a research branch');
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      repository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(repository, 'Activating a research branch');
      const branch = validateBranchName(repository.repoRoot, request.branch);
      if (runGit(repository.repoRoot, ['show-ref', '--verify', '--quiet', `refs/heads/${branch}`]).status !== 0) {
        throw new Error(`Research branch not found: ${branch}`);
      }
      if (repository.branch !== branch) {
        assertCleanResearchSwitch(repository);
        assertBranchNotCheckedOutElsewhere(repository, branch);
        const switched = runGit(repository.repoRoot, ['switch', branch]);
        if (switched.status !== 0) throw new Error(errorMessage(switched, 'Unable to activate the research branch.'));
      }
      const routeNodeId = normalizeTrailerValue(request.routeNodeId, 120);
      upsertResearchBranchMetadata(repository.repoRoot, {
        name: branch,
        ...(routeNodeId ? { routeNodeId } : {}),
      });
      const nextRepository = discoverRepository(request.workspace);
      const response: ProjectGitActivateResearchBranchResult = {
        ok: true,
        repository: nextRepository,
        branch: listResearchBranches(nextRepository).find((item) => item.name === branch),
      };
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: nextRepository.repoRoot,
        reason: 'branch-changed',
        branch,
        head: nextRepository.head,
      });
      return response;
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

const compareCheckpointMetrics = (
  base?: ProjectGitCommitSummary['checkpoint'],
  head?: ProjectGitCommitSummary['checkpoint']
): ProjectGitMetricComparison[] => {
  const baseMetrics = new Map((base?.metrics || []).map((metric) => [metric.name, metric]));
  const headMetrics = new Map((head?.metrics || []).map((metric) => [metric.name, metric]));
  const names = [...new Set([...baseMetrics.keys(), ...headMetrics.keys()])];
  const contextMismatch =
    Boolean(base?.metricContext) !== Boolean(head?.metricContext) ||
    (base?.metricContext &&
      head?.metricContext &&
      (base.metricContext.contractId !== head.metricContext.contractId ||
        base.metricContext.evaluationId !== head.metricContext.evaluationId));
  return names.map((name) => {
    const baseMetric = baseMetrics.get(name);
    const headMetric = headMetrics.get(name);
    let reason: string | undefined;
    if (!baseMetric || !headMetric) reason = 'Metric is missing from one branch.';
    else if (contextMismatch) reason = 'Metric contracts or evaluation protocols differ.';
    else if ((baseMetric.unit || '') !== (headMetric.unit || '')) reason = 'Metric units differ.';
    else if ((baseMetric.direction || '') !== (headMetric.direction || '')) reason = 'Metric directions differ.';
    const comparable = !reason;
    const delta = comparable ? headMetric!.value - baseMetric!.value : undefined;
    const direction = headMetric?.direction || baseMetric?.direction;
    return {
      name,
      unit: headMetric?.unit || baseMetric?.unit,
      direction,
      baseValue: baseMetric?.value,
      headValue: headMetric?.value,
      delta,
      relativeDelta: comparable && baseMetric!.value !== 0 ? delta! / Math.abs(baseMetric!.value) : undefined,
      improvement: comparable ? (direction === 'minimize' ? -delta! : delta!) : undefined,
      comparable,
      reason,
    };
  });
};

const branchForRef = (
  repository: ProjectGitRepository,
  branches: ProjectGitResearchBranch[],
  ref: string,
  sha: string
): ProjectGitResearchBranch =>
  branches.find((branch) => branch.name === ref || branch.ref === ref || branch.head === sha) || {
    name: ref,
    ref,
    head: sha,
    shortHead: sha.slice(0, 7),
    active: repository.head === sha,
    status: repository.head === sha ? 'active' : 'candidate',
    latestCheckpoint: latestCheckpointForRef(repository.repoRoot, sha),
  };

export const compareProjectGitResearchBranches = (
  request: ProjectGitCompareResearchBranchesRequest
): ProjectGitCompareResearchBranchesResult => {
  const fallback: ProjectGitCompareResearchBranchesResult = {
    ok: false,
    ahead: 0,
    behind: 0,
    changedFileCount: 0,
    additions: 0,
    deletions: 0,
    metrics: [],
  };
  try {
    const repository = discoverRepository(request.workspace);
    const baseSha = resolveCommit(repository.repoRoot, request.baseRef);
    const headSha = resolveCommit(repository.repoRoot, request.headRef);
    const mergeBaseResult = runGit(repository.repoRoot, ['merge-base', baseSha, headSha]);
    if (mergeBaseResult.status !== 0)
      throw new Error(errorMessage(mergeBaseResult, 'The branches do not share a merge base.'));
    const mergeBase = textOutput(mergeBaseResult);
    const counts = textOutput(
      runGit(repository.repoRoot, ['rev-list', '--left-right', '--count', `${baseSha}...${headSha}`])
    )
      .split(/\s+/u)
      .map(Number);
    const numstat = runGit(repository.repoRoot, [
      'diff',
      '--numstat',
      '-M',
      mergeBase,
      headSha,
      ...scopePathspec(repository),
    ]);
    if (numstat.status !== 0) throw new Error(errorMessage(numstat, 'Unable to compare research branches.'));
    const stats = summarizeNumstat(numstat.stdout.toString('utf8'));
    const branches = listResearchBranches(repository);
    const base = branchForRef(repository, branches, request.baseRef, baseSha);
    const head = branchForRef(repository, branches, request.headRef, headSha);
    return {
      ok: true,
      repository,
      base,
      head,
      mergeBase,
      behind: Number.isFinite(counts[0]) ? counts[0] : 0,
      ahead: Number.isFinite(counts[1]) ? counts[1] : 0,
      ...stats,
      metrics: compareCheckpointMetrics(base.latestCheckpoint?.checkpoint, head.latestCheckpoint?.checkpoint),
    };
  } catch (error) {
    return { ...fallback, error: error instanceof Error ? error.message : String(error) };
  }
};

export const getProjectGitCommit = (request: ProjectGitCommitRequest): ProjectGitCommitResult =>
  withRepository<ProjectGitCommitResult>(request, {}, (repository) => {
    const sha = resolveCommit(repository.repoRoot, request.sha);
    const summary = getCommitSummary(repository.repoRoot, sha);
    const base = summary.parents[0] || EMPTY_TREE_SHA;
    const pathspec = scopePathspec(repository);
    const nameStatus = runGit(repository.repoRoot, ['diff', '--name-status', '-M20%', base, sha, ...pathspec]);
    const numstat = runGit(repository.repoRoot, ['diff', '--numstat', '-M20%', base, sha, ...pathspec]);
    const stats = parseNumstat(numstat.stdout.toString('utf8'));
    const files = parseNameStatus(nameStatus.stdout.toString('utf8'), stats).map((file) =>
      Object.assign({}, file, {
        path: toWorkspacePath(repository, file.path) || file.path,
        oldPath: toWorkspacePath(repository, file.oldPath),
      })
    );
    const body = textOutput(runGit(repository.repoRoot, ['show', '-s', '--format=%B', sha]));
    return {
      ok: true,
      repository,
      commit: {
        ...summary,
        ...summarizeNumstat(numstat.stdout.toString('utf8')),
        body,
        files,
      },
    };
  });

export const getProjectGitDiff = (request: ProjectGitDiffRequest): ProjectGitDiffResult =>
  withRepository<ProjectGitDiffResult>(request, { content: '', truncated: false, binary: false }, (repository) => {
    const sha = resolveCommit(repository.repoRoot, request.sha);
    const base = getCommitBase(repository.repoRoot, sha, request.parent);
    const contextLines = Math.max(0, Math.min(request.contextLines ?? 3, 20));
    const relativePath = normalizeRelativePath(request.path);
    const pathspec = scopePathspec(repository, relativePath);
    const result = runGit(repository.repoRoot, [
      'diff',
      '--find-renames',
      '--no-color',
      `--unified=${contextLines}`,
      base,
      sha,
      ...pathspec,
    ]);
    if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to read Git diff.'));
    const full = result.stdout.toString('utf8');
    const truncated = Buffer.byteLength(full, 'utf8') > MAX_TEXT_BYTES;
    const content = truncated ? Buffer.from(full).subarray(0, MAX_TEXT_BYTES).toString('utf8') : full;
    return {
      ok: true,
      repository,
      sha,
      base,
      path: relativePath,
      content,
      truncated,
      binary: /Binary files .* differ|GIT binary patch/u.test(full),
    };
  });

export const getProjectGitTree = (request: ProjectGitTreeRequest): ProjectGitTreeResult =>
  withRepository<ProjectGitTreeResult>(request, { entries: [] }, (repository) => {
    const sha = resolveCommit(repository.repoRoot, request.sha);
    const commit = getCommitSummary(repository.repoRoot, sha);
    const base = commit.parents[0] || EMPTY_TREE_SHA;
    const relativePath = normalizeRelativePath(request.path);
    const scopedPath = [repository.workspacePrefix, relativePath].filter(Boolean).join('/');
    const treeish = scopedPath ? `${sha}:${scopedPath}` : sha;
    const result = runGit(repository.repoRoot, ['ls-tree', '-z', treeish]);
    if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to read the Git tree.'));
    const changedResult = runGit(repository.repoRoot, [
      'diff',
      '--name-only',
      '-z',
      '-M',
      base,
      sha,
      ...scopePathspec(repository),
    ]);
    if (changedResult.status !== 0) {
      throw new Error(errorMessage(changedResult, 'Unable to compare the current Git revision.'));
    }
    const changedPaths = new Set(
      changedResult.stdout
        .toString('utf8')
        .split('\0')
        .filter(Boolean)
        .map((filePath) => toWorkspacePath(repository, filePath))
        .filter((filePath): filePath is string => Boolean(filePath))
    );
    const changedPathList = [...changedPaths];
    const entries: ProjectGitTreeEntry[] = result.stdout
      .toString('utf8')
      .split('\0')
      .filter(Boolean)
      .map((line) => {
        const match = /^(\d+)\s+(blob|tree|commit)\s+([a-f0-9]+)\t(.+)$/u.exec(line);
        if (!match) return undefined;
        const [, mode, rawKind, objectId, name] = match;
        const entryPath = [relativePath, name].filter(Boolean).join('/');
        const changedInRevision = changedPathList.some(
          (changedPath) => changedPath === entryPath || changedPath.startsWith(`${entryPath}/`)
        );
        return {
          path: entryPath,
          name,
          kind:
            rawKind === 'tree'
              ? ('directory' as const)
              : rawKind === 'commit'
                ? ('submodule' as const)
                : ('file' as const),
          mode,
          objectId,
          changedInRevision,
        };
      })
      .filter((entry): entry is NonNullable<typeof entry> => Boolean(entry));
    const pathCommitSummaries = getPathCommitSummaries(
      repository,
      sha,
      relativePath,
      entries.map((entry) => entry.name)
    );
    entries.forEach((entry) => {
      entry.lastCommit = pathCommitSummaries.get(entry.name);
    });
    return {
      ok: true,
      repository,
      sha,
      path: relativePath,
      entries,
    };
  });

export const getProjectGitBlob = (request: ProjectGitBlobRequest): ProjectGitBlobResult =>
  withRepository<ProjectGitBlobResult>(request, { binary: false, truncated: false }, (repository) => {
    const sha = resolveCommit(repository.repoRoot, request.sha);
    const relativePath = normalizeRelativePath(request.path);
    if (!relativePath) throw new Error('A project-relative file path is required.');
    const scopedPath = [repository.workspacePrefix, relativePath].filter(Boolean).join('/');
    const sizeResult = runGit(repository.repoRoot, ['cat-file', '-s', `${sha}:${scopedPath}`]);
    const size = Number.parseInt(textOutput(sizeResult), 10);
    if (sizeResult.status !== 0 || !Number.isFinite(size))
      throw new Error(errorMessage(sizeResult, 'Git file not found.'));
    if (size > MAX_BINARY_BYTES) {
      return { ok: true, repository, sha, path: relativePath, size, binary: true, truncated: true };
    }
    const result = runGit(repository.repoRoot, ['show', `${sha}:${scopedPath}`], MAX_BINARY_BYTES + 1024);
    if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to read Git file.'));
    const binary = result.stdout.includes(0);
    if (binary) {
      return {
        ok: true,
        repository,
        sha,
        path: relativePath,
        size,
        binary: true,
        truncated: false,
        contentBase64: result.stdout.toString('base64'),
      };
    }
    const truncated = size > MAX_TEXT_BYTES;
    return {
      ok: true,
      repository,
      sha,
      path: relativePath,
      size,
      binary: false,
      truncated,
      content: result.stdout.subarray(0, MAX_TEXT_BYTES).toString('utf8'),
    };
  });

export const getProjectGitWorkingTree = (request: ProjectGitDiscoverRequest): ProjectGitWorkingTreeResult =>
  withRepository<ProjectGitWorkingTreeResult>(request, { files: [] }, (repository) => {
    const pathspec = scopePathspec(repository);
    const result = runGit(repository.repoRoot, ['status', '--porcelain=v1', '--untracked-files=normal', ...pathspec]);
    if (result.status !== 0) throw new Error(errorMessage(result, 'Unable to read working tree status.'));
    const files = parsePorcelainStatus(porcelainOutput(result)).map((file) =>
      Object.assign({}, file, {
        path: toWorkspacePath(repository, file.path) || file.path,
        oldPath: toWorkspacePath(repository, file.oldPath),
      })
    );
    return { ok: true, repository, files };
  });

export const getProjectGitWorkingDiff = (request: ProjectGitWorkingDiffRequest): ProjectGitWorkingDiffResult =>
  withRepository<ProjectGitWorkingDiffResult>(
    request,
    { content: '', truncated: false, binary: false },
    (repository) => {
      const relativePath = normalizeRelativePath(request.path);
      if (!relativePath) throw new Error('A project-relative file path is required.');
      const repoPath = [repository.workspacePrefix, relativePath].filter(Boolean).join('/');
      const contextLines = Math.max(0, Math.min(request.contextLines ?? 3, 20));
      const status = runGit(repository.repoRoot, [
        'status',
        '--porcelain=v1',
        '--untracked-files=normal',
        '--',
        repoPath,
      ]);
      if (status.status !== 0) throw new Error(errorMessage(status, 'Unable to inspect the working file.'));
      const untracked = porcelainOutput(status)
        .split(/\r?\n/u)
        .some((line) => line.startsWith('?? '));
      const result = untracked
        ? runGit(repository.repoRoot, [
            'diff',
            '--no-index',
            '--no-color',
            `--unified=${contextLines}`,
            process.platform === 'win32' ? 'NUL' : '/dev/null',
            path.join(repository.repoRoot, repoPath),
          ])
        : runGit(repository.repoRoot, [
            'diff',
            '--no-color',
            `--unified=${contextLines}`,
            repository.head ? 'HEAD' : '--cached',
            '--',
            repoPath,
          ]);
      if (result.status !== 0 && !(untracked && result.status === 1)) {
        throw new Error(errorMessage(result, 'Unable to read the working file diff.'));
      }
      const full = result.stdout.toString('utf8');
      const truncated = Buffer.byteLength(full, 'utf8') > MAX_TEXT_BYTES;
      return {
        ok: true,
        repository,
        path: relativePath,
        content: truncated ? Buffer.from(full).subarray(0, MAX_TEXT_BYTES).toString('utf8') : full,
        truncated,
        binary: /Binary files .* differ|GIT binary patch/u.test(full),
      };
    }
  );

const normalizeTrailerValue = (value?: string, maxLength = 180): string | undefined =>
  String(value || '')
    .replace(/[\r\n]+/gu, ' ')
    .trim()
    .slice(0, maxLength) || undefined;

const normalizeCheckpointMetrics = (metrics?: ProjectGitPerformanceMetric[]): ProjectGitPerformanceMetric[] => {
  const names = new Set<string>();
  return (metrics || [])
    .map((metric): ProjectGitPerformanceMetric | undefined => {
      const name = normalizeTrailerValue(metric?.name, 64);
      const value = metric?.value;
      if (!name || typeof value !== 'number' || !Number.isFinite(value) || names.has(name)) return undefined;
      names.add(name);
      const unit = normalizeTrailerValue(metric.unit, 24);
      const direction =
        metric.direction === 'maximize' || metric.direction === 'minimize' ? metric.direction : undefined;
      const normalized: ProjectGitPerformanceMetric = { name, value };
      if (unit) normalized.unit = unit;
      if (direction) normalized.direction = direction;
      return normalized;
    })
    .filter((metric): metric is ProjectGitPerformanceMetric => Boolean(metric))
    .slice(0, 12);
};

const normalizeMetricContext = (value?: ProjectGitMetricContext): ProjectGitMetricContext | undefined => {
  const contractId = normalizeTrailerValue(value?.contractId, 120);
  const evaluationId = normalizeTrailerValue(value?.evaluationId, 160);
  const baselineCommit = normalizeTrailerValue(value?.baselineCommit, 80);
  const requestedCodePath = normalizeTrailerValue(value?.evaluationCode?.path, 300);
  const evaluationCodePath =
    requestedCodePath &&
    !requestedCodePath.startsWith('/') &&
    !/^[a-z]:[\\/]/iu.test(requestedCodePath) &&
    !requestedCodePath.split(/[\\/]+/u).includes('..')
      ? requestedCodePath.replaceAll('\\', '/')
      : undefined;
  const evaluationRuntime = ['python', 'node', 'r', 'notebook'].includes(value?.evaluationCode?.runtime || '')
    ? value?.evaluationCode?.runtime
    : undefined;
  const evaluationEntrypoint = normalizeTrailerValue(value?.evaluationCode?.entrypoint, 160);
  const requestedSha256 = normalizeTrailerValue(value?.evaluationCode?.sha256, 64)?.toLowerCase();
  const evaluationSha256 = requestedSha256 && /^[a-f0-9]{64}$/u.test(requestedSha256) ? requestedSha256 : undefined;
  if (!contractId || !evaluationId) return undefined;
  return {
    contractId,
    evaluationId,
    ...(baselineCommit ? { baselineCommit } : {}),
    ...(evaluationCodePath
      ? {
          evaluationCode: {
            path: evaluationCodePath,
            ...(evaluationRuntime ? { runtime: evaluationRuntime } : {}),
            ...(evaluationEntrypoint ? { entrypoint: evaluationEntrypoint } : {}),
            ...(evaluationSha256 ? { sha256: evaluationSha256 } : {}),
          },
        }
      : {}),
  };
};

const normalizeCheckpointArtifactRef = (
  value?: ProjectGitCheckpointArtifactRef
): ProjectGitCheckpointArtifactRef | undefined => {
  const runId = normalizeTrailerValue(value?.runId, 120);
  const artifactId = normalizeTrailerValue(value?.artifactId, 120);
  const version = value?.version;
  const revision = normalizeTrailerValue(value?.revision, 120);
  if (!runId || !artifactId || !Number.isInteger(version) || (version || 0) < 1) return undefined;
  return { runId, artifactId, version: version!, ...(revision ? { revision } : {}) };
};

const normalizeCheckpointDirectionDecision = (
  repoRoot: string,
  value?: ProjectGitDirectionDecision
): ProjectGitDirectionDecision | undefined => {
  const decision = normalizeProjectGitDirectionDecision(value);
  if (!decision) return undefined;
  return {
    ...decision,
    basisRefs: decision.basisRefs.map((basis) => {
      if (basis.kind !== 'commit') return basis;
      try {
        return Object.assign({}, basis, { ref: resolveCommit(repoRoot, basis.ref) });
      } catch {
        throw new Error(`Direction decision references an unavailable Git commit: ${basis.ref}`);
      }
    }),
  };
};

const normalizeResearchStageReceipt = (
  value?: ProjectGitResearchStageReceipt
): ProjectGitResearchStageReceipt | undefined => {
  if (!value) return undefined;
  const stageId = normalizeTrailerValue(value.stageId, 120);
  const objective = normalizeTrailerValue(value.objective, 500);
  const disposition = value.disposition;
  const validDisposition = ['supported', 'refuted', 'exhausted', 'inconclusive', 'runtime_failed'].includes(
    disposition
  );
  const normalizeList = (items: string[] | undefined, maxItems = 36): string[] =>
    (items || [])
      .map((item) => normalizeTrailerValue(item, 160))
      .filter((item): item is string => Boolean(item))
      .slice(0, maxItems);
  const successCriteria = normalizeList(value.successCriteria, 20);
  const failureCriteria = normalizeList(value.failureCriteria, 20);
  const priorWorkRefs = normalizeList(value.priorWorkRefs);
  const supportingEvidenceIds = normalizeList(value.supportingEvidenceIds);
  const refutingEvidenceIds = normalizeList(value.refutingEvidenceIds);
  const exhaustionEvidenceIds = normalizeList(value.exhaustionEvidenceIds);
  const beliefDelta = normalizeTrailerValue(value.beliefDelta, 500);
  const reflection = normalizeTrailerValue(value.reflection, 800);
  const nextObjective = normalizeTrailerValue(value.nextObjective, 500);
  if (
    !stageId ||
    !objective ||
    !validDisposition ||
    !successCriteria.length ||
    !failureCriteria.length ||
    !beliefDelta ||
    !reflection
  ) {
    return undefined;
  }
  if (disposition === 'supported' && supportingEvidenceIds.length === 0) return undefined;
  if (disposition === 'refuted' && refutingEvidenceIds.length === 0) return undefined;
  if (disposition === 'exhausted' && exhaustionEvidenceIds.length === 0) return undefined;
  return {
    stageId,
    objective,
    successCriteria,
    failureCriteria,
    priorWorkRefs,
    disposition,
    supportingEvidenceIds,
    refutingEvidenceIds,
    ...(exhaustionEvidenceIds.length ? { exhaustionEvidenceIds } : {}),
    beliefDelta,
    reflection,
    ...(nextObjective ? { nextObjective } : {}),
  };
};

const normalizeSummaryCount = (value: number): number => (Number.isFinite(value) ? Math.max(0, Math.round(value)) : 0);

const normalizeTargetSummary = (value?: TargetDiscoveryProgressSummary): TargetDiscoveryProgressSummary | undefined => {
  if (!value) return undefined;
  const leadingCoverage =
    typeof value.leadingCoverage === 'number' && Number.isFinite(value.leadingCoverage)
      ? Math.max(0, Math.min(1, value.leadingCoverage))
      : undefined;
  return {
    candidateCount: normalizeSummaryCount(value.candidateCount),
    advanceCount: normalizeSummaryCount(value.advanceCount),
    validationCount: normalizeSummaryCount(value.validationCount),
    blockerCount: normalizeSummaryCount(value.blockerCount),
    sourceReadyCount: normalizeSummaryCount(value.sourceReadyCount),
    sourceCount: normalizeSummaryCount(value.sourceCount),
    branchCount: normalizeSummaryCount(value.branchCount),
    ...(leadingCoverage == null ? {} : { leadingCoverage }),
    topTargets: (value.topTargets || [])
      .map((item) => normalizeTrailerValue(item, 32))
      .filter((item): item is string => Boolean(item))
      .slice(0, 3),
  };
};

const checkpointCommitBody = (options: {
  stage: string;
  researchStrategy?: ResearchStrategy;
  routeNodeId?: string;
  repairsNodeId?: string;
  runId?: string;
  conversationId?: string;
  verification?: string[];
  metrics?: ProjectGitPerformanceMetric[];
  metricContext?: ProjectGitMetricContext;
  goalId?: string;
  domain?: ProjectGitDomain;
  artifactRef?: ProjectGitCheckpointArtifactRef;
  targetSummary?: TargetDiscoveryProgressSummary;
  researchStage?: ProjectGitResearchStageReceipt;
  directionDecision?: ProjectGitDirectionDecision;
}): string => {
  const directionDecision = normalizeProjectGitDirectionDecision(options.directionDecision);
  const readableDecision = directionDecision
    ? [
        `Decision: ${directionDecision.choice}`,
        `Reason: ${directionDecision.reason}`,
        `Basis: ${directionDecision.basisRefs
          .map((basis) => {
            const reference = basis.kind === 'commit' ? basis.ref.slice(0, 12) : basis.ref;
            return `${basis.kind}:${basis.label || reference}`;
          })
          .join(' · ')}`,
        ...(directionDecision.nextTest ? [`Next test: ${directionDecision.nextTest}`] : []),
        ...(directionDecision.stopIf ? [`Stop if: ${directionDecision.stopIf}`] : []),
        '',
      ]
    : [];
  const lines = [...readableDecision, 'DeepScientist-Checkpoint: true', `DeepScientist-Stage: ${options.stage}`];
  const researchStrategy = normalizeResearchStrategy(options.researchStrategy);
  if (researchStrategy) lines.push(`DeepScientist-Strategy: ${researchStrategy}`);
  const routeNodeId = normalizeTrailerValue(options.routeNodeId, 120);
  if (routeNodeId) lines.push(`DeepScientist-RouteNode: ${routeNodeId}`);
  const repairsNodeId = normalizeTrailerValue(options.repairsNodeId, 120);
  if (repairsNodeId) lines.push(`DeepScientist-RepairsNode: ${repairsNodeId}`);
  const runId = normalizeTrailerValue(options.runId, 120);
  const conversationId = normalizeTrailerValue(options.conversationId, 120);
  if (runId) lines.push(`DeepScientist-Run: ${runId}`);
  if (conversationId) lines.push(`DeepScientist-Conversation: ${conversationId}`);
  const goalId = normalizeTrailerValue(options.goalId, 120);
  if (goalId) lines.push(`DeepScientist-Goal: ${goalId}`);
  if (options.domain) lines.push(`DeepScientist-Domain: ${options.domain}`);
  const artifactRef = normalizeCheckpointArtifactRef(options.artifactRef);
  if (artifactRef) lines.push(`DeepScientist-Artifact: ${JSON.stringify(artifactRef)}`);
  const targetSummary = normalizeTargetSummary(options.targetSummary);
  if (targetSummary) lines.push(`DeepScientist-TargetSummary: ${JSON.stringify(targetSummary)}`);
  const researchStage = normalizeResearchStageReceipt(options.researchStage);
  if (researchStage) lines.push(`DeepScientist-ResearchStage: ${JSON.stringify(researchStage)}`);
  if (directionDecision) lines.push(`DeepScientist-Decision: ${JSON.stringify(directionDecision)}`);
  (options.verification || [])
    .map((item) => normalizeTrailerValue(item))
    .filter((item): item is string => Boolean(item))
    .slice(0, 20)
    .forEach((item) => lines.push(`DeepScientist-Verification: ${item}`));
  normalizeCheckpointMetrics(options.metrics).forEach((metric) => {
    const serialized = normalizeTrailerValue(JSON.stringify(metric), 260);
    if (serialized) lines.push(`DeepScientist-Metric: ${serialized}`);
  });
  const metricContext = normalizeMetricContext(options.metricContext);
  if (metricContext) lines.push(`DeepScientist-MetricContext: ${JSON.stringify(metricContext)}`);
  return lines.join('\n');
};

const normalizeCheckpointIncludePath = (value: string): string | undefined => {
  const relativePath = normalizeRelativePath(value);
  if (!relativePath) return undefined;
  if (relativePath.startsWith(':')) {
    throw new Error('Checkpoint includePaths must be literal project-relative paths, not Git pathspec expressions.');
  }
  return path.posix.normalize(relativePath).replace(/\/$/u, '') || '.';
};

const checkpointWorkspacePath = (repository: ProjectGitRepository, repoPath: string): string => {
  const normalized = normalizeRelativePath(repoPath);
  if (!normalized) throw new Error('Git returned an invalid empty checkpoint path.');
  if (!repository.workspacePrefix) return normalized;
  const prefix = `${repository.workspacePrefix}/`;
  if (!normalized.startsWith(prefix)) {
    throw new Error('Checkpoint paths include content outside the bound project workspace.');
  }
  return normalized.slice(prefix.length);
};

const checkpointPathIsIncluded = (workspacePath: string, includePaths: string[]): boolean =>
  includePaths.some(
    (includePath) => includePath === '.' || workspacePath === includePath || workspacePath.startsWith(`${includePath}/`)
  );

const validateCheckpointRepoPaths = (
  repository: ProjectGitRepository,
  includePaths: string[],
  repoPaths: string[]
): string[] =>
  repoPaths.map((repoPath) => {
    const workspacePath = checkpointWorkspacePath(repository, repoPath);
    if (!checkpointPathIsIncluded(workspacePath, includePaths)) {
      throw new Error('Checkpoint paths include content outside the requested includePaths.');
    }
    if (isSensitiveCheckpointPath(workspacePath)) {
      throw new Error('Checkpoint paths include a credential, cache, build output, or internal artifact directory.');
    }
    return workspacePath;
  });

const listCheckpointChangedRepoPaths = (
  repository: ProjectGitRepository,
  includePaths: string[]
): { repoPaths: string[]; workspacePaths: string[] } => {
  const requestedRepoPaths = includePaths.map(
    (item) => [repository.workspacePrefix, item === '.' ? undefined : item].filter(Boolean).join('/') || '.'
  );
  const tracked = runGit(repository.repoRoot, [
    '--literal-pathspecs',
    'diff',
    '--name-only',
    '--no-renames',
    '-z',
    '--',
    ...requestedRepoPaths,
  ]);
  if (tracked.status !== 0) throw new Error(errorMessage(tracked, 'Unable to inspect tracked checkpoint paths.'));
  const untracked = runGit(repository.repoRoot, [
    '--literal-pathspecs',
    'ls-files',
    '--others',
    '--exclude-standard',
    '-z',
    '--',
    ...requestedRepoPaths,
  ]);
  if (untracked.status !== 0) {
    throw new Error(errorMessage(untracked, 'Unable to inspect untracked checkpoint paths.'));
  }
  const repoPaths = Array.from(
    new Set([tracked, untracked].flatMap((result) => result.stdout.toString('utf8').split('\0').filter(Boolean)))
  );
  return {
    repoPaths,
    workspacePaths: validateCheckpointRepoPaths(repository, includePaths, repoPaths),
  };
};

const unstageCheckpointPaths = (repository: ProjectGitRepository, repoPaths: string[]): void => {
  if (!repoPaths.length) return;
  const hasHead = runGit(repository.repoRoot, ['rev-parse', '--verify', 'HEAD']).status === 0;
  runGit(
    repository.repoRoot,
    hasHead
      ? ['--literal-pathspecs', 'reset', '--quiet', 'HEAD', '--', ...repoPaths]
      : ['--literal-pathspecs', 'rm', '--cached', '-r', '--quiet', '--', ...repoPaths]
  );
};

export const createProjectGitCheckpoint = (request: ProjectGitCheckpointRequest): ProjectGitCheckpointResult => {
  const fallback: ProjectGitCheckpointResult = { ok: false, changedFiles: [] };
  try {
    let repository = discoverRepository(request.workspace);
    return withProjectGitRepositoryLock(repository.repoRoot, () => {
      repository = discoverRepository(request.workspace);
      if (repository.bare) throw new Error('Checkpoints cannot be created in a bare Git repository.');
      const message = String(request.message || '')
        .trim()
        .replace(/\s+/gu, ' ')
        .slice(0, 180);
      if (!message) throw new Error('A checkpoint message is required.');
      const includePaths = Array.from(
        new Set(
          (request.includePaths || [])
            .map((item) => normalizeCheckpointIncludePath(item))
            .filter((item): item is string => Boolean(item))
        )
      );
      if (!includePaths.length)
        throw new Error('Checkpoint includePaths must list at least one project-relative path.');
      if (includePaths.length > 200) throw new Error('A checkpoint cannot include more than 200 explicit paths.');
      if (includePaths.some((item) => item !== '.' && isSensitiveCheckpointPath(item))) {
        throw new Error('Checkpoint paths include a credential, cache, build output, or internal artifact directory.');
      }
      const stagedBefore = runGit(repository.repoRoot, ['diff', '--cached', '--name-only', '-z']);
      if (stagedBefore.status !== 0) throw new Error(errorMessage(stagedBefore, 'Unable to inspect the Git index.'));
      if (stagedBefore.stdout.length > 0) {
        throw new Error(
          'The Git index already contains staged changes. Commit or unstage them before creating a checkpoint.'
        );
      }
      const expanded = listCheckpointChangedRepoPaths(repository, includePaths);
      if (!expanded.repoPaths.length) throw new Error('Checkpoint paths do not contain any Git changes.');
      const stage =
        String(request.stage || 'checkpoint')
          .trim()
          .toLowerCase()
          .replace(/[^a-z0-9._-]+/gu, '-')
          .replace(/^-+|-+$/gu, '')
          .slice(0, 40) || 'checkpoint';
      if (normalizeResearchStrategy(stage)) {
        throw new Error('Checkpoint stage cannot use a reserved research strategy name. Set researchStrategy instead.');
      }
      const explicitResearchStrategy = normalizeResearchStrategy(request.researchStrategy);
      if (request.researchStrategy && !explicitResearchStrategy) throw new Error('Invalid research strategy.');
      // The structured field remains authoritative, while a canonical subject
      // prefix keeps hand-written and imported Git checkpoints interoperable.
      const researchStrategy = explicitResearchStrategy || parseResearchCommitSubject(message).researchStrategy;
      const routeNodeId = normalizeTrailerValue(request.routeNodeId, 120);
      const repairsNodeId = normalizeTrailerValue(request.repairsNodeId, 120);
      if ((researchStrategy === 'repair') !== Boolean(repairsNodeId)) {
        throw new Error('Repair checkpoints require repairsNodeId, and only repair checkpoints may set it.');
      }
      const subject = formatResearchCommitSubject({ message, stage, researchStrategy });
      const verification = (request.verification || [])
        .map((item) => normalizeTrailerValue(item))
        .filter((item): item is string => Boolean(item))
        .slice(0, 20);
      const metrics = normalizeCheckpointMetrics(request.metrics);
      const metricContext = metrics.length ? normalizeMetricContext(request.metricContext) : undefined;
      const goalId = normalizeTrailerValue(request.goalId, 120);
      const domain = request.domain && PROJECT_GIT_DOMAINS.has(request.domain) ? request.domain : undefined;
      const artifactRef = normalizeCheckpointArtifactRef(request.artifactRef);
      const targetSummary = domain === 'target_discovery' ? normalizeTargetSummary(request.targetSummary) : undefined;
      const researchStage = normalizeResearchStageReceipt(request.researchStage);
      if (request.researchStage && !researchStage) {
        throw new Error(
          'The researchStage receipt is invalid. It requires stageId, objective, non-empty successCriteria and failureCriteria, disposition, beliefDelta, reflection, and disposition-appropriate supporting, refuting, or exhaustion evidence ids.'
        );
      }
      const directionDecision = normalizeCheckpointDirectionDecision(repository.repoRoot, request.directionDecision);
      if (request.directionDecision && !directionDecision) {
        throw new Error(
          'The directionDecision is invalid. It requires schema=deepscientist.direction.v1, a valid choice, a concise reason, and at least one evidence, artifact, or commit basis reference.'
        );
      }
      let stagedByCheckpoint = false;
      let stagedPaths: string[] = [];
      try {
        const add = runGit(repository.repoRoot, ['--literal-pathspecs', 'add', '--', ...expanded.repoPaths]);
        if (add.status !== 0) throw new Error(errorMessage(add, 'Unable to stage checkpoint paths.'));
        stagedByCheckpoint = true;
        const staged = runGit(repository.repoRoot, ['diff', '--cached', '--name-only', '--no-renames', '-z']);
        if (staged.status !== 0) throw new Error(errorMessage(staged, 'Unable to verify staged checkpoint paths.'));
        stagedPaths = staged.stdout.toString('utf8').split('\0').filter(Boolean);
        if (!stagedPaths.length) throw new Error('Checkpoint paths did not produce a staged change.');
        validateCheckpointRepoPaths(repository, includePaths, stagedPaths);
        const allowedRepoPaths = new Set(expanded.repoPaths);
        if (stagedPaths.some((item) => !allowedRepoPaths.has(item))) {
          throw new Error('The Git index changed while the checkpoint was being prepared. Retry with a clean index.');
        }
        const commitResult = runGit(repository.repoRoot, [
          '--literal-pathspecs',
          '-c',
          'user.name=DeepScientist',
          '-c',
          'user.email=checkpoint@deepscientist.local',
          'commit',
          '--only',
          '-m',
          subject,
          '-m',
          checkpointCommitBody({
            stage,
            researchStrategy,
            routeNodeId,
            repairsNodeId,
            runId: request.runId,
            conversationId: request.conversationId,
            verification,
            metrics,
            metricContext,
            goalId,
            domain,
            artifactRef,
            targetSummary,
            researchStage,
            directionDecision,
          }),
          '--',
          ...expanded.repoPaths,
        ]);
        if (commitResult.status !== 0) {
          throw new Error(errorMessage(commitResult, 'Git rejected the checkpoint commit.'));
        }
        stagedByCheckpoint = false;
      } catch (error) {
        if (stagedByCheckpoint) unstageCheckpointPaths(repository, expanded.repoPaths);
        throw error;
      }
      const commit = resolveCommit(repository.repoRoot, 'HEAD');
      const response: ProjectGitCheckpointResult = {
        ok: true,
        repository: discoverRepository(request.workspace),
        commit,
        shortCommit: commit.slice(0, 7),
        subject,
        changedFiles: stagedPaths.map((item) => checkpointWorkspacePath(repository, item)),
        stage,
        ...(researchStrategy ? { researchStrategy } : {}),
        ...(routeNodeId ? { routeNodeId } : {}),
        ...(repairsNodeId ? { repairsNodeId } : {}),
        verification,
        ...(metrics.length ? { metrics } : {}),
        ...(metricContext ? { metricContext } : {}),
        ...(goalId ? { goalId } : {}),
        ...(domain ? { domain } : {}),
        ...(artifactRef ? { artifactRef } : {}),
        ...(targetSummary ? { targetSummary } : {}),
        ...(researchStage ? { researchStage } : {}),
        ...(directionDecision ? { directionDecision } : {}),
      };
      notifyProjectGitChanged({
        workspace: request.workspace,
        repoRoot: repository.repoRoot,
        reason: 'checkpoint-created',
        branch: repository.branch,
        head: commit,
      });
      return response;
    });
  } catch (error) {
    return {
      ...fallback,
      error: error instanceof Error ? error.message : String(error),
    };
  }
};

const PROJECT_MANIFEST_RELATIVE_PATH = '.deepscientist/project.json';
const DEEPSCIENTIST_GITIGNORE_RELATIVE_PATH = '.deepscientist/.gitignore';
const DEEPSCIENTIST_GITIGNORE_RULES = ['/artifact-repo/', '/science-artifacts/', '/exports/'];
const LOCAL_PROJECT_EXCLUDES = [
  ...LOCAL_AGENT_RUNTIME_EXCLUDE_RULES.map((entry) => entry.slice(1)),
  '.deepscientist/artifact-repo/',
  '.deepscientist/science-artifacts/',
  '.deepscientist/exports/',
  '.deepscientist/factor-search/',
];

const ensureDeepScientistGitignore = (workspace: string): void => {
  const gitignorePath = path.join(workspace, ...DEEPSCIENTIST_GITIGNORE_RELATIVE_PATH.split('/'));
  fs.mkdirSync(path.dirname(gitignorePath), { recursive: true });
  const current = fs.existsSync(gitignorePath) ? fs.readFileSync(gitignorePath, 'utf8') : '';
  const lines = current.split(/\r?\n/u).filter(Boolean);
  const existing = new Set(lines);
  const missing = DEEPSCIENTIST_GITIGNORE_RULES.filter((entry) => !existing.has(entry));
  if (!missing.length && current.endsWith('\n')) return;
  fs.writeFileSync(gitignorePath, `${[...lines, ...missing].join('\n')}\n`, 'utf8');
};

const readProjectManifest = (workspace: string): unknown => {
  const manifestPath = path.join(workspace, ...PROJECT_MANIFEST_RELATIVE_PATH.split('/'));
  if (!fs.existsSync(manifestPath)) return undefined;
  try {
    return JSON.parse(fs.readFileSync(manifestPath, 'utf8')) as unknown;
  } catch {
    return undefined;
  }
};

const readProjectId = (workspace: string): string | undefined => {
  const manifest = readProjectManifest(workspace);
  if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) return undefined;
  const record = manifest as Record<string, unknown>;
  const value = typeof record.projectId === 'string' ? record.projectId : record.id;
  return typeof value === 'string' && value.trim() ? value.trim() : undefined;
};

const readOrCreateRepositoryProjectId = (repoRoot: string): string => {
  const projectIdPath = path.join(gitCommonDir(repoRoot), 'deepscientist', 'project-id');
  if (fs.existsSync(projectIdPath)) {
    const value = fs.readFileSync(projectIdPath, 'utf8').trim();
    if (value && value.length <= 120 && !value.includes('\0')) return value;
  }
  const projectId = createProjectId();
  fs.mkdirSync(path.dirname(projectIdPath), { recursive: true });
  try {
    fs.writeFileSync(projectIdPath, `${projectId}\n`, { encoding: 'utf8', mode: 0o600, flag: 'wx' });
    return projectId;
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
    const existing = fs.readFileSync(projectIdPath, 'utf8').trim();
    if (existing && existing.length <= 120 && !existing.includes('\0')) return existing;
    throw new Error('The repository contains an invalid DeepScientist project id.', { cause: error });
  }
};

const resolveProjectId = (workspace: string, repoRoot: string, workspacePrefix?: string): string =>
  readProjectId(workspace) ||
  readProjectId(repoRoot) ||
  (workspacePrefix
    ? `osp_${crypto
        .createHash('sha256')
        .update(`${gitCommonDir(repoRoot)}\0${workspacePrefix}`)
        .digest('hex')
        .slice(0, 16)}`
    : readOrCreateRepositoryProjectId(repoRoot));

const writeProjectManifest = (
  workspace: string,
  options: { goal: string; managed: boolean; projectId?: string; createdAt?: number }
): string => {
  const manifestPath = path.join(workspace, ...PROJECT_MANIFEST_RELATIVE_PATH.split('/'));
  fs.mkdirSync(path.dirname(manifestPath), { recursive: true });
  const { manifest, projectId } = mergeProjectManifest(readProjectManifest(workspace), {
    projectId: options.projectId,
    name: options.goal.slice(0, 120),
    goal: options.goal,
    managed: options.managed,
    createdAt: options.createdAt,
    updatedAt: Date.now(),
  });
  const temporaryPath = `${manifestPath}.${process.pid}.${Date.now()}.tmp`;
  fs.writeFileSync(temporaryPath, `${JSON.stringify(manifest, null, 2)}\n`, { encoding: 'utf8', mode: 0o600 });
  fs.renameSync(temporaryPath, manifestPath);
  ensureDeepScientistGitignore(workspace);
  return projectId;
};

const addLocalProjectExcludes = (workspace: string): void => {
  const gitDirResult = runGit(workspace, ['rev-parse', '--git-dir']);
  if (gitDirResult.status !== 0) throw new Error(errorMessage(gitDirResult, 'Unable to locate Git metadata.'));
  const rawGitDir = textOutput(gitDirResult);
  const gitDir = path.isAbsolute(rawGitDir) ? rawGitDir : path.resolve(workspace, rawGitDir);
  const excludePath = path.join(gitDir, 'info', 'exclude');
  fs.mkdirSync(path.dirname(excludePath), { recursive: true });
  const existing = fs.existsSync(excludePath) ? fs.readFileSync(excludePath, 'utf8') : '';
  const lines = new Set(
    existing
      .split(/\r?\n/u)
      .map((line) => line.trim())
      .filter(Boolean)
  );
  const missing = LOCAL_PROJECT_EXCLUDES.filter((entry) => !lines.has(entry));
  if (!missing.length) return;
  const separator = existing && !existing.endsWith('\n') ? '\n' : '';
  fs.appendFileSync(excludePath, `${separator}${missing.join('\n')}\n`, 'utf8');
};

const createSelectedProjectBaseline = (options: {
  workspace: string;
  goal: string;
  conversationId: string;
}): { projectId: string; commit: string } => {
  const projectId = writeProjectManifest(options.workspace, { goal: options.goal, managed: false });
  addLocalProjectExcludes(options.workspace);
  const baselinePaths = [DEEPSCIENTIST_GITIGNORE_RELATIVE_PATH, PROJECT_MANIFEST_RELATIVE_PATH];
  const add = runGit(options.workspace, ['add', '--', ...baselinePaths]);
  if (add.status !== 0) throw new Error(errorMessage(add, 'Unable to stage the DeepScientist project manifest.'));
  const commit = runGit(options.workspace, [
    '-c',
    'user.name=DeepScientist',
    '-c',
    'user.email=checkpoint@deepscientist.local',
    'commit',
    '-m',
    '[project] initialize project history',
    '-m',
    checkpointCommitBody({ stage: 'project', conversationId: options.conversationId }),
  ]);
  if (commit.status !== 0) {
    runGit(options.workspace, ['rm', '--cached', '--quiet', '--', ...baselinePaths]);
    throw new Error(errorMessage(commit, 'Unable to create the project history baseline.'));
  }
  return { projectId, commit: resolveCommit(options.workspace, 'HEAD') };
};

export const prepareManagedProject = (request: ProjectGitPrepareManagedRequest): ProjectGitPrepareManagedResult => {
  try {
    const baseDir = String(request.baseDir || '').trim();
    const goal = String(request.goal || '').trim();
    if (!baseDir) throw new Error('A managed project base directory is required.');
    if (!goal) throw new Error('A goal is required to create a managed project.');
    fs.mkdirSync(baseDir, { recursive: true });
    const resolvedBase = fs.realpathSync(baseDir);
    return withProjectGitPathLock(resolvedBase, () => {
      const managedRoot = path.join(resolvedBase, 'managed-projects');
      fs.mkdirSync(managedRoot, { recursive: true });
      const createdAt = new Date();
      const projectId = `project_${createdAt.toISOString().slice(0, 10).replace(/-/gu, '')}_${crypto.randomBytes(4).toString('hex')}`;
      const workspace = path.join(managedRoot, projectId);
      fs.mkdirSync(workspace, { recursive: true });
      writeProjectManifest(workspace, { projectId, goal, managed: true, createdAt: createdAt.getTime() });
      fs.writeFileSync(
        path.join(workspace, '.gitignore'),
        [
          '.DS_Store',
          '.deepscientist/artifact-repo/',
          '.deepscientist/science-artifacts/',
          '.deepscientist/factor-search/',
          '.agents/skills/',
          '.codex/skills/',
          'node_modules/',
          'out/',
          'dist/',
          'build/',
          'coverage/',
          '.cache/',
          '__pycache__/',
          '.pytest_cache/',
          '*.log',
          '.env',
          '.env.*',
          '*.pem',
          '*.key',
          '',
        ].join('\n'),
        'utf8'
      );
      fs.writeFileSync(path.join(workspace, 'README.md'), `# DeepScientist Project\n\n## Goal\n\n${goal}\n`, 'utf8');
      initializeMainRepository(workspace);
      addLocalProjectExcludes(workspace);
      runGit(workspace, ['config', 'user.name', 'DeepScientist']);
      runGit(workspace, ['config', 'user.email', 'checkpoint@deepscientist.local']);
      const add = runGit(workspace, [
        'add',
        '--',
        '.gitignore',
        'README.md',
        DEEPSCIENTIST_GITIGNORE_RELATIVE_PATH,
        PROJECT_MANIFEST_RELATIVE_PATH,
      ]);
      if (add.status !== 0) throw new Error(errorMessage(add, 'Unable to stage the managed project manifest.'));
      const commit = runGit(workspace, [
        'commit',
        '-m',
        '[project] initialize managed project',
        '-m',
        checkpointCommitBody({ stage: 'project' }),
      ]);
      if (commit.status !== 0) throw new Error(errorMessage(commit, 'Unable to create the managed project baseline.'));
      return { ok: true, workspace, projectId, created: true };
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const prepareManagedGoalProject = prepareManagedProject;

/**
 * Clone a user-approved remote into a fresh local workspace. This is kept
 * separate from prepareProjectWorkspace so local imports never unexpectedly
 * contact a remote and clones never mutate an existing checkout.
 */
export const cloneProjectGit = (request: ProjectGitCloneRequest): ProjectGitCloneResult => {
  let destination: string | undefined;
  let createdDestination = false;
  try {
    const remoteUrl = validateCloneRemote(request.remoteUrl);
    const baseDir = String(request.baseDir || '').trim();
    const requestedDestination = String(request.destination || '').trim();
    if (!requestedDestination && !baseDir) {
      throw new Error('Choose a destination folder before cloning a Git project.');
    }
    if (requestedDestination && baseDir) {
      throw new Error('Specify either destination or baseDir, not both.');
    }
    if (requestedDestination) {
      destination = path.resolve(requestedDestination);
    } else {
      const parent = fs.realpathSync(baseDir);
      if (!fs.statSync(parent).isDirectory()) throw new Error('The clone destination must be a directory.');
      destination = path.join(parent, cloneDirectoryName(remoteUrl));
    }
    if (!destination || destination === path.parse(destination).root) {
      throw new Error('The clone destination is not a usable project folder.');
    }
    return withProjectGitPathLock(path.dirname(destination), () => {
      if (fs.existsSync(destination)) {
        const entries = fs.readdirSync(destination);
        if (entries.length > 0) throw new Error('The clone destination already exists and is not empty.');
      } else {
        fs.mkdirSync(path.dirname(destination), { recursive: true });
        createdDestination = true;
      }

      const args = ['clone', '--origin', 'origin'];
      const depth = request.depth == null ? undefined : Math.max(1, Math.min(10_000, Math.floor(request.depth)));
      if (depth) args.push('--depth', String(depth));
      if (request.ref) args.push('--branch', validateRef(request.ref));
      args.push(remoteUrl, destination);
      const clone = runStandaloneGit(args, undefined, 15 * 60_000);
      if (clone.status !== 0) {
        if (createdDestination) fs.rmSync(destination, { recursive: true, force: true });
        throw new Error(errorMessage(clone, 'The Git repository could not be cloned.'));
      }

      const workspace = fs.realpathSync(destination);
      const repository = discoverRepository(workspace);
      const projectId = resolveProjectId(workspace, repository.repoRoot, repository.workspacePrefix);
      const safeRemote = redactedCloneRemote(remoteUrl);
      const binding: ProjectGitWorkspaceBinding = {
        schema: 'deepscientist.project_git.v1',
        strategy: 'cloned',
        projectId,
        sourceRoot: workspace,
        workspaceRoot: workspace,
        branch: repository.branch,
        baseCommit: repository.head,
        sourceDirty: repository.dirty,
        remoteUrl: safeRemote,
        remoteRef: request.ref,
        trustState: 'unreviewed',
      };
      notifyProjectGitChanged({
        workspace,
        repoRoot: repository.repoRoot,
        reason: 'cloned',
        branch: repository.branch,
        head: repository.head,
      });
      return {
        ok: true,
        workspace,
        projectId,
        created: true,
        repository,
        binding,
        remoteUrl: safeRemote,
        remoteRef: request.ref,
      };
    });
  } catch (error) {
    return {
      ok: false,
      error: error instanceof Error ? error.message : String(error),
    };
  }
};

const safeWorkspaceId = (value: string): string =>
  String(value || '')
    .toLowerCase()
    .replace(/[^a-z0-9_-]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 56) || crypto.randomBytes(8).toString('hex');

export const prepareProjectWorkspace = (
  request: ProjectGitPrepareWorkspaceRequest
): ProjectGitPrepareWorkspaceResult => {
  try {
    const baseDir = String(request.baseDir || '').trim();
    const goal = String(request.goal || '').trim();
    const conversationId = safeWorkspaceId(request.conversationId);
    if (!baseDir) throw new Error('A DeepScientist data directory is required.');
    if (!goal) throw new Error('A goal is required to prepare the project workspace.');

    if (request.strategy === 'managed') {
      const managed = prepareManagedProject({ baseDir, goal });
      if (!managed.ok || !managed.workspace) return managed;
      const initialRepository = discoverRepository(managed.workspace);
      const amend = withProjectGitRepositoryLock(initialRepository.repoRoot, () =>
        runGit(managed.workspace, [
          '-c',
          'user.name=DeepScientist',
          '-c',
          'user.email=checkpoint@deepscientist.local',
          'commit',
          '--amend',
          '-m',
          '[project] initialize managed project',
          '-m',
          checkpointCommitBody({ stage: 'project', conversationId: request.conversationId }),
        ])
      );
      if (amend.status !== 0) {
        throw new Error(errorMessage(amend, 'Unable to bind the managed project baseline to the conversation.'));
      }
      const repository = discoverRepository(managed.workspace);
      return {
        ...managed,
        binding: {
          schema: 'deepscientist.project_git.v1',
          strategy: 'managed',
          projectId: managed.projectId,
          sourceRoot: managed.workspace,
          workspaceRoot: managed.workspace,
          branch: repository.branch,
          baseCommit: repository.head,
          sourceDirty: false,
        },
      };
    }

    if (!request.sourceWorkspace) throw new Error('A source workspace is required for this project strategy.');
    const sourceWorkspace = resolveWorkspace(request.sourceWorkspace);
    const preflight = inspectProjectGitWorkspace({ workspace: sourceWorkspace });
    if (!preflight.ok) throw new Error(preflight.error || 'Unable to inspect the selected project.');

    if (request.strategy === 'current-worktree') {
      let initializedProject: { projectId: string; commit: string } | undefined;
      if (preflight.kind === 'non-git') {
        initializedProject = withProjectGitPathLock(sourceWorkspace, () => {
          initializeMainRepository(sourceWorkspace);
          const repository = discoverRepository(sourceWorkspace);
          return withProjectGitRepositoryLock(repository.repoRoot, () =>
            createSelectedProjectBaseline({
              workspace: sourceWorkspace,
              goal,
              conversationId: request.conversationId,
            })
          );
        });
      }
      const repository = discoverRepository(sourceWorkspace);
      const projectId =
        initializedProject?.projectId ||
        resolveProjectId(sourceWorkspace, repository.repoRoot, repository.workspacePrefix);
      return {
        ok: true,
        workspace: sourceWorkspace,
        projectId,
        created: preflight.kind === 'non-git',
        binding: {
          schema: 'deepscientist.project_git.v1',
          strategy: 'current-worktree',
          projectId,
          sourceRoot: sourceWorkspace,
          workspaceRoot: sourceWorkspace,
          branch: repository.branch,
          baseCommit: repository.head,
          sourceDirty: repository.dirty,
        },
      };
    }

    const repository = preflight.repository;
    if (!repository || !repository.head || repository.bare) {
      throw new Error(
        'The selected Git project needs a non-bare baseline commit before an isolated workspace can be created.'
      );
    }
    assertRepositoryRootWriteScope(repository, 'Creating an isolated project worktree');
    fs.mkdirSync(baseDir, { recursive: true });
    const resolvedBase = fs.realpathSync(baseDir);
    const repoId = crypto.createHash('sha256').update(repository.repoRoot).digest('hex').slice(0, 12);
    const worktreeParent = path.join(resolvedBase, 'project-worktrees', repoId);
    const worktreeRoot = path.join(worktreeParent, conversationId);
    fs.mkdirSync(worktreeParent, { recursive: true });
    if (fs.existsSync(worktreeRoot)) throw new Error('The isolated project workspace already exists.');
    const branchNamespace = request.branchKind === 'conversation-fork' ? 'fork' : 'discovery';
    const branch = `deepscientist/${branchNamespace}/${conversationId}`;
    const add = withProjectGitRepositoryLock(repository.repoRoot, () =>
      runGit(repository.repoRoot, ['worktree', 'add', '-b', branch, worktreeRoot, repository.head])
    );
    if (add.status !== 0) throw new Error(errorMessage(add, 'Unable to create the isolated research workspace.'));
    const workspace = repository.workspacePrefix ? path.join(worktreeRoot, repository.workspacePrefix) : worktreeRoot;
    if (!fs.existsSync(workspace))
      throw new Error('The selected project subdirectory is missing from the new worktree.');
    const projectId =
      readProjectId(workspace) ||
      readProjectId(worktreeRoot) ||
      resolveProjectId(repository.repoRoot, repository.repoRoot);
    return {
      ok: true,
      workspace,
      projectId,
      created: true,
      binding: {
        schema: 'deepscientist.project_git.v1',
        strategy: 'isolated-worktree',
        projectId,
        sourceRoot: sourceWorkspace,
        workspaceRoot: workspace,
        branch,
        baseCommit: repository.head,
        sourceDirty: repository.dirty,
      },
    };
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const prepareGoalProjectWorkspace = prepareProjectWorkspace;

export const bindManagedProjectConversation = (
  request: ProjectGitBindConversationRequest
): ProjectGitBindConversationResult =>
  withRepository<ProjectGitBindConversationResult>(request, {}, (discoveredRepository) =>
    withProjectGitRepositoryLock(discoveredRepository.repoRoot, () => {
      const repository = discoverRepository(request.workspace);
      assertRepositoryRootWriteScope(repository, 'Binding a managed project baseline');
      if (!repository.head) throw new Error('The managed project has no baseline commit.');
      const summary = getCommitSummary(repository.repoRoot, repository.head);
      if (summary.checkpoint?.stage !== 'project') {
        throw new Error('The managed project baseline is not a DeepScientist project checkpoint.');
      }
      if (summary.checkpoint.conversationId === request.conversationId) {
        return { ok: true, repository, commit: summary.sha, shortCommit: summary.shortSha };
      }
      const amend = runGit(repository.repoRoot, [
        '-c',
        'user.name=DeepScientist',
        '-c',
        'user.email=checkpoint@deepscientist.local',
        'commit',
        '--amend',
        '-m',
        summary.subject,
        '-m',
        checkpointCommitBody({
          stage: summary.checkpoint.stage,
          runId: summary.checkpoint.runId,
          conversationId: request.conversationId,
          verification: summary.checkpoint.verification,
          metrics: summary.checkpoint.metrics,
        }),
      ]);
      if (amend.status !== 0)
        throw new Error(errorMessage(amend, 'Unable to bind the managed baseline to the conversation.'));
      const commit = resolveCommit(repository.repoRoot, 'HEAD');
      return {
        ok: true,
        repository: discoverRepository(request.workspace),
        commit,
        shortCommit: commit.slice(0, 7),
      };
    })
  );

export type ProjectWorkspaceDeletionPlan = {
  kind: ProjectWorkspaceDeletionKind;
  targetPath: string;
  worktreesRoot?: string;
  sourceRepositoryRoot?: string;
  branch?: string;
};

export type ProjectWorkspaceDeletionPlanRequest = ProjectWorkspaceDeletionRequest & {
  workspace: string;
  binding?: ProjectGitWorkspaceBinding;
  temporary?: boolean;
};

export type ProjectWorkspaceDeletionPlanResult = {
  ok: boolean;
  plan?: ProjectWorkspaceDeletionPlan;
  error?: string;
};

const isDirectChild = (parent: string, candidate: string): boolean => path.dirname(candidate) === parent;

const isNestedTwoLevelsBelow = (parent: string, candidate: string): boolean => {
  const relative = path.relative(parent, candidate);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) return false;
  return relative.split(path.sep).length === 2;
};

const deletionConversationIds = (request: ProjectWorkspaceDeletionPlanRequest): Set<string> =>
  new Set([request.conversationId, ...(request.deletingConversationIds ?? [])]);

const assertManagedProjectOwnership = (
  request: ProjectWorkspaceDeletionPlanRequest,
  workspace: string,
  managedRoot: string
): void => {
  if (!isDirectChild(managedRoot, workspace)) {
    throw new Error('Only a direct child of the DeepScientist managed-projects directory can be deleted.');
  }
  const manifest = readProjectManifest(workspace);
  if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) {
    throw new Error('The managed project manifest is missing or invalid.');
  }
  const record = manifest as Record<string, unknown>;
  if (record.schema !== 'deepscientist.project.v1' || record.managed !== true) {
    throw new Error('The workspace is not marked as a DeepScientist-managed project.');
  }
  const manifestProjectId = typeof record.projectId === 'string' ? record.projectId : record.id;
  if (request.binding?.projectId && manifestProjectId !== request.binding.projectId) {
    throw new Error('The managed project id does not match the conversation binding.');
  }
  const repository = discoverRepository(workspace);
  if (repository.repoRoot !== workspace || !repository.head) {
    throw new Error('The managed project repository root could not be verified.');
  }
  const rootsResult = runGit(repository.repoRoot, ['rev-list', '--max-parents=0', 'HEAD']);
  if (rootsResult.status !== 0) {
    throw new Error(errorMessage(rootsResult, 'Unable to verify the managed project baseline.'));
  }
  const rootCommits = rootsResult.stdout
    .toString('utf8')
    .split(/\r?\n/u)
    .map((value) => value.trim())
    .filter(Boolean);
  if (rootCommits.length !== 1) {
    throw new Error('The managed project must have exactly one baseline commit.');
  }
  const summary = getCommitSummary(repository.repoRoot, rootCommits[0]);
  if (
    summary.checkpoint?.stage !== 'project' ||
    !summary.checkpoint.conversationId ||
    !deletionConversationIds(request).has(summary.checkpoint.conversationId)
  ) {
    throw new Error('The managed project is not owned by this conversation.');
  }
};

const planIsolatedWorktreeDeletion = (
  request: ProjectWorkspaceDeletionPlanRequest,
  workspace: string,
  worktreesRoot: string
): ProjectWorkspaceDeletionPlan => {
  const binding = request.binding;
  if (!binding || binding.strategy !== 'isolated-worktree') {
    throw new Error('The conversation does not contain an isolated-worktree binding.');
  }
  const repository = discoverRepository(workspace);
  if (!isNestedTwoLevelsBelow(worktreesRoot, repository.repoRoot)) {
    throw new Error('The worktree is outside the DeepScientist project-worktrees directory.');
  }
  const workspaceId = Array.from(deletionConversationIds(request))
    .map((conversationId) => safeWorkspaceId(conversationId))
    .find((candidate) => path.basename(repository.repoRoot) === candidate);
  if (!workspaceId) {
    throw new Error('The worktree directory is not owned by this conversation.');
  }
  const branch = binding.branch;
  if (
    !branch ||
    ![`deepscientist/discovery/${workspaceId}`, `deepscientist/fork/${workspaceId}`].includes(branch) ||
    repository.branch !== branch
  ) {
    throw new Error('The worktree branch does not match the conversation binding.');
  }
  const sourceRepository = discoverRepository(binding.sourceRoot);
  if (gitCommonDir(sourceRepository.repoRoot) !== gitCommonDir(repository.repoRoot)) {
    throw new Error('The worktree and source repository do not share Git metadata.');
  }
  return {
    kind: 'isolated-worktree',
    targetPath: repository.repoRoot,
    worktreesRoot,
    sourceRepositoryRoot: sourceRepository.repoRoot,
    branch,
  };
};

export const planProjectWorkspaceDeletion = (
  request: ProjectWorkspaceDeletionPlanRequest & { baseDir: string }
): ProjectWorkspaceDeletionPlanResult => {
  try {
    const baseDir = fs.realpathSync(request.baseDir);
    const workspace = resolveWorkspace(request.workspace);
    const managedRoot = path.join(baseDir, 'managed-projects');
    const worktreesRoot = path.join(baseDir, 'project-worktrees');
    const temporaryRoot = path.join(baseDir, 'conversations');

    if (request.binding?.strategy === 'managed') {
      const resolvedManagedRoot = fs.realpathSync(managedRoot);
      assertManagedProjectOwnership(request, workspace, resolvedManagedRoot);
      return { ok: true, plan: { kind: 'managed', targetPath: workspace } };
    }

    if (request.binding?.strategy === 'isolated-worktree') {
      const resolvedWorktreesRoot = fs.realpathSync(worktreesRoot);
      return { ok: true, plan: planIsolatedWorktreeDeletion(request, workspace, resolvedWorktreesRoot) };
    }

    if (request.temporary === true) {
      const resolvedTemporaryRoot = fs.realpathSync(temporaryRoot);
      if (
        !isDirectChild(resolvedTemporaryRoot, workspace) ||
        !/^[a-z0-9_-]+-temp-[a-f0-9]{8}$/iu.test(path.basename(workspace))
      ) {
        throw new Error('The temporary workspace is not owned by DeepScientist.');
      }
      return { ok: true, plan: { kind: 'temporary', targetPath: workspace } };
    }

    throw new Error('User-selected project directories cannot be deleted with a conversation.');
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};

export const finalizeProjectWorkspaceDeletion = (
  plan: ProjectWorkspaceDeletionPlan
): { ok: boolean; error?: string } => {
  try {
    if (plan.kind !== 'isolated-worktree') return { ok: true };
    if (!plan.sourceRepositoryRoot || !plan.branch || !plan.worktreesRoot) {
      throw new Error('The isolated-worktree deletion plan is incomplete.');
    }
    return withProjectGitRepositoryLock(plan.sourceRepositoryRoot, () => {
      const prune = runGit(plan.sourceRepositoryRoot, ['worktree', 'prune', '--expire', 'now']);
      if (prune.status !== 0) throw new Error(errorMessage(prune, 'Unable to prune the deleted Git worktree.'));
      const branchExists = runGit(plan.sourceRepositoryRoot, [
        'show-ref',
        '--verify',
        '--quiet',
        `refs/heads/${plan.branch}`,
      ]);
      if (branchExists.status === 0) {
        const removeBranch = runGit(plan.sourceRepositoryRoot, ['branch', '-D', plan.branch]);
        if (removeBranch.status !== 0) {
          throw new Error(errorMessage(removeBranch, 'Unable to delete the isolated Git branch.'));
        }
      }
      const parent = path.dirname(plan.targetPath);
      if (isDirectChild(plan.worktreesRoot, parent) && fs.existsSync(parent) && fs.readdirSync(parent).length === 0) {
        fs.rmdirSync(parent);
      }
      return { ok: true };
    });
  } catch (error) {
    return { ok: false, error: error instanceof Error ? error.message : String(error) };
  }
};
