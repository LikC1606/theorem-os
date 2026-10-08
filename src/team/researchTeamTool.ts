/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { createMathToolTiming } from "../math/mathDiagnostics";
import { lockIsFresh, lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";
import crypto from 'node:crypto';
import { readMathRunSecondProofOwner } from "../math/mathRunInputs";
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { assertMathCanonicalPath, isMathPathWithin } from "../math/mathRunBinding";
import {
  readTrustedMathResearchEvidence,
  signMathResearchObservation,
} from "../math/mathResearchEvidence";
import { readTrustedMathRouteRefutation } from "../math/mathRouteRefutation";
import { recordMathSearchEvidence } from "../math/mathResearchWorkflow";
import type { MathEvidencePacket } from "../math/mathSearchState";
import { canonicalMathJson, mathDigest } from "../math/mathRuntimeIo";
import {
  classifyMathResearchFindingProgress,
  hasMathResearchProgressSignal,
  isMathResearchMainlineProgress,
  type MathResearchFindingProgressClass,
} from "./mathResearchFindingProgress";
import {
  MATH_PROOF_STAGES,
  MATH_WORKFLOW_STAGES,
  MATH_RESEARCH_PROBE_KINDS,
  applyMathResearchFinding,
  researchProbeKindForFinding,
  assertMathLessonsApplied,
  canonicalMathProblemStatementPayloads,
  classifyMathLeanFailure,
  classifyMathProgress,
  evaluateMathWorkflowPreflight,
  normalizeMathHelperReceipt,
  normalizeMathLocalGateReceipt,
  normalizeMathNodeProofReceipt,
  normalizeMathExecutionPolicy,
  normalizeMathPlanExpansion,
  normalizeMathPlanSnapshot,
  normalizeMathDurableProgressCheckpoint,
  normalizeMathResearchProblemContract,
  normalizeMathResearchFinding,
  normalizeMathRouteFingerprint,
  normalizeMathRouteCard,
  normalizeMathWorkflowStage,
  mathRouteStructureSignatureFromNormalized,
  isMathFoundationalLeanAxiom,
  normalizeMathProblemContract,
  updateMathProgressState,
  type MathLocalGateReceipt,
  type MathLeanFailureKind,
  type MathHelperReceipt,
  type MathNodeProofReceipt,
  type MathSolverReadyReceipt,
  type MathProblemContract,
  type MathFastCheck,
  type MathResearchFinding,
  type MathResearchEvidence,
  type MathResearchInsight,
  type MathResearchProbeKind,
  type MathResearchProblemContract,
  type MathDurableProgressCheckpoint,
  type MathFastCheckRuntimeProbe,
  type MathRouteCard,
  type MathRouteProbeReceipt,
} from "../common/types/team/mathematicsTeam";
import {
  mathAssignmentDuplicateDigest,
  selectMathSchedule,
  updateMathRoutePerformanceLedger,
  type MathRouteProgressClass,
} from "./mathAgentScheduling";
import {
  MATHEMATICS_PORTFOLIO_PATH,
  readMathematicsPortfolio,
  validateMathematicsPortfolio,
  type MathematicsPortfolio,
} from "../common/chat/mathematics";
import { isTeamRunAckPersisted } from "../common/types/team/teamTypes";
import {
  RESEARCH_TEAM_ASSIGNMENT_SCHEMA,
  RESEARCH_TEAM_RESULT_SCHEMA,
  createResearchTeamAssignment,
  createResearchTeamResult,
  requiredGitOid,
  type CreateResearchTeamAssignmentInput,
  type CreateResearchTeamResultInput,
  type ResearchTeamAssignment,
  type ResearchTeamAssignmentBinding,
  type ResearchTeamExecutionMode,
  type ResearchTeamMathAssignment,
  type ResearchTeamResult,
} from "../common/types/team/researchTeamContracts";
import { RESEARCH_TEAM_MCP_ACTIONS, type ResearchTeamMcpAction } from "../common/types/team/researchTeamMcp";
import {
  integrateProjectGitAgentBranch,
  listProjectGitResearchTeamAssignments,
  createProjectGitResearchTeamDeliveryId,
  createProjectGitResearchTeamTransportIdempotencyKey,
  recordProjectGitResearchTeamAssignment,
  recordProjectGitResearchTeamDelivery,
  recordProjectGitResearchTeamBudgetCancellation,
  recordProjectGitResearchTeamSupersessionPending,
  readProjectGitResearchTeamAssignment,
  completeProjectGitResearchTeamAssignment,
  supersedeProjectGitResearchTeamAssignment,
  discardProjectGitAgentWorktree,
  notifyProjectGitChanged,
  prepareProjectGitAgentWorktree,
  resolveProjectGitCommit,
  isProjectGitCommitAncestor,
  type ProjectGitIntegrateAgentBranchRequest,
  type ProjectGitIntegrateAgentBranchResult,
  type ProjectGitPrepareAgentWorktreeRequest,
  type ProjectGitPrepareAgentWorktreeResult,
  type ProjectGitResolveCommitRequest,
  type ProjectGitCommitAncestorRequest,
  type ProjectGitDiscardAgentWorktreeRequest,
  type ProjectGitDiscardAgentWorktreeResult,
  type ProjectGitResearchTeamAssignmentReceipt,
  type ProjectGitMathSourceVerificationReceipt,
  type ProjectGitMathVerificationEvidence,
  type ProjectGitResearchTeamPreparedGit,
  type ProjectGitResearchTeamAssignmentListRequest,
  type ProjectGitResearchTeamAssignmentRequest,
  type ProjectGitResearchTeamDeliveryRequest,
  type ProjectGitResearchTeamUsageBaseline,
} from "../project-git/index";
import { isResearchSlotReadyForSuccessor } from "./coreTeamClient";
import type {
  ResearchCoreAgentUsage,
  ResearchCoreRunState,
  ResearchCoreSlotState,
  ResearchCoreTeamClient,
} from "./coreTeamClient";
import {
  certifyFormalVerifications,
  createMathematicsRoutePreflightHarness,
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarations,
  readMathematicsReceiptSecret,
  signMathCandidateReview,
  signMathSolverReadyReceipt,
  verifyMathRouteProbeReceipt,
  mathematicsRoutePreflightEnvironmentFingerprint,
  verifyMathematicsHelperNode,
  readLeanEvalBootstrapReceipt,
  readImo2026BootstrapReceipt,
  verifyImo2026BootstrapReceipt,
  IMO2026_BOOTSTRAP_SCHEMA,
  type MathematicsVerifierBatchItem,
  type MathematicsVerifierBatchRequest,
  type MathematicsVerifierBatchResult,
  type MathematicsRoutePreflightResult,
  type LeanToolchainReadiness,
} from "../math/index";
import type { MathematicsHelperVerificationResult } from "../math/index";
import type { LeanEvalProofLoopResult } from "../math/leanEvalProofLoop";
import type { LeanEvalCounterexampleProbe } from "../math/leanEvalCounterexampleProbe";
import {
  createResearchTeamOrchestrator,
  ResearchTeamOrchestrationError,
  type ResearchTeamOrchestrationEvent,
  type ResearchTeamRuntime,
} from "./orchestrator";
import { authorizeResearchTeamToolAction, type ResearchTeamToolCapability } from "./toolCapability";
import { resolveTeamAgentSlotId, teamAgentIdForSlotId } from "../common/types/team/teamAgentIds";
import {
  normalizeTeamWaitSeconds,
  teamWaitLevelForSeconds,
  type TeamWaitLevel,
} from "../common/types/team/teamWaitPolicy";
import {
  classifyResearchTeamMathProgress,
  expectedResearchTeamAssignmentBinding,
  resolveMathematicsResearchAssignment,
  hydrateMathematicsWorkerResult,
  mathematicsAdvisoryRequestsExecutableLeanWork,
  MATHEMATICS_RESEARCH_HANDOFF_ROOT,
  projectMathematicsAssignmentForWorker,
  projectMathematicsResultForLead,
  validateDurableResearchTeamAssignment,
  mathematicsAssignmentMethodClass,
  type MathematicsAssignmentProjectionEfficiency,
} from "./mathematicsTeamAdapter";
import { createMathematicsProtocolHelp, createResearchTeamResultContract } from "./researchTeamResultContract";
import { collectMathematicsDispatchErrors, MathematicsDispatchValidationError } from "./mathematicsProtocolErrors";
import { mathematicsFormalizationPrejudgesFailure, validateMathematicsWaveLimits } from "./mathematicsDispatchPolicy";
import { isMathLiteRunEnvironment, MathRunInputsIntegrityError } from "../math/mathRunInputs";
import type { MathArtifactAccess } from "../math/mathArtifactStore";
import type { MathIntegrationJournal } from "../math/mathIntegrationJournal";
import { normalizeRuntimeMathAssignment } from "../math/mathAssignmentJournal";
import {
  MathWireValidationError,
  mathLiteProgressIntentSchema,
  normalizeMathArtifactRead,
  normalizeMathLiteDeliveryIntent,
  parseMathArtifactReference,
} from "../math/mathPublicWire";
import {
  MathAssignmentAdapterError,
  projectRuntimeMathAssignmentToExecutionView,
  runtimeMathAssignmentToResearchTeamEnvelope,
} from "../math/mathAssignmentExecutionAdapter";
import {
  MATH_DELIVERY_ENVELOPE_SCHEMA,
  projectMathWorkerDeliveryToEnvelope,
  type MathLiteDeliveryPreparation,
} from "../math/mathWorkerDeliveryAdapter";
import {
  deriveMathV2IntegrationPhase,
  selectMathV2IntegrationBatch,
} from "../math/mathIntegrationSelector";
import {
  prepareMathV2Promotion,
  promoteMathV2DraftToWorktree,
} from "../math/mathIntegrationPromotion";
import {
  mathSourceArtifactOutputSha256,
  normalizeMathSourceArtifact,
} from "../math/mathSourceArtifact";
import type { MathSourceArtifact } from "../common/types/team/mathRuntimeContracts";
import type { MathSourceStageRecovery, MathSourceStageResult } from "../math/mathSourceStaging";
import { MathAssignmentRegistry } from "../math/mathAssignmentRegistry";

export const RESEARCH_TEAM_TOOL_RESULT_SCHEMA = 'deepscientist.research-team.tool-result.v1' as const;
export const RESEARCH_TEAM_DELIVERY_SCHEMA = 'deepscientist.research-team.delivery.v1' as const;
export const FACTOR_RESEARCH_GIT_NAMESPACE = 'factor-research' as const;

export type ResearchTeamDispatchItemInput = Readonly<{
  targetSlotId: string;
  idempotencyKey: string;
  /** Advanced compatibility path for callers that already own the full contract. */
  assignment?: Record<string, unknown>;
  /** Preferred path: the runtime fills identity, lane, Git root, and defaults. */
  task?: string | Record<string, unknown>;
  baseCommit?: string;
  roleTemplateId?: string;
  roleKind?: 'xalpha' | 'generic';
  roleLabel?: string;
  roleInstructions?: string;
  executionMode?: ResearchTeamExecutionMode;
  /** Raw MCP payload; the immutable contract is normalized by createResearchTeamAssignment. */
  math?: Record<string, unknown>;
  acceptanceCriteria?: readonly string[];
  failureCriteria?: readonly string[];
  expectedArtifacts?: readonly string[];
  budget?: Readonly<{ maxMinutes?: number; maxAttempts?: number }>;
  /** Public v2 Mathematics request. It is never converted to a v1 assignment. */
  mathAssignment?: Record<string, unknown>;
}>;

export type ResearchTeamIntegrationItemInput = Readonly<{
  targetSlotId: string;
  /** Compatibility path for callers already holding an exact result. */
  result?: Record<string, unknown>;
  /** Preferred durable reference returned by Worker delivery. */
  deliveryId?: string;
  /** Compact alternative when the assignment identity is already known. */
  assignmentId?: string;
}>;

export type ResearchTeamToolInput = Readonly<{
  action: ResearchTeamMcpAction;
  assignments?: readonly ResearchTeamDispatchItemInput[];
  targetSlotIds?: readonly string[];
  /** Optional mathematical peer for a nonterminal share; host freezes its assignment identity. */
  shareTargetSlotId?: string;
  waitSeconds?: number;
  waitLevel?: TeamWaitLevel;
  result?: Record<string, unknown>;
  deliveries?: readonly ResearchTeamIntegrationItemInput[];
  sourceArtifacts?: readonly MathSourceArtifact[];
  artifactRead?: Readonly<{ ref: string; offsetBytes?: number; maxBytes?: number }>;
}>;

export type ResearchTeamProjectGitDriver = Readonly<{
  prepareAgentWorktree: (request: ProjectGitPrepareAgentWorktreeRequest) => ProjectGitPrepareAgentWorktreeResult;
  resolveCommit?: (request: ProjectGitResolveCommitRequest) => string;
  isCommitAncestor?: (request: ProjectGitCommitAncestorRequest) => boolean;
  discardAgentWorktree?: (request: ProjectGitDiscardAgentWorktreeRequest) => ProjectGitDiscardAgentWorktreeResult;
  integrateAgentBranch: (request: ProjectGitIntegrateAgentBranchRequest) => ProjectGitIntegrateAgentBranchResult;
  recordResearchTeamAssignment?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
  readResearchTeamAssignment?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt | undefined;
  listResearchTeamAssignments?: (
    request: ProjectGitResearchTeamAssignmentListRequest
  ) => readonly ProjectGitResearchTeamAssignmentReceipt[];
  completeResearchTeamAssignment?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
  supersedeResearchTeamAssignment?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
  recordResearchTeamBudgetCancellation?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
  recordResearchTeamSupersessionPending?: (
    request: ProjectGitResearchTeamAssignmentRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
  recordResearchTeamDelivery?: (
    request: ProjectGitResearchTeamDeliveryRequest
  ) => ProjectGitResearchTeamAssignmentReceipt;
}>;

/** Specialized Lean-Eval preparation. A solver workspace is intentionally not
 * a normal Git worktree: it is materialized from the pinned public tree and
 * contains only Submission-owned files. */
export type ResearchTeamLeanEvalWorkspacePreparation = Readonly<{
  ok: boolean;
  workspace: string;
  baseCommit: string;
  branch?: string;
  actualBaseCommit?: string;
  progressBaseCommit?: string;
  solverProjectRoot?: string;
  error?: string;
}>;
type ResearchTeamAssignmentReader = NonNullable<ResearchTeamProjectGitDriver['readResearchTeamAssignment']>;
type ResearchTeamAssignmentListReader = NonNullable<ResearchTeamProjectGitDriver['listResearchTeamAssignments']>;
type ResearchTeamAssignmentValidator = typeof validateAssignment;
type ResearchTeamResultValidator = (
  value: Record<string, unknown> | ResearchTeamResult,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember
) => ResearchTeamResult;
type ResearchTeamPortfolioReader = (capability: ResearchTeamToolCapability) => MathematicsPortfolio | undefined;
type MathV2VerificationItem = Readonly<{
  id: string;
  proofPath: string;
  contentSha256: string;
  theoremName: string;
  statementHash: string;
  leanStatementHash?: string;
  expectedSourceDeclarationHash: string;
  claim?: 'statement' | 'negation';
}>;
type MathV2VerificationResult = Readonly<{
  verified: boolean;
  disposition: 'verified' | 'candidate_rejected' | 'pending' | 'integrity_error';
  diagnostics?: string;
  receipts?: readonly ProjectGitMathSourceVerificationReceipt[];
  evidence?: ProjectGitMathVerificationEvidence;
}>;

function assertMathV2IntegratedSourceIdentity(
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  assignment: ReturnType<typeof normalizeRuntimeMathAssignment>,
  projectRelative = ''
): void {
  const integration = receipt.integration;
  if (
    receipt.state !== 'integrated' ||
    integration?.executionMode !== 'artifact' ||
    integration.reverificationRequired === true ||
    !integration.branch ||
    !integration.headCommit ||
    !integration.mergedCommit ||
    !integration.sourceVerificationReceipts?.length
  ) {
    throw new ResearchTeamOrchestrationError(
      'math_v2_integrated_identity',
      'The integrated v2 assignment is missing durable source verification identity.'
    );
  }
  const targets = assignment.request.verificationTargets;
  const receipts = integration.sourceVerificationReceipts;
  if (receipts.length !== targets.length) {
    throw new ResearchTeamOrchestrationError(
      'math_v2_integrated_identity',
      'The integrated v2 assignment does not contain one kernel receipt for every frozen verification target.'
    );
  }
  const seen = new Set<string>();
  for (const sourceReceipt of receipts) {
    const target = targets.find(
      (candidate) =>
        path.join(projectRelative, assignment.sourceRootRelative, candidate.pathRelative).replaceAll(path.sep, '/') ===
          sourceReceipt.sourcePath && candidate.theoremName === sourceReceipt.theoremName
    );
    if (
      !target ||
      seen.has(target.targetId) ||
      sourceReceipt.targetCommit !== integration.mergedCommit ||
      sourceReceipt.contentSha256 !== sourceReceipt.proofHash ||
      sourceReceipt.statementHash !== target.statementHash ||
      sourceReceipt.leanStatementHash !== target.leanStatementHash ||
      sourceReceipt.sourceDeclarationHash !== target.expectedSourceDeclarationHash ||
      sourceReceipt.verifier !== 'lean-kernel' ||
      sourceReceipt.goalsRemaining !== 0 ||
      sourceReceipt.sorryCount !== 0 ||
      sourceReceipt.admitCount !== 0
    ) {
      throw new ResearchTeamOrchestrationError(
        'math_v2_integrated_identity',
        'The integrated v2 source receipt does not match its frozen verification target.'
      );
    }
    seen.add(target.targetId);
  }
  if (seen.size !== targets.length) {
    throw new ResearchTeamOrchestrationError(
      'math_v2_integrated_identity',
      'The integrated v2 source receipt does not match its frozen verification target.'
    );
  }
}
const MATHEMATICS_DISPATCH_ALLOWED_LANES: Readonly<Record<ResearchTeamMathAssignment['stage'], readonly string[]>> = {
  audit: [],
  diversify: ['strategy-exploration'],
  select: [],
  formalize: ['lean-engineering'],
  local_gate: [],
  review: ['independent-review'],
  official_gate: [],
  replan: ['strategy-exploration'],
  done: [],
};

function assertLeanEvalWorkspaceSurface(workspace: string): void {
  const visit = (directory: string): void => {
    for (const entry of fs.readdirSync(directory)) {
      if (entry === 'Solution.lean') {
        throw new Error('Lean-Eval solver workspace contains protected Solution.lean');
      }
      const absolute = path.join(directory, entry);
      const stat = fs.lstatSync(absolute);
      if (stat.isSymbolicLink()) throw new Error(`Lean-Eval solver workspace contains a symlink: ${entry}`);
      if (stat.isDirectory() && entry !== '.git') visit(absolute);
    }
  };
  visit(workspace);
}
export type ResearchTeamToolContext = Readonly<{
  capability: ResearchTeamToolCapability;
  /**
   * Enables runtime-owned conditional semantic review after a verified
   * FORMALIZE integration. The default remains false so the proof-mainline
   * headless Team keeps its single persistent Formalizer unless the host
   * explicitly provisions a Reviewer surface.
   */
  enableConditionalReviewDispatch?: boolean;
  verifyRunInputs?: () => void;
  readMathAssignmentBinding?: () => Readonly<{
    runId: string;
    bindingDigest: string;
    projectRoot?: string;
    statementHash?: string;
    initialRouteFingerprint?: string;
  }>;
  prepareMathLiteDelivery?: (
    input: Readonly<{
      rawResult: unknown;
      deliveryId: string;
      receipt: ProjectGitResearchTeamAssignmentReceipt;
      assignment: ReturnType<typeof projectRuntimeMathAssignmentToExecutionView>;
    }>
  ) => Promise<MathLiteDeliveryPreparation>;
  hasMathLiteSealedDelivery?: (deliveryId: string) => boolean;
  isUnchangedMathLiteBlockedRetry?: (
    receipt: ProjectGitResearchTeamAssignmentReceipt,
    rawResult: unknown
  ) => boolean | Promise<boolean>;
  prepareMathLiteShare?: (
    input: Readonly<{
      rawResult: unknown;
      targetSlotId?: string;
      receipt: ProjectGitResearchTeamAssignmentReceipt;
      assignment: ReturnType<typeof projectRuntimeMathAssignmentToExecutionView>;
    }>
  ) => Promise<
    Readonly<{
      shareId: string;
      summary: string;
      files: readonly Readonly<{ pathRelative: string; ref: string; sha256: string }>[];
    }>
  >;
  acknowledgeMathLiteShare?: (shareId: string, assignmentId: string) => void | Promise<void>;
  readMathResearchGraph?: () => unknown;
  relayMathLiteProgress?: (client: ResearchCoreTeamClient) => Promise<void>;
  readMathLiteFeedback?: (
    input: Readonly<{
      consume?: boolean;
      receipt: ProjectGitResearchTeamAssignmentReceipt;
      assignment: ReturnType<typeof projectRuntimeMathAssignmentToExecutionView>;
    }>
  ) => Promise<Readonly<Record<string, unknown>>>;
  mathAssignmentRegistry?: MathAssignmentRegistry;
  stageMathSources?: (
    receipts: readonly ProjectGitResearchTeamAssignmentReceipt[],
    artifacts: readonly MathSourceArtifact[]
  ) => Promise<readonly MathSourceStageResult[]>;
  /** Discover source stages persisted by an earlier process invocation. */
  recoverMathSources?: (
    receipts: readonly ProjectGitResearchTeamAssignmentReceipt[]
  ) => Promise<readonly MathSourceStageRecovery[]>;
  prepareMathV2Worktree?: boolean;
  prepareMathV2AssignmentSources?: (
    input: Readonly<{
      assignment: ReturnType<typeof normalizeRuntimeMathAssignment>;
      worktreePath: string;
      replaying: boolean;
    }>
  ) => Promise<Readonly<{ solverProjectRoot: string }>> | Readonly<{ solverProjectRoot: string }>;
  commitMathV2Worktree?: (
    input: Readonly<{
      worktreePath: string;
      includePaths: readonly string[];
      expectedFiles: readonly Readonly<{ pathRelative: string; contentSha256: string }>[];
      assignmentId: string;
      branch: string;
      baseCommit: string;
    }>
  ) => Readonly<{ commit: string }>;
  verifyMathV2Worktree?: (
    request: Readonly<{
      worktreePath: string;
      projectRelative?: string;
      targetCommit: string;
      items: readonly MathV2VerificationItem[];
      signal?: AbortSignal;
    }>
  ) => Promise<MathV2VerificationResult>;
  client?: ResearchCoreTeamClient;
  projectGit?: ResearchTeamProjectGitDriver;
  signal?: AbortSignal;
  sleep?: (milliseconds: number, signal?: AbortSignal) => Promise<void>;
  /** Optional test/runtime override for merged-commit Mathematics certification. */
  certifyMathematics?: (request: MathematicsVerifierBatchRequest) => Promise<MathematicsVerifierBatchResult>;
  /** Optional host-owned verifier for helper declarations introduced by a plan expansion. */
  verifyMathematicsHelperNode?: (
    request: Parameters<typeof verifyMathematicsHelperNode>[0]
  ) => Promise<MathematicsHelperVerificationResult> | MathematicsHelperVerificationResult;
  /**
   * Optional host-owned Lean-Eval proof runner.  When present, Worker
   * FORMALIZE deliveries are reconciled against its kernel-grounded result
   * before the normal ResearchTeamResult validator runs.
   */
  runLeanEvalProofSession?: (
    request: ResearchTeamLeanEvalProofSessionRequest
  ) => Promise<ResearchTeamLeanEvalProofSessionResult> | ResearchTeamLeanEvalProofSessionResult;
  /** Optional host-owned bounded falsification runner for assignment evidence. */
  runLeanEvalCounterexampleProbe?: (
    request: ResearchTeamLeanEvalCounterexampleProbeRequest
  ) => Promise<LeanEvalCounterexampleProbe> | LeanEvalCounterexampleProbe;
  /** Host-owned preflight for a bound IMO assignment. */
  prepareBoundImoFastCheck?: (request: {
    workspaceRoot: string;
    baseCommit?: string;
    signal?: AbortSignal;
  }) => Promise<MathFastCheck> | MathFastCheck;
  prepareLeanEvalWorkspace?: (request: {
    assignment: ResearchTeamAssignment;
    target: ResearchTeamRosterMember;
  }) => ResearchTeamLeanEvalWorkspacePreparation | Promise<ResearchTeamLeanEvalWorkspacePreparation>;
  /** Verifier-owned route composition check run before a bound IMO Formalizer starts. */
  preflightMathematicsRoute?: (request: {
    workspaceRoot: string;
    targetCommit: string;
    problemContract: MathProblemContract;
    routeCard: MathRouteCard;
    signal?: AbortSignal;
  }) => MathematicsRoutePreflightResult | Promise<MathematicsRoutePreflightResult>;
  /** Runtime-owned readiness gate for any Lean FORMALIZE workspace. */
  checkLeanToolchainReadiness?: (request: {
    projectRoot: string;
    env?: NodeJS.ProcessEnv;
    timeoutMs?: number;
  }) => LeanToolchainReadiness;
  /** Runtime-owned immutable artifact reader for the read_artifact action. */
  readMathArtifact?: (
    request: Readonly<{ ref: string; offsetBytes?: number; maxBytes?: number }>,
    access: MathArtifactAccess
  ) => Promise<Readonly<{ text: string; sha256: string; totalBytes: number; nextOffsetBytes?: number }>>;
  /** Durable identity for Git integration side effects in headless math runs. */
  mathIntegrationJournal?: MathIntegrationJournal;
}>;

type ToolResult = {
  _meta?: Record<string, unknown>;
  content: { type: 'text'; text: string }[];
  isError?: boolean;
};

type DirectLeanEvalHelperCheckpoint = Readonly<{
  targetCommit: string;
  solverProjectPath: string;
  sourceFile: string;
  helperPlanNode: Readonly<Record<string, unknown>>;
  receipt: MathHelperReceipt;
  helpers: readonly Readonly<{
    sourceFile: string;
    helperPlanNode: Readonly<Record<string, unknown>>;
    receipt: MathHelperReceipt;
  }>[];
}>;

/**
 * Host-owned proof-session hook.  A Worker may provide a compact result, but
 * when this hook is configured the runtime re-runs the candidate through the
 * pinned Lean-Eval proof loop and uses only the returned patch for progress.
 * Identity fields remain server-owned and are never accepted from the patch.
 */
export type ResearchTeamLeanEvalProofSessionRequest = Readonly<{
  assignment: ResearchTeamAssignment;
  workspaceRoot: string;
  /** Canonical project root for durable cross-assignment outcome calibration. */
  projectRoot?: string;
  workerResult: Readonly<Record<string, unknown>>;
  signal?: AbortSignal;
}>;

export type ResearchTeamLeanEvalProofSessionResult = Readonly<{
  proofLoop: LeanEvalProofLoopResult;
  repairRequest?: Readonly<Record<string, unknown>>;
  resultPatch: Readonly<{
    math: Readonly<Record<string, unknown>>;
    disposition: ResearchTeamResult['disposition'];
    /** Full immutable head read from the prepared worktree after the proof loop. */
    gitHeadCommit: string;
    localGateReceipt?: Readonly<Record<string, unknown>>;
    mathNodeReceipt?: Readonly<Record<string, unknown>>;
    mathHelperReceipt?: Readonly<Record<string, unknown>>;
    mathCheckpoint?: Readonly<Record<string, unknown>>;
    artifactPaths?: readonly string[];
    outputs?: readonly string[];
    limitations?: readonly string[];
    summary?: string;
    nextRecommendation?: string;
  }>;
}>;

export type ResearchTeamLeanEvalCounterexampleProbeRequest = Readonly<{
  assignment: ResearchTeamAssignment;
  workspaceRoot: string;
  projectRoot?: string;
  probe: MathFastCheckRuntimeProbe;
  signal?: AbortSignal;
}>;

type ResearchTeamRosterMember = ResearchTeamToolCapability['roster'][number];
type ValidatedAssignment = Readonly<{
  assignment: ResearchTeamAssignment;
  target: ResearchTeamRosterMember;
}>;
type PreparedAssignment = Readonly<{
  assignment: ResearchTeamAssignment;
  /**
   * The exact immutable assignment persisted before Core enqueue.  In the
   * mathematics formalization path the Worker projection may contain a
   * runtime-materialized research handoff and Git delivery fields; the
   * receipt must use the same handoff-enriched assignment that was written in
   * the prepared WAL, not the pre-materialization validation input.
   */
  receiptAssignment: ResearchTeamAssignment;
  target: ResearchTeamRosterMember;
  advisory: boolean;
  branch?: NonNullable<ProjectGitPrepareAgentWorktreeResult['branch']>;
  workspace?: string;
  preparedGit?: ProjectGitResearchTeamPreparedGit;
  projectionEfficiency?: MathematicsAssignmentProjectionEfficiency;
  usageBaseline?: ResearchCoreAgentUsage;
}>;
type IntegrationRequest = Readonly<{
  targetSlotId: string;
  result: ResearchTeamResult;
}>;
type NormalizedIntegrationBatch = readonly IntegrationRequest[];
type IntegratedDelivery = Readonly<{
  result: ResearchTeamResult;
  target: ResearchTeamRosterMember;
  advisory: boolean;
  /** A completed solver episode whose artifact is intentionally not merged. */
  retainedWithoutMerge?: boolean;
  sourceAssignment?: ResearchTeamAssignment;
  mathProgressControl?: Readonly<Record<string, unknown>>;
  branch?: NonNullable<ProjectGitIntegrateAgentBranchResult['branch']>;
  /** The immutable Worker branch head, distinct from a reverified Lead head. */
  deliveredHeadCommit?: string;
  mergedCommit?: string;
  /** no-ff merge changed the commit identity; a fresh Lean receipt is required. */
  reverificationRequired?: boolean;
  /** A merged-commit certification completed during this integration. */
  reverified?: boolean;
  /** Durable receipts produced by merged-commit certification. */
  reverifiedReceipts?: Readonly<{
    localGateReceipt?: MathLocalGateReceipt;
    mathNodeReceipt?: MathNodeProofReceipt;
    mathHelperReceipt?: MathHelperReceipt;
  }>;
  solverReadyReceipt?: MathSolverReadyReceipt;
  researchContractUpdate?: Readonly<{
    researchContract: MathResearchProblemContract;
    persisted: boolean;
  }>;
  reverificationError?: string;
  integrationEffectId?: string;
  alreadyIntegrated: boolean;
}>;
type RuntimeContext = Readonly<{
  capability: ResearchTeamToolCapability;
  projectGit: ResearchTeamProjectGitDriver;
  deferMathResearchPersistence: boolean;
  readAssignment?: ResearchTeamAssignmentReader;
  listAssignments?: ResearchTeamAssignmentListReader;
  integrationAssignmentIds?: readonly string[];
  completionEligibleAssignmentId?: string;
  /** Shared state used to certify a multi-branch Mathematics wave once. */
  mathematicsBatchReverification?: MathematicsBatchReverificationState;
  readPortfolio: ResearchTeamPortfolioReader;
  validateAssignment: ResearchTeamAssignmentValidator;
  validateResult: ResearchTeamResultValidator;
  certifyMathematics?: (request: MathematicsVerifierBatchRequest) => Promise<MathematicsVerifierBatchResult>;
  verifyMathematicsHelperNode?: ResearchTeamToolContext['verifyMathematicsHelperNode'];
  prepareLeanEvalWorkspace?: ResearchTeamToolContext['prepareLeanEvalWorkspace'];
  preflightMathematicsRoute?: ResearchTeamToolContext['preflightMathematicsRoute'];
  checkLeanToolchainReadiness?: NonNullable<ResearchTeamToolContext['checkLeanToolchainReadiness']>;
  mathIntegrationJournal?: MathIntegrationJournal;
}>;
type ItemResult = Readonly<Record<string, unknown>>;
type OrchestrationEvent = ResearchTeamOrchestrationEvent<
  ResearchTeamAssignment,
  ValidatedAssignment,
  PreparedAssignment,
  IntegrationRequest,
  IntegratedDelivery
>;

class RepairableResearchTeamDeliveryError extends Error {
  constructor(
    message: string,
    readonly repairRequest?: Readonly<Record<string, unknown>>
  ) {
    super(message);
    this.name = 'RepairableResearchTeamDeliveryError';
  }
}

/** Recovery describes durable host state; it never authorizes a changed sealed delivery. */
class MathLiteDeliveryRecoveryError extends ResearchTeamOrchestrationError {
  readonly recovery: Readonly<Record<string, unknown>>;

  constructor(error: unknown, phase: 'preparing' | 'sealed' | 'delivered', signal?: AbortSignal) {
    const message = error instanceof Error ? error.message : String(error);
    const failure = error instanceof ResearchTeamOrchestrationError ? `${error.code}: ${message}` : message;
    const cancelled = signal?.aborted || /cancelled|canceled|abort/iu.test(failure);
    // Before sealing, a rejected file list is the Worker's to correct. Reporting
    // it as host integrity told the model to replay an unsealed delivery, which
    // then failed eight times with not_sealed (run 23e).
    const workerCorrectable = phase === 'preparing' && /delivery_file_unauthorized/iu.test(failure);
    const integrity =
      !workerCorrectable && /integrity|identity|unauthorized|forbidden|permission|capability|outside/iu.test(failure);
    const conflict = /delivery_conflict/iu.test(failure);
    const replay = phase !== 'preparing';
    const code = cancelled
      ? 'math_lite_delivery_cancelled'
      : integrity
        ? 'math_lite_delivery_integrity'
        : conflict
          ? 'math_lite_delivery_conflict'
          : error instanceof ResearchTeamOrchestrationError
            ? error.code
            : replay
              ? 'math_lite_delivery_recovery_pending'
              : 'math_lite_delivery_preparation_failed';
    // error.retryable describes retrying the original request. A conflicting
    // request cannot be repeated, but its unchanged sealed delivery can recover.
    super(code, message, !cancelled && !integrity && !conflict);
    const requestRetryable = replay && !cancelled && !integrity;
    this.recovery = Object.freeze({
      phase,
      // Owner is the actor who must initiate recovery, not who stores the seal.
      owner: integrity ? 'host' : 'worker',
      automaticRetry: false,
      requestRetryable,
      ...(requestRetryable ? { request: { action: 'deliver' } } : {}),
      instruction: cancelled
        ? 'Preserve the current source and frozen delivery. Do not automatically restart a cancelled operation.'
        : integrity
          ? 'Preserve the source and frozen delivery. The host must restore the authorized identity or artifact before recovery; do not change permissions or proof bytes.'
          : replay
            ? conflict
              ? 'The submitted result conflicts with the sealed request and must not be retried. The Worker may call deliver without result to recover the original frozen request; requestRetryable applies only to that recovery request. A changed proof requires a legal successor.'
              : phase === 'delivered'
                ? 'The delivery is already durable. Call deliver without result to resume staging the same frozen files; the host will not send another delivery. A changed proof requires a legal successor.'
                : 'The files and request are sealed. Call deliver without result so the host replays the original frozen delivery. Do not rewrite summary, files or source to repair this operation; a changed proof requires a legal successor.'
            : 'No complete delivery was sealed. Correct the reported preparation error in the current assignment, then call deliver with its result. Current source may be corrected before retry.',
    });
  }
}

const researchTeamOrchestrator = createResearchTeamOrchestrator<
  ResearchTeamAssignment,
  ValidatedAssignment,
  PreparedAssignment,
  IntegrationRequest,
  IntegratedDelivery,
  RuntimeContext,
  ItemResult
>({
  validateAssignment: (request, runtime) => {
    const capability = runtime.context.capability;
    const target = requireWorker(capability, request.targetSlotId);
    let assignment = enrichMathematicsAssignmentRuntimeState(
      runtime.context.validateAssignment(request.assignment, capability, target),
      capability,
      target.slotId,
      runtime.context.readAssignment,
      runtime.context.listAssignments
    );
    if (capability.profileId === 'mathematics-research-team' && assignment.math && assignment.budget) {
      const { budget: _budget, ...withoutBudget } = assignment;
      assignment = Object.freeze(withoutBudget);
    }
    return Object.freeze({ assignment, target });
  },
  prepare: async (_request, validated, runtime) => {
    const capability = runtime.context.capability;
    const modelBoundAssignment = await bindMathematicsExecutionModel(
      validated.assignment,
      validated.target,
      capability.teamId,
      runtime.client,
      runtime.signal
    );
    const runtimeAssignment = await attachBoundImoRoutePreflight(
      modelBoundAssignment,
      capability,
      runtime.context.preflightMathematicsRoute,
      runtime.signal
    );
    const priorReceipt = runtime.context.readAssignment?.({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: validated.target.slotId,
      assignmentId: runtimeAssignment.assignmentId,
    });
    // Dispatch correctness does not depend on a Core usage snapshot.  Reading
    // it here adds two API round trips before every Mathematics Worker can
    // start.  Preserve a durable baseline when one already exists, but collect
    // optional usage telemetry only after the Worker has delivered.
    const usageBaseline = priorReceipt?.usageBaseline as ResearchCoreAgentUsage | undefined;
    if (runtimeAssignment.executionMode === 'advisory') {
      const projection = projectMathematicsAssignmentForWorker(
        runtimeAssignment,
        validated.target,
        runtime.context.readPortfolio(capability)
      );
      persistResearchTeamAssignment(
        runtime.context.projectGit,
        capability,
        runtimeAssignment,
        validated.target,
        'prepared',
        usageBaseline
      );
      return Object.freeze({
        message: projection.serializedAssignment,
        detail: Object.freeze({
          assignment: runtimeAssignment,
          receiptAssignment: runtimeAssignment,
          target: validated.target,
          advisory: true,
          projectionEfficiency: projection.efficiency,
          ...(usageBaseline ? { usageBaseline } : {}),
        }),
      });
    }
    const isLeanEvalAssignment = Boolean(
      runtimeAssignment.math?.problemContract?.officialManifestId?.startsWith('lean-eval:')
    );
    let leanEvalPreparation: ResearchTeamLeanEvalWorkspacePreparation | undefined;
    const prepared: ProjectGitPrepareAgentWorktreeResult = isLeanEvalAssignment
      ? await (async () => {
          const isolated = runtime.context.prepareLeanEvalWorkspace
            ? await runtime.context.prepareLeanEvalWorkspace({
                assignment: runtimeAssignment,
                target: validated.target,
              })
            : undefined;
          if (!isolated?.ok || !isolated.workspace || !isolated.baseCommit || !isolated.branch) {
            throw new ResearchTeamOrchestrationError(
              'lean_eval_workspace_unavailable',
              isolated?.error ||
                'Lean-Eval assignments require the specialized solver workspace driver; a normal Git worktree is forbidden.',
              true
            );
          }
          if (!isolated.actualBaseCommit || !isolated.progressBaseCommit || !isolated.solverProjectRoot) {
            throw new ResearchTeamOrchestrationError(
              'lean_eval_workspace_identity_incomplete',
              'Lean-Eval workspace preparation did not return its private solver baseline and project identity.',
              false
            );
          }
          leanEvalPreparation = isolated;
          return Object.freeze({
            ok: true as const,
            workspace: isolated.workspace,
            branch: Object.freeze({
              name: isolated.branch,
              ref: `refs/heads/${isolated.branch}`,
              head: isolated.baseCommit,
              shortHead: isolated.baseCommit.slice(0, 8),
              active: false,
              status: 'candidate' as const,
              baseCommit: isolated.baseCommit,
              worktreePath: isolated.workspace,
              worktreeState: 'clean' as const,
            }),
          });
        })()
      : runtime.context.projectGit.prepareAgentWorktree({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: validated.target.slotId,
          roleId: validated.target.roleId,
          strategyLane: validated.target.laneId,
          assignmentId: runtimeAssignment.assignmentId,
          orchestrationNamespace: gitNamespace(capability),
          workflowId: capability.workflowId,
          objective: runtimeAssignment.objective,
          from: runtimeAssignment.git.baseCommit,
        });
    if (!prepared.ok || !prepared.branch || !prepared.workspace || !prepared.branch.baseCommit) {
      throw new ResearchTeamOrchestrationError(
        'agent_worktree_unavailable',
        prepared.error || 'Unable to prepare the Research Team Worker Git worktree.',
        true
      );
    }
    if (
      runtimeAssignment.math?.stage === 'formalize' &&
      validated.target.laneId === 'lean-engineering' &&
      runtime.context.checkLeanToolchainReadiness
    ) {
      let readinessRoot = prepared.workspace;
      if (isLeanEvalAssignment) {
        try {
          const receipt = readLeanEvalBootstrapReceipt(path.join(prepared.workspace, 'active-problem.json'));
          if (path.resolve(receipt.workspaceRoot) !== path.resolve(prepared.workspace)) {
            throw new Error('Lean-Eval workspace receipt root does not match the prepared workspace');
          }
          readinessRoot = receipt.projectRoot;
        } catch (error) {
          runtime.context.projectGit.discardAgentWorktree?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: validated.target.slotId,
            assignmentId: runtimeAssignment.assignmentId,
            branch: prepared.branch.name,
            worktreePath: prepared.workspace,
          });
          throw new ResearchTeamOrchestrationError(
            'lean_eval_workspace_unsafe',
            error instanceof Error ? error.message : String(error),
            false
          );
        }
      } else {
        // IMO bootstrap projects live below the workspace (for example
        // generated/imo2026_q5). A normal Git worktree copies that layout,
        // so readiness must probe the Worker worktree's project rather than
        // the worktree root itself. Never reuse the receipt's absolute path:
        // that would probe the Lead workspace.
        const boundImoReceipt = readBoundImo2026Receipt(capability);
        if (boundImoReceipt) {
          const boundWorkspace = path.resolve(boundImoReceipt.workspaceRoot);
          const boundProject = path.resolve(boundImoReceipt.projectRoot);
          const projectRelative = path.relative(boundWorkspace, boundProject);
          if (!projectRelative || projectRelative.startsWith('..' + path.sep) || path.isAbsolute(projectRelative)) {
            throw new ResearchTeamOrchestrationError(
              'imo2026_workspace_unsafe',
              'IMO2026 receipt project root must remain inside its workspace root.',
              false
            );
          }
          try {
            readinessRoot = assertBoundProjectPath(
              fs.realpathSync(prepared.workspace),
              projectRelative,
              'IMO2026 Worker project root'
            );
            const projectStat = fs.lstatSync(readinessRoot);
            if (!projectStat.isDirectory() || projectStat.isSymbolicLink()) {
              throw new Error('IMO2026 Worker project root must be a regular directory');
            }
          } catch (error) {
            runtime.context.projectGit.discardAgentWorktree?.({
              workspace: capability.projectRoot,
              teamId: capability.teamId,
              slotId: validated.target.slotId,
              assignmentId: runtimeAssignment.assignmentId,
              branch: prepared.branch.name,
              worktreePath: prepared.workspace,
            });
            throw new ResearchTeamOrchestrationError(
              'imo2026_workspace_unsafe',
              error instanceof Error ? error.message : String(error),
              false
            );
          }
        }
      }
      const readiness = runtime.context.checkLeanToolchainReadiness({ projectRoot: readinessRoot });
      if (readiness.status !== 'ready') {
        runtime.context.projectGit.discardAgentWorktree?.({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: validated.target.slotId,
          assignmentId: runtimeAssignment.assignmentId,
          branch: prepared.branch.name,
          worktreePath: prepared.workspace,
        });
        throw new ResearchTeamOrchestrationError(
          readiness.status === 'unavailable' ? 'lean_toolchain_unavailable' : 'lean_toolchain_invalid',
          `Lean toolchain readiness gate ${readiness.status}: ${readiness.diagnostics}`,
          readiness.status === 'unavailable'
        );
      }
    }
    if (isLeanEvalAssignment) {
      try {
        assertLeanEvalWorkspaceSurface(prepared.workspace);
      } catch (error) {
        runtime.context.projectGit.discardAgentWorktree?.({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: validated.target.slotId,
          assignmentId: runtimeAssignment.assignmentId,
          branch: prepared.branch.name,
          worktreePath: prepared.workspace,
        });
        throw new ResearchTeamOrchestrationError(
          'lean_eval_workspace_unsafe',
          error instanceof Error ? error.message : String(error),
          false
        );
      }
    }
    // A specialized Lean-Eval workspace has its own private Git baseline. Its
    // commit identity is intentionally different from the project assignment
    // baseCommit, which remains the canonical Team/WAL identity. The ordinary
    // project worktree path must still prove that HEAD equals baseCommit.
    let preparedWorkspaceHead: string | undefined;
    if (!isLeanEvalAssignment && runtime.context.projectGit.resolveCommit) {
      try {
        preparedWorkspaceHead = runtime.context.projectGit.resolveCommit({
          workspace: prepared.workspace,
          reference: 'HEAD',
        });
      } catch {
        preparedWorkspaceHead = undefined;
      }
    }
    const worktreeHeadMismatch =
      !isLeanEvalAssignment &&
      (runtime.context.projectGit.resolveCommit
        ? preparedWorkspaceHead !== runtimeAssignment.git.baseCommit
        : preparedWorkspaceHead !== undefined && preparedWorkspaceHead !== runtimeAssignment.git.baseCommit);
    if (
      prepared.branch.baseCommit !== runtimeAssignment.git.baseCommit ||
      worktreeHeadMismatch ||
      !prepared.branch.name.startsWith(workerBranchPrefix(capability, validated.target))
    ) {
      runtime.context.projectGit.discardAgentWorktree?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: validated.target.slotId,
        assignmentId: runtimeAssignment.assignmentId,
        branch: prepared.branch.name,
        worktreePath: prepared.workspace,
      });
      throw new ResearchTeamOrchestrationError(
        'agent_worktree_identity_mismatch',
        'Prepared Research Team worktree HEAD/baseCommit does not match the assignment Git identity.'
      );
    }
    try {
      const preparedGit: ProjectGitResearchTeamPreparedGit = Object.freeze({
        branch: prepared.branch.name,
        worktreePath: prepared.workspace,
        baseCommit: prepared.branch.baseCommit,
        ...(leanEvalPreparation
          ? {
              actualBaseCommit: leanEvalPreparation.actualBaseCommit,
              progressBaseCommit: leanEvalPreparation.progressBaseCommit,
              solverProjectRoot: leanEvalPreparation.solverProjectRoot,
            }
          : {}),
      });
      const preparedAssignment = materializeIntegratedMathematicsResearchHandoff(
        runtimeAssignment,
        runtime.context.listAssignments,
        capability,
        prepared.workspace
      );
      const assignment = Object.freeze({
        ...preparedAssignment,
        git: Object.freeze({
          ...preparedAssignment.git,
          baseCommit: prepared.branch.baseCommit,
          branch: prepared.branch.name,
          worktreePath: prepared.workspace,
        }),
      });
      const projection = projectMathematicsAssignmentForWorker(assignment, validated.target);
      // A failed worktree preflight is not a prepared dispatch. Persist only
      // after Git identity and the exact Worker projection are both usable.
      persistResearchTeamAssignment(
        runtime.context.projectGit,
        capability,
        preparedAssignment,
        validated.target,
        'prepared',
        usageBaseline,
        undefined,
        preparedGit
      );
      return Object.freeze({
        message: projection.serializedAssignment,
        dispatchWorkspace: prepared.workspace,
        detail: Object.freeze({
          assignment,
          receiptAssignment: preparedAssignment,
          target: validated.target,
          advisory: false,
          branch: prepared.branch,
          workspace: prepared.workspace,
          preparedGit,
          projectionEfficiency: projection.efficiency,
          ...(usageBaseline ? { usageBaseline } : {}),
        }),
      });
    } catch (error) {
      runtime.context.projectGit.discardAgentWorktree?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: validated.target.slotId,
        assignmentId: runtimeAssignment.assignmentId,
        branch: prepared.branch.name,
        worktreePath: prepared.workspace,
      });
      throw error;
    }
  },
  discardPrepared: (_request, _validated, prepared, runtime) => {
    if (prepared.detail.advisory || !runtime.context.projectGit.discardAgentWorktree) return;
    const branch = prepared.detail.branch?.name || prepared.detail.assignment.git.branch;
    const worktreePath = prepared.detail.workspace || prepared.detail.assignment.git.worktreePath;
    if (!branch && !worktreePath) return;
    const discarded = runtime.context.projectGit.discardAgentWorktree({
      workspace: runtime.context.capability.projectRoot,
      teamId: runtime.context.capability.teamId,
      slotId: prepared.detail.target.slotId,
      assignmentId: prepared.detail.assignment.assignmentId,
      ...(branch ? { branch } : {}),
      ...(worktreePath ? { worktreePath } : {}),
    });
    if (!discarded.ok && !discarded.preserved) {
      throw new Error(discarded.error || 'Unable to clean up the prepared Agent worktree.');
    }
  },
  integrate: async (input, runtime) => {
    const capability = runtime.context.capability;
    const target = requireWorker(capability, input.targetSlotId);
    const readAssignment = runtime.context.readAssignment;
    const validateAssignmentOnce = runtime.context.validateAssignment;
    const result = runtime.context.validateResult(input.result, capability, target);
    const durableReceipt = readAssignment?.({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: target.slotId,
      assignmentId: result.assignmentId,
    });
    const sourceAssignment =
      dispatchedAssignments.get(`${capability.teamId}:${result.assignmentId}`) ??
      (durableReceipt
        ? validateDurableResearchTeamAssignment(durableReceipt.assignment, capability, target, validateAssignmentOnce)
        : undefined);
    const startedAt = durableReceipt?.startedAt ? Date.parse(durableReceipt.startedAt) : Number.NaN;
    const assignmentElapsedMs = Number.isFinite(startedAt) ? Math.max(0, Date.now() - startedAt) : undefined;
    let agentUsage: ResearchCoreAgentUsage | undefined;
    // An integrated delivery is already durable and idempotent. Re-reading
    // conversation metadata and usage on a replay only adds two Core API
    // round trips and cannot change integration or progress decisions.
    if (
      durableReceipt?.state !== 'integrated' &&
      shouldReadMathAgentUsage(result, sourceAssignment) &&
      runtime.client.readAgentUsage
    ) {
      try {
        agentUsage = await runtime.client.readAgentUsage(capability.teamId, target.slotId, runtime.signal);
      } catch {
        agentUsage = undefined;
      }
    }
    const usageBaseline =
      dispatchedUsageBaselines.get(`${capability.teamId}:${result.assignmentId}`) ?? durableReceipt?.usageBaseline;
    const assignmentUsage = deriveAssignmentAgentUsage(usageBaseline, agentUsage);
    const outstandingAssignmentCount = countOutstandingMathematicsAssignments(
      capability,
      result,
      sourceAssignment,
      runtime.context.listAssignments,
      runtime.context.validateAssignment,
      runtime.context.integrationAssignmentIds,
      runtime.context.completionEligibleAssignmentId
    );
    const mathProgressControl = deriveIntegratedMathProgressControl(
      result,
      sourceAssignment,
      durableReceipt,
      assignmentElapsedMs,
      assignmentUsage,
      agentUsage,
      outstandingAssignmentCount,
      runtime.context.listAssignments?.({ workspace: capability.projectRoot, teamId: capability.teamId }) ?? []
    );
    let researchContractUpdate: IntegratedDelivery['researchContractUpdate'];
    if (
      durableReceipt?.state !== 'integrated' &&
      ['accepted', 'refuted'].includes(result.disposition) &&
      result.mathResearchFinding &&
      sourceAssignment?.math?.researchContract
    ) {
      const trustedEvidence = durableReceipt
        ? readTrustedAssignmentMathEvidence(result.mathResearchFinding, durableReceipt)
        : readTrustedMathResearchEvidence(result.mathResearchFinding, {
            teamId: capability.teamId,
            assignmentId: result.assignmentId,
          });
      const fallback = applyMathResearchFinding(
        sourceAssignment.math.researchContract,
        result.mathResearchFinding,
        trustedEvidence
      );
      const persisted = runtime.context.deferMathResearchPersistence
        ? undefined
        : updateMathematicsResearchContract({
            workspace: capability.projectRoot,
            contract: sourceAssignment.math.researchContract,
            finding: result.mathResearchFinding,
            trustedEvidence,
          });
      researchContractUpdate = Object.freeze({
        researchContract: persisted?.researchContract ?? fallback,
        persisted: persisted?.updated === true,
      });
    }
    if (durableReceipt?.state === 'integrated') {
      assertIntegratedReceiptMatchesResult(durableReceipt, result);
      const durableMergedCommit = durableReceipt.integration?.mergedCommit;
      if (
        durableMergedCommit &&
        runtime.context.projectGit.isCommitAncestor &&
        !runtime.context.projectGit.isCommitAncestor({
          workspace: capability.projectRoot,
          ancestor: durableMergedCommit,
          descendant: 'HEAD',
        })
      ) {
        throw new ResearchTeamOrchestrationError(
          'integration_replay_mismatch',
          'The durable merged commit is absent from canonical Project Git.'
        );
      }
    }
    if (result.executionMode === 'advisory') {
      return Object.freeze({
        result,
        target,
        advisory: true,
        ...(sourceAssignment ? { sourceAssignment } : {}),
        ...(mathProgressControl ? { mathProgressControl } : {}),
        ...(researchContractUpdate ? { researchContractUpdate } : {}),
        alreadyIntegrated: durableReceipt?.state === 'integrated',
      });
    }
    if (!result.git.branch || !result.git.headCommit) {
      throw new ResearchTeamOrchestrationError(
        'integration_identity_missing',
        'Artifact integration requires an exact branch and headCommit.'
      );
    }
    const directAttempt = sourceAssignment?.math?.directAttempt === true;
    const solverCompleteDirect = directAttempt && isSolverCompleteDirectResult(result, sourceAssignment);
    const declarationClusterComplete =
      directAttempt && isDirectDeclarationClusterCompleteResult(result, sourceAssignment);
    const runtimeSourceProgress = Boolean(result.math?.sourceProgress?.changedDeclarationNames.length);
    assertDirectMathematicsCompletionSourceIntegrity(
      result,
      sourceAssignment,
      capability.projectRoot,
      durableReceipt?.preparedGit?.worktreePath
    );
    if (
      durableReceipt?.integration?.retainedWithoutMerge === true ||
      (durableReceipt?.state !== 'integrated' &&
        directAttempt &&
        !solverCompleteDirect &&
        !declarationClusterComplete &&
        !runtimeSourceProgress)
    ) {
      return Object.freeze({
        result,
        target,
        advisory: false,
        retainedWithoutMerge: true,
        ...(sourceAssignment ? { sourceAssignment } : {}),
        ...(mathProgressControl ? { mathProgressControl } : {}),
        ...(researchContractUpdate ? { researchContractUpdate } : {}),
        deliveredHeadCommit: result.git.headCommit,
        alreadyIntegrated: durableReceipt?.state === 'integrated',
      });
    }
    if (runtime.context.listAssignments) {
      const incomingPaths = assignmentArtifactPaths(sourceAssignment, result.artifactPaths);
      const activeDirectOwnsArtifact = runtime.context
        .listAssignments({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          states: ['accepted'],
        })
        .some((receipt) => {
          if (receipt.assignmentId === result.assignmentId || receipt.state !== 'accepted' || receipt.delivery)
            return false;
          const target = capability.roster.find((member) => member.slotId === receipt.slotId);
          if (!target) return false;
          try {
            const competing = validateDurableResearchTeamAssignment(
              receipt.assignment,
              capability,
              target,
              runtime.context.validateAssignment
            );
            return (
              competing.math?.directAttempt === true &&
              competing.math.stage === 'formalize' &&
              competing.math.statementHash === result.math?.statementHash &&
              competing.git.baseCommit === result.git.baseCommit &&
              artifactPathsOverlap(incomingPaths, assignmentArtifactPaths(competing))
            );
          } catch {
            return false;
          }
        });
      if (activeDirectOwnsArtifact) {
        throw new ResearchTeamOrchestrationError(
          'direct_artifact_owned',
          'An active direct FORMALIZE assignment owns an overlapping artifact; keep helper and partial branches unmerged until it finishes.'
        );
      }
    }
    const effect =
      runtime.context.capability.profileId === 'mathematics-research-team'
        ? await runtime.context.mathIntegrationJournal?.prepare({
            assignmentId: result.assignmentId,
            branch: result.git.branch,
            deliveredHead: result.git.headCommit,
            expectedBase: result.git.baseCommit,
          })
        : undefined;
    const durableMergedCommit =
      durableReceipt?.state === 'integrated' && durableReceipt.integration?.executionMode === 'artifact'
        ? durableReceipt.integration.mergedCommit
        : undefined;
    const integrated = durableMergedCommit
      ? {
          ok: true as const,
          branch: { name: result.git.branch, baseCommit: result.git.baseCommit } as NonNullable<
            ProjectGitIntegrateAgentBranchResult['branch']
          >,
          mergedCommit: durableMergedCommit,
          alreadyIntegrated: true,
        }
      : effect?.observed && effect.mergedCommit
        ? {
            ok: true as const,
            branch: { name: result.git.branch, baseCommit: result.git.baseCommit } as NonNullable<
              ProjectGitIntegrateAgentBranchResult['branch']
            >,
            mergedCommit: effect.mergedCommit,
            alreadyIntegrated: true,
          }
        : runtime.context.projectGit.integrateAgentBranch({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: target.slotId,
            branch: result.git.branch,
            assignmentId: result.assignmentId,
            orchestrationNamespace: gitNamespace(capability),
            expectedHead: result.git.headCommit,
            summary: result.summary,
          });
    if (!integrated.ok || !integrated.branch || !integrated.mergedCommit) {
      throw new ResearchTeamOrchestrationError(
        'integration_failed',
        integrated.error || 'Unable to integrate the Research Team Worker branch.'
      );
    }
    if (effect && runtime.context.mathIntegrationJournal) {
      await runtime.context.mathIntegrationJournal.observe(effect.effectId, integrated.mergedCommit);
    }
    if (durableReceipt?.state === 'integrated' && integrated.alreadyIntegrated !== true) {
      throw new ResearchTeamOrchestrationError(
        'integration_replay_mismatch',
        'The durable receipt says this assignment was integrated, but Git does not contain the delivered head.'
      );
    }
    // A replayed merge can still require certification: the delivered Worker
    // commit and canonical merge commit are different identities regardless of
    // whether Git performed the merge in this process or recovered it.
    const mergedCommitChanged = integrated.mergedCommit !== result.git.headCommit;
    const pendingReverification = durableReceipt?.integration?.reverificationRequired === true;
    let integratedResult = result;
    let reverified = false;
    let reverifiedReceipts = durableReceipt?.integration?.reverifiedReceipts;
    let reverificationError: string | undefined;
    const partialSourceProgressWithoutReceipt =
      runtimeSourceProgress &&
      !pendingReverification &&
      !solverCompleteDirect &&
      !declarationClusterComplete &&
      !result.localGateReceipt &&
      !result.mathNodeReceipt &&
      !result.mathHelperReceipt;
    let reverificationRequired =
      !partialSourceProgressWithoutReceipt && (pendingReverification || (mergedCommitChanged && !reverifiedReceipts));
    if (reverifiedReceipts) {
      try {
        assertPersistedReverifiedMathematics(
          reverifiedReceipts,
          result,
          sourceAssignment,
          capability.projectRoot,
          integrated.mergedCommit
        );
      } catch (error) {
        throw new ResearchTeamOrchestrationError(
          'integration_replay_mismatch',
          error instanceof Error ? error.message : String(error)
        );
      }
      const receiptCommits = [
        reverifiedReceipts.localGateReceipt?.targetCommit,
        reverifiedReceipts.mathNodeReceipt?.targetCommit,
        reverifiedReceipts.mathHelperReceipt?.targetCommit,
      ].filter((commit): commit is string => Boolean(commit));
      if (!receiptCommits.length || receiptCommits.some((commit) => commit !== integrated.mergedCommit)) {
        throw new ResearchTeamOrchestrationError(
          'integration_replay_mismatch',
          'The durable merged receipts do not target the current integrated commit.'
        );
      }
      integratedResult = Object.freeze({
        ...result,
        git: Object.freeze({ ...result.git, headCommit: integrated.mergedCommit }),
        ...(reverifiedReceipts.localGateReceipt ? { localGateReceipt: reverifiedReceipts.localGateReceipt } : {}),
        ...(reverifiedReceipts.mathNodeReceipt ? { mathNodeReceipt: reverifiedReceipts.mathNodeReceipt } : {}),
        ...(reverifiedReceipts.mathHelperReceipt ? { mathHelperReceipt: reverifiedReceipts.mathHelperReceipt } : {}),
      });
      reverified = true;
      reverificationRequired = false;
    } else if (
      result.math &&
      (mergedCommitChanged || pendingReverification) &&
      // Source-level progress is intentionally merged without invoking the
      // full candidate verifier. The candidate may still contain open goals;
      // only a stored kernel receipt is eligible for re-verification here.
      !partialSourceProgressWithoutReceipt
    ) {
      const batchState = runtime.context.mathematicsBatchReverification;
      const batchEligible = Boolean(batchState?.expectedAssignmentIds.has(result.assignmentId));
      if (batchState && batchEligible && sourceAssignment) {
        batchState.entries.set(result.assignmentId, {
          result,
          assignment: sourceAssignment,
          targetSlotId: target.slotId,
          mergedCommit: integrated.mergedCommit,
          ...(effect ? { integrationEffectId: effect.effectId } : {}),
        });
        const batchReady = [...batchState.expectedAssignmentIds].every((assignmentId) =>
          batchState.entries.has(assignmentId)
        );
        if (!batchReady) {
          // The final branch in this wave will certify all receipts against
          // its merged HEAD. Until then every intermediate receipt remains
          // explicitly ineligible for review/gate promotion.
          reverificationRequired = true;
        } else {
          const batchEntries = [...batchState.expectedAssignmentIds].map(
            (assignmentId) => batchState.entries.get(assignmentId)!
          );
          const reverification = await reverifyMergedMathematicsBatch(
            batchEntries,
            capability.projectRoot,
            integrated.mergedCommit,
            runtime.context.certifyMathematics
          );
          if (reverification.verified) {
            const currentIndex = batchEntries.findIndex((entry) => entry.result.assignmentId === result.assignmentId);
            integratedResult = reverification.results[currentIndex] ?? result;
            const receipts = Object.freeze({
              ...(integratedResult.localGateReceipt ? { localGateReceipt: integratedResult.localGateReceipt } : {}),
              ...(integratedResult.mathNodeReceipt ? { mathNodeReceipt: integratedResult.mathNodeReceipt } : {}),
              ...(integratedResult.mathHelperReceipt ? { mathHelperReceipt: integratedResult.mathHelperReceipt } : {}),
            });
            reverifiedReceipts = hasReverifiedReceipt(receipts) ? receipts : undefined;
            reverified = Boolean(reverifiedReceipts);
            reverificationRequired = false;

            // The current event is persisted by presentEvent. Persist the
            // reverified receipts for earlier wave members here so a later
            // REVIEW/OFFICIAL_GATE read never sees stale intermediate flags.
            if (runtime.context.projectGit.completeResearchTeamAssignment) {
              for (const [index, entry] of batchEntries.entries()) {
                if (entry.result.assignmentId === result.assignmentId) continue;
                const verifiedResult = reverification.results[index];
                const verifiedReceipts = Object.freeze({
                  ...(verifiedResult.localGateReceipt ? { localGateReceipt: verifiedResult.localGateReceipt } : {}),
                  ...(verifiedResult.mathNodeReceipt ? { mathNodeReceipt: verifiedResult.mathNodeReceipt } : {}),
                  ...(verifiedResult.mathHelperReceipt ? { mathHelperReceipt: verifiedResult.mathHelperReceipt } : {}),
                });
                try {
                  runtime.context.projectGit.completeResearchTeamAssignment({
                    workspace: capability.projectRoot,
                    teamId: capability.teamId,
                    slotId: entry.targetSlotId,
                    assignmentId: entry.result.assignmentId,
                    integration: {
                      executionMode: 'artifact',
                      branch: entry.result.git.branch,
                      headCommit: entry.result.git.headCommit,
                      mergedCommit: integrated.mergedCommit,
                      ...(hasReverifiedReceipt(verifiedReceipts) ? { reverifiedReceipts: verifiedReceipts } : {}),
                    },
                  });
                  if (entry.integrationEffectId && runtime.context.mathIntegrationJournal) {
                    await runtime.context.mathIntegrationJournal.commit(entry.integrationEffectId, entry.mergedCommit);
                  }
                } catch (error) {
                  reverificationRequired = true;
                  reverificationError =
                    error instanceof Error ? error.message : `Unable to persist batch verification: ${String(error)}`;
                }
              }
            }
          } else if (reverification.error) {
            reverificationRequired = true;
            reverificationError = reverification.error;
            // The earlier members were intentionally left in `accepted`
            // state while the wave was pending. If the single final verifier
            // call fails, still close those integrations durably while
            // retaining the explicit reverification-required gate.
            if (runtime.context.projectGit.completeResearchTeamAssignment) {
              for (const entry of batchEntries) {
                try {
                  runtime.context.projectGit.completeResearchTeamAssignment({
                    workspace: capability.projectRoot,
                    teamId: capability.teamId,
                    slotId: entry.targetSlotId,
                    assignmentId: entry.result.assignmentId,
                    integration: {
                      executionMode: 'artifact',
                      branch: entry.result.git.branch,
                      headCommit: entry.result.git.headCommit,
                      mergedCommit: integrated.mergedCommit,
                      reverificationRequired: true,
                    },
                  });
                  if (entry.integrationEffectId && runtime.context.mathIntegrationJournal) {
                    await runtime.context.mathIntegrationJournal.commit(entry.integrationEffectId, entry.mergedCommit);
                  }
                } catch {
                  // The final event remains retryable; leave an unpersisted
                  // member for the next reconciliation pass to repair.
                }
              }
            }
          }
        }
      } else {
        const reverification = await reverifyMergedMathematics(
          result,
          sourceAssignment,
          capability.projectRoot,
          integrated.mergedCommit,
          runtime.context.certifyMathematics
        );
        if (reverification.verified) {
          integratedResult = reverification.result;
          const receipts = Object.freeze({
            ...(reverification.result.localGateReceipt
              ? { localGateReceipt: reverification.result.localGateReceipt }
              : {}),
            ...(reverification.result.mathNodeReceipt
              ? { mathNodeReceipt: reverification.result.mathNodeReceipt }
              : {}),
            ...(reverification.result.mathHelperReceipt
              ? { mathHelperReceipt: reverification.result.mathHelperReceipt }
              : {}),
          });
          reverifiedReceipts = hasReverifiedReceipt(receipts) ? receipts : undefined;
          reverified = true;
          reverificationRequired = false;
        } else if (reverification.error) {
          // Integration remains durable, but the old Worker receipt must stay
          // visibly ineligible for REVIEW/OFFICIAL_GATE until the next call can
          // certify the merged commit.
          reverificationRequired = true;
          reverificationError = reverification.error;
        }
      }
    }
    let solverReadyReceipt: MathSolverReadyReceipt | undefined;
    if (mathProgressControl?.solver_declared_complete === true && !reverificationRequired) {
      // The solver-ready attestation belongs to the canonical commit produced
      // by integration. `integratedResult.git.headCommit` is the Worker branch
      // head and differs whenever Git creates a merge commit.
      const mergedCommit = integrated.mergedCommit;
      const math = integratedResult.math;
      const secret = readMathematicsReceiptSecret();
      const certifiedCommits = [
        integratedResult.localGateReceipt?.targetCommit,
        integratedResult.mathNodeReceipt?.targetCommit,
        integratedResult.mathHelperReceipt?.targetCommit,
      ].filter((commit): commit is string => Boolean(commit));
      if (certifiedCommits.length && integratedResult.git.headCommit !== mergedCommit) {
        throw new ResearchTeamOrchestrationError(
          'solver_ready_identity_mismatch',
          'Solver-ready attestation requires kernel receipts bound to the canonical merged commit.'
        );
      }
      if (certifiedCommits.some((commit) => commit !== mergedCommit)) {
        throw new ResearchTeamOrchestrationError(
          'solver_ready_identity_mismatch',
          'Solver-ready attestation requires kernel receipts bound to the canonical merged commit.'
        );
      }
      if (secret && mergedCommit && math && certifiedCommits.length) {
        solverReadyReceipt = signMathSolverReadyReceipt(
          {
            teamId: capability.teamId,
            slotId: target.slotId,
            assignmentId: integratedResult.assignmentId,
            deliveryId: createProjectGitResearchTeamDeliveryId(
              capability.teamId,
              target.slotId,
              integratedResult.assignmentId
            ),
            targetCommit: mergedCommit,
            statementHash: math.statementHash,
            routeFingerprint: math.routeFingerprint,
            checkedAt: Date.now(),
          },
          secret
        );
      }
    }
    return Object.freeze({
      result: integratedResult,
      target,
      advisory: false,
      ...(sourceAssignment ? { sourceAssignment } : {}),
      ...(mathProgressControl ? { mathProgressControl } : {}),
      ...(researchContractUpdate ? { researchContractUpdate } : {}),
      branch: integrated.branch,
      deliveredHeadCommit: result.git.headCommit,
      mergedCommit: integrated.mergedCommit,
      ...(capability.profileId === 'mathematics-research-team' && result.math && reverificationRequired
        ? { reverificationRequired: true }
        : {}),
      ...(reverified ? { reverified: true } : {}),
      ...(reverifiedReceipts ? { reverifiedReceipts } : {}),
      ...(solverReadyReceipt ? { solverReadyReceipt } : {}),
      ...(reverificationError ? { reverificationError } : {}),
      ...(effect ? { integrationEffectId: effect.effectId } : {}),
      alreadyIntegrated: integrated.alreadyIntegrated === true,
    });
  },
  present: (event, runtime) => presentEvent(event, runtime),
});

// Lead-side fast path. Git metadata owns the durable assignment receipt; this
// index avoids rereading it between an accepted dispatch and integration.
const dispatchedAssignments = new Map<string, ResearchTeamAssignment>();
const dispatchedUsageBaselines = new Map<string, ResearchCoreAgentUsage>();
const dispatchedAssignmentOrder: string[] = [];
const MAX_DISPATCHED_ASSIGNMENT_INDEX = 2048;

const rememberDispatchedAssignment = (
  key: string,
  assignment: ResearchTeamAssignment,
  usageBaseline?: ResearchCoreAgentUsage
): void => {
  const previousIndex = dispatchedAssignmentOrder.indexOf(key);
  if (previousIndex >= 0) dispatchedAssignmentOrder.splice(previousIndex, 1);
  dispatchedAssignments.set(key, assignment);
  if (usageBaseline) dispatchedUsageBaselines.set(key, usageBaseline);
  else dispatchedUsageBaselines.delete(key);
  dispatchedAssignmentOrder.push(key);
  while (dispatchedAssignmentOrder.length > MAX_DISPATCHED_ASSIGNMENT_INDEX) {
    const oldest = dispatchedAssignmentOrder.shift();
    if (!oldest) break;
    dispatchedAssignments.delete(oldest);
    dispatchedUsageBaselines.delete(oldest);
  }
};

const forgetDispatchedAssignment = (key: string): void => {
  dispatchedAssignments.delete(key);
  dispatchedUsageBaselines.delete(key);
  let index = dispatchedAssignmentOrder.indexOf(key);
  while (index >= 0) {
    dispatchedAssignmentOrder.splice(index, 1);
    index = dispatchedAssignmentOrder.indexOf(key);
  }
};

/**
 * Cancellation is idempotent at the Core boundary.  Keep this operation
 * single-shot: if transport is unavailable, the durable supersession-pending
 * record is left for the next event/status reconciliation instead of blocking
 * the Lead turn behind synchronous backoff.
 */
const cancelAssignmentTurn = async (
  client: ResearchCoreTeamClient,
  teamId: string,
  teamRunId: string,
  slotId: string,
  reason: string
): Promise<void> => {
  if (!client.cancelChildTurn) throw new Error('Core child-turn cancellation is unavailable');
  try {
    await client.cancelChildTurn(teamId, teamRunId, slotId, reason);
  } catch (error) {
    // Core reports an already-finished slot as a 400. Treat that specific
    // state as idempotent cancellation; a different run/slot identity error
    // still needs to fail closed for recovery.
    if (error instanceof Error && /slot has no active batch:/u.test(error.message)) return;
    throw error;
  }
};

/**
 * A v2 reservation whose Worker worktree was never prepared has no Core turn
 * and no source. It must still block a new dispatch (the Lead retries the same
 * request to reuse it), but it cannot conflict with integrating a different,
 * already delivered assignment. Run 23 lost every integrate to this warning.
 */
const UNPREPARED_RESERVATION_WARNING = 'has not completed Worker preparation';
export const isUnpreparedReservationWarning = (warning: string): boolean =>
  warning.startsWith('Prepared assignment ') && warning.includes(UNPREPARED_RESERVATION_WARNING);

const reconcilePreparedResearchTeamAssignments = async (
  capability: ResearchTeamToolCapability,
  projectGit: ResearchTeamProjectGitDriver,
  client: ResearchCoreTeamClient,
  state: ResearchCoreRunState,
  validateAssignmentForRecovery: ResearchTeamAssignmentValidator,
  restoredReceipts?: readonly ProjectGitResearchTeamAssignmentReceipt[]
): Promise<string[]> => {
  if (capability.profileId !== 'mathematics-research-team' || !projectGit.listResearchTeamAssignments) return [];
  const warnings: string[] = [];
  let receipts: readonly ProjectGitResearchTeamAssignmentReceipt[];
  if (restoredReceipts) {
    receipts = restoredReceipts;
  } else {
    try {
      receipts = projectGit.listResearchTeamAssignments({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['prepared'],
      });
    } catch (error) {
      return [`Unable to inspect prepared assignments: ${error instanceof Error ? error.message : String(error)}`];
    }
  }
  const finalizePreparedCleanup = (
    receipt: ProjectGitResearchTeamAssignmentReceipt,
    discarded: ProjectGitDiscardAgentWorktreeResult
  ): void => {
    if (!discarded.ok || !discarded.discarded || discarded.preserved) {
      if (discarded.preserved) {
        warnings.push(
          `Unable to finalize prepared assignment ${receipt.assignmentId}: cleanup preserved the Worker worktree`
        );
      }
      return;
    }
    if (!projectGit.supersedeResearchTeamAssignment) {
      warnings.push(
        `Unable to finalize prepared assignment ${receipt.assignmentId}: supersession persistence is unavailable`
      );
      return;
    }
    const winnerAssignmentId = `recovery-${crypto
      .createHash('sha256')
      .update(`${receipt.teamId}\u0000${receipt.slotId}\u0000${receipt.assignmentId}`, 'utf8')
      .digest('hex')
      .slice(0, 24)}`;
    try {
      projectGit.supersedeResearchTeamAssignment({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        supersession: {
          winnerAssignmentId,
          reason: 'Prepared assignment became orphaned after Core run ended and its managed worktree was cleaned.',
        },
      });
    } catch (error) {
      warnings.push(
        `Unable to finalize prepared assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  };
  for (const receipt of receipts) {
    if (receipt.state !== 'prepared') continue;
    if (receipt.schema === 'deepscientist.research_team_assignment.v2' && !receipt.preparedGit?.worktreePath) {
      warnings.push(
        `Prepared assignment ${receipt.assignmentId} ${UNPREPARED_RESERVATION_WARNING}; retry the original dispatch request to prepare the same reservation before enqueueing.`
      );
      continue;
    }
    const slot = state.slots.find((candidate) => candidate.slotId === receipt.slotId);
    // A restricted or partially restored Core snapshot may omit the Worker
    // slot entirely.  That is not evidence that the prepared assignment was
    // rejected; preserve its worktree until a complete status snapshot can
    // establish the terminal state.
    if (!slot) {
      warnings.push(
        `Unable to reconcile prepared assignment ${receipt.assignmentId}: Worker slot is not visible in Core status`
      );
      continue;
    }
    const active = Boolean(
      state.activeSlotIds.includes(slot.slotId) ||
      slot.queuedForegroundCount > 0 ||
      slot.queuedBackgroundCount > 0 ||
      slot.pendingWakeCount > 0
    );
    if (active) {
      const teamRunId = slot?.teamRunId || state.teamRunId;
      if (!teamRunId) {
        warnings.push(`Prepared assignment ${receipt.assignmentId} is active but has no recoverable teamRunId.`);
        continue;
      }
      // A busy Worker slot is not proof that it is executing this prepared
      // assignment. Promote only when the durable receipt and Core snapshot
      // carry the same run identity; otherwise leave the reservation intact
      // for the idempotent recovery path below.
      if (!receipt.teamRunId || receipt.teamRunId !== teamRunId) {
        warnings.push(
          `Prepared assignment ${receipt.assignmentId} has no matching Core acknowledgement; refusing slot-only promotion.`
        );
        continue;
      }
      const target = capability.roster.find(
        (member) => member.slotId === receipt.slotId && member.roleKind === 'worker'
      );
      if (!target) continue;
      let assignment: ResearchTeamAssignment | undefined;
      try {
        if (receipt.schema === 'deepscientist.research_team_assignment.v2') {
          normalizeRuntimeMathAssignment(receipt.assignment);
        } else
          assignment = validateDurableResearchTeamAssignment(
            receipt.assignment,
            capability,
            target,
            validateAssignmentForRecovery
          );
        projectGit.recordResearchTeamAssignment?.({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: receipt.slotId,
          assignmentId: receipt.assignmentId,
          schema: receipt.schema,
          assignment: receipt.assignment,
          state: 'accepted',
          ...(receipt.preparedGit ? { preparedGit: receipt.preparedGit } : {}),
          ...(receipt.usageBaseline ? { usageBaseline: receipt.usageBaseline } : {}),
          teamRunId,
        });
        if (assignment)
          rememberDispatchedAssignment(
            `${capability.teamId}:${receipt.assignmentId}`,
            assignment,
            receipt.usageBaseline as ResearchCoreAgentUsage | undefined
          );
      } catch (error) {
        warnings.push(
          `Unable to promote prepared assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
        );
      }
      continue;
    }
    // A missing prepared worktree is definitive evidence that this WAL
    // reservation cannot be resumed. Reconcile it immediately even while a
    // different Lead run is active; waiting for global counters to reach zero
    // leaves the stale assignment blocking every retry of the same route.
    if (isOrphanedPreparedMathematicsAssignment(receipt) && projectGit.discardAgentWorktree) {
      const rawAssignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
      const rawGit = rawAssignment && isRecord(rawAssignment.git) ? rawAssignment.git : undefined;
      const branch = receipt.preparedGit?.branch || (typeof rawGit?.branch === 'string' ? rawGit.branch : undefined);
      const worktreePath =
        receipt.preparedGit?.worktreePath ||
        (typeof rawGit?.worktreePath === 'string' ? rawGit.worktreePath : undefined);
      // Private Lean-Eval worktrees live outside the ProjectGit managed roots
      // and may already be gone after a Core restart. There is nothing left
      // to delete in that case; transition the WAL reservation directly so it
      // cannot block a fresh route. Existing worktrees still go through the
      // protected ProjectGit cleanup path below.
      if (worktreePath && !fs.existsSync(worktreePath) && projectGit.supersedeResearchTeamAssignment) {
        const winnerAssignmentId = `recovery-${crypto
          .createHash('sha256')
          .update(`${receipt.teamId}\u0000${receipt.slotId}\u0000${receipt.assignmentId}`, 'utf8')
          .digest('hex')
          .slice(0, 24)}`;
        try {
          projectGit.supersedeResearchTeamAssignment({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: receipt.slotId,
            assignmentId: receipt.assignmentId,
            supersession: {
              winnerAssignmentId,
              reason:
                'Prepared assignment worktree is absent after the Core run ended; the orphaned reservation was superseded automatically.',
            },
          });
        } catch (error) {
          warnings.push(
            `Unable to finalize prepared assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
          );
        }
        continue;
      }
      try {
        const discarded = projectGit.discardAgentWorktree({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: receipt.slotId,
          assignmentId: receipt.assignmentId,
          preserveReceipt: true,
          ...(branch ? { branch } : {}),
          ...(worktreePath ? { worktreePath } : {}),
        });
        if (!discarded.ok && !discarded.preserved) {
          warnings.push(
            `Unable to discard orphan prepared assignment ${receipt.assignmentId}: ${discarded.error || 'cleanup failed'}`
          );
        }
        finalizePreparedCleanup(receipt, discarded);
      } catch (error) {
        warnings.push(
          `Unable to discard orphan prepared assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
        );
      }
      continue;
    }
    // Global run counters include the active Lead turn. The target Worker's
    // own slot projection above is the authority for whether its exact durable
    // assignment can be re-enqueued during that turn.
    const target = capability.roster.find((member) => member.slotId === receipt.slotId && member.roleKind === 'worker');
    if (!target) {
      warnings.push(`Unable to recover prepared assignment ${receipt.assignmentId}: Worker is not in the Team roster`);
      continue;
    }
    if (!projectGit.recordResearchTeamAssignment) {
      warnings.push(`Unable to recover prepared assignment ${receipt.assignmentId}: WAL promotion is unavailable`);
      continue;
    }
    try {
      let message: string;
      let recoveredV1Assignment: ResearchTeamAssignment | undefined;
      if (receipt.schema === 'deepscientist.research_team_assignment.v2') {
        const workers = new Set(
          capability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
        );
        message = JSON.stringify(
          runtimeMathAssignmentToResearchTeamEnvelope(receipt.assignment, {
            workerIds: workers,
            expectedTargetSlotId: receipt.slotId,
            ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
          })
        );
      } else {
        recoveredV1Assignment = validateDurableResearchTeamAssignment(
          receipt.assignment,
          capability,
          target,
          validateAssignmentForRecovery
        );
        message = projectMathematicsAssignmentForWorker(recoveredV1Assignment, target).serializedAssignment;
      }
      // Prepared work may have reached Core before its acknowledgement was lost.
      // Replay the original v2 key and bytes to reconcile that uncertain write.
      const recoveryTransportKey =
        receipt.schema === 'deepscientist.research_team_assignment.v2'
          ? normalizeRuntimeMathAssignment(receipt.assignment).request.idempotencyKey
          : createProjectGitResearchTeamTransportIdempotencyKey(
              `math-prepared-recovery:${capability.teamId}:${receipt.assignmentId}:${state.teamRunId ?? receipt.teamRunId ?? 'unbound'}`
            );
      const acknowledgement = await client.dispatch(
        capability.teamId,
        receipt.slotId,
        message,
        undefined,
        recoveryTransportKey,
        receipt.preparedGit?.worktreePath
      );
      if (
        acknowledgement.team_id !== capability.teamId ||
        acknowledgement.target_slot_id !== receipt.slotId ||
        acknowledgement.accepted_slot_id !== receipt.slotId ||
        acknowledgement.accepted_role !== 'teammate' ||
        !isTeamRunAckPersisted(acknowledgement)
      ) {
        throw new Error('Core did not persist the recovered prepared assignment dispatch.');
      }
      projectGit.recordResearchTeamAssignment({
        schema: receipt.schema,
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        assignment: receipt.assignment,
        state: 'accepted',
        teamRunId: acknowledgement.team_run_id,
        ...(receipt.usageBaseline ? { usageBaseline: receipt.usageBaseline } : {}),
        ...(receipt.preparedGit ? { preparedGit: receipt.preparedGit } : {}),
      });
      if (recoveredV1Assignment) {
        rememberDispatchedAssignment(
          `${capability.teamId}:${receipt.assignmentId}`,
          recoveredV1Assignment,
          receipt.usageBaseline as ResearchCoreAgentUsage | undefined
        );
      }
    } catch (error) {
      warnings.push(
        `Unable to recover prepared assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  return warnings;
};

const reconcilePendingResearchTeamIntegrations = (
  capability: ResearchTeamToolCapability,
  projectGit: ResearchTeamProjectGitDriver,
  receipts: readonly ProjectGitResearchTeamAssignmentReceipt[] | undefined
): string[] => {
  if (
    capability.profileId !== 'mathematics-research-team' ||
    !receipts?.length ||
    !projectGit.completeResearchTeamAssignment
  ) {
    return [];
  }
  const warnings: string[] = [];
  for (const receipt of receipts) {
    if (receipt.state !== 'accepted' || !receipt.integration) continue;
    if (
      receipt.integration.reverificationRequired === true ||
      receipt.integration.retainedWithoutMerge === true ||
      receipt.integration.verification
    )
      continue;
    try {
      projectGit.completeResearchTeamAssignment({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        integration: receipt.integration,
        ...(receipt.mathProgress ? { mathProgress: receipt.mathProgress } : {}),
      });
    } catch (error) {
      warnings.push(
        `Unable to promote pending integration ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  return warnings;
};

const restorePendingResearchTeamSupersessions = async (
  capability: ResearchTeamToolCapability,
  projectGit: ResearchTeamProjectGitDriver,
  client: ResearchCoreTeamClient,
  restoredReceipts?: readonly ProjectGitResearchTeamAssignmentReceipt[],
  supersededAssignmentIds?: Set<string>
): Promise<string[]> => {
  if (
    capability.profileId !== 'mathematics-research-team' ||
    !projectGit.listResearchTeamAssignments ||
    !projectGit.supersedeResearchTeamAssignment
  ) {
    return [];
  }
  const warnings: string[] = [];
  let receipts: readonly ProjectGitResearchTeamAssignmentReceipt[];
  if (restoredReceipts) {
    receipts = restoredReceipts;
  } else {
    try {
      receipts = projectGit.listResearchTeamAssignments({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['accepted'],
      });
    } catch (error) {
      return [`Unable to inspect pending supersessions: ${error instanceof Error ? error.message : String(error)}`];
    }
  }
  for (const receipt of receipts) {
    if (receipt.state !== 'accepted') continue;
    const pending = receipt.supersessionPending;
    if (!pending) continue;
    try {
      if (!receipt.teamRunId) {
        warnings.push(`Unable to cancel superseded assignment ${receipt.assignmentId}: missing teamRunId`);
        continue;
      }
      await cancelAssignmentTurn(
        client,
        capability.teamId,
        receipt.teamRunId,
        receipt.slotId,
        `Mathematics assignment ${receipt.assignmentId} was superseded by ${pending.winnerAssignmentId}`
      );
      projectGit.supersedeResearchTeamAssignment({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        supersession: pending,
      });
      supersededAssignmentIds?.add(receipt.assignmentId);
      forgetDispatchedAssignment(`${capability.teamId}:${receipt.assignmentId}`);
    } catch (error) {
      warnings.push(
        `Unable to retry supersession for ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  return warnings;
};

const restoreResearchTeamRuntimeState = async (
  capability: ResearchTeamToolCapability,
  projectGit: ResearchTeamProjectGitDriver,
  client: ResearchCoreTeamClient,
  restoredReceipts?: readonly ProjectGitResearchTeamAssignmentReceipt[],
  validateAssignmentForRecovery?: ResearchTeamAssignmentValidator,
  state?: ResearchCoreRunState
): Promise<readonly string[]> => {
  let warnings = await restorePendingResearchTeamSupersessions(capability, projectGit, client, restoredReceipts);
  if (capability.profileId !== 'mathematics-research-team' || !projectGit.listResearchTeamAssignments) {
    return warnings;
  }

  // Prepared receipts are write-ahead reservations rather than accepted Core
  // work. Reconcile them before attempting accepted-assignment recovery so a
  // stale reservation cannot keep the slot or route history blocked.
  let preparedState = state;
  if (!preparedState) {
    try {
      await client.ensureSession?.(capability.teamId);
      preparedState = await client.readRunState(capability.teamId, undefined, true);
    } catch (error) {
      return [
        ...warnings,
        `Unable to inspect Core state for prepared assignment recovery: ${error instanceof Error ? error.message : String(error)}`,
      ];
    }
  }
  if (preparedState) {
    warnings = [
      ...warnings,
      ...(await reconcilePreparedResearchTeamAssignments(
        capability,
        projectGit,
        client,
        preparedState,
        validateAssignmentForRecovery ?? validateAssignment,
        restoredReceipts
      )),
    ];
  }

  // Prepared reconciliation only needs the assignment reader and cleanup
  // ports. Accepted assignment requeueing below additionally needs the WAL
  // writer; a missing writer must not disable prepared cleanup.
  if (!projectGit.recordResearchTeamAssignment) return warnings;

  // Core keeps a failed run's assignment receipt, but the queue item belongs
  // to the failed run and is gone. Rebind the exact durable assignment to the
  // current run and enqueue it on the existing Worker slot. This is deliberately
  // performed from recovery/status paths so a Lead does not need to redispatch
  // a compact payload (which would be rejected as an identity conflict).
  let currentState = preparedState;
  if (!currentState) {
    try {
      await client.ensureSession?.(capability.teamId);
      currentState = await client.readRunState(capability.teamId, undefined, true);
    } catch (error) {
      return [
        ...warnings,
        `Unable to inspect Core state for accepted assignment recovery: ${error instanceof Error ? error.message : String(error)}`,
      ];
    }
  }
  if (!currentState?.teamRunId) return warnings;

  let receipts = restoredReceipts;
  if (!receipts) {
    try {
      receipts = projectGit.listResearchTeamAssignments?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['accepted'],
        strict: true,
      });
    } catch (error) {
      return [
        ...warnings,
        `Unable to inspect accepted assignments for recovery: ${error instanceof Error ? error.message : String(error)}`,
      ];
    }
  }
  if (!receipts?.length) return warnings;

  for (const receipt of receipts) {
    if (
      receipt.state !== 'accepted' ||
      receipt.delivery ||
      receipt.integration ||
      receipt.supersessionPending ||
      receipt.budgetCancellation
    ) {
      continue;
    }
    if (receipt.schema === 'deepscientist.research_team_assignment.v2' && !receipt.preparedGit?.worktreePath) {
      warnings.push(
        `Accepted assignment ${receipt.assignmentId} is missing its Worker binding; retry the original dispatch request to recover that binding before resuming.`
      );
      continue;
    }
    const target = capability.roster.find((member) => member.roleKind === 'worker' && member.slotId === receipt.slotId);
    const slot = currentState.slots.find((candidate) => candidate.slotId === receipt.slotId);
    if (!target || !slot) continue;
    const slotHasWork = Boolean(
      currentState.activeSlotIds.includes(slot.slotId) ||
      slot.queuedForegroundCount > 0 ||
      slot.queuedBackgroundCount > 0 ||
      slot.pendingWakeCount > 0
    );
    if (slotHasWork) continue;
    // A receipt already bound to this run can still be orphaned after a
    // terminal Worker turn, so the state check above is authoritative.
    try {
      // Mathematics v2 receipts carry a runtime assignment contract, not the
      // legacy ResearchTeamAssignment v1 shape.  Recovery must preserve that
      // protocol and project it through the v2 envelope; routing it through
      // the v1 validator strands otherwise valid accepted work after a Core
      // restart with `assignment must use ...assignment.v1`.
      let recoveredV1Assignment: ResearchTeamAssignment | undefined;
      let serializedAssignment: string;
      if (receipt.schema === 'deepscientist.research_team_assignment.v2') {
        const workers = new Set(
          capability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
        );
        serializedAssignment = JSON.stringify(
          runtimeMathAssignmentToResearchTeamEnvelope(receipt.assignment, {
            workerIds: workers,
            expectedTargetSlotId: receipt.slotId,
            ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
          })
        );
      } else {
        recoveredV1Assignment = validateAssignmentForRecovery
          ? validateDurableResearchTeamAssignment(receipt.assignment, capability, target, validateAssignmentForRecovery)
          : (receipt.assignment as ResearchTeamAssignment);
        serializedAssignment = projectMathematicsAssignmentForWorker(
          recoveredV1Assignment,
          target
        ).serializedAssignment;
      }
      // The durable assignment id identifies the local WAL record, but it is
      // not a safe Core transport key across Team runs. Core binds an
      // idempotency key to the complete mailbox payload and retains that
      // binding after a run ends. Include the current run so recovery creates
      // a fresh mailbox row after a previous row was consumed, while retries
      // within this run remain idempotent.
      const recoveryTransportKey = createProjectGitResearchTeamTransportIdempotencyKey(
        `math-recovery:${capability.teamId}:${receipt.assignmentId}:${currentState.teamRunId}`
      );
      const acknowledgement = await client.dispatch(
        capability.teamId,
        receipt.slotId,
        serializedAssignment,
        undefined,
        recoveryTransportKey,
        receipt.preparedGit?.worktreePath
      );
      if (
        acknowledgement.team_id !== capability.teamId ||
        acknowledgement.target_slot_id !== receipt.slotId ||
        acknowledgement.accepted_slot_id !== receipt.slotId ||
        acknowledgement.accepted_role !== 'teammate' ||
        !isTeamRunAckPersisted(acknowledgement)
      ) {
        throw new Error('Core did not persist the recovered assignment dispatch.');
      }
      projectGit.recordResearchTeamAssignment({
        schema: receipt.schema,
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        assignment: receipt.assignment,
        state: 'accepted',
        teamRunId: acknowledgement.team_run_id,
        ...(receipt.usageBaseline ? { usageBaseline: receipt.usageBaseline } : {}),
        ...(receipt.preparedGit ? { preparedGit: receipt.preparedGit } : {}),
      });
      if (recoveredV1Assignment) {
        rememberDispatchedAssignment(
          `${capability.teamId}:${receipt.assignmentId}`,
          recoveredV1Assignment,
          receipt.usageBaseline as ResearchCoreAgentUsage | undefined
        );
      }
    } catch (error) {
      warnings.push(
        `Unable to requeue accepted assignment ${receipt.assignmentId}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  return warnings;
};

type MathematicsReverification = Readonly<{
  result: ResearchTeamResult;
  verified: boolean;
  error?: string;
}>;

type MathematicsBatchReverificationInput = Readonly<{
  result: ResearchTeamResult;
  assignment: ResearchTeamAssignment | undefined;
}>;

type MathematicsBatchReverification = Readonly<{
  results: readonly ResearchTeamResult[];
  verified: boolean;
  error?: string;
}>;

type MathematicsBatchReverificationState = {
  expectedAssignmentIds: ReadonlySet<string>;
  entries: Map<
    string,
    MathematicsBatchReverificationInput & {
      targetSlotId: string;
      mergedCommit: string;
      integrationEffectId?: string;
    }
  >;
};

/**
 * A Worker receipt is bound to its branch head. A no-ff merge creates a new
 * Lead commit, so the old receipt cannot be promoted merely because the tree
 * looks similar. Re-run the kernel against the merged commit and rebuild the
 * receipt from verifier output. The proof path is resolved only from the
 * Worker-owned artifact list and is additionally content-hash checked.
 */
async function reverifyMergedMathematics(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined,
  projectRoot: string,
  mergedCommit: string,
  certify: ((request: MathematicsVerifierBatchRequest) => Promise<MathematicsVerifierBatchResult>) | undefined
): Promise<MathematicsReverification> {
  if (!result.math || (!result.localGateReceipt && !result.mathNodeReceipt && !result.mathHelperReceipt)) {
    return Object.freeze({ result, verified: true });
  }
  if (!certify) {
    return Object.freeze({
      result,
      verified: false,
      error: 'Merged commit requires a fresh Lean receipt, but the Mathematics certifier is unavailable.',
    });
  }

  const candidatePaths = [...result.artifactPaths, ...(assignment?.math?.artifactPaths ?? [])];
  const proofPathByHash = new Map<string, string | undefined>();
  const proofHashByPath = new Map<string, string | undefined>();
  const proofPathForHash = (proofHash: string): string | undefined => {
    if (proofPathByHash.has(proofHash)) return proofPathByHash.get(proofHash);
    for (const candidate of candidatePaths) {
      const proofPath = projectRelativeLeanArtifactPath(projectRoot, candidate);
      if (!proofPath) continue;
      const absolute = path.resolve(projectRoot, proofPath);
      if (!proofHashByPath.has(proofPath)) {
        try {
          proofHashByPath.set(proofPath, crypto.createHash('sha256').update(fs.readFileSync(absolute)).digest('hex'));
        } catch {
          // A stale artifact path is ignored; the final error is explicit below.
          proofHashByPath.set(proofPath, undefined);
        }
      }
      if (proofHashByPath.get(proofPath) === proofHash) {
        proofPathByHash.set(proofHash, proofPath);
        return proofPath;
      }
    }
    proofPathByHash.set(proofHash, undefined);
    return undefined;
  };

  const receipts: Array<
    | { kind: 'local'; receipt: MathLocalGateReceipt }
    | { kind: 'node'; receipt: MathNodeProofReceipt }
    | { kind: 'helper'; receipt: MathHelperReceipt }
  > = [];
  if (result.localGateReceipt) receipts.push({ kind: 'local', receipt: result.localGateReceipt });
  if (result.mathNodeReceipt) receipts.push({ kind: 'node', receipt: result.mathNodeReceipt });
  if (result.mathHelperReceipt) receipts.push({ kind: 'helper', receipt: result.mathHelperReceipt });
  const prepared = receipts.map(({ kind, receipt }, index) => ({
    kind,
    receipt,
    claim: kind === 'local' ? receipt.claim || 'statement' : ('statement' as const),
    proofPath: proofPathForHash(receipt.proofHash),
    expectedSourceDeclarationHash:
      kind === 'local'
        ? assignment?.math?.problemContract
          ? hashMathFormalSourceDeclaration(
              receipt.claim === 'negation'
                ? assignment.math.problemContract.formalNegationStatement || ''
                : assignment.math.problemContract.formalStatement,
              receipt.theoremName
            )
          : undefined
        : kind === 'node'
          ? (() => {
              const nodeReceipt = receipt as MathNodeProofReceipt;
              const route = assignment?.math?.routeCards?.find(
                (card) => card.routeFingerprint === assignment.math?.routeFingerprint
              );
              const node = route?.planNodes.find((candidate) => candidate.id === nodeReceipt.planNodeId);
              return node
                ? hashMathFormalSourceDeclaration(node.provisionalLeanStatement, nodeReceipt.theoremName)
                : undefined;
            })()
          : (() => {
              const helperReceipt = receipt as MathHelperReceipt;
              const node = result.math?.planAfter?.planNodes.find(
                (candidate) => candidate.id === helperReceipt.helperPlanNodeId
              );
              return node
                ? hashMathFormalSourceDeclaration(node.provisionalLeanStatement, helperReceipt.declarationName)
                : undefined;
            })(),
    id: `merged-reverification-${kind}-${index + 1}`,
  }));
  const missing = prepared.find((item) => !item.proofPath);
  if (missing) {
    return Object.freeze({
      result,
      verified: false,
      error: `Unable to locate the committed Lean proof for ${missing.kind} receipt ${missing.receipt.receiptId}.`,
    });
  }
  const unbound = prepared.find((item) => !item.expectedSourceDeclarationHash);
  if (unbound) {
    return Object.freeze({
      result,
      verified: false,
      error: `Unable to bind ${unbound.kind} receipt ${unbound.receipt.receiptId} to its frozen Lean declaration.`,
    });
  }

  let batch: MathematicsVerifierBatchResult;
  try {
    batch = await certify({
      projectRoot,
      targetCommit: mergedCommit,
      items: prepared.map((item) => ({
        id: item.id,
        proofPath: item.proofPath!,
        theoremName:
          item.kind === 'helper'
            ? (item.receipt as MathHelperReceipt).declarationName
            : (item.receipt as MathLocalGateReceipt | MathNodeProofReceipt).theoremName,
        statementHash: item.receipt.statementHash,
        ...(item.kind === 'local' && assignment?.math?.problemContract
          ? {
              leanStatementHash:
                item.claim === 'negation'
                  ? assignment.math.problemContract.leanNegationHash
                  : assignment.math.problemContract.leanStatementHash,
            }
          : item.kind === 'local' && (item.receipt as MathLocalGateReceipt).leanStatementHash
            ? { leanStatementHash: (item.receipt as MathLocalGateReceipt).leanStatementHash }
            : {}),
        expectedSourceDeclarationHash: item.expectedSourceDeclarationHash!,
        claim: item.claim,
      })),
    });
  } catch (error) {
    return Object.freeze({ result, verified: false, error: error instanceof Error ? error.message : String(error) });
  }
  if (
    batch.status !== 'kernel_verified' ||
    batch.targetCommit.toLowerCase() !== mergedCommit.toLowerCase() ||
    batch.results.length !== prepared.length
  ) {
    return Object.freeze({
      result,
      verified: false,
      error: `Lean certification returned an incomplete batch for merged commit ${mergedCommit}.`,
    });
  }
  const byId = new Map(batch.results.map((item) => [item.checkId, item]));
  if (byId.size !== batch.results.length) {
    return Object.freeze({
      result,
      verified: false,
      error: 'Lean certification returned duplicate check identities during merged re-verification.',
    });
  }
  const failed = prepared.find((item) => {
    const verification = byId.get(item.id);
    return (
      !verification ||
      verification.checkId !== item.id ||
      verification.status !== 'kernel_verified' ||
      verification.verifier !== 'lean-kernel' ||
      verification.targetCommit.toLowerCase() !== mergedCommit.toLowerCase() ||
      verification.proofPath !== item.proofPath ||
      verification.statementHash !== item.receipt.statementHash ||
      verification.claim !== item.claim ||
      verification.goalsRemaining !== 0 ||
      verification.sorryCount !== 0 ||
      verification.admitCount !== 0 ||
      !verification.axioms.every(isMathFoundationalLeanAxiom) ||
      !verification.receiptId.trim() ||
      (item.kind === 'local' &&
        ((item.claim === 'negation'
          ? assignment?.math?.problemContract?.leanNegationHash
          : assignment?.math?.problemContract?.leanStatementHash) ||
          (item.receipt as MathLocalGateReceipt).leanStatementHash) !== undefined &&
        verification.leanStatementHash !==
          ((item.claim === 'negation'
            ? assignment?.math?.problemContract?.leanNegationHash
            : assignment?.math?.problemContract?.leanStatementHash) ||
            (item.receipt as MathLocalGateReceipt).leanStatementHash)) ||
      verification.proofHash !== item.receipt.proofHash ||
      verification.theoremName !==
        (item.kind === 'helper'
          ? (item.receipt as MathHelperReceipt).declarationName
          : (item.receipt as MathLocalGateReceipt | MathNodeProofReceipt).theoremName) ||
      !verification.theoremDeclarationHash ||
      verification.theoremDeclarationHash !==
        (item.kind === 'helper'
          ? (item.receipt as MathHelperReceipt).declarationHash
          : (item.receipt as MathLocalGateReceipt | MathNodeProofReceipt).theoremDeclarationHash) ||
      verification.sourceDeclarationHash !== item.expectedSourceDeclarationHash
    );
  });
  if (failed) {
    const verification = byId.get(failed.id);
    return Object.freeze({
      result,
      verified: false,
      error:
        verification?.error ||
        `Lean certification did not reproduce the ${failed.kind} receipt on merged commit ${mergedCommit}.`,
    });
  }

  let localGateReceipt: MathLocalGateReceipt | undefined;
  let mathNodeReceipt: MathNodeProofReceipt | undefined;
  let mathHelperReceipt: MathHelperReceipt | undefined;
  for (const item of prepared) {
    const verification = byId.get(item.id)!;
    const common = {
      receiptId: verification.receiptId,
      targetCommit: mergedCommit,
      statementHash: item.receipt.statementHash,
      ...(item.kind === 'local' ? { claim: item.claim } : {}),
      ...(item.kind === 'local' && assignment?.math?.problemContract
        ? {
            leanStatementHash:
              item.claim === 'negation'
                ? assignment.math.problemContract.leanNegationHash
                : assignment.math.problemContract.leanStatementHash,
          }
        : item.kind === 'local' && (item.receipt as MathLocalGateReceipt).leanStatementHash
          ? { leanStatementHash: (item.receipt as MathLocalGateReceipt).leanStatementHash }
          : {}),
      routeFingerprint: item.receipt.routeFingerprint,
      status: 'kernel_verified' as const,
      verifier: 'lean-kernel' as const,
      proofHash: verification.proofHash,
      theoremDeclarationHash: verification.theoremDeclarationHash!,
      sourceDeclarationHash: verification.sourceDeclarationHash!,
      goalsRemaining: 0 as const,
      sorryCount: 0 as const,
      admitCount: 0 as const,
      axioms: Object.freeze([]),
      checkedAt: verification.checkedAt,
    };
    if (item.kind === 'local') {
      localGateReceipt = normalizeMathLocalGateReceipt({ ...common, theoremName: verification.theoremName! });
    } else if (item.kind === 'node') {
      mathNodeReceipt = normalizeMathNodeProofReceipt({
        ...common,
        theoremName: verification.theoremName!,
        planNodeId: (item.receipt as MathNodeProofReceipt).planNodeId,
      });
    } else {
      const prior = item.receipt as MathHelperReceipt;
      mathHelperReceipt = normalizeMathHelperReceipt({
        ...prior,
        receiptId: verification.receiptId,
        targetCommit: mergedCommit,
        declarationName: verification.theoremName!,
        proofHash: verification.proofHash,
        declarationHash: verification.theoremDeclarationHash!,
        sourceDeclarationHash: verification.sourceDeclarationHash!,
        checkedAt: verification.checkedAt,
      });
    }
  }
  const nextResult = Object.freeze({
    ...result,
    git: Object.freeze({ ...result.git, headCommit: mergedCommit }),
    ...(localGateReceipt ? { localGateReceipt } : {}),
    ...(mathNodeReceipt ? { mathNodeReceipt } : {}),
    ...(mathHelperReceipt ? { mathHelperReceipt } : {}),
  });
  return Object.freeze({ result: nextResult, verified: true });
}

/**
 * Certify every receipt produced by one artifact integration wave against the
 * final Lead commit in one verifier batch.  No-ff merges change commit
 * identity, so verifying each intermediate commit repeats the same Lean
 * preparation and import compilation.  The final commit is still checked for
 * every unique proof/theorem pair; only the redundant intermediate checks are
 * removed.
 */
async function reverifyMergedMathematicsBatch(
  entries: readonly MathematicsBatchReverificationInput[],
  projectRoot: string,
  mergedCommit: string,
  certify: ((request: MathematicsVerifierBatchRequest) => Promise<MathematicsVerifierBatchResult>) | undefined
): Promise<MathematicsBatchReverification> {
  const results = entries.map(({ result }) => result);
  const activeEntries = entries.filter(
    ({ result }) =>
      Boolean(result.math) && Boolean(result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt)
  );
  if (!activeEntries.length) return Object.freeze({ results, verified: true });
  if (!certify) {
    return Object.freeze({
      results,
      verified: false,
      error: 'Merged commit requires a fresh Lean receipt, but the Mathematics certifier is unavailable.',
    });
  }

  type ReceiptEntry =
    | { kind: 'local'; receipt: MathLocalGateReceipt }
    | { kind: 'node'; receipt: MathNodeProofReceipt }
    | { kind: 'helper'; receipt: MathHelperReceipt };
  type PreparedReceipt = Readonly<{
    entryIndex: number;
    kind: ReceiptEntry['kind'];
    receipt: ReceiptEntry['receipt'];
    claim: 'statement' | 'negation';
    proofPath: string;
    expectedSourceDeclarationHash: string;
    expectedLeanStatementHash?: string;
    verificationId: string;
  }>;

  const prepared: PreparedReceipt[] = [];
  const verificationItems = new Map<string, MathematicsVerifierBatchItem>();
  // Different declaration selectors may intentionally share one Lean file.
  // Cache its content hash across the whole wave instead of rereading and
  // hashing the same source once per assignment.
  const proofHashByPath = new Map<string, string | undefined>();
  for (const [entryIndex, entry] of entries.entries()) {
    const { result, assignment } = entry;
    if (!result.math) continue;
    const receipts: ReceiptEntry[] = [];
    if (result.localGateReceipt) receipts.push({ kind: 'local', receipt: result.localGateReceipt });
    if (result.mathNodeReceipt) receipts.push({ kind: 'node', receipt: result.mathNodeReceipt });
    if (result.mathHelperReceipt) receipts.push({ kind: 'helper', receipt: result.mathHelperReceipt });
    if (!receipts.length) continue;

    const candidatePaths = [...result.artifactPaths, ...(assignment?.math?.artifactPaths ?? [])];
    const proofPathForHash = (proofHash: string): string | undefined => {
      for (const candidate of candidatePaths) {
        const proofPath = projectRelativeLeanArtifactPath(projectRoot, candidate);
        if (!proofPath) continue;
        const absolute = path.resolve(projectRoot, proofPath);
        if (!proofHashByPath.has(proofPath)) {
          try {
            proofHashByPath.set(proofPath, crypto.createHash('sha256').update(fs.readFileSync(absolute)).digest('hex'));
          } catch {
            proofHashByPath.set(proofPath, undefined);
          }
        }
        if (proofHashByPath.get(proofPath) === proofHash) return proofPath;
      }
      return undefined;
    };

    for (const { kind, receipt } of receipts) {
      const proofPath = proofPathForHash(receipt.proofHash);
      if (!proofPath) {
        return Object.freeze({
          results,
          verified: false,
          error: `Unable to locate the committed Lean proof for ${kind} receipt ${receipt.receiptId}.`,
        });
      }
      const expectedSourceDeclarationHash =
        kind === 'local'
          ? assignment?.math?.problemContract
            ? hashMathFormalSourceDeclaration(
                receipt.claim === 'negation'
                  ? assignment.math.problemContract.formalNegationStatement || ''
                  : assignment.math.problemContract.formalStatement,
                receipt.theoremName
              )
            : undefined
          : kind === 'node'
            ? (() => {
                const nodeReceipt = receipt as MathNodeProofReceipt;
                const route = assignment?.math?.routeCards?.find(
                  (card) => card.routeFingerprint === assignment.math?.routeFingerprint
                );
                const node = route?.planNodes.find((candidate) => candidate.id === nodeReceipt.planNodeId);
                return node
                  ? hashMathFormalSourceDeclaration(node.provisionalLeanStatement, nodeReceipt.theoremName)
                  : undefined;
              })()
            : (() => {
                const helperReceipt = receipt as MathHelperReceipt;
                const node = result.math?.planAfter?.planNodes.find(
                  (candidate) => candidate.id === helperReceipt.helperPlanNodeId
                );
                return node
                  ? hashMathFormalSourceDeclaration(node.provisionalLeanStatement, helperReceipt.declarationName)
                  : undefined;
              })();
      if (!expectedSourceDeclarationHash) {
        return Object.freeze({
          results,
          verified: false,
          error: `Unable to bind ${kind} receipt ${receipt.receiptId} to its frozen Lean declaration.`,
        });
      }
      const claim = kind === 'local' ? receipt.claim || 'statement' : ('statement' as const);
      const expectedLeanStatementHash =
        kind === 'local'
          ? assignment?.math?.problemContract
            ? claim === 'negation'
              ? assignment.math.problemContract.leanNegationHash
              : assignment.math.problemContract.leanStatementHash
            : (receipt as MathLocalGateReceipt).leanStatementHash
          : undefined;
      const theoremName = kind === 'helper' ? receipt.declarationName : receipt.theoremName;
      const verificationKey = [
        proofPath,
        kind,
        receipt.statementHash,
        theoremName,
        expectedSourceDeclarationHash,
        expectedLeanStatementHash ?? '',
      ].join('\0');
      let verificationId: string | undefined;
      for (const [id, item] of verificationItems) {
        if (
          [
            item.proofPath,
            kind,
            item.statementHash,
            item.theoremName,
            item.expectedSourceDeclarationHash,
            item.leanStatementHash ?? '',
          ].join('\0') === verificationKey
        ) {
          verificationId = id;
          break;
        }
      }
      if (!verificationItems.has(verificationId ?? '')) {
        verificationId = `merged-reverification-batch-${verificationItems.size + 1}`;
        verificationItems.set(verificationId, {
          id: verificationId,
          proofPath,
          theoremName,
          statementHash: receipt.statementHash,
          ...(expectedLeanStatementHash ? { leanStatementHash: expectedLeanStatementHash } : {}),
          expectedSourceDeclarationHash,
          claim,
        });
      }
      prepared.push({
        entryIndex,
        kind,
        receipt,
        claim,
        proofPath,
        expectedSourceDeclarationHash,
        ...(expectedLeanStatementHash ? { expectedLeanStatementHash } : {}),
        verificationId,
      });
    }
  }

  let batch: MathematicsVerifierBatchResult;
  try {
    batch = await certify({
      projectRoot,
      targetCommit: mergedCommit,
      items: [...verificationItems.values()],
    });
  } catch (error) {
    return Object.freeze({ results, verified: false, error: error instanceof Error ? error.message : String(error) });
  }
  if (
    batch.status !== 'kernel_verified' ||
    batch.targetCommit.toLowerCase() !== mergedCommit.toLowerCase() ||
    batch.results.length !== verificationItems.size
  ) {
    return Object.freeze({
      results,
      verified: false,
      error: `Lean certification returned an incomplete batch for merged commit ${mergedCommit}.`,
    });
  }
  const byId = new Map(batch.results.map((item) => [item.checkId, item]));
  if (byId.size !== batch.results.length) {
    return Object.freeze({
      results,
      verified: false,
      error: 'Lean certification returned duplicate check identities during merged re-verification.',
    });
  }
  for (const item of prepared) {
    const verification = byId.get(item.verificationId);
    const theoremName =
      item.kind === 'helper'
        ? (item.receipt as MathHelperReceipt).declarationName
        : (item.receipt as MathLocalGateReceipt | MathNodeProofReceipt).theoremName;
    if (
      !verification ||
      verification.checkId !== item.verificationId ||
      verification.status !== 'kernel_verified' ||
      verification.verifier !== 'lean-kernel' ||
      verification.targetCommit.toLowerCase() !== mergedCommit.toLowerCase() ||
      verification.proofPath !== item.proofPath ||
      verification.statementHash !== item.receipt.statementHash ||
      verification.claim !== item.claim ||
      verification.goalsRemaining !== 0 ||
      verification.sorryCount !== 0 ||
      verification.admitCount !== 0 ||
      !verification.axioms.every(isMathFoundationalLeanAxiom) ||
      !verification.receiptId.trim() ||
      (item.expectedLeanStatementHash !== undefined &&
        verification.leanStatementHash !== item.expectedLeanStatementHash) ||
      verification.proofHash !== item.receipt.proofHash ||
      verification.theoremName !== theoremName ||
      !verification.theoremDeclarationHash ||
      verification.theoremDeclarationHash !==
        (item.kind === 'helper'
          ? (item.receipt as MathHelperReceipt).declarationHash
          : (item.receipt as MathLocalGateReceipt | MathNodeProofReceipt).theoremDeclarationHash) ||
      verification.sourceDeclarationHash !== item.expectedSourceDeclarationHash
    ) {
      return Object.freeze({
        results,
        verified: false,
        error:
          verification?.error ||
          `Lean certification did not reproduce the ${item.kind} receipt on merged commit ${mergedCommit}.`,
      });
    }
  }

  const nextResults = results.map((result, entryIndex) => {
    const own = prepared.filter((item) => item.entryIndex === entryIndex);
    if (!own.length) return result;
    let localGateReceipt: MathLocalGateReceipt | undefined;
    let mathNodeReceipt: MathNodeProofReceipt | undefined;
    let mathHelperReceipt: MathHelperReceipt | undefined;
    for (const item of own) {
      const verification = byId.get(item.verificationId)!;
      const common = {
        receiptId: verification.receiptId,
        targetCommit: mergedCommit,
        statementHash: item.receipt.statementHash,
        ...(item.kind === 'local' ? { claim: item.claim } : {}),
        ...(item.expectedLeanStatementHash ? { leanStatementHash: item.expectedLeanStatementHash } : {}),
        routeFingerprint: item.receipt.routeFingerprint,
        status: 'kernel_verified' as const,
        verifier: 'lean-kernel' as const,
        proofHash: verification.proofHash,
        theoremDeclarationHash: verification.theoremDeclarationHash!,
        sourceDeclarationHash: verification.sourceDeclarationHash!,
        goalsRemaining: 0 as const,
        sorryCount: 0 as const,
        admitCount: 0 as const,
        axioms: Object.freeze([]),
        checkedAt: verification.checkedAt,
      };
      if (item.kind === 'local') {
        localGateReceipt = normalizeMathLocalGateReceipt({ ...common, theoremName: verification.theoremName! });
      } else if (item.kind === 'node') {
        mathNodeReceipt = normalizeMathNodeProofReceipt({
          ...common,
          theoremName: verification.theoremName!,
          planNodeId: (item.receipt as MathNodeProofReceipt).planNodeId,
        });
      } else {
        mathHelperReceipt = normalizeMathHelperReceipt({
          ...(item.receipt as MathHelperReceipt),
          receiptId: verification.receiptId,
          targetCommit: mergedCommit,
          declarationName: verification.theoremName!,
          proofHash: verification.proofHash,
          declarationHash: verification.theoremDeclarationHash!,
          sourceDeclarationHash: verification.sourceDeclarationHash!,
          checkedAt: verification.checkedAt,
        });
      }
    }
    return Object.freeze({
      ...result,
      git: Object.freeze({ ...result.git, headCommit: mergedCommit }),
      ...(localGateReceipt ? { localGateReceipt } : {}),
      ...(mathNodeReceipt ? { mathNodeReceipt } : {}),
      ...(mathHelperReceipt ? { mathHelperReceipt } : {}),
    });
  });
  return Object.freeze({ results: nextResults, verified: true });
}

async function dispatchRuntimeMathAssignments(
  values: readonly ResearchTeamDispatchItemInput[],
  context: ResearchTeamToolContext
): Promise<ToolResult> {
  const registry = context.mathAssignmentRegistry;
  if (!registry)
    throw new ResearchTeamOrchestrationError(
      'math_v2_dispatch_unavailable',
      'The v2 assignment registry is unavailable.'
    );
  const capability = context.capability;
  const client = requireClient(context.client);
  const workers = new Set(
    capability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
  );
  const items: Record<string, unknown>[] = [];
  const prepareV2Worktree = async (
    receipt: ProjectGitResearchTeamAssignmentReceipt,
    runtimeAssignment: ReturnType<typeof normalizeRuntimeMathAssignment>,
    replaying: boolean
  ): Promise<ProjectGitResearchTeamPreparedGit> => {
    if (!context.prepareMathV2Worktree) {
      throw new ResearchTeamOrchestrationError(
        'agent_worktree_unavailable',
        'The accepted v2 assignment is missing its Worker worktree binding and this runtime cannot recover it.',
        true
      );
    }
    const target = capability.roster.find((member) => member.slotId === receipt.slotId && member.roleKind === 'worker');
    if (!target?.laneId)
      throw new ResearchTeamOrchestrationError(
        'foreign_or_lead_slot',
        'The v2 assignment target is not a Worker lane.'
      );
    const prepared = context.projectGit?.prepareAgentWorktree({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: receipt.slotId,
      roleId: target.roleId,
      strategyLane: target.laneId,
      assignmentId: receipt.assignmentId,
      orchestrationNamespace: gitNamespace(capability),
      workflowId: capability.workflowId,
      objective: runtimeAssignment.request.objective,
      from: runtimeAssignment.baseCommit,
    });
    if (!prepared?.ok || !prepared.branch?.name || !prepared.workspace || !prepared.branch.baseCommit)
      throw new ResearchTeamOrchestrationError(
        'agent_worktree_unavailable',
        prepared?.error || 'Unable to prepare the v2 Worker worktree.',
        true
      );
    const preparedSources = context.prepareMathV2AssignmentSources
      ? await context.prepareMathV2AssignmentSources({
          assignment: runtimeAssignment,
          worktreePath: prepared.workspace,
          replaying,
        })
      : undefined;
    return {
      branch: prepared.branch.name,
      worktreePath: prepared.workspace,
      baseCommit: prepared.branch.baseCommit,
      ...(preparedSources
        ? {
            actualBaseCommit: prepared.branch.baseCommit,
            progressBaseCommit: prepared.branch.baseCommit,
            solverProjectRoot: preparedSources.solverProjectRoot,
          }
        : {}),
    };
  };
  for (const item of values) {
    if (!item.mathAssignment)
      throw new ResearchTeamOrchestrationError(
        'math_v2_dispatch_mixed',
        'A v2 dispatch wave cannot mix v1 and v2 assignments.'
      );
    const receipt = await registry.prepare(item.mathAssignment);
    const runtimeAssignment = normalizeRuntimeMathAssignment(receipt.assignment);
    if (receipt.state === 'integrated' || receipt.state === 'superseded') {
      items.push({
        status: receipt.state === 'integrated' ? 'already_integrated' : 'already_superseded',
        protocol: 'v2',
        assignment_id: receipt.assignmentId,
        run_id: runtimeAssignment.runId,
        binding_digest: runtimeAssignment.bindingDigest,
        ...(receipt.supersession ? { winner_assignment_id: receipt.supersession.winnerAssignmentId } : {}),
      });
      continue;
    }
    // A durable accepted receipt with a Core run identity already has an
    // acknowledged transport row. Returning it is idempotent; status/recovery
    // paths are responsible for requeueing only when the prior turn ended.
    if (receipt.state === 'accepted' && receipt.teamRunId) {
      let preparedGit = receipt.preparedGit;
      let bindingRecovered = false;
      if (!preparedGit?.worktreePath) {
        // An earlier runtime could acknowledge Core before persisting the
        // Git binding. Recover the same accepted assignment in place; do not
        // dispatch a second Core turn or invent a worktree identity.
        preparedGit = await prepareV2Worktree(receipt, runtimeAssignment, true);
        const recordAssignment = context.projectGit?.recordResearchTeamAssignment;
        if (!recordAssignment) {
          throw new ResearchTeamOrchestrationError(
            'dispatch_not_persisted',
            'The recovered v2 Worker binding cannot be persisted to the assignment WAL.',
            true
          );
        }
        const persisted = recordAssignment({
          schema: 'deepscientist.research_team_assignment.v2',
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: receipt.slotId,
          assignmentId: receipt.assignmentId,
          assignment: receipt.assignment,
          state: 'accepted',
          teamRunId: receipt.teamRunId,
          preparedGit,
        });
        if (!persisted.preparedGit?.worktreePath) {
          throw new ResearchTeamOrchestrationError(
            'dispatch_not_persisted',
            'The assignment WAL did not retain the recovered v2 Worker binding.',
            true
          );
        }
        bindingRecovered = true;
      }
      items.push({
        status: 'already_accepted',
        protocol: 'v2',
        target_slot_id: receipt.slotId,
        assignment_id: receipt.assignmentId,
        run_id: runtimeAssignment.runId,
        binding_digest: runtimeAssignment.bindingDigest,
        team_run_id: receipt.teamRunId,
        ...(bindingRecovered ? { binding_recovered: true } : {}),
      });
      continue;
    }
    let preparedGit: ProjectGitResearchTeamPreparedGit | undefined;
    if (context.prepareMathV2Worktree) {
      preparedGit = await prepareV2Worktree(receipt, runtimeAssignment, Boolean(receipt.preparedGit?.worktreePath));
      const persistedPreparation = context.projectGit?.recordResearchTeamAssignment?.({
        schema: 'deepscientist.research_team_assignment.v2',
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: receipt.slotId,
        assignmentId: receipt.assignmentId,
        assignment: receipt.assignment,
        state: 'prepared',
        preparedGit,
      });
      if (persistedPreparation?.preparedGit?.worktreePath !== preparedGit.worktreePath)
        throw new ResearchTeamOrchestrationError(
          'dispatch_not_persisted',
          'Worker preparation was not durably recorded; retry the original dispatch before enqueueing.',
          true
        );
    }
    const envelope = runtimeMathAssignmentToResearchTeamEnvelope(receipt.assignment, { workerIds: workers });
    const assignment = receipt.assignment as {
      request: { idempotencyKey: string };
      runId: string;
      bindingDigest: string;
    };
    const acknowledgement = await client.dispatch(
      capability.teamId,
      receipt.slotId,
      JSON.stringify(envelope),
      context.signal,
      assignment.request.idempotencyKey,
      preparedGit?.worktreePath
    );
    if (
      acknowledgement.team_id !== capability.teamId ||
      acknowledgement.target_slot_id !== receipt.slotId ||
      acknowledgement.accepted_slot_id !== receipt.slotId ||
      !isTeamRunAckPersisted(acknowledgement)
    )
      throw new ResearchTeamOrchestrationError(
        'dispatch_not_persisted',
        'Core did not persist the v2 assignment dispatch.',
        true
      );
    const persistedAcceptance = context.projectGit?.recordResearchTeamAssignment?.({
      schema: 'deepscientist.research_team_assignment.v2',
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: receipt.slotId,
      assignmentId: receipt.assignmentId,
      assignment: receipt.assignment,
      state: 'accepted',
      teamRunId: acknowledgement.team_run_id,
      ...(preparedGit ? { preparedGit } : {}),
    });
    // Core acknowledgement is not sufficient by itself: a transport success
    // followed by a WAL write loss would leave an accepted turn that cannot be
    // safely resumed or independently verified. Keep the same reservation
    // retryable and never report accepted until the durable receipt contains
    // the exact Core run identity and, for prepared v2 work, its Git binding.
    if (
      !persistedAcceptance ||
      persistedAcceptance.state !== 'accepted' ||
      persistedAcceptance.teamRunId !== acknowledgement.team_run_id ||
      (preparedGit && persistedAcceptance.preparedGit?.worktreePath !== preparedGit.worktreePath)
    ) {
      throw new ResearchTeamOrchestrationError(
        'dispatch_not_persisted',
        'Core accepted the v2 assignment but the durable WAL did not retain its run and Git binding; retry the original dispatch.',
        true
      );
    }
    items.push({
      status: 'accepted',
      protocol: 'v2',
      target_slot_id: receipt.slotId,
      assignment_id: receipt.assignmentId,
      run_id: assignment.runId,
      binding_digest: assignment.bindingDigest,
      team_run_id: acknowledgement.team_run_id,
    });
  }
  return result({
    schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
    action: 'dispatch',
    status: 'accepted',
    team_id: capability.teamId,
    items,
    accepted_count: items.length,
  });
}

type ConditionalReviewDispatch = Readonly<{
  status: 'accepted' | 'deferred' | 'skipped' | 'failed';
  reason?:
    | 'no_local_gate_receipt'
    | 'receipt_commit_mismatch'
    | 'reverification_required'
    | 'already_reviewed'
    | 'no_reviewer_surface'
    | 'reviewer_busy'
    | 'reviewer_capacity'
    | 'assignment_source_unavailable';
  target_slot_id?: string;
  assignment_id?: string;
  idempotency_key?: string;
  receipt_id?: string;
  target_commit?: string;
  dispatch_status?: string;
  error?: string;
}>;

/**
 * Dispatch one short-lived semantic review only after an artifact integration
 * has a receipt that is bound to the exact canonical commit. The default
 * headless path leaves this disabled; interactive/high-confidence hosts opt in
 * through `enableConditionalReviewDispatch` and must provide a Reviewer lane.
 */
async function dispatchConditionalMathematicsReviews(
  batch: NormalizedIntegrationBatch,
  items: readonly ItemResult[],
  context: ResearchTeamToolContext
): Promise<ReadonlyMap<string, ConditionalReviewDispatch>> {
  const decisions = new Map<string, ConditionalReviewDispatch>();
  if (!context.enableConditionalReviewDispatch || context.capability.profileId !== 'mathematics-research-team') {
    return decisions;
  }
  const reviewer = context.capability.roster.find(
    (member) => member.roleKind === 'worker' && member.laneId === 'independent-review'
  );
  if (!reviewer) {
    for (const request of batch) {
      if (request.result.assignmentBinding?.stage === 'formalize' && request.result.localGateReceipt) {
        decisions.set(request.result.assignmentId, Object.freeze({ status: 'skipped', reason: 'no_reviewer_surface' }));
      }
    }
    return decisions;
  }
  const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
  const readAssignment = projectGit.readResearchTeamAssignment;
  const listAssignments = projectGit.listResearchTeamAssignments;
  const history = listAssignments
    ? listAssignments({ workspace: context.capability.projectRoot, teamId: context.capability.teamId })
    : [];
  const client = context.client;
  if (!client?.readRunState) {
    for (const request of batch) {
      if (request.result.assignmentBinding?.stage === 'formalize' && request.result.localGateReceipt) {
        decisions.set(request.result.assignmentId, Object.freeze({ status: 'skipped', reason: 'no_reviewer_surface' }));
      }
    }
    return decisions;
  }
  let runState: ResearchCoreRunState;
  try {
    runState = await client.readRunState(context.capability.teamId, context.signal, true);
  } catch (error) {
    for (const request of batch) {
      if (request.result.assignmentBinding?.stage === 'formalize' && request.result.localGateReceipt) {
        decisions.set(
          request.result.assignmentId,
          Object.freeze({
            status: 'deferred',
            reason: 'no_reviewer_surface',
            error: error instanceof Error ? error.message : String(error),
          })
        );
      }
    }
    return decisions;
  }
  const reviewerState = runState.slots.find((slot) => slot.slotId === reviewer.slotId);
  let reviewerBusy = Boolean(
    reviewerState &&
    (runState.activeSlotIds.includes(reviewer.slotId) ||
      reviewerState.queuedForegroundCount > 0 ||
      reviewerState.queuedBackgroundCount > 0 ||
      reviewerState.pendingWakeCount > 0)
  );
  const activeWorkerCount = runState.activeSlotIds.filter((slotId) => slotId !== context.capability.slotId).length;
  const capacityBusy = activeWorkerCount >= Math.max(1, context.capability.reasoningConcurrency);

  for (const [index, request] of batch.entries()) {
    const result = request.result;
    if (result.assignmentBinding?.stage !== 'formalize') continue;
    const item = items[index];
    const receiptValue =
      isRecord(item?.merged_commit_receipts) && isRecord(item.merged_commit_receipts.local_gate_receipt)
        ? item.merged_commit_receipts.local_gate_receipt
        : result.localGateReceipt;
    if (!receiptValue) {
      if (result.localGateReceipt) {
        decisions.set(result.assignmentId, Object.freeze({ status: 'skipped', reason: 'no_local_gate_receipt' }));
      }
      continue;
    }
    let receipt: MathLocalGateReceipt;
    try {
      receipt = normalizeMathLocalGateReceipt(receiptValue as MathLocalGateReceipt);
    } catch (error) {
      decisions.set(
        result.assignmentId,
        Object.freeze({
          status: 'skipped',
          reason: 'no_local_gate_receipt',
          error: error instanceof Error ? error.message : String(error),
        })
      );
      continue;
    }
    const targetCommit = typeof item?.merged_commit === 'string' ? item.merged_commit : '';
    if (!targetCommit || receipt.targetCommit !== targetCommit) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'receipt_commit_mismatch', receipt_id: receipt.receiptId })
      );
      continue;
    }
    if (item?.reverification_required === true) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'reverification_required', receipt_id: receipt.receiptId })
      );
      continue;
    }
    const alreadyReviewed = history.some((candidate) => {
      if (!isRecord(candidate.assignment) || !isRecord(candidate.assignment.math)) return false;
      const math = candidate.assignment.math;
      const candidateReceipt = isRecord(math.localGateReceipt) ? math.localGateReceipt : undefined;
      return (
        ['prepared', 'accepted', 'integrated'].includes(candidate.state) &&
        math.stage === 'review' &&
        candidateReceipt?.receiptId === receipt.receiptId
      );
    });
    if (alreadyReviewed) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'already_reviewed', receipt_id: receipt.receiptId })
      );
      continue;
    }
    if (reviewerBusy) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'deferred', reason: 'reviewer_busy', target_slot_id: reviewer.slotId })
      );
      continue;
    }
    if (capacityBusy) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'deferred', reason: 'reviewer_capacity', target_slot_id: reviewer.slotId })
      );
      continue;
    }
    if (!readAssignment) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'assignment_source_unavailable', receipt_id: receipt.receiptId })
      );
      continue;
    }
    const sourceReceipt = readAssignment({
      workspace: context.capability.projectRoot,
      teamId: context.capability.teamId,
      slotId: request.targetSlotId,
      assignmentId: result.assignmentId,
    });
    if (!sourceReceipt) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'assignment_source_unavailable', receipt_id: receipt.receiptId })
      );
      continue;
    }
    let sourceAssignment: ResearchTeamAssignment;
    try {
      const sourceTarget = context.capability.roster.find((member) => member.slotId === request.targetSlotId);
      if (!sourceTarget) throw new Error('formalizer slot is absent from the Team roster');
      sourceAssignment = validateDurableResearchTeamAssignment(
        sourceReceipt.assignment,
        context.capability,
        sourceTarget,
        validateAssignment
      );
    } catch (error) {
      decisions.set(
        result.assignmentId,
        Object.freeze({
          status: 'skipped',
          reason: 'assignment_source_unavailable',
          receipt_id: receipt.receiptId,
          error: error instanceof Error ? error.message : String(error),
        })
      );
      continue;
    }
    if (sourceAssignment.math?.stage !== 'formalize' || !sourceAssignment.math.problemContract) {
      decisions.set(
        result.assignmentId,
        Object.freeze({ status: 'skipped', reason: 'assignment_source_unavailable', receipt_id: receipt.receiptId })
      );
      continue;
    }
    const reviewAssignmentId = `review-${crypto
      .createHash('sha256')
      .update(`${context.capability.teamId}\u0000${receipt.receiptId}\u0000${targetCommit}`)
      .digest('hex')
      .slice(0, 48)}`;
    const idempotencyKey = `conditional-review:${crypto
      .createHash('sha256')
      .update(`${context.capability.teamId}\u0000${receipt.receiptId}`)
      .digest('hex')
      .slice(0, 48)}`;
    const oldAlignment = sourceAssignment.math.alignmentCheck;
    const oldRouteSelection = sourceAssignment.math.routeSelection;
    const {
      activePlanNodeId: _activePlanNodeId,
      failureLedger: _failureLedger,
      proofPlan: _proofPlan,
      proofState: _proofState,
      applicableLessons: _applicableLessons,
      ...reviewMathBase
    } = sourceAssignment.math;
    const reviewMath = {
      ...reviewMathBase,
      stage: 'review' as const,
      workflowStage: 'review' as const,
      alignmentCheck: oldAlignment ? { ...oldAlignment, contractCommit: targetCommit } : oldAlignment,
      ...(oldRouteSelection
        ? {
            routeSelection: {
              ...oldRouteSelection,
              selectionCommit: targetCommit,
              rebasedFromCommit: oldRouteSelection.selectionCommit,
              revalidatedAtCommit: targetCommit,
            },
          }
        : {}),
      localGateReceipt: receipt,
    };
    const reviewAssignment = createResearchTeamAssignment({
      ...sourceAssignment,
      assignmentId: reviewAssignmentId,
      laneId: 'independent-review',
      executionMode: 'advisory',
      roleTemplateId: undefined,
      roleLabel: 'Conditional independent semantic review',
      roleInstructions:
        'Read only the frozen candidate commit and LOCAL_GATE receipt. Return one signed CandidateReview; do not edit, commit, or run the official comparator.',
      title: `Independent review: ${sourceAssignment.title}`,
      objective:
        'Audit the exact locally verified candidate for statement alignment, quantifiers, assumptions, declaration identity, and proof gaps.',
      acceptanceCriteria: ['Return one CandidateReview bound to the frozen LOCAL_GATE receipt and reviewed commit.'],
      failureCriteria: ['Do not review an unverified, rebased, or receipt-mismatched candidate.'],
      evidenceRefs: [...new Set([...sourceAssignment.evidenceRefs, `lean-receipt:${receipt.receiptId}`])],
      doNotRepeat: [...new Set([...sourceAssignment.doNotRepeat, `review:${receipt.receiptId}`])],
      expectedArtifacts: ['CandidateReview'],
      falsificationPlan: {
        hypothesis: 'The locally verified candidate exactly proves the frozen mathematical statement.',
        test: 'Audit the statement, assumptions, declaration identity, and receipt-bound proof.',
        failureSignal: 'Any mismatch, missing obligation, or unsupported assumption in the frozen candidate.',
      },
      math: reviewMath,
      git: { projectRoot: sourceAssignment.git.projectRoot, baseCommit: targetCommit },
    });
    const dispatchResponse = await runResearchTeamTool(
      {
        action: 'dispatch',
        assignments: [
          {
            targetSlotId: reviewer.slotId,
            idempotencyKey,
            assignment: reviewAssignment as unknown as Record<string, unknown>,
          },
        ],
      },
      { ...context, enableConditionalReviewDispatch: false }
    );
    const dispatchPayload =
      dispatchResponse.content[0]?.type === 'text'
        ? (JSON.parse(dispatchResponse.content[0].text) as Record<string, unknown>)
        : undefined;
    const dispatchItem =
      Array.isArray(dispatchPayload?.items) && isRecord(dispatchPayload.items[0])
        ? dispatchPayload.items[0]
        : undefined;
    const dispatchStatus = typeof dispatchPayload?.status === 'string' ? dispatchPayload.status : 'unavailable';
    const accepted = dispatchStatus === 'accepted' || dispatchStatus === 'partial';
    decisions.set(
      result.assignmentId,
      Object.freeze({
        status: accepted ? 'accepted' : dispatchStatus === 'deferred' ? 'deferred' : 'failed',
        target_slot_id: reviewer.slotId,
        assignment_id: reviewAssignmentId,
        idempotency_key: idempotencyKey,
        receipt_id: receipt.receiptId,
        target_commit: targetCommit,
        dispatch_status: dispatchStatus,
        ...(dispatchItem?.error && isRecord(dispatchItem.error)
          ? { error: String(dispatchItem.error.message ?? dispatchItem.error.code ?? 'review dispatch failed') }
          : {}),
      })
    );
    // A single reviewer surface is intentionally consumed once per integrate
    // call. A later event can reuse it after the review delivery arrives.
    reviewerBusy = true;
  }
  return decisions;
}

export async function runResearchTeamTool(
  input: ResearchTeamToolInput,
  context: ResearchTeamToolContext
): Promise<ToolResult> {
  const elapsed = createMathToolTiming();
  const response = await runResearchTeamToolOperation(input, context);
  if (
    context.capability.profileId !== 'mathematics-research-team' ||
    (input.action !== 'deliver' && input.action !== 'integrate')
  )
    return response;
  // MCP metadata does not change sealed delivery bytes or exact replay payloads.
  return {
    ...response,
    _meta: {
      ...response._meta,
      'deepscientist/timing': {
        phase: input.action === 'deliver' ? 'delivery' : 'integration',
        durationMs: elapsed().toolWallMs,
        measurement: 'tool_wall_including_verifier',
      },
    },
  };
}

async function runResearchTeamToolOperation(
  input: ResearchTeamToolInput,
  context: ResearchTeamToolContext
): Promise<ToolResult> {
  try {
    const action = requireAction(input.action);
    authorizeResearchTeamToolAction(action, context.capability);
    if (
      input.sourceArtifacts !== undefined &&
      (action !== 'integrate' || context.capability.profileId !== 'mathematics-research-team')
    )
      throw new ResearchTeamOrchestrationError('invalid', 'Source artifacts require Mathematics integrate.');
    if (context.capability.profileId === 'mathematics-research-team') context.verifyRunInputs?.();
    switch (action) {
      case 'read_feedback': {
        const cap = context.capability;
        if (cap.roleKind !== 'worker' || cap.profileId !== 'mathematics-research-team' || !context.readMathLiteFeedback)
          throw new ResearchTeamOrchestrationError('unauthorized', 'Feedback requires an assigned mathematics Worker.');
        context.signal?.throwIfAborted();
        const driver = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
        const receipts =
          driver
            .listResearchTeamAssignments?.({ workspace: cap.projectRoot, teamId: cap.teamId, strict: true })
            .filter(
              (r) =>
                r.slotId === cap.slotId &&
                r.state === 'accepted' &&
                !r.delivery &&
                !r.integration &&
                !r.supersessionPending &&
                !r.budgetCancellation
            ) ?? [];
        const binding = context.readMathAssignmentBinding?.();
        if (receipts.length !== 1 || !binding || receipts[0]!.schema !== 'deepscientist.research_team_assignment.v2')
          throw new ResearchTeamOrchestrationError(
            'math_feedback_assignment_unavailable',
            'Feedback requires one active v2 assignment.'
          );
        const receipt = receipts[0]!;
        const assignment = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
          expectedRunId: binding.runId,
          expectedBindingDigest: binding.bindingDigest,
          expectedTargetSlotId: cap.slotId,
          ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
        });
        if (
          !['formalize', 'research'].includes(assignment.kind) ||
          assignment.assignmentId !== receipt.assignmentId ||
          receipt.teamId !== cap.teamId
        )
          throw new ResearchTeamOrchestrationError(
            'unauthorized',
            'Feedback requires the bound mathematics assignment.'
          );
        const feedback = await context.readMathLiteFeedback({ receipt, assignment, consume: true });
        context.signal?.throwIfAborted();
        const current = driver.listResearchTeamAssignments!({
          workspace: cap.projectRoot,
          teamId: cap.teamId,
          strict: true,
        }).find((r) => r.assignmentId === receipt.assignmentId);
        if (!current || !isDeepStrictEqual(current, receipt))
          throw new ResearchTeamOrchestrationError(
            'math_feedback_assignment_changed',
            'Assignment changed while reading feedback.'
          );
        return result({ schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA, action: 'read_feedback', ...feedback });
      }
      case 'describe':
        return result(describeCapability(context.capability));
      case 'dispatch': {
        const runtimeAssignments =
          input.assignments?.filter((item) => Boolean(item && item.mathAssignment !== undefined)) ?? [];
        if (runtimeAssignments.length) {
          if (runtimeAssignments.length !== input.assignments?.length)
            throw new ResearchTeamOrchestrationError(
              'math_v2_dispatch_mixed',
              'A v2 dispatch wave cannot mix v1 and v2 assignments.'
            );
          return await dispatchRuntimeMathAssignments(runtimeAssignments, context);
        }
        const readPortfolio = memoizeResearchTeamPortfolioReader(readCanonicalMathematicsPortfolio);
        const listAssignmentsSource = (context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER).listResearchTeamAssignments;
        const listAssignments = memoizeResearchTeamAssignmentListReader(listAssignmentsSource);
        const validateAssignmentForBatch = memoizeResearchTeamAssignmentValidator(validateAssignment, readPortfolio);
        // The queue may run after another MCP invocation has durably recorded
        // an assignment. Do not reuse the batch validator's WeakMap result or
        // its cached history inside the serialized dispatch operation.
        // A dispatch wave is validated and queued as one unit. Reuse the
        // memoized portfolio snapshot across its validators so each Worker
        // does not repeat the same project-directory scan.
        const runtimeReadPortfolio = readPortfolio;
        const validateAssignmentForRuntime = memoizeResearchTeamAssignmentValidator(
          validateAssignment,
          runtimeReadPortfolio
        );
        const assignments = await normalizeDispatchBatch(
          input.assignments,
          context.capability,
          validateAssignmentForBatch,
          listAssignments,
          context
        );
        // normalizeDispatchBatch already needs an assignment history for
        // duplicate ownership checks. Reuse that memoized snapshot through
        // recovery and preparation so one dispatch wave does not rescan the
        // assignment WAL once per Worker.
        const assignmentSnapshot =
          context.capability.profileId === 'mathematics-research-team' && listAssignments
            ? listAssignments({ workspace: context.capability.projectRoot, teamId: context.capability.teamId })
            : undefined;
        const runtime = toRuntime(context, validateAssignmentForRuntime, {
          readPortfolio: runtimeReadPortfolio,
          ...(listAssignments ? { listAssignments } : {}),
        });
        const recoveryWarnings = await restoreResearchTeamRuntimeState(
          context.capability,
          runtime.context.projectGit,
          runtime.client,
          assignmentSnapshot,
          runtime.context.validateAssignment
        );
        if (recoveryWarnings.length) {
          throw new ResearchTeamOrchestrationError(
            'recovery_pending',
            `Research Team recovery is incomplete; do not dispatch until the previous assignment is reconciled: ${recoveryWarnings.join('; ')}`,
            true
          );
        }
        const items = await researchTeamOrchestrator.dispatchMany(assignments, runtime);
        const acceptedCount = items.filter((item) => item.status === 'accepted').length;
        const deferred = items.some((item) => ['capacity', 'target_busy'].includes(String(item.status)));
        const blocker = dispatchBlocker(items);
        return result({
          schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
          action,
          status:
            acceptedCount === items.length
              ? 'accepted'
              : acceptedCount > 0
                ? 'partial'
                : deferred
                  ? 'deferred'
                  : 'unavailable',
          team_id: context.capability.teamId,
          items,
          accepted_count: acceptedCount,
          should_end_turn: acceptedCount > 0,
          ...(acceptedCount > 0
            ? {
                instruction:
                  'Dispatch is accepted. End this Lead turn now; Core will wake the same conversation on Worker delivery or a terminal event.',
              }
            : {}),
          ...(blocker ? { blocker } : {}),
        });
      }
      case 'status': {
        if (context.capability.profileId === 'mathematics-research-team') {
          if (input.waitLevel !== undefined || (input.waitSeconds !== undefined && input.waitSeconds !== 0))
            throw new ResearchTeamOrchestrationError(
              'invalid',
              'Mathematics status is an immediate read-only snapshot.'
            );
          const capability = context.capability;
          const targets = normalizeStatusTargets(input.targetSlotIds, capability);
          let state = await requireClient(context.client).readRunState(capability.teamId, context.signal, true);
          const coreObservedAt = new Date().toISOString();
          const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
          const listAssignments = projectGit.listResearchTeamAssignments;
          if (!listAssignments)
            throw new ResearchTeamOrchestrationError('integrity', 'Assignment snapshot is unavailable.');
          let assignments = listAssignments({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            strict: true,
          });
          const hasRecoverableAssignment = assignments.some((receipt) => {
            if (receipt.state === 'prepared') return true;
            if (
              receipt.state !== 'accepted' ||
              receipt.delivery ||
              receipt.integration ||
              receipt.supersessionPending ||
              receipt.budgetCancellation
            ) {
              return false;
            }
            const slot = state.slots.find((candidate) => candidate.slotId === receipt.slotId);
            return Boolean(
              slot &&
              !state.activeSlotIds.includes(slot.slotId) &&
              slot.queuedForegroundCount === 0 &&
              slot.queuedBackgroundCount === 0 &&
              slot.pendingWakeCount === 0
            );
          });
          const recoveryWarnings = hasRecoverableAssignment
            ? await restoreResearchTeamRuntimeState(
                capability,
                projectGit,
                requireClient(context.client),
                assignments,
                validateAssignment,
                state
              )
            : [];
          if (hasRecoverableAssignment) {
            // Refresh both snapshots so a successful requeue is immediately
            // visible to the Lead instead of being projected as stale queued.
            state = await requireClient(context.client).readRunState(capability.teamId, context.signal, true);
            assignments = listAssignments({
              workspace: capability.projectRoot,
              teamId: capability.teamId,
              strict: true,
            });
          }
          if (capability.roleKind === 'lead' && context.relayMathLiteProgress) {
            await context.relayMathLiteProgress(requireClient(context.client));
            state = await requireClient(context.client).readRunState(capability.teamId, context.signal, true);
          }
          const walObservedAt = new Date().toISOString();
          const selected = state.slots.filter((slot) => targets.includes(slot.slotId));
          const pending = assignments.filter((receipt) => receipt.state === 'prepared' || receipt.state === 'accepted');
          const counts = new Map<string, number>();
          for (const receipt of pending) counts.set(receipt.slotId, (counts.get(receipt.slotId) ?? 0) + 1);
          const consistencyIssues: Array<{
            path: string;
            code: 'integrity';
            message: string;
          }> = [];
          if (recoveryWarnings.length) {
            consistencyIssues.push(
              ...recoveryWarnings.map((message) => ({ path: 'recovery', code: 'integrity' as const, message }))
            );
          }
          let observedV2RunId: string | undefined;
          let observedV2BindingDigest: string | undefined;
          const workerIds = new Set(
            capability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
          );
          const pendingAssignments = pending.map((receipt) => {
            let v2View: ReturnType<typeof projectRuntimeMathAssignmentToExecutionView> | undefined;
            if (receipt.schema === 'deepscientist.research_team_assignment.v2') {
              try {
                v2View = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
                  workerIds,
                  expectedTargetSlotId: receipt.slotId,
                  ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
                });
                if (v2View.assignmentId !== receipt.assignmentId) {
                  throw new MathAssignmentAdapterError(
                    'integrity',
                    'The durable v2 assignment id does not match its WAL receipt.'
                  );
                }
                if (observedV2RunId && observedV2RunId !== v2View.runId) {
                  throw new MathAssignmentAdapterError(
                    'run_mismatch',
                    'The v2 assignment run identity is inconsistent.'
                  );
                }
                if (observedV2BindingDigest && observedV2BindingDigest !== v2View.bindingDigest) {
                  throw new MathAssignmentAdapterError(
                    'binding_mismatch',
                    'The v2 assignment binding identity is inconsistent.'
                  );
                }
                observedV2RunId = v2View.runId;
                observedV2BindingDigest = v2View.bindingDigest;
              } catch (error) {
                consistencyIssues.push({
                  path: `assignments.${receipt.assignmentId}`,
                  code: 'integrity',
                  message:
                    error instanceof MathAssignmentAdapterError
                      ? `v2 assignment integrity failure (${error.code}).`
                      : 'v2 assignment integrity failure.',
                });
              }
            }
            const orphanedAccepted = isOrphanedAcceptedMathematicsAssignment(receipt);
            // Keep the WAL/Core hand-off state explicit in status output. This
            // lets the Lead distinguish a reservation that is safe to retry
            // from an accepted turn whose durable Git binding is missing,
            // without inferring lifecycle state from free-form warnings.
            const lifecycle =
              receipt.state === 'prepared'
                ? receipt.preparedGit?.worktreePath
                  ? 'prepared_bound'
                  : 'prepared_unbound'
                : receipt.state === 'accepted'
                  ? receipt.preparedGit?.worktreePath
                    ? receipt.teamRunId
                      ? 'accepted_bound'
                      : 'accepted_unbound'
                    : 'accepted_missing_binding'
                  : receipt.state;
            const executionState = orphanedAccepted
              ? 'stale'
              : receipt.delivery
                ? isRecord(receipt.delivery.result) &&
                  (receipt.delivery.result.status === 'blocked' ||
                    (receipt.delivery.result.schema === MATH_DELIVERY_ENVELOPE_SCHEMA &&
                      isRecord(receipt.delivery.result.delivery) &&
                      receipt.delivery.result.delivery.status === 'blocked'))
                  ? 'blocked'
                  : 'delivered'
                : receipt.state === 'prepared'
                  ? 'prepared'
                  : state.slots.some(
                        (slot) =>
                          slot.slotId === receipt.slotId &&
                          slot.state === 'running' &&
                          (!receipt.teamRunId || receipt.teamRunId === (slot.teamRunId ?? state.teamRunId))
                      )
                    ? 'running'
                    : 'queued';
            return {
              assignment_id: receipt.assignmentId,
              slot_id: receipt.slotId,
              state: executionState,
              lifecycle,
              wal_state: receipt.state,
              has_prepared_git: Boolean(receipt.preparedGit?.worktreePath),
              has_core_run: Boolean(receipt.teamRunId),
              ...(orphanedAccepted ? { stale: true, recovery: 'orphaned_accepted' as const } : {}),
              ...(v2View
                ? {
                    protocol: 'v2' as const,
                    idempotency_key: v2View.idempotencyKey,
                    run_id: v2View.runId,
                    binding_digest: v2View.bindingDigest,
                    base_commit: v2View.baseCommit,
                    kind: v2View.kind,
                    objective: v2View.objective,
                    ...(v2View.request.consumerAssignmentIds
                      ? { consumer_assignment_ids: v2View.request.consumerAssignmentIds }
                      : {}),
                    ...(v2View.request.researchQuestion ? { research_question: v2View.request.researchQuestion } : {}),
                    artifact_grants: v2View.artifactGrants,
                  }
                : { protocol: 'v1' as const }),
            };
          });
          const orphanedAccepted = pending.filter(isOrphanedAcceptedMathematicsAssignment);
          if (orphanedAccepted.length) {
            consistencyIssues.push({
              path: 'assignments',
              code: 'integrity',
              message: `Ignored ${orphanedAccepted.length} accepted assignment(s) whose prepared worktree no longer exists; Core has no recoverable batch for them.`,
            });
          }
          const inconsistent =
            [...counts.values()].some((count) => count > 1) ||
            new Set(state.slots.map((slot) => slot.slotId)).size !== state.slots.length ||
            new Set(assignments.map((receipt) => receipt.assignmentId)).size !== assignments.length ||
            assignments.some((receipt) => receipt.teamId !== capability.teamId) ||
            state.teamId !== capability.teamId ||
            pending.some((receipt) => !state.slots.some((slot) => slot.slotId === receipt.slotId)) ||
            consistencyIssues.length > 0;
          if ([...counts.values()].some((count) => count > 1)) {
            consistencyIssues.push({
              path: 'assignments',
              code: 'integrity',
              message: 'A Worker slot has more than one active assignment.',
            });
          }
          if (new Set(state.slots.map((slot) => slot.slotId)).size !== state.slots.length) {
            consistencyIssues.push({
              path: 'core.slots',
              code: 'integrity',
              message: 'Core returned duplicate Worker slots.',
            });
          }
          if (new Set(assignments.map((receipt) => receipt.assignmentId)).size !== assignments.length) {
            consistencyIssues.push({
              path: 'assignments',
              code: 'integrity',
              message: 'Assignment WAL contains duplicate ids.',
            });
          }
          if (assignments.some((receipt) => receipt.teamId !== capability.teamId)) {
            consistencyIssues.push({
              path: 'assignments',
              code: 'integrity',
              message: 'Assignment WAL contains a foreign team id.',
            });
          }
          if (state.teamId !== capability.teamId) {
            consistencyIssues.push({
              path: 'core.team_id',
              code: 'integrity',
              message: 'Core team identity does not match the capability.',
            });
          }
          if (pending.some((receipt) => !state.slots.some((slot) => slot.slotId === receipt.slotId))) {
            consistencyIssues.push({
              path: 'assignments',
              code: 'integrity',
              message: 'A pending assignment targets a missing Core slot.',
            });
          }
          const selectedPendingAssignments = pendingAssignments.filter((assignment) =>
            targets.includes(assignment.slot_id)
          );
          const activeWorkerSlots = selected
            .filter((slot) => state.activeSlotIds.includes(slot.slotId))
            .map((slot) => slot.slotId);
          const occupiedWorkerIds = new Set([
            ...state.activeSlotIds.filter((slotId) => workerIds.has(slotId)),
            ...state.slots
              .filter(
                (slot) =>
                  workerIds.has(slot.slotId) &&
                  (slot.state !== 'idle' ||
                    slot.queuedForegroundCount > 0 ||
                    slot.queuedBackgroundCount > 0 ||
                    slot.pendingWakeCount > 0)
              )
              .map((slot) => slot.slotId),
            ...pending.map((receipt) => receipt.slotId),
          ]);
          const remainingCapacity = Math.max(0, capability.reasoningConcurrency - occupiedWorkerIds.size);
          const availableWorkerSlots =
            !inconsistent && consistencyIssues.length === 0 && remainingCapacity > 0
              ? selected
                  .filter(
                    (slot) =>
                      workerIds.has(slot.slotId) &&
                      !occupiedWorkerIds.has(slot.slotId) &&
                      slot.state === 'idle' &&
                      !slot.activeTurnId &&
                      !slot.blockedReason &&
                      !slot.runtimeHealth
                  )
                  .map((slot) => slot.slotId)
              : [];
          const workActive =
            activeWorkerSlots.length > 0 ||
            selectedPendingAssignments.some(
              (assignment) => !assignment.stale && ['prepared', 'queued', 'running'].includes(assignment.state)
            );
          // A blocked or rejected formalizer remains occupied until its sealed delivery is
          // resumed through the normal predecessor-aware dispatch path.  Keep
          // that ownership visible, but expose the one legal successor action
          // when the same slot has no active writer or foreground work. This is a
          // read-only projection: dispatch still revalidates the WAL, seal,
          // permissions and source identity before accepting it.
          const continuationActions = selectedPendingAssignments.flatMap((assignment) => {
            if (inconsistent || capability.roleKind !== 'lead') return [];
            if (
              !['blocked', 'delivered'].includes(assignment.state) ||
              assignment.protocol !== 'v2' ||
              assignment.kind !== 'formalize'
            )
              return [];
            const receipt = assignments.find((candidate) => candidate.assignmentId === assignment.assignment_id);
            const slot = selected.find((candidate) => candidate.slotId === assignment.slot_id);
            const deliveryId = receipt?.delivery?.deliveryId;
            if (
              !receipt ||
              !deliveryId ||
              !context.hasMathLiteSealedDelivery?.(deliveryId) ||
              !slot ||
              !isResearchSlotReadyForSuccessor(state, capability.teamId, slot.slotId) ||
              receipt.supersessionPending ||
              receipt.budgetCancellation
            )
              return [];
            const binding = context.readMathAssignmentBinding?.();
            if (!binding) return [];
            const [selection] = selectMathV2IntegrationBatch([receipt], [deliveryId], {
              expectedRunId: binding.runId,
              expectedBindingDigest: binding.bindingDigest,
            });
            if (!selection) return [];
            const phase = deriveMathV2IntegrationPhase(selection);
            if (!['blocked_report', 'private_rejected', 'canonical_rejected'].includes(phase)) return [];
            return [
              {
                predecessor_assignment_id: receipt.assignmentId,
                request: {
                  action: 'dispatch' as const,
                  assignments: [
                    {
                      target_slot_id: slot.slotId,
                      task:
                        phase === 'blocked_report'
                          ? `Continue the retained proof from sealed assignment ${receipt.assignmentId}. Inspect its frozen source, retained notes, provisional research reports and real compiler evidence, then advance the original target.${formatBlockedPredecessorHandoff(receipt.delivery?.result)}`
                          : `Repair the rejected proof from sealed assignment ${receipt.assignmentId}. Inspect its frozen source and actual verifier diagnostics, preserve the original target, and continue in this legal successor.`,
                    },
                  ],
                },
                reason: phase === 'blocked_report' ? 'blocked_formalize_sealed' : 'rejected_formalize_sealed',
              },
            ];
          });
          const shouldEndTurn = workActive && availableWorkerSlots.length === 0 && continuationActions.length === 0;
          return result({
            schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
            action,
            status: 'observed',
            team_id: capability.teamId,
            observation: {
              status: 'observed',
              state: ['completed', 'failed', 'cancelled'].includes(state.runStatus ?? '')
                ? state.runStatus
                : state.runStatus === 'accepted'
                  ? 'starting'
                  : state.activeSlotIds.length || state.activeEnqueueLeaseCount
                    ? 'running'
                    : 'quiescent',
              team_run_id: state.teamRunId ?? null,
              source: 'core_snapshot+assignment_wal',
              core_observed_at: coreObservedAt,
              wal_observed_at: walObservedAt,
              observed_at: walObservedAt,
              slots: selected.map((slot) => ({
                slot_id: slot.slotId,
                state: slot.state,
                queued_foreground_count: slot.queuedForegroundCount,
                queued_background_count: slot.queuedBackgroundCount,
                pending_wake_count: slot.pendingWakeCount,
                heartbeat: {
                  status: researchTeamHeartbeatStatus(slot),
                  slow: slot.activeTurnSlow ?? false,
                  active_turn_id: slot.activeTurnId ?? null,
                  active_turn_elapsed_ms: slot.activeTurnElapsedMs ?? null,
                  runtime_health: slot.runtimeHealth ?? 'healthy',
                  blocked_reason: slot.blockedReason ?? null,
                },
              })),
              active_worker_slots: activeWorkerSlots,
              available_worker_slots: availableWorkerSlots,
              remaining_reasoning_capacity: remainingCapacity,
              pending_assignments: selectedPendingAssignments,
              ...(context.readMathResearchGraph ? { research_graph: context.readMathResearchGraph() } : {}),
              continuation_actions: continuationActions,
              terminal_assignment_counts: {
                integrated: assignments.filter((receipt) => receipt.state === 'integrated').length,
                superseded: assignments.filter((receipt) => receipt.state === 'superseded').length,
              },
              consistency_issues: inconsistent
                ? consistencyIssues.length
                  ? consistencyIssues
                  : [
                      {
                        path: '$',
                        code: 'integrity' as const,
                        message: 'Core and assignment snapshots require runtime reconciliation.',
                      },
                    ]
                : [],
            },
            should_end_turn: shouldEndTurn,
            instruction: shouldEndTurn
              ? 'Worker work is active or queued. End this Lead turn now; Core will wake the same conversation on delivery or a terminal event.'
              : continuationActions.length
                ? 'A blocked proof has a sealed delivery and an idle owner. Dispatch exactly the listed successor action through the normal lifecycle; do not edit the sealed source or create a competing assignment.'
                : workActive
                  ? 'Independent Worker capacity is available. Dispatch only a concrete independent obligation using frozen evidence; do not replace or duplicate active work. If no independent work is useful, end this turn and await evidence. Do not poll unchanged status.'
                  : 'Use this snapshot for one lifecycle decision. Do not repeat an unchanged status call in this turn.',
          });
        }
        const runtime = toRuntime(context);
        const targetSlotIds = normalizeStatusTargets(input.targetSlotIds, context.capability);
        const observed = await researchTeamOrchestrator.status(
          {
            targetSlotIds,
            waitSeconds: normalizeTeamWaitSeconds(input.waitSeconds, input.waitLevel),
          },
          runtime
        );
        return result({
          schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
          action,
          status: observed.status === 'observed' ? 'observed' : 'unavailable',
          team_id: context.capability.teamId,
          observation: observed,
        });
      }
      case 'read_artifact': {
        if (context.capability.profileId !== 'mathematics-research-team' || !context.readMathArtifact) {
          throw new ResearchTeamOrchestrationError(
            'math_artifact_unavailable',
            'The immutable mathematics artifact store is unavailable.'
          );
        }
        if (
          typeof input.artifactRead?.ref !== 'string' ||
          parseMathArtifactReference(input.artifactRead.ref)?.scheme !== 'math-artifact'
        ) {
          throw new ResearchTeamOrchestrationError(
            'math_artifact_reference_required',
            'read_artifact requires an exact math-artifact://run-id/artifact-id reference supplied in assignment inputs or an acknowledged share. File paths are not artifact references. Read authorized local files with ordinary file tools inside your assigned worktree; if no artifact was supplied, do not invent a reference. This tool does not read filesystem paths.'
          );
        }
        const request = normalizeMathArtifactRead(input.artifactRead);
        let access: MathArtifactAccess = { role: 'lead' };
        if (context.capability.roleKind === 'worker') {
          const listAssignments = (context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER).listResearchTeamAssignments;
          if (!listAssignments)
            throw new ResearchTeamOrchestrationError('integrity', 'Assignment snapshot is unavailable.');
          const active = listAssignments({
            workspace: context.capability.projectRoot,
            teamId: context.capability.teamId,
            states: ['prepared', 'accepted'],
            strict: true,
          }).filter(
            (receipt) =>
              receipt.slotId === context.capability.slotId &&
              !receipt.supersessionPending &&
              !receipt.budgetCancellation
          );
          if (active.length !== 1) {
            throw new ResearchTeamOrchestrationError(
              'math_artifact_assignment_unavailable',
              'The Worker must have exactly one active assignment before reading an artifact.'
            );
          }
          let grants: readonly string[] = [];
          if (
            active[0]!.schema === 'deepscientist.research_team_assignment.v2' &&
            active[0]!.assignment &&
            typeof active[0]!.assignment === 'object'
          ) {
            grants = normalizeRuntimeMathAssignment(active[0]!.assignment).artifactGrants;
          }
          access = {
            role: 'worker',
            assignmentId: active[0]!.assignmentId,
            grants: new Set(grants),
          };
        }
        const artifact = await context.readMathArtifact(request, access);
        return result({
          schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
          action,
          status: 'read',
          artifact,
        });
      }
      case 'deliver':
        return await deliverResult(input.result, context);
      case 'share':
        return await shareRuntimeMathProgress(input.result, context, input.shareTargetSlotId);
      case 'integrate': {
        const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
        const recoveryReceiptSnapshot = projectGit.listResearchTeamAssignments?.({
          workspace: context.capability.projectRoot,
          teamId: context.capability.teamId,
          states: ['prepared', 'accepted'],
        });
        const preparationRuntime = toRuntime(context, undefined, {
          ...(recoveryReceiptSnapshot ? { listAssignments: () => recoveryReceiptSnapshot } : {}),
        });
        const recoveryWarnings = await restoreResearchTeamRuntimeState(
          context.capability,
          preparationRuntime.context.projectGit,
          preparationRuntime.client,
          recoveryReceiptSnapshot,
          preparationRuntime.context.validateAssignment
        );
        const integrateBlockers = recoveryWarnings.filter((warning) => !isUnpreparedReservationWarning(warning));
        if (integrateBlockers.length) {
          throw new ResearchTeamOrchestrationError(
            'recovery_pending',
            `Research Team recovery is incomplete; do not integrate until the previous assignment is reconciled: ${integrateBlockers.join('; ')}`,
            true
          );
        }
        if (context.capability.profileId === 'mathematics-research-team' && input.deliveries) {
          let v2Receipts: ProjectGitResearchTeamAssignmentReceipt[] = [];
          for (const item of input.deliveries) {
            if (
              [item.result !== undefined, item.deliveryId !== undefined, item.assignmentId !== undefined].filter(
                Boolean
              ).length !== 1
            )
              throw new ResearchTeamOrchestrationError(
                'invalid',
                'Provide exactly one of result, deliveryId, or assignmentId.'
              );
            const target = requireWorker(context.capability, item.targetSlotId);
            const candidate = item.deliveryId
              ? readResearchTeamDeliveryReceipt(
                  item.deliveryId,
                  context.capability,
                  preparationRuntime.context.readAssignment
                )
              : item.assignmentId
                ? preparationRuntime.context.readAssignment?.({
                    workspace: context.capability.projectRoot,
                    teamId: context.capability.teamId,
                    slotId: target.slotId,
                    assignmentId: stableId(item.assignmentId, 'assignment_id'),
                  })
                : undefined;
            if (candidate?.schema === 'deepscientist.research_team_assignment.v2') {
              if (candidate.teamId !== context.capability.teamId || candidate.slotId !== target.slotId)
                throw new ResearchTeamOrchestrationError(
                  'integrity',
                  'The v2 delivery does not belong to the selected Worker.'
                );
              v2Receipts.push(candidate);
            }
            if (item.result && isRecord(item.result) && item.result.schema === MATH_DELIVERY_ENVELOPE_SCHEMA) {
              throw new ResearchTeamOrchestrationError(
                'math_v2_integration_writer_pending',
                'Use the durable v2 delivery selector; direct v2 envelopes cannot be integrated as v1 results.'
              );
            }
          }
          if (v2Receipts.length) {
            if (v2Receipts.length !== input.deliveries.length)
              throw new ResearchTeamOrchestrationError(
                'math_v2_integration_mixed',
                'A v2 integration wave cannot mix protocols.'
              );
            const binding = context.readMathAssignmentBinding?.();
            if (!binding)
              throw new ResearchTeamOrchestrationError('integrity', 'The frozen v2 run binding is unavailable.');
            const boundProjectRoot = binding.projectRoot ?? context.capability.projectRoot;
            assertMathCanonicalPath(boundProjectRoot);
            if (!isMathPathWithin(context.capability.projectRoot, boundProjectRoot))
              throw new ResearchTeamOrchestrationError(
                'integrity',
                'The frozen Lean project is outside the Team workspace.'
              );
            const projectRelative = path
              .relative(context.capability.projectRoot, boundProjectRoot)
              .split(path.sep)
              .join('/');
            const originalV2Receipts = v2Receipts;
            const selections = selectMathV2IntegrationBatch(
              v2Receipts,
              v2Receipts.map((receipt) => receipt.delivery?.deliveryId ?? ''),
              {
                expectedRunId: binding.runId,
                expectedBindingDigest: binding.bindingDigest,
              }
            );
            const phaseByAssignment = new Map(
              selections.map((selection) => [selection.receipt.assignmentId, deriveMathV2IntegrationPhase(selection)])
            );
            const unsupported = selections.find((selection) =>
              ['invalid_record', 'superseded_history', 'private_integrity_error', 'canonical_integrity_error'].includes(
                phaseByAssignment.get(selection.receipt.assignmentId)!
              )
            );
            if (unsupported) {
              throw new ResearchTeamOrchestrationError(
                'math_v2_reverification_identity',
                `The v2 assignment ${unsupported.receipt.assignmentId} is not in a recoverable integration phase (${phaseByAssignment.get(unsupported.receipt.assignmentId)}).`
              );
            }
            // Independent deliveries are separate durable transactions. Complete one
            // member's private + canonical checks before starting the next, so a later
            // rejection/interruption cannot discard an earlier member's real receipt.
            // Recover old canonical-pending waves together at their recorded commit.
            const overlaps = (left: string, right: string) => {
              const a = path.resolve(boundProjectRoot, left).split(path.sep).join('/');
              const b = path.resolve(boundProjectRoot, right).split(path.sep).join('/');
              return a === b || a.startsWith(`${b}/`) || b.startsWith(`${a}/`);
            };
            const writeSets = selections.map(({ assignment }) => [
              assignment.sourceRootRelative,
              ...(assignment.request.sharedWritePaths ?? []),
            ]);
            const independent =
              selections.length > 1 &&
              selections.every((selection, index) => {
                if (phaseByAssignment.get(selection.receipt.assignmentId) === 'canonical_pending') return false;
                return selections.every((other, otherIndex) => {
                  if (index === otherIndex) return true;
                  if (selection.assignment.request.predecessorAssignmentId === other.assignment.assignmentId)
                    return false;
                  if (writeSets[index]!.some((left) => writeSets[otherIndex]!.some((right) => overlaps(left, right))))
                    return false;
                  // Frozen artifact inputs already exist independently of canonical merge;
                  // live paths into another member's write scope are not independent.
                  return !(selection.assignment.request.inputs ?? []).some(
                    (input) =>
                      'path' in input && writeSets[otherIndex]!.some((writePath) => overlaps(input.path, writePath))
                  );
                });
              });
            if (independent) {
              const members: Record<string, unknown>[] = [];
              for (const selection of selections) {
                const selector = input.deliveries.find((item) => item.targetSlotId === selection.receipt.slotId)!;
                const identity = {
                  delivery_id: selection.delivery.deliveryId,
                  assignment_id: selection.receipt.assignmentId,
                };
                if (context.signal?.aborted) {
                  members.push({
                    ...identity,
                    status: 'cancelled',
                    next_action: 'Resume this exact delivery only after explicit restart.',
                    integration_complete: false,
                  });
                  continue;
                }
                const response = await runResearchTeamToolOperation(
                  {
                    ...input,
                    deliveries: [selector],
                    ...(input.sourceArtifacts
                      ? {
                          sourceArtifacts: input.sourceArtifacts.filter(
                            (artifact) => artifact.deliveryId === selection.delivery.deliveryId
                          ),
                        }
                      : {}),
                  },
                  context
                );
                const text = response.content.find((entry) => entry.type === 'text');
                const payload = text?.type === 'text' ? (JSON.parse(text.text) as Record<string, unknown>) : {};
                const item = Array.isArray(payload.items) && isRecord(payload.items[0]) ? payload.items[0] : {};
                const completed = payload.integration_complete === true;
                const error = isRecord(payload.error) ? payload.error : undefined;
                const retryable = !error || error.retryable === true;
                const rejected = payload.status === 'candidate_rejected';
                members.push({
                  ...item,
                  ...identity,
                  status: completed
                    ? String(item.status ?? payload.status)
                    : context.signal?.aborted
                      ? 'cancelled'
                      : String(payload.status ?? 'unavailable'),
                  integration_complete: completed,
                  ...(payload.error ? { error: payload.error } : {}),
                  ...(payload.verification_error ? { verification_error: payload.verification_error } : {}),
                  ...(isRecord(payload.continuation) ? { continuation: payload.continuation } : {}),
                  ...(typeof payload.should_end_turn === 'boolean' ? { should_end_turn: payload.should_end_turn } : {}),
                  ...(typeof payload.instruction === 'string' ? { instruction: payload.instruction } : {}),
                  pending: payload.pending ?? (completed ? [] : ['integration_recovery']),
                  next_action: completed
                    ? 'Use the retained integrated result; do not repeat proof generation. Original-target verification remains independent.'
                    : payload.status === 'blocked' && typeof payload.instruction === 'string'
                      ? payload.instruction
                      : rejected
                        ? 'Dispatch the unique repair successor after the prior execution has ended; do not overwrite this frozen candidate.'
                        : context.signal?.aborted
                          ? 'Preserve this exact delivery and resume only after explicit restart.'
                          : !retryable
                            ? 'Correct the reported identity, permission or source problem before retry; do not repeat this unchanged operation.'
                            : 'Retry integrate with this same delivery to recover its durable state; do not rotate an unchecked candidate.',
                });
              }
              const integratedCount = members.filter((member) => member.integration_complete === true).length;
              // Earlier member observations can become stale after later writes.
              // Refresh only the lifecycle view; failure cannot undo any receipts.
              let continuation: Record<string, unknown> | undefined;
              if (members.some((member) => isRecord(member.continuation))) {
                try {
                  const observed = await runResearchTeamTool({ action: 'status' }, context);
                  const observedText = observed.content.find((entry) => entry.type === 'text');
                  continuation =
                    observedText?.type === 'text' ? JSON.parse(observedText.text) : { status: 'unavailable' };
                } catch {
                  continuation = {
                    status: 'unavailable',
                    error: 'math_batch_observation_unavailable',
                  };
                }
              }
              return result({
                schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
                action,
                protocol: 'v2',
                status: integratedCount === members.length ? 'integrated' : integratedCount ? 'partial' : 'pending',
                integration_complete: integratedCount === members.length,
                integrated_count: integratedCount,
                items: members,
                ...(continuation ? { continuation, should_end_turn: continuation.should_end_turn === true } : {}),
                pending: members
                  .filter((member) => member.integration_complete !== true)
                  .map((member) => ({
                    assignment_id: member.assignment_id,
                    next_action: member.next_action,
                    pending: member.pending,
                    ...(member.continuation ? { continuation: member.continuation } : {}),
                  })),
                instruction:
                  continuation && continuation.status !== 'observed'
                    ? 'Member integration results are recorded; current runtime observation is unavailable. Retry status before deciding capacity. Do not repeat integration solely to refresh status.'
                    : 'Each item reports its own durable integration state and next action. Retain completed members; use the latest attached observation for lifecycle decisions. Blocked reports require their legal continuation, not repeated integration. This batch result does not replace independent verification of every original theorem target.',
              });
            }
            const passiveItems = new Map<string, Record<string, unknown>>();
            const completePassive = context.projectGit?.completeResearchTeamAssignment;
            for (const selection of selections) {
              const phase = phaseByAssignment.get(selection.receipt.assignmentId)!;
              if (phase === 'advisory_report') {
                if (selection.receipt.state !== 'integrated') {
                  if (!completePassive)
                    throw new ResearchTeamOrchestrationError(
                      'math_v2_advisory_pending',
                      'The advisory report is durable, but the host completion port is unavailable.',
                      true
                    );
                  completePassive({
                    workspace: context.capability.projectRoot,
                    teamId: context.capability.teamId,
                    slotId: selection.receipt.slotId,
                    assignmentId: selection.receipt.assignmentId,
                    integration: { executionMode: 'advisory' },
                  });
                }
                passiveItems.set(selection.receipt.assignmentId, {
                  delivery_id: selection.delivery.deliveryId,
                  assignment_id: selection.receipt.assignmentId,
                  status: selection.receipt.state === 'integrated' ? 'already_advisory_accepted' : 'advisory_accepted',
                  provisional: true,
                  verification_status: 'not_formally_verified',
                });
              } else if (phase === 'blocked_report') {
                passiveItems.set(selection.receipt.assignmentId, {
                  delivery_id: selection.delivery.deliveryId,
                  assignment_id: selection.receipt.assignmentId,
                  status: 'blocked_report_accepted',
                  blockers: selection.delivery.delivery.blockers ?? [],
                });
              } else if (phase === 'private_rejected' || phase === 'canonical_rejected') {
                passiveItems.set(selection.receipt.assignmentId, {
                  delivery_id: selection.delivery.deliveryId,
                  assignment_id: selection.receipt.assignmentId,
                  status: 'candidate_rejected',
                  verification_error:
                    selection.receipt.integration?.verification?.diagnostics ??
                    'The frozen candidate was rejected by complete source verification.',
                  next_action: 'Dispatch the unique repair successor after the prior execution has ended.',
                });
              }
            }
            const activeSelections = selections.filter(
              (selection) => !passiveItems.has(selection.receipt.assignmentId)
            );
            const presentItems = (
              formalItems: readonly Record<string, unknown>[]
            ): readonly Record<string, unknown>[] => {
              const formalByAssignment = new Map(formalItems.map((item) => [String(item.assignment_id ?? ''), item]));
              return Object.freeze(
                originalV2Receipts.map(
                  (receipt) => passiveItems.get(receipt.assignmentId) ?? formalByAssignment.get(receipt.assignmentId)!
                )
              );
            };
            if (!activeSelections.length) {
              const hasBlocked = [...phaseByAssignment.values()].includes('blocked_report');
              const hasRejected = [...phaseByAssignment.values()].some(
                (phase) => phase === 'private_rejected' || phase === 'canonical_rejected'
              );
              // Advisory integration closes that report, not the proof. Reuse
              // the authorized Core + strict WAL status path after the write,
              // so the Lead cannot mistake a completed Researcher for active
              // work or lose the blocked proof owner's retained assignment.
              // A failed observation must not roll back or obscure integration;
              // it is returned separately and can be retried through status.
              const observed = await runResearchTeamTool({ action: 'status' }, context);
              const observedText = observed.content.find((entry) => entry.type === 'text');
              const continuation =
                observedText?.type === 'text'
                  ? (JSON.parse(observedText.text) as Record<string, unknown>)
                  : { status: 'unavailable' };
              return result({
                schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
                action,
                protocol: 'v2',
                status: hasBlocked ? 'blocked' : hasRejected ? 'candidate_rejected' : 'integrated',
                integration_complete: !hasBlocked && !hasRejected,
                pending: hasBlocked ? ['explicit_successor_or_resume'] : hasRejected ? ['repair_successor'] : [],
                items: presentItems([]),
                continuation,
                should_end_turn: continuation.should_end_turn === true,
                instruction:
                  continuation.status !== 'observed'
                    ? 'Integration is recorded; runtime observation is unavailable. Retry status before deciding capacity. Do not repeat integration solely to refresh status.'
                    : 'This integration acknowledges only the selected reports. Use the attached current observation for the next lifecycle decision; an accepted advisory report is no longer outstanding research. Resume a blocked proof through its legal successor when evidence enables it, or dispatch a concrete independent investigation to available capacity. Only an original-target receipt completes the theorem.',
              });
            }
            v2Receipts = activeSelections.map((selection) => selection.receipt);
            const v2SourceArtifacts = input.sourceArtifacts
              ? new Map(
                  v2Receipts.map((receipt) => [
                    receipt.assignmentId,
                    input.sourceArtifacts!.filter((artifact) => artifact.deliveryId === receipt.delivery!.deliveryId),
                  ])
                )
              : undefined;
            if (v2Receipts.every((receipt) => receipt.state === 'integrated')) {
              const resolveCommit = context.projectGit?.resolveCommit;
              const isCommitAncestor = context.projectGit?.isCommitAncestor;
              const journal = context.mathIntegrationJournal;
              if (!resolveCommit || !isCommitAncestor || !journal) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_integrated_recovery_pending',
                  'The integrated v2 wave requires the host Git identity checks and integration journal.',
                  true
                );
              }
              const finalCommits = new Set(
                v2Receipts.map((receipt) => receipt.integration?.mergedCommit).filter(Boolean)
              );
              if (finalCommits.size !== 1) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_integrated_identity',
                  'The integrated v2 wave does not share one final canonical commit.'
                );
              }
              for (const receipt of v2Receipts) {
                const assignment = normalizeRuntimeMathAssignment(receipt.assignment);
                assertMathV2IntegratedSourceIdentity(receipt, assignment, projectRelative);
                const integration = receipt.integration!;
                const branchHead = resolveCommit({
                  workspace: context.capability.projectRoot,
                  reference: integration.branch!,
                });
                if (
                  branchHead.toLowerCase() !== integration.headCommit!.toLowerCase() ||
                  !isCommitAncestor({
                    workspace: context.capability.projectRoot,
                    ancestor: integration.headCommit!,
                    descendant: integration.mergedCommit!,
                  }) ||
                  !isCommitAncestor({
                    workspace: context.capability.projectRoot,
                    ancestor: integration.mergedCommit!,
                    descendant: 'HEAD',
                  })
                ) {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_integrated_identity',
                    'The integrated v2 Git identity is no longer reachable from the canonical project.'
                  );
                }
                const effect = await journal.prepare({
                  assignmentId: receipt.assignmentId,
                  branch: integration.branch!,
                  deliveredHead: integration.headCommit!,
                  expectedBase: assignment.baseCommit,
                });
                if (!effect.observed || !effect.mergedCommit) {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_integrated_recovery_pending',
                    'The integrated v2 merge effect has not been durably observed.',
                    true
                  );
                }
                await journal.commit(effect.effectId, effect.mergedCommit);
              }
              return result({
                schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
                action,
                protocol: 'v2',
                status: 'already_integrated',
                integration_complete: true,
                pending: [],
                items: v2Receipts.map((receipt) => ({
                  delivery_id: receipt.delivery!.deliveryId,
                  assignment_id: receipt.assignmentId,
                  merged_commit: receipt.integration!.mergedCommit,
                  already_integrated: true,
                })),
              });
            }
            const assignments = v2Receipts.map((receipt) => normalizeRuntimeMathAssignment(receipt.assignment));
            const phases = v2Receipts.map((receipt) => phaseByAssignment.get(receipt.assignmentId)!);
            const integratedIndices = phases
              .map((phase, index) => (phase === 'canonical_verified' ? index : -1))
              .filter((index) => index >= 0);
            const privatePendingIndices = phases
              .map((phase, index) => (phase === 'private_pending' ? index : -1))
              .filter((index) => index >= 0);
            const canonicalPendingIndices = phases
              .map((phase, index) => (phase === 'canonical_pending' ? index : -1))
              .filter((index) => index >= 0);
            const freshIndices = v2Receipts
              .map((_receipt, index) => (phases[index] === 'fresh_source' ? index : -1))
              .filter((index) => index >= 0);
            const recoveredStages = v2SourceArtifacts
              ? undefined
              : context.recoverMathSources
                ? await context.recoverMathSources(v2Receipts)
                : undefined;
            const recoveredByDelivery = new Map((recoveredStages ?? []).map((stage) => [stage.deliveryId, stage]));
            if (!v2SourceArtifacts && !context.recoverMathSources && freshIndices.length > 0)
              throw new ResearchTeamOrchestrationError(
                'math_v2_integration_writer_pending',
                'Source staging requires source_artifacts or the host source-stage recovery port.'
              );
            const sourceEntries = v2Receipts.map((receipt, index) => {
              const assignment = assignments[index]!;
              if (v2SourceArtifacts) {
                const rawArtifacts = v2SourceArtifacts.get(assignment.assignmentId) ?? [];
                if (!rawArtifacts.length)
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_source_artifact_missing',
                    'Source artifacts are missing for a selected delivery.'
                  );
                const normalizedArtifacts = rawArtifacts.map((rawArtifact) =>
                  normalizeMathSourceArtifact(rawArtifact, {
                    assignmentId: assignment.assignmentId,
                    deliveryId: receipt.delivery!.deliveryId,
                    baseCommit: assignment.baseCommit,
                    sourceRoot: path.resolve(boundProjectRoot, assignment.sourceRootRelative),
                    verificationTargets: assignment.request.verificationTargets,
                  })
                );
                const artifact = normalizedArtifacts[0]!;
                const outputHash = mathSourceArtifactOutputSha256(artifact);
                if (
                  normalizedArtifacts.some(
                    (candidate) =>
                      candidate.pathRelative !== artifact.pathRelative ||
                      mathSourceArtifactOutputSha256(candidate) !== outputHash
                  )
                )
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_source_artifact_conflict',
                    'Multiple targets for one source must share one frozen source result.'
                  );
                return Object.freeze({
                  pathRelative: artifact.pathRelative,
                  contentSha256: outputHash,
                  targets: normalizedArtifacts.map((candidate) => ({
                    verificationTargetId: candidate.verificationTargetId,
                    theoremName: candidate.theoremName,
                    statementHash: candidate.statementHash,
                    ...(candidate.leanStatementHash ? { leanStatementHash: candidate.leanStatementHash } : {}),
                    expectedSourceDeclarationHash: candidate.expectedSourceDeclarationHash,
                    ...(candidate.claim ? { claim: candidate.claim } : {}),
                  })),
                  artifact,
                });
              }
              const recovered = recoveredByDelivery.get(receipt.delivery!.deliveryId);
              if (!recovered?.ready) {
                const integration = receipt.integration;
                const evidence = integration?.verification;
                const evidenceIndex = evidence?.itemIds.findIndex((id) => id.startsWith(`${assignment.assignmentId}:`));
                const targetId =
                  evidenceIndex !== undefined && evidenceIndex >= 0
                    ? evidence!.itemIds[evidenceIndex]!.slice(assignment.assignmentId.length + 1)
                    : undefined;
                const target = targetId
                  ? assignment.request.verificationTargets.find((candidate) => candidate.targetId === targetId)
                  : new Set(assignment.request.verificationTargets.map((candidate) => candidate.pathRelative)).size ===
                      1
                    ? assignment.request.verificationTargets[0]
                    : undefined;
                const sourceHash =
                  evidenceIndex !== undefined && evidenceIndex >= 0 ? evidence!.sourceHashes[evidenceIndex] : undefined;
                if (
                  !target ||
                  !sourceHash ||
                  !integration?.headCommit ||
                  !['private_pending', 'canonical_pending', 'canonical_verified'].includes(phases[index])
                )
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_integration_writer_pending',
                    `Durable source stage for ${receipt.assignmentId} is incomplete; resend source_artifacts to repair it.`
                  );
                const recoveredTargets = assignment.request.verificationTargets.filter(
                  (candidate) => candidate.pathRelative === target.pathRelative
                );
                return Object.freeze({
                  pathRelative: target.pathRelative,
                  contentSha256: sourceHash,
                  targets: (recoveredTargets.length ? recoveredTargets : [target]).map((candidate) => ({
                    verificationTargetId: candidate.targetId,
                    theoremName: candidate.theoremName,
                    statementHash: candidate.statementHash,
                    ...(candidate.leanStatementHash ? { leanStatementHash: candidate.leanStatementHash } : {}),
                    expectedSourceDeclarationHash: candidate.expectedSourceDeclarationHash,
                    ...(candidate.claim ? { claim: candidate.claim } : {}),
                  })),
                });
              }
              const recoveredTargets = assignment.request.verificationTargets.filter(
                (candidate) => candidate.pathRelative === recovered.pathRelative
              );
              return Object.freeze({
                pathRelative: recovered.pathRelative,
                contentSha256: recovered.resultContentSha256 ?? recovered.contentSha256,
                targets: (recoveredTargets.length ? recoveredTargets : [recovered]).map((candidate) => ({
                  verificationTargetId: 'targetId' in candidate ? candidate.targetId : candidate.verificationTargetId,
                  theoremName: 'targetId' in candidate ? candidate.theoremName : candidate.theoremName,
                  statementHash: candidate.statementHash,
                  ...('leanStatementHash' in candidate && candidate.leanStatementHash
                    ? { leanStatementHash: candidate.leanStatementHash }
                    : {}),
                  expectedSourceDeclarationHash: candidate.expectedSourceDeclarationHash,
                  ...('claim' in candidate && candidate.claim ? { claim: candidate.claim } : {}),
                })),
              });
            });
            const verificationItems = sourceEntries.flatMap((source, index) =>
              source.targets.map(
                (target): MathV2VerificationItem =>
                  Object.freeze({
                    id: `${assignments[index]!.assignmentId}:${target.verificationTargetId}`,
                    proofPath: path
                      .join(projectRelative, assignments[index]!.sourceRootRelative, source.pathRelative)
                      .replaceAll(path.sep, '/'),
                    contentSha256: source.contentSha256,
                    theoremName: target.theoremName,
                    statementHash: target.statementHash,
                    ...(target.leanStatementHash ? { leanStatementHash: target.leanStatementHash } : {}),
                    expectedSourceDeclarationHash: target.expectedSourceDeclarationHash,
                    ...(target.claim ? { claim: target.claim } : {}),
                  })
              )
            );
            const verificationItemsByAssignment = assignments.map((assignment) =>
              verificationItems.filter((item) => item.id.startsWith(`${assignment.assignmentId}:`))
            );
            if (
              integratedIndices.length +
                privatePendingIndices.length +
                canonicalPendingIndices.length +
                freshIndices.length !==
              v2Receipts.length
            ) {
              throw new ResearchTeamOrchestrationError(
                'math_v2_reverification_identity',
                'The v2 integration wave contains an unsupported WAL phase.'
              );
            }
            const knownFinalCommits = new Set(
              [...integratedIndices, ...canonicalPendingIndices]
                .map((index) => v2Receipts[index]!.integration?.mergedCommit)
                .filter(Boolean)
            );
            if (knownFinalCommits.size > 1) {
              throw new ResearchTeamOrchestrationError(
                'math_v2_reverification_identity',
                'The recovering v2 integration wave does not share one final canonical commit.'
              );
            }
            const knownFinalCommit = [...knownFinalCommits][0];
            for (const index of [...integratedIndices, ...canonicalPendingIndices]) {
              const integration = v2Receipts[index]!.integration;
              if (
                integration?.executionMode !== 'artifact' ||
                !integration.branch ||
                !integration.headCommit ||
                !integration.mergedCommit
              ) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_reverification_identity',
                  'The recovering v2 assignment is missing its durable Git identity.'
                );
              }
            }
            const staged =
              freshIndices.length && v2SourceArtifacts
                ? await context.stageMathSources(
                    freshIndices.map((index) => v2Receipts[index]!),
                    freshIndices.flatMap((index) => v2SourceArtifacts.get(v2Receipts[index]!.assignmentId) ?? [])
                  )
                : [];
            const promotions: Array<{
              receiptIndex: number;
              assignmentId: string;
              deliveryId: string;
              branch: string;
              worktreePath: string;
              files: readonly string[];
              verificationItems: readonly MathV2VerificationItem[];
            }> = [];
            const commitWorktree = context.commitMathV2Worktree;
            const verifyWorktree = context.verifyMathV2Worktree;
            const journal = context.mathIntegrationJournal;
            const integrateBranch = context.projectGit?.integrateAgentBranch;
            const recordAssignment = context.projectGit?.recordResearchTeamAssignment;
            const completeAssignment = context.projectGit?.completeResearchTeamAssignment;
            const resolveCommit = context.projectGit?.resolveCommit;
            const isCommitAncestor = context.projectGit?.isCommitAncestor;
            const recoveryReady = Boolean(
              verifyWorktree &&
              journal &&
              completeAssignment &&
              (integratedIndices.length === 0 || (resolveCommit && isCommitAncestor))
            );
            const freshPromotionReady = Boolean(
              commitWorktree &&
              integrateBranch &&
              recordAssignment &&
              freshIndices.every((index) => v2Receipts[index]!.preparedGit)
            );
            if (!recoveryReady || (freshIndices.length > 0 && !freshPromotionReady)) {
              if (knownFinalCommit) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_reverification_pending',
                  'The recovering v2 wave requires all host verification, Git integration, WAL, and journal ports.',
                  true
                );
              }
              return result({
                schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
                action,
                protocol: 'v2',
                status: 'drafts_staged',
                integration_complete: false,
                pending: ['kernel_verification', 'canonical_git_integration'],
                items: staged.map((item) => ({
                  delivery_id: item.deliveryId,
                  assignment_id: item.assignmentId,
                  plan_id: item.planId,
                  path_relative: item.pathRelative,
                  content_sha256: item.contentSha256,
                })),
              });
            }
            if (freshIndices.length) {
              for (const index of freshIndices) {
                const receipt = v2Receipts[index]!;
                const assignment = assignments[index]!;
                const promotion = prepareMathV2Promotion(receipt, assignment, context.capability.projectRoot);
                const source = sourceEntries[index]!;
                const files = promoteMathV2DraftToWorktree(
                  promotion,
                  assignment,
                  [{ pathRelative: source.pathRelative, contentSha256: source.contentSha256 }],
                  context.capability.projectRoot,
                  boundProjectRoot
                );
                const assignmentVerificationItems = verificationItemsByAssignment[index]!;
                promotions.push({
                  receiptIndex: index,
                  assignmentId: assignment.assignmentId,
                  deliveryId: receipt.delivery!.deliveryId,
                  branch: promotion.branch,
                  worktreePath: promotion.worktreePath,
                  files,
                  verificationItems: assignmentVerificationItems,
                });
              }
            }
            const commits = promotions.map((promotion) =>
              commitWorktree!({
                ...promotion,
                includePaths: promotion.files,
                expectedFiles: [
                  {
                    pathRelative: promotion.verificationItems[0]!.proofPath,
                    contentSha256: promotion.verificationItems[0]!.contentSha256,
                  },
                ],
                baseCommit: assignments[promotion.receiptIndex]!.baseCommit,
              })
            );
            const privateVerificationFailures: string[] = [];
            const privateVerificationResults: Array<{
              promotion: (typeof promotions)[number];
              verification: MathV2VerificationResult;
              commit: (typeof commits)[number];
            }> = [];
            const privatePendingVerificationResults: Array<{
              receiptIndex: number;
              verification: MathV2VerificationResult;
            }> = [];
            if (commits.length > 0) {
              for (let index = 0; index < promotions.length; index++) {
                const verification = await verifyWorktree!({
                  worktreePath: promotions[index]!.worktreePath,
                  ...(projectRelative ? { projectRelative } : {}),
                  targetCommit: commits[index]!.commit,
                  items: promotions[index]!.verificationItems,
                  signal: context.signal,
                });
                if (!verification.verified) {
                  privateVerificationFailures.push(
                    verification.diagnostics || `Lean rejected assignment ${promotions[index]!.assignmentId}.`
                  );
                  privateVerificationResults.push({
                    promotion: promotions[index]!,
                    verification,
                    commit: commits[index]!,
                  });
                }
              }
            }
            const privatePendingVerifiedIndices: number[] = [];
            for (const index of privatePendingIndices) {
              const receipt = v2Receipts[index]!;
              const integration = receipt.integration;
              if (
                !integration?.branch ||
                !integration.headCommit ||
                integration.mergedCommit ||
                integration.retainedWithoutMerge !== true
              ) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_reverification_identity',
                  `Private pending assignment ${receipt.assignmentId} is missing its exact unmerged Git identity.`
                );
              }
              const verification = await verifyWorktree!({
                worktreePath: context.capability.projectRoot,
                ...(projectRelative ? { projectRelative } : {}),
                targetCommit: integration.headCommit,
                items: verificationItemsByAssignment[index]!,
                signal: context.signal,
              });
              if (verification.disposition === 'integrity_error') {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_reverification_identity',
                  verification.diagnostics || `Private verification identity failed for ${receipt.assignmentId}.`
                );
              }
              if (verification.verified) privatePendingVerifiedIndices.push(index);
              else {
                privateVerificationFailures.push(
                  verification.diagnostics || `Lean rejected assignment ${receipt.assignmentId}.`
                );
                privatePendingVerificationResults.push({ receiptIndex: index, verification });
              }
            }
            if (privateVerificationResults.length) {
              for (const rejected of privateVerificationResults) {
                const evidence = rejected.verification.evidence;
                if (rejected.verification.disposition === 'integrity_error') {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_reverification_identity',
                    rejected.verification.diagnostics || 'Private candidate verification returned an integrity error.'
                  );
                }
                if (!evidence) {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_reverification_pending',
                    'A failed private verification did not return durable host evidence.',
                    true
                  );
                }
                const receipt = v2Receipts[rejected.promotion.receiptIndex]!;
                recordAssignment!({
                  schema: 'deepscientist.research_team_assignment.v2',
                  workspace: context.capability.projectRoot,
                  teamId: context.capability.teamId,
                  slotId: receipt.slotId,
                  assignmentId: receipt.assignmentId,
                  assignment: receipt.assignment,
                  state: 'accepted',
                  integration: {
                    executionMode: 'artifact',
                    branch: rejected.promotion.branch,
                    headCommit: rejected.commit.commit,
                    retainedWithoutMerge: true,
                    verification: evidence,
                  },
                });
              }
            }
            for (const rejected of privatePendingVerificationResults) {
              const receipt = v2Receipts[rejected.receiptIndex]!;
              const integration = receipt.integration!;
              const evidence = rejected.verification.evidence;
              if (!evidence) {
                throw new ResearchTeamOrchestrationError(
                  'math_v2_reverification_pending',
                  `Private verification for ${receipt.assignmentId} did not return durable host evidence.`,
                  true
                );
              }
              recordAssignment!({
                schema: 'deepscientist.research_team_assignment.v2',
                workspace: context.capability.projectRoot,
                teamId: context.capability.teamId,
                slotId: receipt.slotId,
                assignmentId: receipt.assignmentId,
                assignment: receipt.assignment,
                state: 'accepted',
                integration: {
                  executionMode: 'artifact',
                  branch: integration.branch,
                  headCommit: integration.headCommit,
                  retainedWithoutMerge: true,
                  verification: evidence,
                },
              });
            }
            const effects = new Map<number, Readonly<{ effectId: string; mergedCommit: string }>>();
            if (!privateVerificationFailures.length && privatePendingVerificationResults.length === 0) {
              for (const index of [...integratedIndices, ...canonicalPendingIndices]) {
                const receipt = v2Receipts[index]!;
                if (receipt.state === 'integrated') {
                  assertMathV2IntegratedSourceIdentity(receipt, assignments[index]!, projectRelative);
                  const integration = receipt.integration!;
                  if (
                    resolveCommit!({
                      workspace: context.capability.projectRoot,
                      reference: integration.branch!,
                    }).toLowerCase() !== integration.headCommit!.toLowerCase() ||
                    !isCommitAncestor!({
                      workspace: context.capability.projectRoot,
                      ancestor: integration.headCommit!,
                      descendant: integration.mergedCommit!,
                    }) ||
                    !isCommitAncestor!({
                      workspace: context.capability.projectRoot,
                      ancestor: integration.mergedCommit!,
                      descendant: 'HEAD',
                    })
                  ) {
                    throw new ResearchTeamOrchestrationError(
                      'math_v2_integrated_identity',
                      'The integrated v2 Git identity is no longer reachable from the canonical project.'
                    );
                  }
                }
                const integration = receipt.integration!;
                const effect = await journal!.prepare({
                  assignmentId: receipt.assignmentId,
                  branch: integration.branch!,
                  deliveredHead: integration.headCommit!,
                  expectedBase: assignments[index]!.baseCommit,
                });
                if (!effect.observed || !effect.mergedCommit) {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_reverification_pending',
                    'A recovering v2 merge effect has not been durably observed.',
                    true
                  );
                }
                effects.set(index, { effectId: effect.effectId, mergedCommit: effect.mergedCommit });
              }
              for (const index of privatePendingVerifiedIndices) {
                const receipt = v2Receipts[index]!;
                const integration = receipt.integration!;
                const assignment = assignments[index]!;
                const effect = await journal!.prepare({
                  assignmentId: receipt.assignmentId,
                  branch: integration.branch!,
                  deliveredHead: integration.headCommit!,
                  expectedBase: assignment.baseCommit,
                });
                const integrated =
                  effect.observed && effect.mergedCommit
                    ? { ok: true as const, mergedCommit: effect.mergedCommit }
                    : integrateBranch!({
                        workspace: context.capability.projectRoot,
                        teamId: context.capability.teamId,
                        slotId: receipt.slotId,
                        branch: integration.branch!,
                        assignmentId: receipt.assignmentId,
                        orchestrationNamespace: gitNamespace(context.capability),
                        expectedHead: integration.headCommit!,
                        summary: 'Mathematics private candidate integration',
                      });
                if (!integrated.ok || !integrated.mergedCommit)
                  throw new ResearchTeamOrchestrationError(
                    'integration_failed',
                    integrated.error || 'Unable to merge the verified private Mathematics worktree.'
                  );
                if (!effect.observed) await journal!.observe(effect.effectId, integrated.mergedCommit);
                effects.set(index, { effectId: effect.effectId, mergedCommit: integrated.mergedCommit });
              }
              for (let index = 0; index < promotions.length; index++) {
                const commit = commits[index]!;
                const promotion = promotions[index]!;
                const receiptIndex = promotion.receiptIndex;
                const assignment = assignments[receiptIndex]!;
                const effect = await journal!.prepare({
                  assignmentId: assignment.assignmentId,
                  branch: promotion.branch,
                  deliveredHead: commit.commit,
                  expectedBase: assignment.baseCommit,
                });
                if (knownFinalCommit && !effect.observed) {
                  throw new ResearchTeamOrchestrationError(
                    'math_v2_reverification_identity',
                    'A partially recorded v2 wave would require a duplicate canonical merge.'
                  );
                }
                const integrated =
                  effect.observed && effect.mergedCommit
                    ? { ok: true as const, mergedCommit: effect.mergedCommit }
                    : integrateBranch!({
                        workspace: context.capability.projectRoot,
                        teamId: context.capability.teamId,
                        slotId: v2Receipts[receiptIndex]!.slotId,
                        branch: promotion.branch,
                        assignmentId: assignment.assignmentId,
                        orchestrationNamespace: gitNamespace(context.capability),
                        expectedHead: commit.commit,
                        summary: 'Mathematics source integration',
                      });
                if (!integrated.ok || !integrated.mergedCommit)
                  throw new ResearchTeamOrchestrationError(
                    'integration_failed',
                    integrated.error || 'Unable to merge the v2 Mathematics worktree.'
                  );
                if (!effect.observed) await journal!.observe(effect.effectId, integrated.mergedCommit);
                effects.set(receiptIndex, { effectId: effect.effectId, mergedCommit: integrated.mergedCommit });
              }
            }
            const finalMergedCommit =
              knownFinalCommit ??
              (privatePendingVerifiedIndices.length
                ? effects.get(privatePendingVerifiedIndices.at(-1)!)?.mergedCommit
                : promotions.length
                  ? effects.get(promotions.at(-1)!.receiptIndex)?.mergedCommit
                  : undefined);
            let canonicalVerification: MathV2VerificationResult | undefined;
            const activeIndices = [...canonicalPendingIndices, ...privatePendingVerifiedIndices, ...freshIndices].sort(
              (left, right) => left - right
            );
            if (finalMergedCommit && !privateVerificationFailures.length) {
              const activeVerificationItems = activeIndices.flatMap((index) => verificationItemsByAssignment[index]!);
              canonicalVerification = await verifyWorktree!({
                worktreePath: context.capability.projectRoot,
                ...(projectRelative ? { projectRelative } : {}),
                targetCommit: finalMergedCommit,
                items: activeVerificationItems,
                signal: context.signal,
              });
              const canonicalReceiptsComplete =
                canonicalVerification.verified &&
                canonicalVerification.receipts?.length === activeVerificationItems.length;
              for (let activeIndex = 0; activeIndex < activeIndices.length; activeIndex++) {
                const index = activeIndices[activeIndex]!;
                const receipt = v2Receipts[index]!;
                const assignment = assignments[index]!;
                const promotion = promotions.find((candidate) => candidate.receiptIndex === index);
                const commit = promotion ? commits[promotions.indexOf(promotion)] : undefined;
                const assignmentItems = verificationItemsByAssignment[index]!;
                const assignmentReceipts = (canonicalVerification.receipts ?? []).filter((candidate) =>
                  assignmentItems.some(
                    (item) => item.theoremName === candidate.theoremName && item.proofPath === candidate.sourcePath
                  )
                );
                const sourceVerificationReceipt = assignmentReceipts[0];
                const verifiedOriginalTarget = assignment.request.verificationTargets?.find(
                  (target) =>
                    target.statementHash === binding.statementHash &&
                    target.claim !== 'negation' &&
                    sourceVerificationReceipt?.statementHash === target.statementHash &&
                    sourceVerificationReceipt.theoremName === target.theoremName
                );
                const receiptSecret = readMathematicsReceiptSecret();
                const solverReadyReceipt =
                  canonicalReceiptsComplete &&
                  sourceVerificationReceipt &&
                  verifiedOriginalTarget &&
                  binding.initialRouteFingerprint &&
                  receiptSecret
                    ? signMathSolverReadyReceipt(
                        {
                          teamId: context.capability.teamId,
                          slotId: receipt.slotId,
                          assignmentId: assignment.assignmentId,
                          deliveryId: receipt.delivery!.deliveryId,
                          targetCommit: finalMergedCommit,
                          statementHash: verifiedOriginalTarget.statementHash,
                          routeFingerprint: binding.initialRouteFingerprint,
                          checkedAt: Date.now(),
                        },
                        receiptSecret
                      )
                    : undefined;
                const priorIntegration = receipt.integration;
                const verificationEvidence = canonicalVerification?.evidence;
                const assignmentVerificationEvidence =
                  verificationEvidence &&
                  verificationItemsByAssignment[index]!.some((item) => verificationEvidence.itemIds.includes(item.id))
                    ? verificationEvidence
                    : undefined;
                const integration = {
                  executionMode: 'artifact' as const,
                  branch: priorIntegration?.branch ?? promotion?.branch,
                  headCommit: priorIntegration?.headCommit ?? commit?.commit,
                  mergedCommit: finalMergedCommit,
                  ...(canonicalReceiptsComplete
                    ? { sourceVerificationReceipts: assignmentReceipts }
                    : {
                        reverificationRequired: true as const,
                        ...(assignmentVerificationEvidence ? { verification: assignmentVerificationEvidence } : {}),
                      }),
                  ...(solverReadyReceipt ? { solverReadyReceipt } : {}),
                };
                if (canonicalReceiptsComplete) {
                  completeAssignment!({
                    workspace: context.capability.projectRoot,
                    teamId: context.capability.teamId,
                    slotId: receipt.slotId,
                    assignmentId: assignment.assignmentId,
                    integration,
                  });
                  const effect = effects.get(index);
                  if (!effect) throw new Error('math_integration_effect_integrity');
                  await journal!.commit(effect.effectId, effect.mergedCommit);
                  if (solverReadyReceipt)
                    retireCompetingMathProofOwner(context, receipt.slotId, assignment.assignmentId);
                } else {
                  recordAssignment!({
                    schema: 'deepscientist.research_team_assignment.v2',
                    workspace: context.capability.projectRoot,
                    teamId: context.capability.teamId,
                    slotId: receipt.slotId,
                    assignmentId: assignment.assignmentId,
                    assignment: receipt.assignment,
                    state: 'accepted',
                    integration,
                  });
                }
              }
              if (canonicalReceiptsComplete) {
                for (const index of integratedIndices) {
                  const effect = effects.get(index);
                  if (!effect) throw new Error('math_integration_effect_integrity');
                  await journal!.commit(effect.effectId, effect.mergedCommit);
                }
              }
            }
            const integrationComplete = Boolean(
              finalMergedCommit &&
              canonicalVerification?.verified &&
              canonicalVerification.receipts?.length ===
                activeIndices.flatMap((index) => verificationItemsByAssignment[index]!).length
            );
            return result({
              schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
              action,
              protocol: 'v2',
              status: integrationComplete
                ? 'integrated'
                : privatePendingVerificationResults.some(
                      ({ verification }) => verification.disposition === 'candidate_rejected'
                    ) ||
                    privateVerificationResults.some(
                      ({ verification }) => verification.disposition === 'candidate_rejected'
                    )
                  ? 'candidate_rejected'
                  : finalMergedCommit
                    ? 'integrated_pending_verification'
                    : commits.some(Boolean)
                      ? 'worktree_committed'
                      : promotions.length
                        ? 'worktree_promoted'
                        : 'drafts_staged',
              integration_complete: integrationComplete,
              pending: integrationComplete
                ? []
                : privatePendingVerificationResults.some(
                      ({ verification }) => verification.disposition === 'candidate_rejected'
                    ) ||
                    privateVerificationResults.some(
                      ({ verification }) => verification.disposition === 'candidate_rejected'
                    )
                  ? ['repair_successor']
                  : finalMergedCommit
                    ? ['kernel_verification']
                    : ['kernel_verification', 'canonical_git_integration'],
              ...(privateVerificationFailures.length
                ? { verification_error: privateVerificationFailures.join('; ') }
                : canonicalVerification?.diagnostics
                  ? { verification_error: canonicalVerification.diagnostics }
                  : {}),
              items: v2Receipts.map((receipt, index) => {
                const stagedItem = staged.find((item) => item.assignmentId === receipt.assignmentId);
                const promotion = promotions.find((candidate) => candidate.receiptIndex === index);
                const commit = promotion ? commits[promotions.indexOf(promotion)] : undefined;
                return {
                  delivery_id: receipt.delivery!.deliveryId,
                  assignment_id: receipt.assignmentId,
                  path_relative: sourceEntries[index]!.pathRelative,
                  content_sha256: sourceEntries[index]!.contentSha256,
                  ...(stagedItem ? { plan_id: stagedItem.planId } : {}),
                  ...(promotion ? { promotion } : {}),
                  ...(commit ? { commit: commit.commit } : {}),
                  ...(finalMergedCommit ? { merged_commit: finalMergedCommit } : {}),
                };
              }),
            });
          }
        }
        if (input.sourceArtifacts !== undefined)
          throw new ResearchTeamOrchestrationError(
            'math_v2_integration_mixed',
            'Source artifacts require durable v2 deliveries.'
          );
        const batch = normalizeIntegrationBatch(
          input.deliveries,
          context.capability,
          preparationRuntime.context.projectGit,
          preparationRuntime.context.readAssignment,
          preparationRuntime.context.validateAssignment,
          preparationRuntime.context.validateResult
        );
        const integrationAssignmentIds = Object.freeze(batch.map((item) => item.result.assignmentId));
        const mathematicsArtifactAssignmentIds = Object.freeze(
          batch.filter((item) => item.result.executionMode !== 'advisory').map((item) => item.result.assignmentId)
        );
        const mathematicsBatchReverification =
          context.capability.profileId === 'mathematics-research-team' && mathematicsArtifactAssignmentIds.length > 1
            ? {
                expectedAssignmentIds: new Set(mathematicsArtifactAssignmentIds),
                entries: new Map(),
              }
            : undefined;
        const runtime: ResearchTeamRuntime<RuntimeContext> = Object.freeze({
          ...preparationRuntime,
          context: Object.freeze({
            ...preparationRuntime.context,
            deferMathResearchPersistence:
              context.capability.profileId === 'mathematics-research-team' && integrationAssignmentIds.length > 1,
            integrationAssignmentIds,
            completionEligibleAssignmentId: integrationAssignmentIds[integrationAssignmentIds.length - 1],
            ...(mathematicsBatchReverification ? { mathematicsBatchReverification } : {}),
          }),
        });
        const items = await researchTeamOrchestrator.integrateMany(batch, runtime);
        const conditionalReviewDispatches = await dispatchConditionalMathematicsReviews(batch, items, context);
        const integratedCount = items.filter((item) =>
          [
            'integrated',
            'already_integrated',
            'advisory_accepted',
            'retained_unmerged',
            'already_retained_unmerged',
          ].includes(String(item.status))
        ).length;
        const mathResearchWaveSynthesis = deriveMathResearchWaveSynthesis(
          batch,
          items,
          context.capability,
          context.capability.projectRoot
        );
        const presentedItems = items.map((item, index) => {
          const assignmentId = batch[index]?.result.assignmentId;
          const reviewDispatch = assignmentId ? conditionalReviewDispatches.get(assignmentId) : undefined;
          const projected = reviewDispatch ? { ...item, review_dispatch: reviewDispatch } : item;
          if (!mathResearchWaveSynthesis) return Object.freeze(projected);
          const { next_assignment: _nextAssignment, ...withoutNextAssignment } = projected;
          return Object.freeze(withoutNextAssignment);
        });
        return result({
          schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
          action,
          status: integratedCount === items.length ? 'integrated' : integratedCount > 0 ? 'partial' : 'unavailable',
          team_id: context.capability.teamId,
          items: presentedItems,
          integrated_count: integratedCount,
          ...(mathResearchWaveSynthesis ? { math_research_wave_synthesis: mathResearchWaveSynthesis } : {}),
        });
      }
    }
  } catch (error) {
    return errorResult(input.action, error, context.capability);
  }
}

function dispatchBlocker(items: readonly ItemResult[]): Readonly<Record<string, unknown>> | undefined {
  if (!items.length || items.some((item) => item.status === 'accepted')) return undefined;
  const errors = items
    .map((item) => (isRecord(item.error) ? item.error : undefined))
    .filter((error): error is Record<string, unknown> => Boolean(error));
  const requiresLeadCheckpoint =
    errors.length === items.length &&
    errors.every(
      (error) =>
        error.code === 'agent_worktree_unavailable' &&
        /lead checkpoint|clean the project before dispatching an agent worktree/iu.test(String(error.message || ''))
    );
  if (!requiresLeadCheckpoint) return undefined;
  return Object.freeze({
    code: 'lead_checkpoint_required',
    retryable: true,
    recovery_action: 'project_workspace.checkpoint',
    message:
      'No Worker was started. Verify the intended Lead changes, create one explicit project checkpoint, then retry this wave with the returned commit as every assignment git.baseCommit.',
  });
}

function appendRuntimeCounterexampleProbeEvidence(
  resultInput: Record<string, unknown>,
  assignment: ResearchTeamAssignment,
  probe: LeanEvalCounterexampleProbe,
  teamId: string
): Record<string, unknown> {
  if (!isRecord(resultInput.math)) return resultInput;
  const math = resultInput.math;
  const existing = Array.isArray(math.evidenceDelta)
    ? math.evidenceDelta.filter((item): item is Record<string, unknown> => isRecord(item))
    : [];
  const runtimeProbe = assignment.math?.fastCheck?.runtimeProbe;
  const probeIdentity = crypto
    .createHash('sha256')
    .update(
      JSON.stringify({
        statementHash: assignment.math?.statementHash,
        runtimeProbe,
        outcome: probe.outcome,
        casesChecked: probe.casesChecked,
        witness: probe.witness,
        proofStateFingerprint: probe.proofStateFingerprint,
      })
    )
    .digest('hex');
  const ref = `lean-counterexample-probe:${assignment.assignmentId}:${probeIdentity}`;
  if (existing.some((item) => item.ref === ref)) return resultInput;
  const detail =
    probe.outcome === 'counterexample_found'
      ? `Runtime bounded Lean probe found a witness${probe.witness ? `: ${probe.witness}` : ''}.`
      : probe.outcome === 'no_counterexample_found'
        ? `Runtime bounded Lean probe found no witness in ${probe.casesChecked} sampled case(s).`
        : `Runtime bounded Lean probe was inconclusive after ${probe.casesChecked} sampled case(s).`;
  const skipped = probe.casesSkipped ? ` ${probe.casesSkipped} case(s) were excluded by the precondition.` : '';
  const diagnostic = probe.diagnostics.find((value) => typeof value === 'string' && value.trim());
  const sampledCases = runtimeProbe?.cases ?? ['0', '1', '2', '3'];
  const expressionHash = runtimeProbe
    ? crypto.createHash('sha256').update(runtimeProbe.expression, 'utf8').digest('hex')
    : undefined;
  const preconditionHash = runtimeProbe?.precondition
    ? crypto.createHash('sha256').update(runtimeProbe.precondition, 'utf8').digest('hex')
    : undefined;
  const candidateCommit =
    isRecord(resultInput.git) && typeof resultInput.git.headCommit === 'string'
      ? resultInput.git.headCommit
      : undefined;
  const provenance = [
    `statementHash=${assignment.math?.statementHash ?? 'unknown'}`,
    `scope=bounded; sampledCases=${JSON.stringify(sampledCases).slice(0, 1_200)}`,
    ...(expressionHash ? [`expressionSha256=${expressionHash}`] : []),
    ...(preconditionHash ? [`preconditionSha256=${preconditionHash}`] : []),
    `command=${probe.command ?? 'lake env lean <sandboxed-counterexample-probe>'}`,
    'reproducibility=single_run',
    `baseCommit=${assignment.git.baseCommit}`,
    ...(candidateCommit ? [`candidateCommit=${candidateCommit}`] : []),
    ...(probe.proofStateFingerprint ? [`proofStateFingerprint=${probe.proofStateFingerprint}`] : []),
    ...(probe.sandboxBackend ? [`sandboxBackend=${probe.sandboxBackend}`] : []),
  ].join('; ');
  const summary = `${detail}${skipped}${diagnostic ? ` ${diagnostic}` : ''} ${provenance}`.slice(0, 4_000);
  const evidence = Object.freeze({
    kind: 'counterexample_probe',
    ref,
    summary,
  });
  const nextSingleObjective =
    probe.outcome === 'counterexample_found'
      ? 'Freeze the canonical formal negation and dispatch a refutation follow-up; formal refuted status still requires a Lean negation receipt and the official comparator.'
      : undefined;
  const observation =
    probe.attempted && probe.proofStateFingerprint && runtimeProbe
      ? signMathResearchObservation({
          teamId,
          assignmentId: assignment.assignmentId,
          fingerprint: probe.proofStateFingerprint,
          provenance: {
            inputDigest: crypto.createHash('sha256').update(JSON.stringify(runtimeProbe), 'utf8').digest('hex'),
            casesDigest: crypto
              .createHash('sha256')
              .update(
                JSON.stringify({
                  cases: probe.casesUsed ?? sampledCases,
                  originalCases: probe.originalCasesUsed ?? [],
                }),
                'utf8'
              )
              .digest('hex'),
            expression: runtimeProbe.expression.slice(0, 1_000),
            ...(runtimeProbe.precondition ? { precondition: runtimeProbe.precondition.slice(0, 500) } : {}),
            mode: runtimeProbe.mode ?? 'proposition',
            outcome: probe.outcome,
            casesChecked: probe.casesChecked,
            casesRequested: probe.casesRequested ?? sampledCases.length,
            ...(probe.witness
              ? { witnessDigest: crypto.createHash('sha256').update(probe.witness, 'utf8').digest('hex') }
              : {}),
          },
          statement: `${detail}${skipped}`.slice(0, 1_500),
        })
      : undefined;
  const finding = isRecord(resultInput.mathResearchFinding) ? resultInput.mathResearchFinding : undefined;
  const findingEvidenceRefs =
    finding && Array.isArray(finding.evidenceRefs)
      ? finding.evidenceRefs.filter((value): value is string => typeof value === 'string' && Boolean(value.trim()))
      : [];
  const findingEvidence =
    finding && Array.isArray(finding.evidence)
      ? finding.evidence.filter((value): value is Record<string, unknown> => isRecord(value))
      : [];
  const researchEvidenceRef = observation?.reference ?? ref;
  const runtimeFindingEvidence = Object.freeze({
    grade: probe.attempted ? 'runtime_checked' : 'observed',
    scope: 'bounded_observation',
    statement: `${detail}${skipped}`.slice(0, 4_000),
    reference: ref,
  });
  return Object.freeze({
    ...resultInput,
    ...(finding
      ? {
          mathResearchFinding: Object.freeze({
            ...finding,
            evidenceRefs: Object.freeze([...new Set([...findingEvidenceRefs, researchEvidenceRef])]),
            evidence: Object.freeze([...findingEvidence, runtimeFindingEvidence]),
          }),
        }
      : {}),
    math: Object.freeze({
      ...math,
      evidenceDelta: Object.freeze([...existing, evidence]),
      ...(nextSingleObjective ? { nextSingleObjective } : {}),
    }),
  });
}

/**
 * Re-verify a Worker-provided helper receipt before it reaches result
 * normalization. The receipt metadata selects the artifact and declaration;
 * the returned receipt is always rebuilt from the kernel verifier output.
 */
async function verifyDeliveredMathematicsHelper(
  value: Record<string, unknown>,
  assignment: ResearchTeamAssignment,
  projectRoot: string,
  targetCommit: string,
  verifier: ResearchTeamToolContext['verifyMathematicsHelperNode']
): Promise<Record<string, unknown>> {
  let rawReceipt = isRecord(value.mathHelperReceipt) ? value.mathHelperReceipt : undefined;
  const math = isRecord(value.math) ? value.math : undefined;
  const expansion =
    math && isRecord(math.planExpansion) ? normalizeMathPlanExpansion(math.planExpansion as never) : undefined;
  if (!rawReceipt && !expansion) return value;
  if (!verifier) {
    throw new Error('Mathematics helper receipt requires the host Lean helper verifier');
  }
  if (assignment.math?.stage !== 'formalize' || assignment.laneId !== 'lean-engineering') {
    throw new Error('Mathematics helper receipt is only valid for a formalization assignment');
  }
  if (!expansion) {
    throw new Error('Mathematics helper receipt requires a validated planExpansion');
  }
  const artifactPaths = [...(assignment.math.artifactPaths ?? []), ...assignment.expectedArtifacts].map((artifact) =>
    artifact.split('#', 1)[0]!.replaceAll('\\', '/')
  );
  if (!rawReceipt) {
    // A plan expansion may omit receipt metadata. Discover a newly committed
    // helper by matching each added node's canonical declaration header.
    const discovered: Array<{
      node: (typeof expansion.addedNodes)[number];
      sourceFile: string;
      declarationName: string;
      declarationKind: 'theorem' | 'definition';
      declarationType: string;
      importModules: readonly string[];
    }> = [];
    for (const sourceFile of artifactPaths) {
      if (!sourceFile.toLowerCase().endsWith('.lean')) continue;
      let source: string;
      try {
        source = execFileSync('git', ['show', `${targetCommit}:${sourceFile}`], {
          cwd: projectRoot,
          encoding: 'utf8',
          maxBuffer: 512 * 1024,
        });
      } catch {
        continue;
      }
      for (const node of expansion.addedNodes) {
        for (const declaration of inspectLeanDeclarations(source)) {
          const declarationKind = declaration.kind === 'definition' ? 'definition' : 'theorem';
          if (declarationKind !== (node.kind === 'definition' ? 'definition' : 'theorem')) continue;
          const declarationHash = hashMathFormalSourceDeclaration(node.provisionalLeanStatement, declaration.name);
          if (!declarationHash || declarationHash !== hashMathFormalSourceDeclaration(source, declaration.name))
            continue;
          discovered.push({
            node,
            sourceFile,
            declarationName: declaration.name,
            declarationKind,
            declarationType: declaration.declarationType,
            importModules: Object.freeze(
              [...source.matchAll(/^\s*import\s+([^\s]+)/gmu)].map((match) => match[1]!).filter(Boolean)
            ),
          });
        }
      }
    }
    if (discovered.length !== 1) return value;
    const selected = discovered[0]!;
    rawReceipt = {
      helperPlanNodeId: selected.node.id,
      parentPlanNodeId: selected.node.parentNodeId,
      declarationKind: selected.declarationKind,
      declarationName: selected.declarationName,
      declarationType: selected.declarationType,
      sourceFile: selected.sourceFile,
      importModules: selected.importModules,
      sourceProvenance: selected.node.sourceProvenance ?? [],
    };
  }
  const helperNode = expansion.addedNodes.find((node) => node.id === rawReceipt!.helperPlanNodeId);
  if (!helperNode || !helperNode.parentNodeId || helperNode.parentNodeId !== rawReceipt.parentPlanNodeId) {
    throw new Error('Mathematics helper receipt does not identify a node introduced by planExpansion');
  }
  const directAttempt = assignment.math.directAttempt === true;
  if (directAttempt && (expansion.expandedNodeId !== 'direct-goal' || helperNode.parentNodeId !== 'direct-goal')) {
    throw new Error('Direct Mathematics helper expansion must bind the helper directly beneath direct-goal');
  }
  const sourceFile = typeof rawReceipt.sourceFile === 'string' ? rawReceipt.sourceFile.trim() : '';
  if (!sourceFile || !sourceFile.toLowerCase().endsWith('.lean') || !artifactPaths.includes(sourceFile)) {
    throw new Error('Mathematics helper receipt sourceFile must be one of the assigned Lean artifacts');
  }
  const declarationKind =
    rawReceipt.declarationKind === 'definition' || rawReceipt.declarationKind === 'theorem'
      ? rawReceipt.declarationKind
      : undefined;
  const declarationName = typeof rawReceipt.declarationName === 'string' ? rawReceipt.declarationName.trim() : '';
  const expectedDeclarationKind = helperNode.kind === 'definition' ? 'definition' : 'theorem';
  const importModules = Array.isArray(rawReceipt.importModules)
    ? rawReceipt.importModules.filter((item): item is string => typeof item === 'string' && Boolean(item.trim()))
    : [];
  const sourceProvenance = Array.isArray(rawReceipt.sourceProvenance) ? rawReceipt.sourceProvenance : [];
  if (declarationKind !== expectedDeclarationKind) {
    throw new Error(
      `Mathematics helper declaration kind must match expanded node: expected ${expectedDeclarationKind}`
    );
  }
  if (!declarationName) {
    throw new Error('Mathematics helper receipt declaration metadata is incomplete');
  }
  const verification = await verifier({
    projectRoot,
    proofPath: sourceFile,
    theoremName: declarationName,
    declarationKind,
    helperPlanNodeId: helperNode.id,
    parentPlanNodeId: helperNode.parentNodeId!,
    statementHash: assignment.math.statementHash,
    routeFingerprint: assignment.math.routeFingerprint,
    targetCommit,
    importModules,
    sourceProvenance: (helperNode.sourceProvenance ?? sourceProvenance) as never,
  });
  if (verification.status !== 'kernel_verified' || !verification.receipt) {
    throw new Error(verification.error || 'Mathematics helper failed Lean kernel verification');
  }
  const verifiedMath =
    directAttempt && math
      ? Object.freeze({
          ...math,
          planExpansion: Object.freeze({
            ...expansion,
            expandedNodeId: 'direct-goal',
            addedNodes: Object.freeze([helperNode]),
          }),
        })
      : math;
  return Object.freeze({
    ...value,
    ...(verifiedMath ? { math: verifiedMath } : {}),
    mathHelperReceipt: verification.receipt,
  });
}

const gitText = (workspace: string, args: readonly string[]): string =>
  execFileSync('git', ['-C', workspace, ...args], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'ignore'],
    maxBuffer: 2 * 1024 * 1024,
  }).trim();

const gitBlob = (workspace: string, commit: string, relativePath: string): string | undefined => {
  try {
    return execFileSync('git', ['-C', workspace, 'show', `${commit}:${relativePath}`], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      maxBuffer: 2 * 1024 * 1024,
    });
  } catch {
    return undefined;
  }
};

const gitNameStatus = (
  workspace: string,
  from: string,
  to: string
): readonly Readonly<{ status: string; path: string }>[] => {
  const raw = execFileSync('git', ['-C', workspace, 'diff', '--name-status', '--no-renames', '-z', from, to], {
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'ignore'],
    maxBuffer: 2 * 1024 * 1024,
  });
  const fields = raw.split('\0');
  const entries: Array<Readonly<{ status: string; path: string }>> = [];
  for (let index = 0; index + 1 < fields.length; index += 2) {
    const status = fields[index]?.trim() || '';
    const relativePath = fields[index + 1]?.trim().replaceAll('\\', '/') || '';
    if (status && relativePath) entries.push(Object.freeze({ status, path: relativePath }));
  }
  return Object.freeze(entries);
};

function qualifiedLeanDeclarationCandidates(
  source: string,
  declarationName: string,
  moduleName: string
): readonly string[] {
  const localName = declarationName.split('.').at(-1) || declarationName;
  const candidates = new Set<string>();
  if (declarationName.includes('.')) candidates.add(declarationName);
  const namespaceMatches = [
    ...stripLeanCommentsAndStrings(source).matchAll(/^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$/gmu),
  ];
  for (const match of namespaceMatches.toReversed()) {
    if (match[1]) candidates.add(`${match[1]}.${localName}`);
  }
  if (moduleName) candidates.add(`${moduleName}.${localName}`);
  candidates.add(localName);
  return Object.freeze([...candidates]);
}

/**
 * Accept a helper-only Lean-Eval commit as a nonterminal checkpoint. The
 * complete Submission theorem is intentionally not compiled here: it may
 * still contain the public template hole. Every byte in the candidate delta
 * must remain in a manifest-owned helper file, and every introduced declaration
 * receives its own kernel receipt before the checkpoint is accepted.
 */
async function checkpointDirectLeanEvalHelper(
  value: Record<string, unknown>,
  assignment: ResearchTeamAssignment,
  workspaceRoot: string,
  verifier: ResearchTeamToolContext['verifyMathematicsHelperNode']
): Promise<DirectLeanEvalHelperCheckpoint | undefined> {
  if (
    assignment.math?.stage !== 'formalize' ||
    assignment.math.directAttempt !== true ||
    assignment.math.activePlanNodeId !== 'direct-goal' ||
    !assignment.math.problemContract?.officialManifestId?.startsWith('lean-eval:')
  ) {
    return undefined;
  }
  const math = isRecord(value.math) ? value.math : undefined;
  const claimsWholeProofCompletion =
    math?.routeDisposition === 'advance' &&
    Number(math.openGoalCountBefore) > 0 &&
    Number(math.openGoalCountAfter) === 0;
  if (claimsWholeProofCompletion) return undefined;

  const git = isRecord(value.git) ? value.git : undefined;
  const targetCommit = typeof git?.headCommit === 'string' ? git.headCommit.trim().toLowerCase() : '';
  if (!/^[0-9a-f]{40,64}$/u.test(targetCommit)) return undefined;
  const canonicalWorkspace = fs.realpathSync(path.resolve(workspaceRoot));
  let receipt: ReturnType<typeof readLeanEvalBootstrapReceipt>;
  try {
    receipt = readLeanEvalBootstrapReceipt(path.join(canonicalWorkspace, 'active-problem.json'));
  } catch {
    return undefined;
  }
  if (fs.realpathSync(path.resolve(receipt.workspaceRoot)) !== canonicalWorkspace) {
    throw new Error('Lean-Eval helper checkpoint workspace does not match its bootstrap receipt');
  }
  if (gitText(canonicalWorkspace, ['rev-parse', 'HEAD']).toLowerCase() !== targetCommit) {
    throw new Error('Lean-Eval helper checkpoint must target the current prepared Worker HEAD');
  }

  const solverProjectRoot = fs.realpathSync(path.resolve(receipt.projectRoot));
  const solverProjectPrefix = path.relative(canonicalWorkspace, solverProjectRoot).replaceAll(path.sep, '/');
  if (!solverProjectPrefix || solverProjectPrefix.startsWith('../') || path.isAbsolute(solverProjectPrefix)) {
    throw new Error('Lean-Eval helper checkpoint solver project is outside the prepared workspace');
  }
  const helperFiles = new Map<string, string>();
  for (const solverFile of receipt.solverOwnedFiles) {
    const normalized = solverFile.trim().replaceAll('\\', '/');
    if (!normalized.startsWith('Submission/') || !normalized.toLowerCase().endsWith('.lean')) continue;
    helperFiles.set(`${solverProjectPrefix}/${normalized}`, normalized);
  }
  if (!helperFiles.size) return undefined;

  const rootCommit = gitText(canonicalWorkspace, ['rev-list', '--max-parents=0', targetCommit]).split(/\s+/u).at(-1);
  const parentCommit = gitText(canonicalWorkspace, ['rev-parse', `${targetCommit}^`]).toLowerCase();
  if (!rootCommit || !/^[0-9a-f]{40,64}$/u.test(parentCommit)) return undefined;
  const completeDelta = gitNameStatus(canonicalWorkspace, rootCommit, targetCommit);
  const latestDelta = gitNameStatus(canonicalWorkspace, parentCommit, targetCommit);
  if (
    !completeDelta.length ||
    !latestDelta.length ||
    completeDelta.some((entry) => entry.status.startsWith('D') || !helperFiles.has(entry.path)) ||
    latestDelta.some((entry) => entry.status.startsWith('D') || !helperFiles.has(entry.path))
  ) {
    return undefined;
  }

  for (const entry of completeDelta) {
    const baseSource = gitBlob(canonicalWorkspace, rootCommit, entry.path) ?? '';
    const candidateSource = gitBlob(canonicalWorkspace, targetCommit, entry.path);
    if (candidateSource === undefined) return undefined;
    if (leanProofEscapeCount(candidateSource) > leanProofEscapeCount(baseSource)) {
      throw new Error(
        `Lean-Eval helper checkpoint adds a forbidden Lean proof escape in ${helperFiles.get(entry.path)}`
      );
    }
  }

  const introduced: Array<{
    sourceFile: string;
    source: string;
    declaration: Readonly<{
      name: string;
      kind: 'theorem' | 'definition';
      declarationType: string;
    }>;
  }> = [];
  for (const entry of latestDelta) {
    const before = gitBlob(canonicalWorkspace, parentCommit, entry.path) ?? '';
    const after = gitBlob(canonicalWorkspace, targetCommit, entry.path);
    if (after === undefined) return undefined;
    const beforeDeclarations = new Map(
      inspectLeanDeclarations(before).map((declaration) => [
        declaration.name,
        hashMathFormalSourceDeclaration(before, declaration.name),
      ])
    );
    const afterDeclarations = inspectLeanDeclarations(after);
    if (
      [...beforeDeclarations].some(
        ([name, declarationHash]) => hashMathFormalSourceDeclaration(after, name) !== declarationHash
      )
    ) {
      return undefined;
    }
    for (const declaration of afterDeclarations) {
      if (
        !beforeDeclarations.has(declaration.name) &&
        (declaration.kind === 'theorem' || declaration.kind === 'definition')
      ) {
        introduced.push({
          sourceFile: helperFiles.get(entry.path)!,
          source: after,
          declaration: {
            name: declaration.name,
            kind: declaration.kind,
            declarationType: declaration.declarationType,
          },
        });
      }
    }
  }
  if (!introduced.length) return undefined;
  if (!verifier) throw new Error('Lean-Eval helper checkpoint requires the host Lean helper verifier');

  const helpers: Array<DirectLeanEvalHelperCheckpoint['helpers'][number]> = [];
  for (const selected of introduced) {
    const declarationHash = hashMathFormalSourceDeclaration(selected.source, selected.declaration.name);
    if (!declarationHash) return undefined;
    const helperPlanNodeId = `direct-helper-${crypto
      .createHash('sha256')
      .update(`${targetCommit}\0${selected.sourceFile}\0${selected.declaration.name}\0${declarationHash}`)
      .digest('hex')
      .slice(0, 20)}`;
    const moduleName = selected.sourceFile.replace(/\.lean$/u, '').replaceAll('/', '.');
    const importModules = Object.freeze(
      [...selected.source.matchAll(/^\s*import\s+([^\s]+)/gmu)].map((match) => match[1]!).filter(Boolean)
    );
    const sourceProvenance = Object.freeze([
      Object.freeze({
        kind: 'local' as const,
        locator: selected.sourceFile,
        compatibility: 'exact' as const,
        commit: targetCommit,
        evidenceRef: `lean-helper:${targetCommit}:${selected.sourceFile}:${selected.declaration.name}`,
      }),
    ]);
    const proposedNode = Object.freeze({
      id: helperPlanNodeId,
      informalClaim: `Kernel-checked local helper ${selected.declaration.name}.`,
      provisionalLeanStatement: `${selected.declaration.kind === 'definition' ? 'def' : 'theorem'} ${selected.declaration.declarationType} := by`,
      dependsOn: Object.freeze([] as string[]),
      parentNodeId: 'direct-goal',
      role: 'auxiliary' as const,
      kind: 'ported_helper' as const,
      status: 'proposed' as const,
      evidenceRefs: Object.freeze([] as string[]),
      sourceProvenance,
    });
    normalizeMathPlanExpansion({
      expandedNodeId: 'direct-goal',
      addedNodes: [proposedNode],
      reason: 'Retain a kernel-checked dependency while the whole direct goal remains open.',
      evidenceRefs: [`lean-helper:${selected.sourceFile}:${selected.declaration.name}`],
    });

    let verified: MathematicsHelperVerificationResult | undefined;
    let verificationError = '';
    let verifiedDeclarationName = '';
    for (const declarationName of qualifiedLeanDeclarationCandidates(
      selected.source,
      selected.declaration.name,
      moduleName
    )) {
      // eslint-disable-next-line no-await-in-loop
      const candidate = await verifier({
        projectRoot: solverProjectRoot,
        proofPath: selected.sourceFile,
        theoremName: declarationName,
        declarationKind: selected.declaration.kind,
        helperPlanNodeId,
        parentPlanNodeId: 'direct-goal',
        statementHash: assignment.math.statementHash,
        routeFingerprint: assignment.math.routeFingerprint,
        targetCommit,
        importModules,
        sourceProvenance,
        forbiddenImportModules: ['Solution', 'Submission.Solution'],
      });
      if (candidate.status === 'kernel_verified' && candidate.receipt) {
        verified = candidate;
        verifiedDeclarationName = declarationName;
        break;
      }
      verificationError = candidate.error || 'Lean kernel rejected the helper declaration';
    }
    if (!verified?.receipt) throw new Error(verificationError || 'Lean kernel rejected the helper declaration');
    const helperReceipt = normalizeMathHelperReceipt(verified.receipt);
    if (
      helperReceipt.declarationName !== verifiedDeclarationName ||
      helperReceipt.declarationKind !== selected.declaration.kind ||
      helperReceipt.targetCommit !== targetCommit ||
      helperReceipt.statementHash !== assignment.math.statementHash ||
      helperReceipt.routeFingerprint !== assignment.math.routeFingerprint ||
      helperReceipt.helperPlanNodeId !== helperPlanNodeId ||
      helperReceipt.parentPlanNodeId !== 'direct-goal' ||
      helperReceipt.sourceFile !== selected.sourceFile ||
      helperReceipt.sourceDeclarationHash !== declarationHash ||
      helperReceipt.goalsRemaining !== 0 ||
      helperReceipt.sorryCount !== 0 ||
      helperReceipt.admitCount !== 0 ||
      !helperReceipt.axioms.every(isMathFoundationalLeanAxiom)
    ) {
      throw new Error('Lean-Eval helper verifier returned a receipt that does not match the committed declaration');
    }
    const helperPlanNode = Object.freeze({
      ...proposedNode,
      status: 'kernel_verified' as const,
      evidenceRefs: Object.freeze([`lean-receipt:${helperReceipt.receiptId}`]),
    });
    helpers.push(Object.freeze({ sourceFile: selected.sourceFile, helperPlanNode, receipt: helperReceipt }));
  }
  // Do not expose a partially verified batch as accepted progress.
  return Object.freeze({
    targetCommit,
    solverProjectPath: solverProjectPrefix,
    ...helpers[0]!,
    helpers: Object.freeze(helpers),
  });
}

async function shareRuntimeMathProgress(
  rawResult: unknown,
  context: ResearchTeamToolContext,
  targetSlotId?: string,
  expectedAssignmentId?: string
): Promise<ToolResult> {
  const { capability } = context;
  if (
    capability.roleKind !== 'worker' ||
    capability.profileId !== 'mathematics-research-team' ||
    !context.prepareMathLiteShare
  ) {
    throw new ResearchTeamOrchestrationError('unauthorized', 'Progress sharing requires a mathematics lite Worker.');
  }
  const intent = mathLiteProgressIntentSchema.parse(rawResult);
  context.signal?.throwIfAborted();
  const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
  const active =
    projectGit
      .listResearchTeamAssignments?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['accepted'],
        strict: true,
      })
      .filter(
        (receipt) =>
          receipt.state === 'accepted' &&
          !receipt.delivery &&
          !receipt.integration &&
          !receipt.supersessionPending &&
          !receipt.budgetCancellation
      ) ?? [];
  const owned = active.filter((receipt) => receipt.slotId === capability.slotId);
  const binding = context.readMathAssignmentBinding?.();
  if (owned.length !== 1 || !binding || owned[0]!.schema !== 'deepscientist.research_team_assignment.v2') {
    throw new ResearchTeamOrchestrationError(
      'math_share_assignment_unavailable',
      'Sharing requires exactly one accepted v2 assignment without a final delivery.'
    );
  }
  const receipt = owned[0]!;
  if (expectedAssignmentId !== undefined && receipt.assignmentId !== expectedAssignmentId) {
    throw new ResearchTeamOrchestrationError(
      'math_share_assignment_changed',
      'The original progress assignment identity changed. Do not publish its remaining content to a successor.'
    );
  }
  const assignment = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: binding.bindingDigest,
    expectedTargetSlotId: capability.slotId,
    ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
  });
  if (receipt.assignmentId !== assignment.assignmentId || receipt.teamId !== capability.teamId) {
    throw new ResearchTeamOrchestrationError('integrity', 'The progress assignment identity is inconsistent.');
  }
  let shared: Awaited<ReturnType<NonNullable<ResearchTeamToolContext['prepareMathLiteShare']>>>;
  try {
    shared = await context.prepareMathLiteShare({
      rawResult,
      receipt,
      assignment,
      ...(targetSlotId ? { targetSlotId } : {}),
    });
  } catch (error) {
    context.signal?.throwIfAborted();
    if (
      !intent.files?.length ||
      !(error instanceof Error) ||
      (!(error instanceof ResearchTeamOrchestrationError && error.code === 'math_share_attachment_unavailable') &&
        ![
          'math_lite_delivery_file_missing',
          'math_lite_delivery_file_encoding',
          'math_lite_delivery_source_changed',
        ].includes(error.message))
    ) {
      throw error;
    }
    return {
      ...result({
        schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
        action: 'share',
        status: 'unavailable',
        accepted: false,
        message_sent: false,
        error: { code: 'math_share_attachment_not_frozen', message: error.message, retryable: true },
        recovery: {
          instruction:
            'No progress message was sent. If the summary contains the complete provisional finding, retry the exact summary-only request below now. Repair and share attachments separately afterwards. This does not deliver or verify the assignment.',
          request: {
            action: 'share',
            ...(targetSlotId ? { target_slot_id: targetSlotId } : {}),
            result: { summary: intent.summary },
          },
        },
      }),
      isError: true,
    };
  }
  context.signal?.throwIfAborted();
  const current = projectGit.listResearchTeamAssignments!({
    workspace: capability.projectRoot,
    teamId: capability.teamId,
    strict: true,
  }).find((entry) => entry.assignmentId === receipt.assignmentId);
  if (
    !current ||
    current.state !== 'accepted' ||
    current.delivery ||
    current.integration ||
    current.supersessionPending ||
    current.budgetCancellation ||
    current.teamId !== receipt.teamId ||
    current.slotId !== receipt.slotId ||
    !isDeepStrictEqual(current.assignment, receipt.assignment) ||
    !isDeepStrictEqual(current.preparedGit, receipt.preparedGit)
  ) {
    throw new ResearchTeamOrchestrationError(
      'math_share_assignment_changed',
      'The assignment changed before progress publication.'
    );
  }
  const lead = capability.roster.find((member) => member.roleKind === 'lead');
  const client = requireClient(context.client);
  if (!lead || !client.deliver)
    throw new ResearchTeamOrchestrationError('unavailable', 'Progress delivery transport is unavailable.');
  // Team state for the Lead's own decision: which Workers currently hold no active
  // assignment. Informational only; it neither requests nor schedules any dispatch.
  const busySlots = new Set(
    (
      projectGit.listResearchTeamAssignments?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['prepared', 'accepted'],
        strict: true,
      }) ?? []
    )
      .filter(
        (entry) =>
          (entry.state === 'prepared' || entry.state === 'accepted') &&
          !entry.delivery &&
          !entry.integration &&
          !entry.supersessionPending &&
          !entry.budgetCancellation
      )
      .map((entry) => entry.slotId)
  );
  const idleWorkers =
    assignment.kind === 'formalize'
      ? capability.roster
          .filter((member) => member.roleKind === 'worker' && !busySlots.has(member.slotId))
          .map((member) => ({
            agentId: teamAgentIdForSlotId(member.slotId, capability.roster) ?? member.slotId,
            ...(member.laneId ? { laneId: member.laneId } : {}),
          }))
      : [];
  const message = JSON.stringify({
    schema: 'deepscientist.math.progress-share.v1',
    runId: assignment.runId,
    bindingDigest: assignment.bindingDigest,
    assignmentId: receipt.assignmentId,
    targetSlotId: capability.slotId,
    ...shared,
    ...(idleWorkers.length ? { idleWorkers } : {}),
    provisional: true,
    instruction:
      'Research progress only; not a final delivery or proof acceptance. The source assignment remains active.',
  });
  const ack = await client.deliver(
    capability.teamId,
    capability.slotId,
    lead.slotId,
    message,
    context.signal,
    `math-share-${shared.shareId}`
  );
  if (
    ack.team_id !== capability.teamId ||
    ack.accepted_slot_id !== lead.slotId ||
    ack.target_slot_id !== lead.slotId ||
    ack.accepted_role !== 'lead' ||
    !isTeamRunAckPersisted(ack)
  ) {
    throw new ResearchTeamOrchestrationError(
      'math_share_not_persisted',
      'Core did not persist progress for the Lead; retry the unchanged share.',
      true
    );
  }
  context.signal?.throwIfAborted();
  await context.acknowledgeMathLiteShare?.(shared.shareId, receipt.assignmentId);
  return result({
    schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
    action: 'share',
    status: 'shared',
    accepted: true,
    ...shared,
    provisional: true,
    assignment_state: 'accepted',
    instruction:
      'Progress is shared without ending this assignment. Retain the same source and proof owner. Continue independent obligations; if none remain while linked research is outstanding, end only this conversational turn and wait for feedback, not a terminal delivery.',
  });
}

/** Reuse ordinary immutable shares without expanding their public byte budget. */
async function shareBlockedMathProgress(
  intent: ReturnType<typeof normalizeMathLiteDeliveryIntent>,
  context: ResearchTeamToolContext,
  expectedAssignmentId: string,
  instruction: string
): Promise<ToolResult> {
  const blockers = intent.blockers ?? [];
  const blockerPrefix = 'Remaining blockers:\n';
  const combined = blockers.length ? `${intent.summary}\n${blockerPrefix}${blockers.join('\n')}` : intent.summary;
  const summaries: string[] = [];
  if (mathLiteProgressIntentSchema.safeParse({ summary: combined }).success) {
    summaries.push(combined);
  } else {
    summaries.push(intent.summary);
    let pending = '';
    for (const blocker of blockers) {
      const candidate = pending ? `${pending}\n${blocker}` : `${blockerPrefix}${blocker}`;
      if (pending && !mathLiteProgressIntentSchema.safeParse({ summary: candidate }).success) {
        summaries.push(pending);
        pending = `${blockerPrefix}${blocker}`;
      } else {
        pending = candidate;
      }
    }
    if (pending) summaries.push(pending);
  }
  let shared: ToolResult | undefined;
  for (const [index, summary] of summaries.entries()) {
    // The existing share identity and transport key make completed groups exact
    // replays if a later group fails. Attach files only to the first group.
    // eslint-disable-next-line no-await-in-loop
    shared = await shareRuntimeMathProgress(
      { summary, ...(index === 0 && intent.files ? { files: intent.files } : {}) },
      context,
      undefined,
      expectedAssignmentId
    );
    if (shared.isError) {
      let attachmentRecovery = false;
      try {
        const payload = JSON.parse(shared.content[0]?.text ?? '{}') as Record<string, unknown>;
        attachmentRecovery =
          payload.error &&
          typeof payload.error === 'object' &&
          (payload.error as Record<string, unknown>).code === 'math_share_attachment_not_frozen';
      } catch {
        attachmentRecovery = false;
      }
      if (!attachmentRecovery || index !== 0 || !intent.files?.length) return shared;
      // Keep the complete blocked intent in the legal deliver recovery request.
      // Retrying that unchanged request after repairing the attachment re-enters
      // this loop and sends every summary/blocker group under the same assignment.
      let payload: Record<string, unknown> = {};
      try {
        payload = JSON.parse(shared.content[0]?.text ?? '{}') as Record<string, unknown>;
      } catch {
        payload = {};
      }
      return {
        ...result({
          ...payload,
          recovery: {
            ...(payload.recovery && typeof payload.recovery === 'object' ? payload.recovery : {}),
            instruction:
              'Repair the attachment, then retry this exact deliver request. It retains the complete blocked summary and all blockers; the host will replay every progress group under the same assignment.',
            request: {
              action: 'deliver',
              result: {
                status: intent.status,
                summary: intent.summary,
                ...(intent.files ? { files: intent.files } : {}),
                ...(intent.blockers ? { blockers: intent.blockers } : {}),
              },
            },
          },
        }),
        isError: true,
      };
    }
  }
  const payload = JSON.parse(shared!.content[0]!.text) as Record<string, unknown>;
  return {
    ...shared!,
    ...result({
      ...payload,
      instruction: `All summary and blocker content has been shared without ending this assignment. ${instruction} ${payload.instruction}`,
    }),
  };
}

async function deliverRuntimeMathResult(
  rawResult: unknown,
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  context: ResearchTeamToolContext
): Promise<ToolResult> {
  const { capability } = context;
  const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
  if (!projectGit.recordResearchTeamDelivery)
    throw new ResearchTeamOrchestrationError('integrity', 'Durable v2 delivery storage is unavailable.');
  const binding = context.readMathAssignmentBinding?.();
  if (!binding) throw new ResearchTeamOrchestrationError('integrity', 'The frozen v2 run binding is unavailable.');
  const view = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
    expectedRunId: binding.runId,
    expectedBindingDigest: binding.bindingDigest,
    expectedTargetSlotId: capability.slotId,
    ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
  });
  if (
    receipt.teamId !== capability.teamId ||
    receipt.assignmentId !== view.assignmentId ||
    receipt.slotId !== capability.slotId
  )
    throw new ResearchTeamOrchestrationError('integrity', 'The v2 assignment receipt identity is inconsistent.');
  const deliveryId = createProjectGitResearchTeamDeliveryId(capability.teamId, capability.slotId, receipt.assignmentId);
  let deliveryPhase: 'preparing' | 'sealed' | 'delivered' = receipt.delivery ? 'delivered' : 'preparing';
  try {
    context.signal?.throwIfAborted();
    if (deliveryPhase === 'preparing' && context.hasMathLiteSealedDelivery?.(deliveryId)) deliveryPhase = 'sealed';
    if (
      rawResult !== undefined &&
      context.prepareMathLiteShare &&
      !receipt.delivery &&
      !receipt.integration &&
      !context.hasMathLiteSealedDelivery?.(deliveryId) &&
      (await context.isUnchangedMathLiteBlockedRetry?.(receipt, rawResult))
    ) {
      const intent = normalizeMathLiteDeliveryIntent(rawResult);
      return await shareBlockedMathProgress(
        intent,
        context,
        receipt.assignmentId,
        'This checkpoint is unchanged. Continue in this same assignment with a concrete source change or a test of the unresolved inference.'
      );
    }
    // Preserve an active proof episode while its own linked investigation is
    // outstanding. Use the existing immutable share path, never seal a partial
    // proof merely to wait for evidence. Already sealed requests must replay.
    if (
      rawResult !== undefined &&
      context.prepareMathLiteDelivery &&
      context.readMathLiteFeedback &&
      context.prepareMathLiteShare &&
      context.hasMathLiteSealedDelivery &&
      !context.hasMathLiteSealedDelivery(deliveryId) &&
      view.kind === 'formalize' &&
      !receipt.delivery &&
      !receipt.integration
    ) {
      const intent = normalizeMathLiteDeliveryIntent(rawResult);
      if (intent.status === 'blocked') {
        const feedback = await context.readMathLiteFeedback({ receipt, assignment: view });
        if (
          Array.isArray(feedback.outstanding_research_assignment_ids) &&
          feedback.outstanding_research_assignment_ids.length > 0
        ) {
          return await shareBlockedMathProgress(
            intent,
            context,
            receipt.assignmentId,
            'Linked research is still outstanding. Continue independent obligations in this same assignment, or end only this conversational turn while waiting for feedback.'
          );
        }
      }
    }
    const prepared = context.prepareMathLiteDelivery
      ? await context.prepareMathLiteDelivery({ rawResult, deliveryId, receipt, assignment: view })
      : undefined;
    if (prepared && deliveryPhase === 'preparing') deliveryPhase = 'sealed';
    context.signal?.throwIfAborted();
    const envelope = projectMathWorkerDeliveryToEnvelope(prepared?.delivery ?? rawResult, {
      deliveryId,
      assignmentId: receipt.assignmentId,
      targetSlotId: capability.slotId,
    });
    for (const evidence of envelope.delivery.evidence) {
      const ref = parseMathArtifactReference(evidence.ref);
      if (ref?.scheme === 'math-artifact' && ref.runId !== view.runId)
        throw new ResearchTeamOrchestrationError(
          'unauthorized',
          'Delivery evidence belongs to a different mathematics run.'
        );
    }
    if (
      receipt.delivery &&
      (receipt.delivery.deliveryId !== deliveryId || !isDeepStrictEqual(receipt.delivery.result, envelope))
    )
      throw new ResearchTeamOrchestrationError(
        'delivery_conflict',
        'This assignment already has a different durable delivery.'
      );
    const lead = capability.roster.find((member) => member.roleKind === 'lead');
    if (!lead) throw new Error('Research Team capability is missing its Lead');
    const message = JSON.stringify({
      schema: MATH_DELIVERY_ENVELOPE_SCHEMA,
      team_id: capability.teamId,
      run_id: view.runId,
      binding_digest: view.bindingDigest,
      source_slot_id: capability.slotId,
      delivery_id: deliveryId,
      assignment_id: receipt.assignmentId,
      delivery: envelope.delivery,
      ...(view.kind === 'research'
        ? {
            provisional: true,
            instruction:
              'The research report is complete, but its mathematical claims are unverified. Check the decisive inference against the original hypotheses, including empty and boundary cases, before expanding downstream formalization. A counterexample to a weakened surrogate does not refute the original theorem.',
          }
        : {}),
    });
    const transportKey = createProjectGitResearchTeamTransportIdempotencyKey(deliveryId);
    // A WAL delivery is only written after Core confirms persistence. Replays of
    // that receipt recover source staging and must not wake or enqueue Lead twice.
    let stored = receipt;
    let transportReceipt: Record<string, unknown> = { enqueue_status: 'already_persisted' };
    if (!receipt.delivery) {
      const client = requireClient(context.client);
      context.signal?.throwIfAborted();
      const acknowledgement = client.deliver
        ? await client.deliver(capability.teamId, capability.slotId, lead.slotId, message, context.signal, transportKey)
        : await client.dispatch(capability.teamId, lead.slotId, message, context.signal, transportKey);
      if (
        acknowledgement.team_id !== capability.teamId ||
        acknowledgement.target_slot_id !== lead.slotId ||
        acknowledgement.accepted_slot_id !== lead.slotId ||
        acknowledgement.accepted_role !== 'lead' ||
        !isTeamRunAckPersisted(acknowledgement)
      )
        throw new ResearchTeamOrchestrationError(
          'delivery_not_persisted',
          'Core did not persist the v2 delivery for this Lead.',
          true
        );
      stored = projectGit.recordResearchTeamDelivery({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: capability.slotId,
        assignmentId: receipt.assignmentId,
        result: envelope,
        leadPayloadBytes: Buffer.byteLength(message, 'utf8'),
      });
      transportReceipt = {
        team_run_id: acknowledgement.team_run_id,
        enqueue_status: acknowledgement.enqueue_status ?? 'accepted',
      };
    }
    if (stored.delivery?.deliveryId !== deliveryId || !isDeepStrictEqual(stored.delivery.result, envelope))
      throw new ResearchTeamOrchestrationError(
        'integrity',
        'The durable v2 delivery does not match the acknowledged payload.'
      );
    deliveryPhase = 'delivered';
    context.signal?.throwIfAborted();
    if (prepared?.sourceArtifacts.length) {
      if (!context.stageMathSources) {
        throw new ResearchTeamOrchestrationError(
          'math_v2_integration_writer_pending',
          'The host cannot stage the frozen source delivery.'
        );
      }
      await context.stageMathSources([stored], prepared.sourceArtifacts);
    }
    return result({
      schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
      action: 'deliver',
      protocol: 'v2',
      status: 'delivered',
      accepted: true,
      team_id: capability.teamId,
      source_slot_id: capability.slotId,
      lead_slot_id: lead.slotId,
      assignment_id: receipt.assignmentId,
      delivery_id: deliveryId,
      ...transportReceipt,
      should_end_turn: true,
      instruction:
        'This delivery is durable. End this turn now; do not edit or redispatch the sealed assignment. The Lead owns the next lifecycle decision.',
    });
  } catch (error) {
    if (!context.prepareMathLiteDelivery) throw error;
    // Sealing may have completed immediately before preparation was interrupted.
    // Never tell the caller that it can edit a request whose seal is durable.
    if (deliveryPhase === 'preparing') {
      try {
        if (context.hasMathLiteSealedDelivery?.(deliveryId)) deliveryPhase = 'sealed';
      } catch (stateError) {
        throw new MathLiteDeliveryRecoveryError(stateError, 'sealed', context.signal);
      }
    }
    throw new MathLiteDeliveryRecoveryError(error, deliveryPhase, context.signal);
  }
}

async function deliverResult(
  rawResult: Record<string, unknown> | undefined,
  context: ResearchTeamToolContext
): Promise<ToolResult> {
  const capability = context.capability;
  if (capability.roleKind !== 'worker') throw new Error('Only a Research Team Worker can deliver a result');
  const caller = requireRosterMember(capability, capability.slotId);
  const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
  const readAssignment = memoizeResearchTeamAssignmentReader(projectGit.readResearchTeamAssignment);
  const listAssignments = memoizeResearchTeamAssignmentListReader(projectGit.listResearchTeamAssignments);
  try {
    if (capability.profileId === 'mathematics-research-team' && listAssignments) {
      const active = listAssignments({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        states: ['prepared', 'accepted'],
        strict: true,
      }).filter((receipt) => receipt.slotId === capability.slotId && ['prepared', 'accepted'].includes(receipt.state));
      if (active.some((receipt) => receipt.schema === 'deepscientist.research_team_assignment.v2')) {
        if (active.length !== 1)
          throw new ResearchTeamOrchestrationError(
            'integrity',
            'A v2 Worker delivery requires exactly one active assignment.'
          );
        return await deliverRuntimeMathResult(rawResult, active[0]!, context);
      }
    }
  } catch (error) {
    if (error instanceof ResearchTeamOrchestrationError) throw error;
    throw new RepairableResearchTeamDeliveryError(error instanceof Error ? error.message : String(error));
  }
  const validateAssignmentOnce = memoizeResearchTeamAssignmentValidator(validateAssignment);
  let receiptSecret: string | undefined;
  let receiptSecretLoaded = false;
  const readReceiptSecret = (): string | undefined => {
    if (!receiptSecretLoaded) {
      receiptSecret = readMathematicsReceiptSecret();
      receiptSecretLoaded = true;
    }
    return receiptSecret;
  };
  let resultPayload: ResearchTeamResult;
  try {
    const normalizedWorkerResult = normalizeResearchTeamWireRecord(requiredRecord(rawResult, 'result'), 'result');
    let resultInput = hydrateMathematicsWorkerResult(
      normalizedWorkerResult,
      capability,
      caller,
      readAssignment,
      validateAssignmentOnce,
      projectGit.resolveCommit
    );
    let helperCheckpointTrusted = false;
    const workerMath = isRecord(resultInput.math) ? resultInput.math : undefined;
    const structuredBlockedFormalRoute =
      resultInput.disposition === 'blocked' &&
      workerMath?.routeDisposition === 'reject' &&
      workerMath?.infraStatus === 'ready' &&
      Number.isSafeInteger(workerMath.openGoalCountBefore) &&
      Number(workerMath.openGoalCountBefore) > 0 &&
      Number.isSafeInteger(workerMath.openGoalCountAfter) &&
      Number(workerMath.openGoalCountAfter) > 0 &&
      typeof workerMath.openGoalAfter === 'string' &&
      Boolean(workerMath.openGoalAfter.trim()) &&
      typeof workerMath.nextSingleObjective === 'string' &&
      Boolean(workerMath.nextSingleObjective.trim());
    const explicitFormalRouteRefutation =
      (workerMath?.routeDisposition === 'reject' &&
        Array.isArray(workerMath.evidenceDelta) &&
        workerMath.evidenceDelta.some(
          (item) =>
            isRecord(item) &&
            item.kind === 'route_refutation' &&
            typeof item.ref === 'string' &&
            Boolean(item.ref.trim()) &&
            typeof item.summary === 'string' &&
            Boolean(item.summary.trim())
        )) ||
      structuredBlockedFormalRoute;
    // A configured host runner is the authority for Lean-Eval FORMALIZE
    // progress.  It receives the exact prepared worktree and Worker payload
    // only as context; its result patch is deliberately limited to progress,
    // receipts, and presentation fields.  Assignment identity, bindings, and
    // Git base/branch ownership continue to come from the durable runtime. An
    // exact route refutation closes the route before a candidate proof exists,
    // so compiling the benchmark's placeholder Submission.lean would turn a
    // valid obstruction into a spurious proof-repair request.
    if (context.runLeanEvalProofSession && caller.laneId === 'lean-engineering' && !explicitFormalRouteRefutation) {
      const assignmentId = typeof resultInput.assignmentId === 'string' ? resultInput.assignmentId : undefined;
      const durableReceipt = assignmentId
        ? readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: caller.slotId,
            assignmentId,
          })
        : undefined;
      const sourceAssignment = assignmentId
        ? (dispatchedAssignments.get(`${capability.teamId}:${assignmentId}`) ??
          (durableReceipt
            ? validateDurableResearchTeamAssignment(
                durableReceipt.assignment,
                capability,
                caller,
                validateAssignmentOnce
              )
            : undefined))
        : undefined;
      if (
        sourceAssignment?.math?.stage === 'formalize' &&
        sourceAssignment.math.problemContract?.officialManifestId?.startsWith('lean-eval:') &&
        durableReceipt?.state !== 'integrated' &&
        !durableReceipt?.delivery
      ) {
        const workspaceRoot =
          durableReceipt?.preparedGit?.worktreePath ||
          sourceAssignment.git.worktreePath ||
          (isRecord(resultInput.git) && typeof resultInput.git.worktreePath === 'string'
            ? resultInput.git.worktreePath
            : undefined);
        if (!workspaceRoot) {
          throw new Error('Lean-Eval proof session requires the prepared Worker worktree');
        }
        const parentPlanNodeId = sourceAssignment.math?.activePlanNodeId?.trim() || 'direct-goal';
        let helperCheckpointAccepted = false;
        const helperCheckpoint = await checkpointDirectLeanEvalHelper(
          resultInput,
          sourceAssignment,
          workspaceRoot,
          context.verifyMathematicsHelperNode
        );
        if (helperCheckpoint) {
          // A helper checkpoint is a real mathematical boundary: the helper
          // has a kernel receipt and the Worker has committed it.  Turn it
          // into the ordinary partial FORMALIZE delivery so the assignment
          // closes and the Lead can schedule the next dependency.  Returning
          // a private `helper_checkpointed` status here used to leave the
          // assignment accepted forever and repeatedly wake the same Worker.
          // The v1 result envelope carries one canonical helper receipt. Keep
          // the first helper as the promoted frontier node; later helpers in
          // the same commit remain source-level support and can be promoted
          // by a subsequent committed delta. This preserves the one-receipt
          // contract while still ending the stalled Worker episode.
          const primaryHelper = helperCheckpoint.helpers[0]!;
          const helperNodes = Object.freeze([primaryHelper.helperPlanNode]);
          const helperReceipt = primaryHelper.receipt;
          const helperEvidence = Object.freeze([
            Object.freeze({
              kind: 'helper_declaration',
              ref: `lean-receipt:${helperReceipt.receiptId}`,
              summary: `Kernel-checked helper ${helperReceipt.declarationName} is available to the whole-problem proof.`,
            }),
          ]);
          const priorMath = isRecord(resultInput.math) ? resultInput.math : {};
          const priorBefore = Number.isSafeInteger(priorMath.openGoalCountBefore)
            ? Number(priorMath.openGoalCountBefore)
            : 0;
          const priorAfter = Number.isSafeInteger(priorMath.openGoalCountAfter)
            ? Number(priorMath.openGoalCountAfter)
            : 0;
          const openGoalCountBefore = Math.max(1, priorBefore, priorAfter);
          const openGoalCountAfter = Math.max(1, priorAfter, 1);
          resultInput = Object.freeze({
            ...resultInput,
            disposition: 'accepted',
            summary:
              typeof resultInput.summary === 'string' && resultInput.summary.trim()
                ? resultInput.summary
                : 'Kernel-verified helper retained; the whole-problem goal remains open.',
            mathHelperReceipt: helperReceipt,
            math: Object.freeze({
              ...priorMath,
              statementHash: sourceAssignment.math?.statementHash,
              routeFingerprint: sourceAssignment.math?.routeFingerprint,
              activePlanNodeId: parentPlanNodeId,
              checkedDeclarationsAdded: 1,
              openGoalCountBefore,
              openGoalCountAfter,
              evidenceDelta: helperEvidence,
              planExpansion: Object.freeze({
                expandedNodeId: parentPlanNodeId,
                addedNodes: helperNodes,
                reason: 'Retain kernel-checked dependencies while the whole-problem theorem remains open.',
                evidenceRefs: Object.freeze([`lean-receipt:${helperReceipt.receiptId}`]),
              }),
              verifiedPlanNodeIdsAdded: Object.freeze([String(primaryHelper.helperPlanNode.id)]),
              routeDisposition: 'blocked',
              nextSingleObjective:
                'Use the retained kernel-verified helper(s) to construct the next missing dependency for the whole-problem goal.',
              infraStatus: 'ready',
            }),
            git: Object.freeze({
              ...(isRecord(resultInput.git) ? resultInput.git : {}),
              headCommit: helperCheckpoint.targetCommit,
            }),
          });
          // Rehydrate so assignment-bound identity and the trusted plan
          // snapshots are derived exactly like every other Worker delivery.
          resultInput = hydrateMathematicsWorkerResult(
            resultInput,
            capability,
            caller,
            readAssignment,
            validateAssignmentOnce,
            projectGit.resolveCommit
          );
          helperCheckpointAccepted = true;
          helperCheckpointTrusted = true;
        }
        if (!helperCheckpointAccepted) {
          const session = await context.runLeanEvalProofSession({
            assignment: sourceAssignment,
            workspaceRoot,
            projectRoot: capability.projectRoot,
            workerResult: Object.freeze({ ...resultInput }),
            signal: context.signal,
          });
          if (
            !session ||
            !session.proofLoop ||
            !isRecord(session.resultPatch) ||
            !isRecord(session.resultPatch.math) ||
            typeof session.resultPatch.gitHeadCommit !== 'string' ||
            !session.resultPatch.gitHeadCommit.trim()
          ) {
            throw new Error('Lean-Eval proof session must return a runtime-owned math patch and full Git head commit');
          }
          const runtimeEvidencePacket = isRecord(session.resultPatch.math.evidencePacket)
            ? session.resultPatch.math.evidencePacket
            : undefined;
          const researchProblemId =
            sourceAssignment.math?.problemContract?.problemId ?? sourceAssignment.math?.researchContract?.problemId;
          if (runtimeEvidencePacket && researchProblemId && !isMathLiteRunEnvironment(process.env)) {
            // Persist failed proof waves before returning a repair request; the
            // diagnostic is evidence that Lead pivot decisions depend on.
            const sourceMath = sourceAssignment.math;
            const researchBinding = sourceMath
              ? {
                  teamId: capability.teamId,
                  slotId: caller.slotId,
                  workerId: caller.roleId,
                  statementHash: sourceMath.statementHash,
                  assignmentDigest: mathDigest(canonicalMathJson(durableReceipt?.assignment ?? sourceAssignment)),
                  initialRouteFingerprint: sourceMath.routeFingerprint,
                  routeRevisionsSupported:
                    sourceMath.directAttempt === true &&
                    sourceMath.stage === 'formalize' &&
                    !sourceMath.routeCards?.length &&
                    !sourceMath.proofPlan,
                }
              : undefined;
            await recordMathSearchEvidence({
              projectRoot: capability.projectRoot,
              problemId: researchProblemId,
              assignmentId: sourceAssignment.assignmentId,
              packet: runtimeEvidencePacket as MathEvidencePacket,
              ...(researchBinding && sourceMath
                ? {
                    binding: researchBinding,
                    route: { fingerprint: sourceMath.routeFingerprint, objective: sourceAssignment.objective },
                  }
                : {}),
            });
          }
          if (session.repairRequest) {
            throw new RepairableResearchTeamDeliveryError(
              'Lean-Eval rejected the current candidate. Apply the runtime repair request and deliver the changed candidate again without ending this solver episode.',
              session.repairRequest
            );
          }
          const patch = session.resultPatch;
          const patchResult: Record<string, unknown> = {
            ...resultInput,
            math: Object.freeze({ ...patch.math }),
          };
          patchResult.disposition = patch.disposition;
          if (patch.summary) patchResult.summary = patch.summary;
          if (patch.nextRecommendation) patchResult.nextRecommendation = patch.nextRecommendation;
          if (patch.outputs) patchResult.outputs = Object.freeze([...patch.outputs]);
          if (patch.limitations) patchResult.limitations = Object.freeze([...patch.limitations]);
          if (patch.artifactPaths) patchResult.artifactPaths = Object.freeze([...patch.artifactPaths]);
          if (patch.mathCheckpoint) patchResult.mathCheckpoint = patch.mathCheckpoint;
          if (patch.localGateReceipt) patchResult.localGateReceipt = patch.localGateReceipt;
          if (patch.mathNodeReceipt) patchResult.mathNodeReceipt = patch.mathNodeReceipt;
          if (patch.mathHelperReceipt) patchResult.mathHelperReceipt = patch.mathHelperReceipt;
          const currentGit = isRecord(resultInput.git) ? resultInput.git : undefined;
          if (!currentGit) throw new Error('Lean-Eval proof session cannot bind a missing Worker Git identity');
          patchResult.git = Object.freeze({ ...currentGit, headCommit: patch.gitHeadCommit });
          // The proof runner replaces the Worker math payload and advances HEAD.
          // Rehydrate once more so runtime-owned sourceProgress is derived from
          // the runner's final commit instead of being lost with the old payload.
          resultInput = hydrateMathematicsWorkerResult(
            Object.freeze(patchResult),
            capability,
            caller,
            readAssignment,
            validateAssignmentOnce,
            projectGit.resolveCommit
          );
        }
      }
    }
    // Helper receipts are never accepted from Worker claims alone. Rebind the
    // helper to the durable assignment and verify the committed declaration
    // before normal result validation and Lead projection.
    const helperExpansionRequested =
      isRecord(resultInput.math) &&
      isRecord(resultInput.math.planExpansion) &&
      Boolean(context.verifyMathematicsHelperNode);
    if ((isRecord(resultInput.mathHelperReceipt) || helperExpansionRequested) && !helperCheckpointTrusted) {
      const assignmentId = typeof resultInput.assignmentId === 'string' ? resultInput.assignmentId : undefined;
      const durableReceipt = assignmentId
        ? readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: caller.slotId,
            assignmentId,
          })
        : undefined;
      const sourceAssignment = assignmentId
        ? (dispatchedAssignments.get(`${capability.teamId}:${assignmentId}`) ??
          (durableReceipt
            ? validateDurableResearchTeamAssignment(
                durableReceipt.assignment,
                capability,
                caller,
                validateAssignmentOnce
              )
            : undefined))
        : undefined;
      if (!sourceAssignment) throw new Error('Mathematics helper receipt has no durable assignment');
      const headCommit =
        isRecord(resultInput.git) && typeof resultInput.git.headCommit === 'string' ? resultInput.git.headCommit : '';
      if (!headCommit) throw new Error('Mathematics helper receipt requires a committed Worker head');
      const verificationRoot =
        isRecord(resultInput.git) && typeof resultInput.git.worktreePath === 'string'
          ? resultInput.git.worktreePath
          : sourceAssignment.git.worktreePath || capability.projectRoot;
      resultInput = await verifyDeliveredMathematicsHelper(
        resultInput,
        sourceAssignment,
        verificationRoot,
        headCommit,
        context.verifyMathematicsHelperNode
      );
      // Rebuild runtime-owned plan/checkpoint state now that the verifier has
      // supplied the canonical helper receipt (including auto-discovered
      // helpers omitted from the compact Worker payload).
      resultInput = hydrateMathematicsWorkerResult(
        resultInput,
        capability,
        caller,
        readAssignment,
        validateAssignmentOnce,
        projectGit.resolveCommit
      );
    }
    // A bounded counterexample probe is runtime-owned evidence. Formalizers
    // use their prepared checkout; Strategy uses the authenticated canonical
    // Lean project as read-only input while the runner owns and deletes the
    // temporary probe file.
    if (
      context.runLeanEvalCounterexampleProbe &&
      (caller.laneId === 'lean-engineering' || caller.laneId === 'strategy-exploration')
    ) {
      const assignmentId = typeof resultInput.assignmentId === 'string' ? resultInput.assignmentId : undefined;
      const durableReceipt = assignmentId
        ? readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: caller.slotId,
            assignmentId,
          })
        : undefined;
      const sourceAssignment = assignmentId
        ? (dispatchedAssignments.get(`${capability.teamId}:${assignmentId}`) ??
          (durableReceipt
            ? validateDurableResearchTeamAssignment(
                durableReceipt.assignment,
                capability,
                caller,
                validateAssignmentOnce
              )
            : undefined))
        : undefined;
      const workspaceRoot =
        caller.laneId === 'strategy-exploration'
          ? sourceAssignment && path.resolve(sourceAssignment.git.projectRoot) === path.resolve(capability.projectRoot)
            ? capability.projectRoot
            : undefined
          : durableReceipt?.preparedGit?.worktreePath ||
            sourceAssignment?.git.worktreePath ||
            (isRecord(resultInput.git) && typeof resultInput.git.worktreePath === 'string'
              ? resultInput.git.worktreePath
              : undefined);
      const runtimeProbe = sourceAssignment?.math?.fastCheck?.runtimeProbe;
      if (sourceAssignment && workspaceRoot && runtimeProbe && durableReceipt?.state !== 'integrated') {
        const probe = await context.runLeanEvalCounterexampleProbe({
          assignment: sourceAssignment,
          workspaceRoot,
          projectRoot: capability.projectRoot,
          probe: runtimeProbe,
          signal: context.signal,
        });
        resultInput = appendRuntimeCounterexampleProbeEvidence(resultInput, sourceAssignment, probe, capability.teamId);
      }
    }
    resultPayload = validateResult(resultInput, capability, caller, readAssignment, validateAssignmentOnce);
    const durableReceipt =
      capability.profileId === 'mathematics-research-team'
        ? readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: caller.slotId,
            assignmentId: resultPayload.assignmentId,
          })
        : undefined;
    if (durableReceipt && ['accepted', 'integrated'].includes(durableReceipt.state)) {
      const sourceAssignment = validateDurableResearchTeamAssignment(
        durableReceipt.assignment,
        capability,
        caller,
        validateAssignmentOnce
      );
      assertMeaningfulDirectMathematicsFormalizeEpisode(resultPayload, sourceAssignment, durableReceipt.preparedGit);
      assertDirectMathematicsCompletionSourceIntegrity(
        resultPayload,
        sourceAssignment,
        capability.projectRoot,
        durableReceipt.preparedGit?.worktreePath
      );
    }
    if (resultPayload.mathReview) {
      const secret = readReceiptSecret();
      if (!secret) throw new Error('The local mathematics receipt signing key is unavailable.');
      const { source: _source, attestation: _attestation, ...unsignedReview } = resultPayload.mathReview;
      const deliveryId = createProjectGitResearchTeamDeliveryId(
        capability.teamId,
        capability.slotId,
        resultPayload.assignmentId
      );
      resultPayload = Object.freeze({
        ...resultPayload,
        mathReview: signMathCandidateReview(
          unsignedReview,
          {
            teamId: capability.teamId,
            slotId: capability.slotId,
            assignmentId: resultPayload.assignmentId,
            deliveryId,
            laneId: caller.laneId,
          },
          secret
        ),
      });
    }
  } catch (error) {
    if (error instanceof RepairableResearchTeamDeliveryError) throw error;
    throw new RepairableResearchTeamDeliveryError(error instanceof Error ? error.message : String(error));
  }
  const lead = capability.roster.find((member) => member.roleKind === 'lead');
  if (!lead) throw new Error('Research Team capability is missing its Lead');
  const deliveryId = createProjectGitResearchTeamDeliveryId(
    capability.teamId,
    capability.slotId,
    resultPayload.assignmentId
  );
  const client = requireClient(context.client);
  const sourceAgentId = teamAgentIdForSlotId(capability.slotId, capability.roster);
  const deliveryBase = {
    schema: RESEARCH_TEAM_DELIVERY_SCHEMA,
    team_id: capability.teamId,
    profile_id: capability.profileId,
    workflow_id: capability.workflowId,
    source_slot_id: capability.slotId,
    source_role_id: capability.roleId,
    source_agent_id: sourceAgentId,
    source_display_name: caller.displayName,
    lane_id: caller.laneId,
  };
  let genericAssignmentReceiptAvailable = false;
  if (capability.profileId !== 'mathematics-research-team' && projectGit.recordResearchTeamDelivery && readAssignment) {
    try {
      const receipt = readAssignment({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: capability.slotId,
        assignmentId: resultPayload.assignmentId,
      });
      genericAssignmentReceiptAvailable = receipt?.state === 'accepted' || receipt?.state === 'integrated';
    } catch {
      // Legacy generic deliveries may predate durable assignment receipts.
    }
  }
  const persistDelivery =
    Boolean(projectGit.recordResearchTeamDelivery) &&
    (capability.profileId === 'mathematics-research-team' || genericAssignmentReceiptAvailable);
  const compactMathDelivery = capability.profileId === 'mathematics-research-team' && persistDelivery;
  const delivery = Object.freeze(
    compactMathDelivery
      ? {
          ...deliveryBase,
          ...projectMathematicsResultForLead(resultPayload, deliveryId, sourceAgentId ?? capability.slotId),
        }
      : {
          ...deliveryBase,
          ...(persistDelivery ? { delivery_id: deliveryId, assignment_id: resultPayload.assignmentId } : {}),
          result: resultPayload,
        }
  );
  const serializedDelivery = JSON.stringify(delivery);
  // Keep the human-readable delivery identity local. Core receives only the
  // bounded deterministic transport key, which is reused for every retry.
  const transportIdempotencyKey = createProjectGitResearchTeamTransportIdempotencyKey(deliveryId);
  let acknowledgement;
  try {
    acknowledgement = client.deliver
      ? await client.deliver(
          capability.teamId,
          capability.slotId,
          lead.slotId,
          serializedDelivery,
          context.signal,
          transportIdempotencyKey
        )
      : await client.dispatch(
          capability.teamId,
          lead.slotId,
          serializedDelivery,
          context.signal,
          transportIdempotencyKey
        );
  } catch (error) {
    throw new ResearchTeamOrchestrationError(
      'delivery_dispatch_failed',
      error instanceof Error ? error.message : String(error),
      true
    );
  }
  if (
    acknowledgement.team_id !== capability.teamId ||
    acknowledgement.target_slot_id !== lead.slotId ||
    acknowledgement.accepted_slot_id !== lead.slotId ||
    acknowledgement.accepted_role !== 'lead'
  ) {
    throw new Error('Core accepted the Research Team delivery for an unexpected Lead slot');
  }
  if (!isTeamRunAckPersisted(acknowledgement)) {
    throw new ResearchTeamOrchestrationError(
      'delivery_not_persisted',
      'Core did not persist the Research Team delivery',
      true
    );
  }
  // A local delivery receipt is evidence of Core acceptance, never of an
  // attempted request. Persist it only after the matching ack is validated.
  const durableDelivery = persistDelivery
    ? projectGit.recordResearchTeamDelivery?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: capability.slotId,
        assignmentId: resultPayload.assignmentId,
        result: resultPayload,
        leadPayloadBytes: Buffer.byteLength(serializedDelivery, 'utf8'),
      })
    : undefined;
  if (resultPayload.executionMode !== 'advisory') {
    notifyProjectGitChanged({
      workspace: resultPayload.git.projectRoot,
      repoRoot: resultPayload.git.projectRoot,
      reason: 'agent-delivered',
      branch: resultPayload.git.branch,
      head: resultPayload.git.headCommit,
    });
  }
  const resultPayloadBytes =
    durableDelivery?.delivery?.resultPayloadBytes ?? Buffer.byteLength(JSON.stringify(resultPayload), 'utf8');
  const leadPayloadBytes = durableDelivery?.delivery?.leadPayloadBytes ?? Buffer.byteLength(serializedDelivery, 'utf8');
  return result({
    schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
    action: 'deliver',
    status: 'delivered',
    accepted: true,
    team_id: capability.teamId,
    source_slot_id: capability.slotId,
    lead_slot_id: lead.slotId,
    assignment_id: resultPayload.assignmentId,
    delivery_id: durableDelivery?.delivery?.deliveryId ?? null,
    team_run_id: acknowledgement.team_run_id,
    enqueue_status: acknowledgement.enqueue_status ?? 'accepted',
    message_id: acknowledgement.message_id ?? null,
    efficiency: Object.freeze({
      result_payload_bytes: resultPayloadBytes,
      lead_payload_bytes: leadPayloadBytes,
      lead_projection_ratio: leadPayloadBytes / Math.max(1, resultPayloadBytes),
    }),
  });
}

function readResearchTeamDeliveryReceipt(
  deliveryId: string,
  capability: ResearchTeamToolCapability,
  readAssignment: ResearchTeamAssignmentReader | undefined
): ProjectGitResearchTeamAssignmentReceipt | undefined {
  if (!readAssignment) return undefined;
  let matched: ProjectGitResearchTeamAssignmentReceipt | undefined;
  for (const member of capability.roster) {
    if (member.roleKind !== 'worker') continue;
    const prefix = createProjectGitResearchTeamDeliveryId(capability.teamId, member.slotId, '');
    if (!deliveryId.startsWith(prefix)) continue;
    let assignmentId: string;
    try {
      assignmentId = stableId(deliveryId.slice(prefix.length), 'delivery assignment_id');
    } catch {
      continue;
    }
    const receipt = readAssignment({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: member.slotId,
      assignmentId,
    });
    if (
      !receipt ||
      receipt.teamId !== capability.teamId ||
      receipt.slotId !== member.slotId ||
      receipt.assignmentId !== assignmentId ||
      receipt.delivery?.deliveryId !== deliveryId
    ) {
      continue;
    }
    if (matched) return undefined;
    matched = receipt;
  }
  return matched;
}

function toRuntime(
  context: ResearchTeamToolContext,
  validateAssignmentForRuntime: ResearchTeamAssignmentValidator | undefined = undefined,
  options: Readonly<{
    deferMathResearchPersistence?: boolean;
    readPortfolio?: ResearchTeamPortfolioReader;
    listAssignments?: ResearchTeamAssignmentListReader;
  }> = {}
): ResearchTeamRuntime<RuntimeContext> {
  const capability = context.capability;
  if (capability.roleKind !== 'lead') throw new Error('Research Team orchestration requires the Lead capability');
  const projectGit = context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER;
  const readAssignment = memoizeResearchTeamAssignmentReader(projectGit.readResearchTeamAssignment);
  const listAssignments =
    options.listAssignments ?? memoizeResearchTeamAssignmentListReader(projectGit.listResearchTeamAssignments);
  const readPortfolio = options.readPortfolio ?? memoizeResearchTeamPortfolioReader(readCanonicalMathematicsPortfolio);
  const validateAssignmentForRuntimeResolved =
    validateAssignmentForRuntime ?? memoizeResearchTeamAssignmentValidator(validateAssignment, readPortfolio);
  const validateResultForRuntime = memoizeResearchTeamResultValidator((value, resultCapability, target) =>
    validateResult(value, resultCapability, target, readAssignment, validateAssignmentForRuntimeResolved)
  );
  return Object.freeze({
    teamId: capability.teamId,
    coordinatorSlotId: capability.slotId,
    reasoningConcurrency: capability.reasoningConcurrency,
    client: requireClient(context.client),
    ...(capability.profileId === 'mathematics-research-team' && context.verifyRunInputs
      ? {
          assertExecutionAllowed: () => {
            try {
              context.verifyRunInputs?.();
            } catch (error) {
              if (!(error instanceof MathRunInputsIntegrityError)) throw error;
              throw new ResearchTeamOrchestrationError('math_run_inputs_integrity_failed', error.message, false);
            }
          },
        }
      : {}),
    context: Object.freeze({
      capability,
      projectGit,
      deferMathResearchPersistence: options.deferMathResearchPersistence === true,
      validateAssignment: validateAssignmentForRuntimeResolved,
      validateResult: validateResultForRuntime,
      ...(readAssignment ? { readAssignment } : {}),
      ...(listAssignments ? { listAssignments } : {}),
      readPortfolio,
      ...(context.prepareLeanEvalWorkspace ? { prepareLeanEvalWorkspace: context.prepareLeanEvalWorkspace } : {}),
      ...(context.preflightMathematicsRoute ? { preflightMathematicsRoute: context.preflightMathematicsRoute } : {}),
      ...(context.checkLeanToolchainReadiness
        ? { checkLeanToolchainReadiness: context.checkLeanToolchainReadiness }
        : {}),
      ...(context.mathIntegrationJournal ? { mathIntegrationJournal: context.mathIntegrationJournal } : {}),
      ...(context.verifyMathematicsHelperNode
        ? { verifyMathematicsHelperNode: context.verifyMathematicsHelperNode }
        : context.projectGit
          ? {}
          : { verifyMathematicsHelperNode }),
      // The production MCP path uses the default Project Git driver.  Tests
      // and embedded callers that inject a driver must explicitly inject a
      // certifier too, so a fake Git repository is never accidentally handed
      // to the real Lean process.
      ...(context.certifyMathematics
        ? { certifyMathematics: context.certifyMathematics }
        : context.projectGit
          ? {}
          : { certifyMathematics: certifyFormalVerifications }),
    }),
    signal: context.signal,
    sleep: context.sleep,
  });
}

async function normalizeDispatchBatch(
  values: readonly ResearchTeamDispatchItemInput[] | undefined,
  capability: ResearchTeamToolCapability,
  validateAssignmentForBatch: ResearchTeamAssignmentValidator,
  listAssignments?: ResearchTeamAssignmentListReader,
  context?: ResearchTeamToolContext
) {
  if (!values?.length) throw new Error('dispatch requires a non-empty assignments list');
  if (values.length > capability.agentLimit) throw new Error('dispatch assignments exceed the Team Agent limit');
  if (values.length > capability.reasoningConcurrency) {
    throw new Error(
      `dispatch accepts at most ${capability.reasoningConcurrency} assignments in one wave; send a later wave only after a real Worker delivery`
    );
  }
  const checkedSources = new Map<object, ReturnType<typeof readDispatchAssignmentSource>>();
  if (capability.profileId === 'mathematics-research-team') {
    collectMathematicsDispatchErrors(values, {
      target: (value) => requireWorker(capability, value as string),
      key: (value) => stableId(value, 'idempotency_key'),
      task: (item) => checkedSources.set(item, readDispatchAssignmentSource(item)),
      base: (value) => requiredGitOid(value, 'baseCommit'),
    });
  }
  const targets = new Set<string>();
  const keys = new Set<string>();
  const assignmentIds = new Set<string>();
  const assignmentHistory =
    capability.profileId === 'mathematics-research-team' && listAssignments
      ? listAssignments({ workspace: capability.projectRoot, teamId: capability.teamId })
      : undefined;
  const trustedFastCheck =
    capability.profileId === 'mathematics-research-team' &&
    isBoundImoMathematicsWorkspace(capability) &&
    context?.prepareBoundImoFastCheck &&
    values.some((item) => !isRecord(item.assignment))
      ? await context.prepareBoundImoFastCheck({
          workspaceRoot: capability.projectRoot,
          ...(values.find((item) => item.baseCommit)?.baseCommit
            ? { baseCommit: values.find((item) => item.baseCommit)?.baseCommit }
            : {}),
          signal: context.signal,
        })
      : undefined;
  const normalized = values.map((item) => {
    const target = requireWorker(capability, item.targetSlotId);
    const targetSlotId = target.slotId;
    const requestedIdempotencyKey = stableId(item.idempotencyKey, 'idempotency_key');
    const idempotencyKey = recoveryIdempotencyKeyForOrphanedPreparedAssignment(
      requestedIdempotencyKey,
      targetSlotId,
      assignmentHistory
    );
    const validatedAssignment = validateAssignmentForBatch(
      normalizeAssignmentInput(
        item,
        idempotencyKey,
        capability,
        target,
        assignmentHistory,
        checkedSources.get(item),
        trustedFastCheck
      ),
      capability,
      target
    );
    // Full-assignment callers may carry the old compact id explicitly. Rebind
    // only that stale identity; all other immutable assignment fields remain
    // unchanged for the retry.
    const assignment =
      idempotencyKey !== requestedIdempotencyKey && validatedAssignment.assignmentId === requestedIdempotencyKey
        ? Object.freeze({ ...validatedAssignment, assignmentId: idempotencyKey })
        : validatedAssignment;
    if (targets.has(targetSlotId) || keys.has(idempotencyKey) || assignmentIds.has(assignment.assignmentId)) {
      throw new Error('dispatch assignments must use unique Worker slots, assignment ids, and idempotency keys');
    }
    targets.add(targetSlotId);
    keys.add(idempotencyKey);
    assignmentIds.add(assignment.assignmentId);
    return Object.freeze({ targetSlotId, idempotencyKey, assignment });
  });
  validateMathematicsDispatchWave(normalized, capability, assignmentHistory);
  for (const { assignment } of normalized) {
    assertBoundImoFormalizationProvenance(assignment, assignmentHistory ?? [], capability);
  }
  if (assignmentHistory) {
    const waveAssignments = normalized.map(({ assignment }) => assignment);
    for (const { assignment, targetSlotId } of normalized) {
      assertNoConcurrentDuplicateMathematicsArtifact(assignment, assignmentHistory, capability, targetSlotId);
      assertNoConcurrentDuplicateMathematicsResearch(assignment, assignmentHistory, capability);
      assertNoConcurrentDuplicateMathematicsDependency(assignment, assignmentHistory, capability, waveAssignments);
    }
  } else {
    const waveAssignments = normalized.map(({ assignment }) => assignment);
    for (const assignment of waveAssignments) {
      assertNoConcurrentDuplicateMathematicsDependency(assignment, [], capability, waveAssignments);
    }
  }
  return Object.freeze(normalized);
}

function validateMathematicsDispatchWave(
  items: readonly Readonly<{ assignment: ResearchTeamAssignment }>[],
  capability: ResearchTeamToolCapability,
  assignmentHistory?: readonly ProjectGitResearchTeamAssignmentReceipt[]
): void {
  if (capability.profileId !== 'mathematics-research-team') return;
  type MathAssignment = ResearchTeamAssignment & { math: ResearchTeamMathAssignment };
  const mathAssignments: MathAssignment[] = [];
  let missingMathMetadata = false;
  for (const { assignment } of items) {
    if (!assignment.math) {
      missingMathMetadata = true;
      continue;
    }
    mathAssignments.push(assignment as MathAssignment);
  }
  if (missingMathMetadata) {
    throw new Error('Mathematics dispatch wave requires math metadata on every assignment');
  }
  if (!mathAssignments.length) return;

  const stage = mathAssignments[0].math.stage;
  for (let index = 1; index < mathAssignments.length; index += 1) {
    if (mathAssignments[index].math.stage !== stage) {
      throw new Error('Mathematics dispatch wave must contain one proof stage');
    }
  }
  const permitted = MATHEMATICS_DISPATCH_ALLOWED_LANES[stage];
  if (!permitted.length) {
    throw new Error(`Mathematics ${stage.toUpperCase()} is Lead-owned and cannot dispatch Workers`);
  }
  const expectedMode = stage === 'formalize' ? 'artifact' : 'advisory';
  for (const assignment of mathAssignments) {
    if (!permitted.includes(assignment.laneId)) {
      throw new Error(`Mathematics ${stage.toUpperCase()} dispatch uses an incompatible Worker lane`);
    }
    if ((assignment.executionMode ?? 'artifact') !== expectedMode) {
      throw new Error(`Mathematics ${stage.toUpperCase()} dispatch uses the wrong execution mode`);
    }
    // Bound IMO runs begin with one persistent Lean owner. A Strategy Worker
    // is useful only after that owner has produced durable evidence; allowing
    // an advisory wave beside an untouched formalization creates two long
    // model turns with no source handoff or falsifiable Lean obligation.
    if (
      isBoundImoMathematicsWorkspace(capability) &&
      assignment.laneId === 'strategy-exploration' &&
      assignment.executionMode === 'advisory'
    ) {
      const hasLeanEvidence = (assignmentHistory ?? []).some((receipt) => {
        if (!isRecord(receipt.assignment)) return false;
        const request = isRecord(receipt.assignment.request) ? receipt.assignment.request : undefined;
        if (request?.kind !== 'formalize') return false;
        return Boolean(receipt.delivery || receipt.integration || receipt.state === 'integrated');
      });
      if (!hasLeanEvidence) {
        throw new Error(
          'Bound IMO research dispatch requires a durable Lean delivery or integrated progress checkpoint first'
        );
      }
    }
  }
  const explorationWave = stage === 'diversify' || stage === 'replan';
  const routeProposalModes = new Set(
    mathAssignments.map((assignment) => assignment.math.routeProposalMode ?? 'research')
  );
  if (explorationWave && routeProposalModes.size !== 1) {
    throw new Error('Mathematics exploration wave cannot mix research actions with route candidates');
  }
  if (explorationWave && routeProposalModes.has('research')) {
    // Two complementary probes can establish the initial state faster, but
    // only when Lead has given them different route/method identities and
    // different falsification targets. This prevents the duplicate first-wave
    // reasoning observed in the IMO runs without serializing useful discovery.
    const statementHashes = new Set(mathAssignments.map((assignment) => assignment.math.statementHash));
    const baseCommits = new Set(mathAssignments.map((assignment) => assignment.git.baseCommit));
    const hasPriorDiscoveryDelivery = [...(assignmentHistory ?? [])].some((receipt) => {
      if (!receipt.delivery || !['accepted', 'integrated'].includes(receipt.state)) return false;
      if (!isRecord(receipt.assignment)) return false;
      const assignment = receipt.assignment;
      const math = isRecord(assignment.math) ? assignment.math : undefined;
      const git = isRecord(assignment.git) ? assignment.git : undefined;
      return (
        math &&
        ['diversify', 'replan'].includes(String(math.stage)) &&
        (!math.routeProposalMode || math.routeProposalMode === 'research') &&
        statementHashes.has(String(math.statementHash)) &&
        baseCommits.has(String(git?.baseCommit))
      );
    });
    if (!hasPriorDiscoveryDelivery) {
      if (mathAssignments.length > 2) {
        throw new Error('The first Mathematics discovery wave permits at most two complementary Workers');
      }
      const routeMethodPairs = mathAssignments.map(
        (assignment) =>
          `${normalizeMathRouteFingerprint(assignment.math.routeFingerprint)}\u0000${mathematicsAssignmentMethodClass(assignment)}`
      );
      if (new Set(routeMethodPairs).size !== routeMethodPairs.length) {
        throw new Error(
          'First-wave Mathematics Workers must use a distinct route fingerprint or a distinct method class'
        );
      }
      const falsificationTargets = mathAssignments.map((assignment) =>
        `${assignment.falsificationPlan.test}\u0000${assignment.falsificationPlan.failureSignal}`
          .trim()
          .toLowerCase()
          .replace(/\s+/gu, ' ')
      );
      if (new Set(falsificationTargets).size !== falsificationTargets.length) {
        throw new Error('First-wave Mathematics Workers must test distinct falsification targets');
      }
    }
    const objectives = mathAssignments.map((assignment) =>
      assignment.objective.trim().toLowerCase().replace(/\s+/gu, ' ')
    );
    if (new Set(objectives).size !== objectives.length) {
      throw new Error('Parallel Mathematics research actions must have distinct objectives');
    }
  }
  const directAttempts = mathAssignments.filter((assignment) => assignment.math.directAttempt === true);
  if (stage === 'formalize' && isBoundImoMathematicsWorkspace(capability) && mathAssignments.length > 1) {
    throw new Error('Bound IMO FORMALIZE uses one persistent Formalizer for the selected route cluster');
  }
  if (directAttempts.length > 0) {
    if (directAttempts.length !== mathAssignments.length) {
      throw new Error('Mathematics dispatch cannot mix direct and routed assignments in one wave');
    }
    if (directAttempts.length === 1) return;
    if (stage !== 'formalize') {
      throw new Error('Parallel Mathematics direct assignments are allowed only in FORMALIZE');
    }
  }
  validateMathematicsWaveLimits({
    stage,
    count: mathAssignments.length,
    reasoningConcurrency: capability.reasoningConcurrency,
    routes: mathAssignments.map((assignment) => normalizeMathRouteFingerprint(assignment.math.routeFingerprint)),
    artifactPaths:
      stage === 'formalize'
        ? mathAssignments.flatMap((assignment) => assignmentArtifactPaths(assignment))
        : mathAssignments.flatMap((assignment) => assignment.math.artifactPaths ?? []),
    requireDistinctRoutes: explorationWave && routeProposalModes.has('candidate'),
    phase: 'dispatch',
  });
  const tasks = new Set<string>();
  if (stage !== 'formalize') return;
  for (const assignment of mathAssignments) {
    if (!assignment.math.activePlanNodeId) {
      throw new Error('Mathematics FORMALIZE assignments require activePlanNodeId');
    }
    // A plan node is the unit of mathematical ownership.  Distinct route
    // labels or artifact paths do not make two attempts on the same tightly
    // coupled Lean goal independent; allowing them concurrently caused the
    // IMO runs to duplicate the same List.Perm/endgame work and waste turns.
    const task = `${assignment.math.statementHash}\u0000${assignment.git.baseCommit}\u0000${assignment.math.activePlanNodeId}`;
    if (tasks.has(task)) {
      throw new Error(
        'Parallel Mathematics FORMALIZE assignments must target distinct plan nodes (statement/base ownership)'
      );
    }
    tasks.add(task);
  }
}

function isWholeProblemDirectAttempt(
  assignment: ResearchTeamAssignment | undefined,
  result?: ResearchTeamResult
): boolean {
  if (assignment?.math?.directAttempt !== true) return false;
  const activePlanNodeId = assignment.math.activePlanNodeId ?? result?.math?.activePlanNodeId;
  return !activePlanNodeId || activePlanNodeId === 'direct-goal';
}

function isDirectProofCompletionResult(result: ResearchTeamResult, assignment?: ResearchTeamAssignment): boolean {
  const helperOnly = Boolean(result.mathHelperReceipt) && !result.localGateReceipt && !result.mathNodeReceipt;
  return Boolean(
    !helperOnly &&
    result.assignmentBinding?.stage === 'formalize' &&
    result.math?.routeDisposition === 'advance' &&
    result.math.openGoalCountBefore > 0 &&
    result.math.openGoalCountAfter === 0 &&
    result.git.headCommit &&
    result.git.headCommit !== result.git.baseCommit &&
    (!assignment || result.git.headCommit !== assignment.git.baseCommit)
  );
}

function isSolverCompleteDirectResult(result: ResearchTeamResult, assignment?: ResearchTeamAssignment): boolean {
  // `directAttempt=true` is also used for parallel declaration clusters. Only
  // the normalized `direct-goal` node owns the whole-problem completion claim.
  return Boolean(isWholeProblemDirectAttempt(assignment, result) && isDirectProofCompletionResult(result));
}

function isDirectDeclarationClusterCompleteResult(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined
): boolean {
  return Boolean(
    assignment?.math?.directAttempt === true &&
    assignment.math.stage === 'formalize' &&
    !isWholeProblemDirectAttempt(assignment, result) &&
    isDirectProofCompletionResult(result)
  );
}

const LEAN_PROOF_ESCAPE_PATTERN = /\b(?:sorry|admit|native_decide)\b|\baxiom\s+[A-Za-z_][A-Za-z0-9_']*/gu;
const baseLeanProofEscapeCache = new Map<string, number>();
const BASE_LEAN_PROOF_ESCAPE_CACHE_MAX_ENTRIES = 256;

function stripLeanCommentsAndStrings(source: string): string {
  return source
    .replace(/\/\*[\s\S]*?\*\//gu, ' ')
    .replace(/--[^\r\n]*/gu, ' ')
    .replace(/"(?:\\.|[^"\\])*"/gu, ' ');
}

function leanProofEscapeCount(source: string): number {
  return [...stripLeanCommentsAndStrings(source).matchAll(LEAN_PROOF_ESCAPE_PATTERN)].length;
}

function baseLeanProofEscapeCount(projectRoot: string, baseCommit: string, relativePath: string): number {
  const cacheKey = `${projectRoot}\u0000${baseCommit}\u0000${relativePath}`;
  const cached = baseLeanProofEscapeCache.get(cacheKey);
  if (cached !== undefined) {
    baseLeanProofEscapeCache.delete(cacheKey);
    baseLeanProofEscapeCache.set(cacheKey, cached);
    return cached;
  }
  let count = 0;
  try {
    const source = execFileSync('git', ['show', `${baseCommit}:${relativePath}`], {
      cwd: projectRoot,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    });
    count = leanProofEscapeCount(source);
  } catch {
    // A synthetic/fake Git driver may not have an inspectable base object. In
    // that case the source itself is still checked and any marker is treated
    // as newly introduced.
    count = 0;
  }
  baseLeanProofEscapeCache.set(cacheKey, count);
  while (baseLeanProofEscapeCache.size > BASE_LEAN_PROOF_ESCAPE_CACHE_MAX_ENTRIES) {
    const oldest = baseLeanProofEscapeCache.keys().next().value;
    if (oldest === undefined) break;
    baseLeanProofEscapeCache.delete(oldest);
  }
  return count;
}

/**
 * Reject a completed direct result (whole problem or declaration cluster)
 * that added a known Lean proof escape. This is a source-integrity gate only;
 * theorem correctness remains the external evaluator's responsibility.
 */
function assertDirectMathematicsCompletionSourceIntegrity(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined,
  projectRoot: string,
  preparedWorktreePath?: string
): void {
  if (
    !assignment ||
    (!isSolverCompleteDirectResult(result, assignment) && !isDirectDeclarationClusterCompleteResult(result, assignment))
  ) {
    return;
  }
  const candidates = assignmentArtifactPaths(assignment, result.artifactPaths);
  if (!candidates.length) return;
  const worktreePath = result.git.worktreePath || preparedWorktreePath || projectRoot;
  if (!path.isAbsolute(worktreePath)) return;
  for (const candidate of candidates) {
    const relativePath = projectRelativeLeanArtifactPath(worktreePath, candidate);
    if (!relativePath) continue;
    const artifactPath = path.resolve(worktreePath, relativePath);
    let source: string;
    try {
      source = fs.readFileSync(artifactPath, 'utf8');
    } catch {
      // Artifact existence and exact compiler receipts are validated by the
      // independent evaluator. Do not turn a missing optional selector into a
      // second evaluator or a costly compiler invocation here.
      continue;
    }
    const currentCount = leanProofEscapeCount(source);
    if (!currentCount) continue;
    const baselineCount = baseLeanProofEscapeCount(projectRoot, assignment.git.baseCommit, relativePath);
    if (currentCount <= baselineCount) continue;
    throw new Error(
      `Direct Mathematics completion adds a forbidden Lean proof escape in ${candidate}; continue the solver episode without sorry, admit, native_decide, or a new axiom.`
    );
  }
}

function countOutstandingMathematicsAssignments(
  capability: ResearchTeamToolCapability,
  result: ResearchTeamResult,
  sourceAssignment: ResearchTeamAssignment | undefined,
  listAssignments: ResearchTeamAssignmentListReader | undefined,
  validateAssignmentOnce: ResearchTeamAssignmentValidator,
  integrationAssignmentIds: readonly string[] = [],
  completionEligibleAssignmentId?: string
): number {
  if (!listAssignments || capability.profileId !== 'mathematics-research-team') return 0;
  const currentNodeId = sourceAssignment?.math?.activePlanNodeId ?? result.math?.activePlanNodeId;
  const solverCompleteDirect =
    sourceAssignment?.math?.directAttempt === true && isSolverCompleteDirectResult(result, sourceAssignment);
  const integrationAssignments = new Set(integrationAssignmentIds);
  const outstanding = listAssignments({
    workspace: capability.projectRoot,
    teamId: capability.teamId,
    states: ['accepted'],
  }).filter((receipt) => {
    if (
      receipt.state !== 'accepted' ||
      receipt.assignmentId === result.assignmentId ||
      receipt.supersessionPending ||
      receipt.budgetCancellation?.status === 'succeeded'
    ) {
      return false;
    }
    if (isOrphanedAcceptedMathematicsAssignment(receipt)) return false;
    if (integrationAssignments.has(receipt.assignmentId)) return false;
    const target = capability.roster.find((member) => member.roleKind === 'worker' && member.slotId === receipt.slotId);
    if (!target) return false;
    try {
      const pending = validateDurableResearchTeamAssignment(
        receipt.assignment,
        capability,
        target,
        validateAssignmentOnce
      );
      // Once a direct candidate is solver-complete, read-only discovery can no
      // longer change its bytes and must not delay external evaluation.  Keep
      // only other artifact FORMALIZE assignments in the completion barrier;
      // those may own disjoint declarations that are genuinely still open.
      if (solverCompleteDirect && (pending.executionMode === 'advisory' || pending.math?.stage !== 'formalize')) {
        return false;
      }
      // A winner for one explicit proof node cancels same-node competitors
      // during integration. Declaration-disjoint nodes and all other accepted
      // work remain part of the Lead's completion obligation.
      if (
        currentNodeId &&
        pending.math?.stage === 'formalize' &&
        pending.math.statementHash === result.math?.statementHash &&
        pending.math.activePlanNodeId === currentNodeId &&
        pending.git.baseCommit === result.git.baseCommit
      ) {
        return false;
      }
      return true;
    } catch {
      // An accepted receipt that cannot be interpreted safely must block a
      // whole-problem completion declaration rather than disappear from it.
      return true;
    }
  }).length;
  // Artifact integrations are serialized in request order. Only the last item
  // in a multi-delivery batch may declare whole-problem completion; earlier
  // items are intermediate commits even though the caller receives one batch
  // response after every item has integrated.
  return completionEligibleAssignmentId && completionEligibleAssignmentId !== result.assignmentId
    ? outstanding + 1
    : outstanding;
}

function assignmentArtifactPaths(
  assignment: ResearchTeamAssignment | undefined,
  fallback: readonly string[] = []
): readonly string[] {
  const declared = assignment?.math?.artifactPaths?.length
    ? assignment.math.artifactPaths
    : assignment?.expectedArtifacts?.length
      ? assignment.expectedArtifacts
      : fallback;
  return Object.freeze([...new Set(declared.map((value) => value.trim()).filter(Boolean))]);
}

/** Resolve an artifact selector to the project-relative file used by Lean. */
function projectRelativeLeanArtifactPath(projectRoot: string, candidate: unknown): string | undefined {
  if (typeof candidate !== 'string') return undefined;
  const normalized = candidate.trim().replaceAll('\\', '/');
  const selector = normalized.indexOf('#');
  const filePath = (selector >= 0 ? normalized.slice(0, selector) : normalized).trim();
  if (!filePath || path.extname(filePath).toLowerCase() !== '.lean') return undefined;
  if (filePath.startsWith('/') || filePath.split('/').includes('..') || filePath.includes('\0')) return undefined;
  const absolute = path.resolve(projectRoot, filePath);
  const relative = path.relative(path.resolve(projectRoot), absolute);
  if (relative.startsWith('..') || path.isAbsolute(relative)) return undefined;
  return relative.replaceAll(path.sep, '/');
}

type ReverifiedMathematicsReceipts = Readonly<{
  localGateReceipt?: MathLocalGateReceipt;
  mathNodeReceipt?: MathNodeProofReceipt;
  mathHelperReceipt?: MathHelperReceipt;
}>;

/** Validate durable merged receipts before using them as a replay shortcut. */
function assertPersistedReverifiedMathematics(
  receipts: ReverifiedMathematicsReceipts,
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined,
  projectRoot: string,
  mergedCommit: string
): void {
  if (!result.math) throw new Error('Persisted merged mathematics receipts require MathProgressDelta');
  const expectedKinds = [
    result.localGateReceipt ? 'localGateReceipt' : undefined,
    result.mathNodeReceipt ? 'mathNodeReceipt' : undefined,
    result.mathHelperReceipt ? 'mathHelperReceipt' : undefined,
  ].filter((kind): kind is string => Boolean(kind));
  const actualKinds = [
    receipts.localGateReceipt ? 'localGateReceipt' : undefined,
    receipts.mathNodeReceipt ? 'mathNodeReceipt' : undefined,
    receipts.mathHelperReceipt ? 'mathHelperReceipt' : undefined,
  ].filter((kind): kind is string => Boolean(kind));
  if (expectedKinds.length !== actualKinds.length || expectedKinds.some((kind) => !actualKinds.includes(kind))) {
    throw new Error('Persisted merged mathematics receipts do not cover the same receipt set as the delivered result');
  }

  const proofCandidates = assignmentArtifactPaths(assignment, result.artifactPaths);
  const assertProofHash = (proofHash: string): void => {
    const found = proofCandidates.some((candidate) => {
      const relative = projectRelativeLeanArtifactPath(projectRoot, candidate);
      if (!relative) return false;
      try {
        const actual = crypto
          .createHash('sha256')
          .update(fs.readFileSync(path.resolve(projectRoot, relative)))
          .digest('hex');
        return actual === proofHash;
      } catch {
        return false;
      }
    });
    if (!found)
      throw new Error('Persisted merged mathematics receipt proof hash is not present in the project artifacts');
  };

  if (receipts.localGateReceipt) {
    assertLocalGateReceiptMatches(
      receipts.localGateReceipt,
      result.math.statementHash,
      result.math.routeFingerprint,
      mergedCommit
    );
    assertReceiptTheoremMatchesContract(
      receipts.localGateReceipt,
      assignment?.math?.problemContract,
      assignment?.math?.fastCheck?.candidateClaim
    );
    assertProofHash(receipts.localGateReceipt.proofHash);
  }
  if (receipts.mathNodeReceipt) {
    if (!assignment || !result.math.activePlanNodeId) {
      throw new Error('Persisted merged node receipt has no immutable assignment plan context');
    }
    assertMathNodeReceiptMatches(
      receipts.mathNodeReceipt,
      result.math.statementHash,
      result.math.routeFingerprint,
      receipts.mathNodeReceipt.planNodeId,
      mergedCommit,
      assignment
    );
    assertProofHash(receipts.mathNodeReceipt.proofHash);
  }
  if (receipts.mathHelperReceipt) {
    assertMathHelperReceiptMatches(receipts.mathHelperReceipt, result, mergedCommit);
    assertProofHash(receipts.mathHelperReceipt.proofHash);
  }
}

function artifactPathsOverlap(left: readonly string[], right: readonly string[]): boolean {
  if (!left.length || !right.length) return false;
  const owned = new Set(left);
  return right.some((artifactPath) => owned.has(artifactPath));
}

/**
 * An accepted assignment can outlive its disposable worktree when Core was
 * restarted between the WAL write and batch creation. It is no longer an
 * ownership claim: keeping it in duplicate checks permanently blocks the
 * next proof node even though Core has no corresponding work.
 */
function isOrphanedAcceptedMathematicsAssignment(receipt: ProjectGitResearchTeamAssignmentReceipt): boolean {
  if (receipt.state !== 'accepted' || receipt.delivery || receipt.supersessionPending) return false;
  const rawAssignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
  const rawGit = rawAssignment && isRecord(rawAssignment.git) ? rawAssignment.git : undefined;
  const worktreePath =
    receipt.preparedGit?.worktreePath ?? (typeof rawGit?.worktreePath === 'string' ? rawGit.worktreePath : undefined);
  return Boolean(worktreePath && path.isAbsolute(worktreePath) && !fs.existsSync(worktreePath));
}

/**
 * A prepared artifact assignment is only a WAL reservation until Core accepts
 * its mailbox message. If the private solver worktree disappeared before that
 * point, retaining the reservation blocks the same route forever: a new
 * worktree would produce a different mailbox fingerprint for the old key.
 */
export function isOrphanedPreparedMathematicsAssignment(receipt: ProjectGitResearchTeamAssignmentReceipt): boolean {
  if (receipt.state !== 'prepared' || receipt.delivery) return false;
  const rawAssignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
  const rawGit = rawAssignment && isRecord(rawAssignment.git) ? rawAssignment.git : undefined;
  const worktreePath =
    receipt.preparedGit?.worktreePath ?? (typeof rawGit?.worktreePath === 'string' ? rawGit.worktreePath : undefined);
  return Boolean(worktreePath && path.isAbsolute(worktreePath) && !fs.existsSync(worktreePath));
}

export function recoveryIdempotencyKeyForOrphanedPreparedAssignment(
  requestedKey: string,
  targetSlotId: string,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[] | undefined
): string {
  const orphan = assignmentHistory?.find(
    (receipt) =>
      receipt.assignmentId === requestedKey &&
      receipt.slotId === targetSlotId &&
      isOrphanedPreparedMathematicsAssignment(receipt)
  );
  if (!orphan) return requestedKey;
  const suffix = `-recovery-${crypto
    .createHash('sha256')
    .update(`${orphan.teamId}\u0000${orphan.assignmentId}\u0000${orphan.updatedAt}`, 'utf8')
    .digest('hex')
    .slice(0, 12)}`;
  return `${requestedKey.slice(0, Math.max(1, 128 - suffix.length))}${suffix}`;
}

/**
 * With a second proof owner, the first host-verified original-target
 * integration wins. The other Lean Engineer's open attempt would otherwise
 * stay pending and hold solver_ready (mathRunObservation) forever.
 */
export function retireCompetingMathProofOwner(
  context: ResearchTeamToolContext,
  winnerSlotId: string,
  winnerAssignmentId: string
): void {
  const projectGit = context.projectGit;
  if (!readMathRunSecondProofOwner(process.env) || !projectGit?.supersedeResearchTeamAssignment) return;
  const leanSlots = new Set(
    context.capability.roster.filter((member) => member.laneId === 'lean-engineering').map((member) => member.slotId)
  );
  for (const other of projectGit.listResearchTeamAssignments({
    workspace: context.capability.projectRoot,
    teamId: context.capability.teamId,
  })) {
    if (
      other.assignmentId === winnerAssignmentId ||
      other.slotId === winnerSlotId ||
      !leanSlots.has(other.slotId) ||
      !['prepared', 'accepted'].includes(other.state) ||
      other.integration
    )
      continue;
    try {
      projectGit.supersedeResearchTeamAssignment({
        workspace: context.capability.projectRoot,
        teamId: context.capability.teamId,
        slotId: other.slotId,
        assignmentId: other.assignmentId,
        supersession: {
          winnerAssignmentId,
          reason: 'The other proof owner produced the first host-verified original-target integration.',
        },
      });
    } catch {
      // The observation keeps solver_ready blocked; the Lead sees the pending attempt.
    }
  }
}

/** Exactly one other original-target attempt, on the other Lean Engineer slot, when the run froze it. */
export function allowsSecondMathematicsProofOwner(input: {
  enabled: boolean;
  leanSlots: ReadonlySet<string>;
  targetSlotId?: string;
  activeSlotId: string;
  concurrentProofOwners: number;
}): boolean {
  return (
    input.enabled &&
    input.leanSlots.size >= 2 &&
    input.targetSlotId !== undefined &&
    input.leanSlots.has(input.targetSlotId) &&
    input.leanSlots.has(input.activeSlotId) &&
    input.activeSlotId !== input.targetSlotId &&
    input.concurrentProofOwners === 0
  );
}

function assertNoConcurrentDuplicateMathematicsArtifact(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[],
  capability: ResearchTeamToolCapability,
  targetSlotId?: string
): void {
  if (
    assignment.executionMode === 'advisory' ||
    assignment.math?.stage !== 'formalize' ||
    !assignment.math.activePlanNodeId
  ) {
    return;
  }
  // A Team built with a second proof owner has two Lean Engineer slots. Exactly
  // one concurrent original-target attempt on the other Lean slot is allowed;
  // the first host-verified integration supersedes the other.
  const leanSlots = new Set(
    capability.roster.filter((member) => member.laneId === 'lean-engineering').map((member) => member.slotId)
  );
  // Only a run that froze a second proof owner may relax the single-owner rule;
  // an ordinary roster with two Lean slots keeps it (existing guard tests).
  const secondProofOwner = readMathRunSecondProofOwner(process.env);
  let concurrentProofOwners = 0;
  for (const receipt of assignmentHistory) {
    if (
      receipt.assignmentId === assignment.assignmentId ||
      !['prepared', 'accepted'].includes(receipt.state) ||
      receipt.delivery ||
      receipt.budgetCancellation?.status === 'succeeded'
    ) {
      continue;
    }
    if (isOrphanedAcceptedMathematicsAssignment(receipt) || isOrphanedPreparedMathematicsAssignment(receipt)) continue;
    const target = capability.roster.find((member) => member.slotId === receipt.slotId);
    if (!target) continue;
    let active: ResearchTeamAssignment;
    try {
      active = validateDurableResearchTeamAssignment(receipt.assignment, capability, target, validateAssignment);
    } catch {
      continue;
    }
    if (
      active.executionMode !== 'advisory' &&
      active.math?.stage === 'formalize' &&
      active.math.statementHash === assignment.math.statementHash &&
      active.git.baseCommit === assignment.git.baseCommit &&
      (active.math.activePlanNodeId === assignment.math.activePlanNodeId ||
        (isBoundImoMathematicsWorkspace(capability) &&
          active.math.routeFingerprint === assignment.math.routeFingerprint))
    ) {
      if (
        allowsSecondMathematicsProofOwner({
          enabled: secondProofOwner,
          leanSlots,
          targetSlotId,
          activeSlotId: receipt.slotId,
          concurrentProofOwners,
        })
      ) {
        concurrentProofOwners += 1;
        continue;
      }
      throw new Error(
        isBoundImoMathematicsWorkspace(capability)
          ? 'Bound IMO route already has an active persistent Formalizer; continue through that Worker slot'
          : 'Mathematics artifact assignment duplicates an active statement, base commit, and tightly coupled plan node'
      );
    }
  }
}

/**
 * Guard the gap between separate Lead dispatch calls. The wave-level check
 * catches duplicate discovery objectives submitted together, but two calls
 * can validate before either Core acknowledgement is durable. An un-delivered
 * prepared or Core-accepted advisory assignment with the same immutable route
 * identity and objective is therefore already doing the work; starting another
 * Worker only duplicates an expensive model turn. Prepared records are kept in
 * this guard because recovery reconciles them before a new dispatch wave is
 * allowed to proceed. Completed deliveries are ignored so a later Lead can
 * issue a genuinely new follow-up after the finding arrives.
 */
function assertNoConcurrentDuplicateMathematicsResearch(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[],
  capability: ResearchTeamToolCapability
): void {
  if (
    capability.profileId !== 'mathematics-research-team' ||
    assignment.executionMode !== 'advisory' ||
    !assignment.math ||
    !['diversify', 'replan'].includes(assignment.math.stage) ||
    assignment.math.routeProposalMode === 'candidate'
  ) {
    return;
  }
  const objective = assignment.objective.trim().toLowerCase().replace(/\s+/gu, ' ');
  if (!objective) return;
  for (const receipt of assignmentHistory) {
    if (
      receipt.assignmentId === assignment.assignmentId ||
      !['prepared', 'accepted'].includes(receipt.state) ||
      receipt.delivery ||
      receipt.supersessionPending ||
      receipt.budgetCancellation?.status === 'succeeded'
    ) {
      continue;
    }
    if (isOrphanedAcceptedMathematicsAssignment(receipt)) continue;
    const target = capability.roster.find((member) => member.roleKind === 'worker' && member.slotId === receipt.slotId);
    if (!target) continue;
    let active: ResearchTeamAssignment;
    try {
      active = validateDurableResearchTeamAssignment(receipt.assignment, capability, target, validateAssignment);
    } catch {
      continue;
    }
    if (
      active.executionMode === 'advisory' &&
      active.math &&
      ['diversify', 'replan'].includes(active.math.stage) &&
      active.math.routeProposalMode !== 'candidate' &&
      active.math.statementHash === assignment.math.statementHash &&
      active.git.baseCommit === assignment.git.baseCommit &&
      active.math.routeFingerprint === assignment.math.routeFingerprint &&
      active.objective.trim().toLowerCase().replace(/\s+/gu, ' ') === objective
    ) {
      throw new Error(
        'Mathematics discovery objective is already active on another Worker; wait for its delivery before dispatching it again'
      );
    }
  }
}

/**
 * A refuted route is a durable tombstone, not an invitation to keep spawning
 * local repairs.  Compiler failures and ordinary stalls remain repairable;
 * only a semantic refutation (wrong statement, counterexample, or duplicate
 * route) closes the route until Lead selects a different route fingerprint.
 */
export function receiptTombstonesMathematicsRoute(
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  statementHash: string,
  routeFingerprint: string,
  structureSignature?: string
): boolean {
  if (!['accepted', 'integrated'].includes(receipt.state) || !isRecord(receipt.assignment)) return false;
  const rawAssignment = receipt.assignment;
  const rawMath = isRecord(rawAssignment.math) ? rawAssignment.math : undefined;
  if (!rawMath || rawMath.statementHash !== statementHash) {
    return false;
  }
  const rawRouteFingerprint =
    typeof rawMath.routeFingerprint === 'string' ? normalizeMathRouteFingerprint(rawMath.routeFingerprint) : undefined;
  let routeMatches = rawRouteFingerprint === routeFingerprint;
  if (!routeMatches && structureSignature && Array.isArray(rawMath.routeCards)) {
    for (const rawCard of rawMath.routeCards) {
      if (!isRecord(rawCard)) continue;
      try {
        const normalized = normalizeMathRouteCard(rawCard as never);
        if (mathRouteStructureSignatureFromNormalized(normalized) === structureSignature) {
          routeMatches = true;
          break;
        }
      } catch {
        // Invalid legacy cards cannot safely establish structural identity.
      }
    }
  }
  if (!routeMatches) {
    const delivered = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
    const deliveredCard = delivered && isRecord(delivered.mathRouteCard) ? delivered.mathRouteCard : undefined;
    if (deliveredCard && structureSignature) {
      try {
        routeMatches =
          mathRouteStructureSignatureFromNormalized(normalizeMathRouteCard(deliveredCard as never)) ===
          structureSignature;
      } catch {
        routeMatches = false;
      }
    }
  }
  if (!routeMatches) return false;

  const delivered = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
  const finding = delivered && isRecord(delivered.mathResearchFinding) ? delivered.mathResearchFinding : undefined;
  if (!finding) return false;
  try {
    const normalized = normalizeMathResearchFinding(finding as never);
    const evidence = readTrustedAssignmentMathEvidence(normalized, receipt);
    return (
      classifyMathResearchFindingProgress(normalized, normalized.mainlineImpact ?? 'stalled', undefined, evidence)
        .kind === 'route_refuted'
    );
  } catch {
    // Legacy or malformed reports cannot establish a mathematical refutation.
    return false;
  }
}

function readTrustedAssignmentMathEvidence(
  finding: MathResearchFinding,
  receipt: ProjectGitResearchTeamAssignmentReceipt
) {
  const observations = readTrustedMathResearchEvidence(finding, receipt);
  const assignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
  const math = assignment && isRecord(assignment.math) ? assignment.math : undefined;
  if (!math || !Array.isArray(math.routeCards)) return observations;
  const routeCards = math.routeCards;
  const git = isRecord(assignment?.git) ? assignment.git : undefined;
  if (typeof git?.baseCommit !== 'string') return observations;
  const refutations = finding.evidenceRefs.flatMap((reference) =>
    routeCards.flatMap((rawCard: unknown) => {
      try {
        const routeCard = normalizeMathRouteCard(rawCard as never);
        if (routeCard.statementHash !== math.statementHash || routeCard.routeFingerprint !== math.routeFingerprint)
          return [];
        const verified = readTrustedMathRouteRefutation(reference, {
          teamId: receipt.teamId,
          assignmentId: receipt.assignmentId,
          routeCard,
          baseCommit: git.baseCommit as string,
        });
        return verified
          ? [
              {
                grade: 'kernel_verified' as const,
                scope: 'approach' as const,
                statement: `Route ${verified.routeFingerprint} requires refuted obligation ${verified.planNodeId}`,
                reference,
              },
            ]
          : [];
      } catch {
        return [];
      }
    })
  );
  return [...observations, ...refutations];
}

function mathematicsRouteTombstoned(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[]
): boolean {
  const math = assignment.math;
  if (!math || !['formalize', 'replan'].includes(math.stage)) return false;
  const structureSignature = math.routeCards?.find((card) => card.routeFingerprint === math.routeFingerprint);
  const normalizedStructureSignature = structureSignature
    ? mathRouteStructureSignatureFromNormalized(structureSignature)
    : undefined;
  return assignmentHistory.some((receipt) =>
    receiptTombstonesMathematicsRoute(
      receipt,
      math.statementHash,
      normalizeMathRouteFingerprint(math.routeFingerprint),
      normalizedStructureSignature
    )
  );
}

export function mathematicsBlockingDependencySignature(assignment: ResearchTeamAssignment): string | undefined {
  const math = assignment.math;
  if (!math || math.stage !== 'formalize' || math.directAttempt === true || !math.activePlanNodeId) return undefined;
  const routeFingerprint = normalizeMathRouteFingerprint(math.routeFingerprint);
  const route = math.routeCards?.find(
    (card) => normalizeMathRouteFingerprint(card.routeFingerprint) === routeFingerprint
  );
  if (!route) return undefined;
  const nodeById = new Map(route.planNodes.map((node) => [node.id, node]));
  const blocking = new Set<string>();
  const relevantNodeIds = new Set<string>();
  const visited = new Set<string>();
  const visit = (nodeId: string): void => {
    if (visited.has(nodeId)) return;
    visited.add(nodeId);
    relevantNodeIds.add(nodeId);
    const node = nodeById.get(nodeId);
    if (!node) return;
    for (const dependencyId of node.dependsOn) {
      const dependency = nodeById.get(dependencyId);
      if (!dependency) continue;
      if (dependency.status !== 'kernel_verified') {
        const claim = dependency.provisionalLeanStatement.trim().replace(/\s+/gu, ' ').toLowerCase();
        blocking.add(`${dependency.role}:${dependency.kind ?? 'theorem'}:${claim}`);
      }
      visit(dependencyId);
    }
  };
  visit(math.activePlanNodeId);
  // A plan node can be actionable while still waiting on the same untyped
  // premise/API bridge as another node. Treat that shared coverage gap as a
  // dependency frontier too; otherwise two syntactically distinct nodes will
  // launch identical library-retrieval work in parallel.
  const premiseByName = new Map(route.premiseBundle.premises.map((premise) => [premise.declarationName, premise]));
  for (const coverage of route.premiseBundle.coverage) {
    if (!relevantNodeIds.has(coverage.planNodeId) || coverage.selfContained) continue;
    const unresolved = coverage.unresolvedNeed?.trim().replace(/\s+/gu, ' ').toLowerCase();
    const untyped = coverage.premiseDeclarationNames
      .map((name) => premiseByName.get(name))
      .filter((premise): premise is NonNullable<typeof premise> => Boolean(premise && premise.status !== 'typed'))
      .map((premise) => premise.declarationName.trim().replace(/\s+/gu, ' ').toLowerCase())
      .toSorted();
    if (unresolved) blocking.add(`premise:${unresolved}`);
    for (const declaration of untyped) blocking.add(`premise:${declaration}`);
  }
  // An actionable node can still be an unverified API bridge whose source
  // lookup is the real shared bottleneck.  Route selection deliberately
  // requires a structurally complete premise bundle, so represent this gap
  // on the plan node itself instead of making the whole route unselectable.
  // Only explicit api_bridge nodes participate; ordinary theorem nodes may
  // legitimately cite the same Mathlib module while proving independent
  // claims.
  for (const nodeId of relevantNodeIds) {
    const node = nodeById.get(nodeId);
    if (!node || node.status === 'kernel_verified' || node.kind !== 'api_bridge') continue;
    const source = node.sourceProvenance?.[0];
    const locator = source?.locator.trim().replace(/\s+/gu, ' ').toLowerCase();
    blocking.add(
      locator
        ? `api:${source?.kind ?? 'source'}:${locator}`
        : `api:${node.provisionalLeanStatement.trim().replace(/\s+/gu, ' ').toLowerCase()}`
    );
  }
  if (!blocking.size) return undefined;
  return [...blocking].toSorted().join('\u0001');
}

function mathematicsProofFrontierIdentity(assignment: ResearchTeamAssignment):
  | Readonly<{
      progressFingerprint?: string;
      proofStateFingerprint?: string;
    }>
  | undefined {
  const math = assignment.math;
  if (!math || math.stage !== 'formalize') return undefined;
  const ledger = math.failureLedger;
  if (!ledger?.progressFingerprint && !ledger?.proofStateFingerprint) return undefined;
  return Object.freeze({
    ...(ledger.progressFingerprint ? { progressFingerprint: ledger.progressFingerprint } : {}),
    ...(ledger.proofStateFingerprint ? { proofStateFingerprint: ledger.proofStateFingerprint } : {}),
  });
}

function assertNoConcurrentDuplicateMathematicsDependency(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[],
  capability: ResearchTeamToolCapability,
  waveAssignments: readonly ResearchTeamAssignment[] = []
): void {
  const signature = mathematicsBlockingDependencySignature(assignment);
  const frontier = mathematicsProofFrontierIdentity(assignment);
  if (!signature && !frontier) return;
  const methodClass = mathematicsAssignmentMethodClass(assignment);
  const candidates = [
    ...waveAssignments,
    ...assignmentHistory.flatMap((receipt) => {
      if (receipt.assignmentId === assignment.assignmentId || !['prepared', 'accepted'].includes(receipt.state))
        return [];
      const target = capability.roster.find(
        (member) => member.roleKind === 'worker' && member.slotId === receipt.slotId
      );
      if (!target) return [];
      try {
        return [validateDurableResearchTeamAssignment(receipt.assignment, capability, target, validateAssignment)];
      } catch {
        return [];
      }
    }),
  ];
  for (const other of candidates) {
    if (other.assignmentId === assignment.assignmentId) continue;
    const otherFrontier = mathematicsProofFrontierIdentity(other);
    if (
      frontier &&
      otherFrontier &&
      assignment.math?.statementHash === other.math?.statementHash &&
      assignment.git.baseCommit === other.git.baseCommit &&
      ((frontier.progressFingerprint && frontier.progressFingerprint === otherFrontier.progressFingerprint) ||
        (frontier.proofStateFingerprint && frontier.proofStateFingerprint === otherFrontier.proofStateFingerprint))
    ) {
      throw new Error(
        'Mathematics FORMALIZE assignment shares the same durable proof frontier; wait for that solver episode to advance'
      );
    }
    if (
      !signature ||
      other.math?.statementHash !== assignment.math?.statementHash ||
      other.git.baseCommit !== assignment.git.baseCommit ||
      other.executionMode !== 'artifact' ||
      mathematicsAssignmentMethodClass(other) !== methodClass ||
      mathematicsBlockingDependencySignature(other) !== signature
    ) {
      continue;
    }
    throw new Error(
      'Mathematics FORMALIZE assignment shares the same unresolved dependency frontier and method as active work; wait for that dependency to advance'
    );
  }
}

function hasReverifiedReceipt(value: {
  localGateReceipt?: unknown;
  mathNodeReceipt?: unknown;
  mathHelperReceipt?: unknown;
}): boolean {
  return Boolean(value.localGateReceipt || value.mathNodeReceipt || value.mathHelperReceipt);
}

function readDispatchAssignmentSource(item: Readonly<{ assignment?: unknown; task?: unknown }>) {
  const hasFullAssignment = isRecord(item.assignment);
  const structuredTask = isRecord(item.task) ? normalizeResearchTeamWireRecord(item.task, 'task') : undefined;
  const task =
    typeof item.task === 'string'
      ? item.task.trim()
      : typeof structuredTask?.objective === 'string'
        ? structuredTask.objective.trim()
        : '';
  if (hasFullAssignment === Boolean(task)) {
    throw new Error('dispatch requires exactly one of assignment or task');
  }
  return { hasFullAssignment, structuredTask, task };
}

function normalizeAssignmentInput(
  item: ResearchTeamDispatchItemInput,
  idempotencyKey: string,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  assignmentHistory?: readonly ProjectGitResearchTeamAssignmentReceipt[],
  source = readDispatchAssignmentSource(item),
  trustedFastCheck?: MathFastCheck
): Record<string, unknown> {
  const { hasFullAssignment, structuredTask, task } = source;
  const structuredMath = isRecord(structuredTask?.math) ? structuredTask.math : undefined;
  if (hasFullAssignment) {
    const assignment = normalizeResearchTeamWireRecord(item.assignment as Record<string, unknown>, 'assignment');
    // DeepSeek often selects the documented full-assignment compatibility
    // path even when the preferred compact task path is shown first.  Apply
    // the same runtime-owned mathematics hydration here so a nearly complete
    // payload cannot spend a whole Lead turn repairing immutable contract
    // fields one at a time.
    if (
      capability.profileId === 'mathematics-research-team' &&
      isBoundImoMathematicsWorkspace(capability) &&
      isRecord(assignment.math)
    ) {
      const git = isRecord(assignment.git) ? assignment.git : undefined;
      const baseCommit = typeof git?.baseCommit === 'string' ? git.baseCommit : item.baseCommit;
      const hydratedMath = normalizePreferredMathematicsDispatchMath(
        assignment.math,
        baseCommit,
        capability,
        target,
        assignmentHistory
      );
      if (hydratedMath) return { ...assignment, math: hydratedMath };
    }
    return assignment;
  }

  const title =
    typeof structuredTask?.title === 'string' && structuredTask.title.trim()
      ? structuredTask.title.trim()
      : firstTaskLine(task);
  const structuredAcceptanceCriteria = Array.isArray(structuredTask?.acceptanceCriteria)
    ? structuredTask.acceptanceCriteria
    : undefined;
  const structuredFailureCriteria = Array.isArray(structuredTask?.failureCriteria)
    ? structuredTask.failureCriteria
    : undefined;
  const structuredExpectedArtifacts = Array.isArray(structuredTask?.expectedArtifacts)
    ? structuredTask.expectedArtifacts
    : undefined;
  const structuredEvidenceRefs = Array.isArray(structuredTask?.evidenceRefs) ? structuredTask.evidenceRefs : undefined;
  const structuredDoNotRepeat = Array.isArray(structuredTask?.doNotRepeat) ? structuredTask.doNotRepeat : undefined;
  const structuredFalsificationPlan = isRecord(structuredTask?.falsificationPlan)
    ? structuredTask.falsificationPlan
    : undefined;
  const math = normalizePreferredMathematicsDispatchMath(
    item.math ?? structuredMath,
    item.baseCommit,
    capability,
    target,
    assignmentHistory,
    trustedFastCheck
  );
  return {
    schema: RESEARCH_TEAM_ASSIGNMENT_SCHEMA,
    assignmentId: idempotencyKey,
    workflowId: capability.workflowId,
    laneId: target.laneId,
    ...(item.roleTemplateId ? { roleTemplateId: item.roleTemplateId } : {}),
    ...(item.roleKind ? { roleKind: item.roleKind } : {}),
    ...(item.roleLabel ? { roleLabel: item.roleLabel } : {}),
    ...(item.roleInstructions ? { roleInstructions: item.roleInstructions } : {}),
    ...(item.executionMode
      ? { executionMode: item.executionMode }
      : math && isBoundImoMathematicsWorkspace(capability)
        ? { executionMode: target.laneId === 'lean-engineering' ? 'artifact' : 'advisory' }
        : {}),
    ...(math ? { math } : {}),
    title,
    objective: task,
    acceptanceCriteria: item.acceptanceCriteria?.length
      ? item.acceptanceCriteria
      : structuredAcceptanceCriteria?.length
        ? structuredAcceptanceCriteria
        : ['Return one usable result or a precise blocker to the Lead.'],
    failureCriteria: item.failureCriteria?.length
      ? item.failureCriteria
      : structuredFailureCriteria?.length
        ? structuredFailureCriteria
        : ['No usable result or precise blocker can be returned with the available data, tools, and time.'],
    evidenceRefs: structuredEvidenceRefs ?? [],
    doNotRepeat: structuredDoNotRepeat ?? [],
    expectedArtifacts: item.expectedArtifacts?.length
      ? item.expectedArtifacts
      : structuredExpectedArtifacts?.length
        ? structuredExpectedArtifacts
        : ['A concise Worker delivery; include committed paths only when the task changes project files.'],
    falsificationPlan: structuredFalsificationPlan ?? {
      hypothesis: `The assigned task can produce a useful result: ${title}`,
      test: 'Complete the task and report the observable result, limitation, or blocker.',
      failureSignal: 'The Worker cannot return a usable result or a precise blocker.',
    },
    git: {
      projectRoot: capability.projectRoot,
      baseCommit: item.baseCommit,
    },
    ...(item.budget ? { budget: item.budget } : {}),
  };
}

/**
 * Compile short Lead-authored mathematics intent into the canonical execution
 * contract. Full assignment callers stay strict; only the preferred task path
 * receives this compatibility and durable-context hydration.
 */
function normalizePreferredMathematicsDispatchMath(
  input: Record<string, unknown> | undefined,
  baseCommit: string | undefined,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  assignmentHistory?: readonly ProjectGitResearchTeamAssignmentReceipt[],
  trustedFastCheck?: MathFastCheck
): Record<string, unknown> | undefined {
  if (capability.profileId !== 'mathematics-research-team') return input;

  const boundImoContract = isBoundImoMathematicsWorkspace(capability);
  // A bound IMO proof-mainline has one persistent Lean Worker.  The model is
  // allowed to send only the task text; the adapter owns the immutable
  // contract and must still produce a valid first assignment.  Keep this
  // fallback limited to the Lean lane so ordinary mathematics discovery and
  // compatibility callers remain strict.
  const autoBoundMainline = boundImoContract && target.laneId === 'lean-engineering' && input === undefined;
  if (!input && !autoBoundMainline) return input;
  input = input ?? {};

  // Recovery actions are emitted in the public snake_case wire shape. Keep
  // this alias explicit on the preferred compact path so a Lead can place
  // `next_assignment.execution_policy` directly under `math` without losing
  // the durable tactic/query/model cursor during later hydration.
  input = normalizePreferredMathematicsExecutionPolicyAlias(input);
  input = normalizeResearchTeamWireRecord(input, 'math');
  input = hydratePreferredImoMathematicsContract(input, baseCommit, capability, trustedFastCheck);
  input = normalizePreferredMathematicsExecutionPolicyAlias(input);
  // `problemId` is part of the trusted contract identity. Compact Lead
  // payloads often carry the research contract without repeating it; bind it
  // from problemContract before strict normalization instead of spending a
  // model turn repairing a deterministic metadata omission.
  if (isRecord(input.researchContract) && isRecord(input.problemContract)) {
    const researchProblemId = String(input.researchContract.problemId ?? '').trim();
    const contractProblemId = String(input.problemContract.problemId ?? '').trim();
    if (!researchProblemId && contractProblemId) {
      input = {
        ...input,
        researchContract: { ...input.researchContract, problemId: contractProblemId },
      };
    }
  }
  const proofMainline = boundImoContract && capability.agentLimit === 1 && capability.reasoningConcurrency === 1;
  if (boundImoContract && target.laneId === 'lean-engineering' && !input.routeFingerprint) {
    const problemId = isRecord(input.problemContract) ? String(input.problemContract.problemId || '').trim() : '';
    if (!problemId) throw new Error('Bound IMO mathematics contract requires problemContract.problemId');
    input = {
      ...input,
      routeFingerprint: `${problemId.replace(/_/gu, '-')}-mainline-direct-v1`,
    };
  }
  if (input.routeProposalMode !== undefined && input.routeProposalMode !== 'candidate') {
    const { routeProposalMode: _leadMethodLabel, ...withoutInvalidRouteProposalMode } = input;
    input = withoutInvalidRouteProposalMode;
  }
  const statementHash = typeof input.statementHash === 'string' ? input.statementHash.trim().toLowerCase() : '';
  if (statementHash && isRecord(input.fastCheck)) {
    input = { ...input, fastCheck: { ...input.fastCheck, statementHash } };
  }

  const proposesCandidate = input.routeProposalMode === 'candidate';
  const suppliedStage = typeof input.stage === 'string' ? input.stage.trim() : '';
  let stage = suppliedStage;
  if (target.laneId === 'strategy-exploration') {
    stage = proposesCandidate || ['replan', 'route_replan'].includes(suppliedStage) ? 'replan' : 'diversify';
  } else if (target.laneId === 'lean-engineering') {
    stage = 'formalize';
  } else if (target.laneId === 'independent-review') {
    stage = 'review';
  }
  if (!MATH_PROOF_STAGES.includes(stage as ResearchTeamMathAssignment['stage'])) {
    throw new Error(
      `Research Team math.stage is invalid for ${target.laneId ?? 'this Worker'}; expected one of ` +
        `${MATH_PROOF_STAGES.join('|')}`
    );
  }

  const canonicalStage = stage as ResearchTeamMathAssignment['stage'];
  const expectedWorkflowStage = proposesCandidate ? 'candidate' : normalizeMathWorkflowStage(canonicalStage);
  const workflowStage = expectedWorkflowStage;
  const stageScopedInput: Record<string, unknown> = {
    ...input,
    ...(boundImoContract &&
    canonicalStage === 'formalize' &&
    target.laneId === 'lean-engineering' &&
    (autoBoundMainline || proofMainline)
      ? { directAttempt: true, activePlanNodeId: input.activePlanNodeId || 'direct-goal' }
      : {}),
  };
  // A route replan can inherit this FORMALIZE-only coordinate from the stalled
  // source assignment. The preferred compact path drops it deterministically;
  // callers that submit full assignments still receive strict validation.
  if (canonicalStage !== 'formalize') delete stageScopedInput['activePlanNodeId'];

  // Alignment is a runtime contract, not a model vocabulary.  Accept the
  // common natural-language equivalent emitted by models and normalize the
  // timestamp before strict validation so the next field error is not hidden
  // behind a deterministic spelling/format repair.
  if (isRecord(stageScopedInput.alignmentCheck)) {
    let alignmentCheck = canonicalizePreferredAlignmentCheck(stageScopedInput.alignmentCheck);
    // Full-assignment compatibility callers sometimes omit (or emit an empty)
    // forbiddenChanges list. It is a projection of the trusted problem
    // contract, so fill it atomically instead of spending successive Lead
    // turns repairing one deterministic schema field at a time.
    const problemContract = isRecord(stageScopedInput.problemContract) ? stageScopedInput.problemContract : undefined;
    const knownTraps = Array.isArray(problemContract?.knownTraps)
      ? problemContract.knownTraps.filter(
          (value): value is string => typeof value === 'string' && value.trim().length > 0
        )
      : undefined;
    if (
      knownTraps?.length &&
      (!Array.isArray(alignmentCheck.forbiddenChanges) || alignmentCheck.forbiddenChanges.length === 0)
    ) {
      alignmentCheck = { ...alignmentCheck, forbiddenChanges: [...knownTraps] };
    }
    stageScopedInput.alignmentCheck = alignmentCheck;
  }
  if (isRecord(stageScopedInput.fastCheck)) {
    stageScopedInput.fastCheck = {
      ...stageScopedInput.fastCheck,
      checkedAt: normalizePreferredMathCheckedAt(stageScopedInput.fastCheck.checkedAt),
    };
  }

  const durableHistory = [...(assignmentHistory ?? [])]
    .reverse()
    .filter((receipt) => receipt.state === 'accepted' || receipt.state === 'integrated');
  const continuationSourceId = isRecord(input.sessionContinuation)
    ? String(input.sessionContinuation.sourceAssignmentId ?? '')
    : '';
  const matchingReceipts = durableHistory.filter((receipt) => {
    const assignment = receipt.assignment;
    return (
      isRecord(assignment) &&
      isRecord(assignment.math) &&
      isRecord(assignment.git) &&
      assignment.math.statementHash === statementHash &&
      assignment.git.baseCommit === baseCommit
    );
  });
  if (proofMainline && canonicalStage === 'formalize' && stageScopedInput.directAttempt === true) {
    const previousMainline = matchingReceipts.find(
      (receipt) =>
        receipt.slotId === target.slotId &&
        isRecord(receipt.assignment) &&
        receipt.assignment.laneId === 'lean-engineering' &&
        isRecord(receipt.assignment.math) &&
        receipt.assignment.math.directAttempt === true
    );
    if (previousMainline && !isRecord(stageScopedInput['sessionContinuation'])) {
      stageScopedInput['sessionContinuation'] = {
        sourceAssignmentId: previousMainline.assignmentId,
        mode: 'reuse_source_slot',
        purpose: 'candidate_repair',
      };
    }
  }
  const immutableSource =
    matchingReceipts.find(
      (receipt) =>
        receipt.assignmentId === continuationSourceId &&
        isRecord(receipt.assignment) &&
        isRecord(receipt.assignment.math) &&
        isRecord(receipt.assignment.math.problemContract) &&
        isRecord(receipt.assignment.math.fastCheck) &&
        isRecord(receipt.assignment.math.alignmentCheck)
    ) ??
    matchingReceipts.find(
      (receipt) =>
        isRecord(receipt.assignment) &&
        isRecord(receipt.assignment.math) &&
        isRecord(receipt.assignment.math.problemContract) &&
        isRecord(receipt.assignment.math.fastCheck) &&
        isRecord(receipt.assignment.math.alignmentCheck)
    );
  let inherited: Record<string, unknown> = {};
  if (immutableSource && isRecord(immutableSource.assignment) && isRecord(immutableSource.assignment.math)) {
    // A bound adapter has already replaced these fields with the immutable
    // contract on disk. Older advisory receipts must never overwrite a newer
    // trusted FAST_CHECK decision or statement/alignment binding.
    inherited = boundImoContract
      ? immutableSource.assignment.math.executionPolicy
        ? { executionPolicy: immutableSource.assignment.math.executionPolicy }
        : {}
      : {
          problemContract: immutableSource.assignment.math.problemContract,
          fastCheck: immutableSource.assignment.math.fastCheck,
          alignmentCheck: immutableSource.assignment.math.alignmentCheck,
          ...(input.executionPolicy === undefined && immutableSource.assignment.math.executionPolicy
            ? { executionPolicy: immutableSource.assignment.math.executionPolicy }
            : {}),
        };
  }

  const directAttempt = stageScopedInput.directAttempt === true;
  const normalizedRoute =
    typeof input.routeFingerprint === 'string' ? normalizeMathRouteFingerprint(input.routeFingerprint) : '';
  const leadRouteAssessment = isRecord(input.routeAssessment)
    ? {
        ...input.routeAssessment,
        assessorSessionId: `${capability.teamId}:${capability.slotId}:route-selection`,
        checkedAt: normalizePreferredMathCheckedAt(input.routeAssessment.checkedAt),
      }
    : undefined;
  if (boundImoContract && canonicalStage === 'formalize' && !directAttempt && !leadRouteAssessment) {
    throw new Error('Bound IMO routed FORMALIZE requires a fresh Lead-owned routeAssessment');
  }
  if (!directAttempt && (canonicalStage === 'formalize' || canonicalStage === 'review')) {
    const routeSource = matchingReceipts.find((receipt) => {
      if (!isRecord(receipt.assignment) || !isRecord(receipt.assignment.math)) return false;
      const cards = Array.isArray(receipt.assignment.math.routeCards) ? receipt.assignment.math.routeCards : [];
      const deliveryResult = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
      const deliveredCard =
        deliveryResult && isRecord(deliveryResult.mathRouteCard) ? deliveryResult.mathRouteCard : undefined;
      const deliveredRouteMatches = Boolean(
        deliveredCard &&
        typeof deliveredCard.routeFingerprint === 'string' &&
        normalizeMathRouteFingerprint(deliveredCard.routeFingerprint) === normalizedRoute
      );
      if (boundImoContract && canonicalStage === 'formalize') {
        return (
          receipt.state === 'integrated' &&
          receipt.assignment.laneId === 'strategy-exploration' &&
          ['diversify', 'replan'].includes(String(receipt.assignment.math.stage)) &&
          deliveredRouteMatches
        );
      }
      return (
        cards.some(
          (card) =>
            isRecord(card) &&
            typeof card.routeFingerprint === 'string' &&
            normalizeMathRouteFingerprint(card.routeFingerprint) === normalizedRoute
        ) || deliveredRouteMatches
      );
    });
    if (!routeSource && boundImoContract && canonicalStage === 'formalize') {
      throw new Error('Bound IMO routed FORMALIZE requires a durable Strategy route delivery');
    }
    if (routeSource && isRecord(routeSource.assignment) && isRecord(routeSource.assignment.math)) {
      const sourceMath = routeSource.assignment.math;
      const deliveryResult = isRecord(routeSource.delivery?.result) ? routeSource.delivery.result : undefined;
      const deliveredCard =
        deliveryResult && isRecord(deliveryResult.mathRouteCard) ? deliveryResult.mathRouteCard : undefined;
      const sourceRouteCards =
        boundImoContract && canonicalStage === 'formalize'
          ? []
          : Array.isArray(sourceMath.routeCards)
            ? [...sourceMath.routeCards]
            : [];
      if (deliveredCard) {
        const deliveredFingerprint =
          typeof deliveredCard.routeFingerprint === 'string'
            ? normalizeMathRouteFingerprint(deliveredCard.routeFingerprint)
            : '';
        const existingIndex = sourceRouteCards.findIndex(
          (candidate) =>
            isRecord(candidate) &&
            typeof candidate.routeFingerprint === 'string' &&
            normalizeMathRouteFingerprint(candidate.routeFingerprint) === deliveredFingerprint
        );
        if (existingIndex >= 0) sourceRouteCards[existingIndex] = deliveredCard;
        else sourceRouteCards.push(deliveredCard);
      }
      // Preferred dispatch accepts only durable Strategy output here. Route
      // cards authored in the FORMALIZE request would bypass route selection.
      const routeCards = sourceRouteCards.map((candidate) =>
        isRecord(candidate) &&
        typeof candidate.routeFingerprint === 'string' &&
        normalizeMathRouteFingerprint(candidate.routeFingerprint) === normalizedRoute &&
        leadRouteAssessment
          ? { ...candidate, assessment: leadRouteAssessment }
          : candidate
      );
      inherited = {
        ...inherited,
        ...(input.executionPolicy === undefined && sourceMath.executionPolicy
          ? { executionPolicy: sourceMath.executionPolicy }
          : {}),
        ...(routeCards.length ? { routeCards } : {}),
        ...(routeCards.length
          ? {
              routeSelection: {
                statementHash,
                selectionCommit: baseCommit,
                primaryFingerprint: normalizedRoute,
                comparedFingerprints: routeCards
                  .filter(
                    (candidate): candidate is Record<string, unknown> =>
                      isRecord(candidate) && typeof candidate.routeFingerprint === 'string'
                  )
                  .map((candidate) => normalizeMathRouteFingerprint(String(candidate.routeFingerprint))),
                rationale: 'Selected from the durable, independently checked Team route delivery.',
                selectedAt: Math.max(1, Date.parse(routeSource.updatedAt) || Date.now()),
              },
            }
          : {}),
      };
    }
  }

  if (canonicalStage === 'review') {
    const proofSource = matchingReceipts.find((receipt) => {
      const result = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
      return result && isRecord(result.localGateReceipt);
    });
    const proofResult = proofSource && isRecord(proofSource.delivery?.result) ? proofSource.delivery.result : undefined;
    if (proofResult && isRecord(proofResult.localGateReceipt)) {
      inherited = { ...inherited, localGateReceipt: proofResult.localGateReceipt };
    }
  }

  return {
    ...stageScopedInput,
    ...inherited,
    stage: canonicalStage,
    workflowStage,
  };
}

function normalizePreferredMathematicsExecutionPolicyAlias(input: Record<string, unknown>): Record<string, unknown> {
  const hasCanonical = Object.prototype.hasOwnProperty.call(input, 'executionPolicy');
  const hasWire = Object.prototype.hasOwnProperty.call(input, 'execution_policy');
  if (!hasWire) return input;
  const { execution_policy: executionPolicy, ...withoutWireAlias } = input;
  // The preferred path may receive a recovery action merged with a newer
  // canonical policy. The canonical value is authoritative in that case;
  // full assignment callers still use the strict wire normalizer unchanged.
  if (hasCanonical) return withoutWireAlias;
  return { ...withoutWireAlias, executionPolicy };
}

function hydratePreferredImoMathematicsContract(
  input: Record<string, unknown>,
  baseCommit: string | undefined,
  capability: ResearchTeamToolCapability,
  trustedFastCheck?: MathFastCheck
): Record<string, unknown> {
  const boundImoReceipt = readBoundImo2026Receipt(capability);
  const contractPath = boundImoReceipt
    ? path.join(boundImoReceipt.projectRoot, 'docs', 'humanize', 'math-contract.json')
    : path.join(capability.projectRoot, 'docs', 'humanize', 'math-contract.json');
  const receipt = readBoundLeanEvalReceipt(capability);
  if (receipt) {
    const trustedContract = receipt.contract;
    const {
      statementHash: _statementHash,
      problemContract: _problemContract,
      routeCards: _routeCards,
      routeSelection: _routeSelection,
      routeProbeReceipt: _routeProbeReceipt,
      ...leadOwnedInput
    } = input;
    const receiptRouteFingerprint = normalizeMathRouteFingerprint(receipt.routeFingerprint);
    const fastCheck = trustedFastCheck ?? {
      statementHash: trustedContract.statementHash,
      checkedAt: receipt.createdAt,
      method: 'lean-eval-bootstrap-contract-preflight',
      checkedCaseCount: 1,
      outcome: 'inconclusive',
      candidateClaim: 'statement',
      directAttemptRecommended: false,
      summary:
        'The pinned Lean-Eval bootstrap receipt and public contract identity were checked. No bounded mathematical counterexample sweep was run; proof search must treat this FAST_CHECK as inconclusive.',
      evidenceRefs: [`lean-eval-bootstrap:${receipt.receiptId}`],
    };
    const alignment = {
      problemId: trustedContract.problemId,
      statementHash: trustedContract.statementHash,
      leanStatementHash: trustedContract.leanStatementHash,
      contractCommit: baseCommit,
      assessorSessionId: `${capability.teamId}:${capability.slotId}`,
      goalInOwnWords: trustedContract.formalStatement,
      quantifiedObjects: ['All quantified objects in the frozen formal statement.'],
      assumptions: [...trustedContract.assumptions],
      forbiddenChanges: [...trustedContract.knownTraps],
      officialVerificationCommand: trustedContract.officialVerificationCommand,
      verdict: 'exact',
      assumptionDelta: [] as string[],
      quantifierDelta: [] as string[],
      domainDelta: [] as string[],
    };
    return {
      ...leadOwnedInput,
      statementHash: trustedContract.statementHash,
      problemContract: trustedContract,
      routeFingerprint: receiptRouteFingerprint,
      ...(receipt.executionPolicy ? { executionPolicy: receipt.executionPolicy } : {}),
      fastCheck: {
        ...fastCheck,
        statementHash: trustedContract.statementHash,
        checkedAt: receipt.createdAt,
      },
      alignmentCheck: canonicalizePreferredAlignmentCheck({
        ...alignment,
        problemId: trustedContract.problemId,
        statementHash: trustedContract.statementHash,
        leanStatementHash: trustedContract.leanStatementHash,
        contractCommit: baseCommit,
        // The assessor is runtime identity, not solver-authored
        // mathematics. Bind it to the Lead slot when older or
        // compact dispatch payloads omit the field.
        assessorSessionId:
          typeof alignment.assessorSessionId === 'string' && alignment.assessorSessionId.trim()
            ? alignment.assessorSessionId
            : `${capability.teamId}:${capability.slotId}`,
      }),
    };
  }
  if (!fs.existsSync(contractPath)) return input;

  let parsed: unknown;
  try {
    parsed = JSON.parse(fs.readFileSync(contractPath, 'utf8')) as unknown;
  } catch (error) {
    throw new Error(`Bound IMO mathematics contract is unreadable: ${String(error)}`);
  }
  if (!isRecord(parsed) || parsed.schema !== 'deepscientist.imo2026.math-contract.v1') {
    throw new Error('Bound IMO mathematics contract has an unsupported schema');
  }
  if (!isRecord(parsed.problemContract) || !isRecord(parsed.alignmentTemplate)) {
    throw new Error('Bound IMO mathematics contract requires problemContract and alignmentTemplate');
  }
  const statementHash =
    typeof parsed.problemContract.statementHash === 'string'
      ? parsed.problemContract.statementHash.trim().toLowerCase()
      : '';
  if (!statementHash) throw new Error('Bound IMO mathematics contract requires problemContract.statementHash');
  if (parsed.fastCheckTemplate !== undefined && !isRecord(parsed.fastCheckTemplate)) {
    throw new Error('Bound IMO mathematics contract fastCheckTemplate must be an object');
  }
  const contractFastCheck = isRecord(parsed.fastCheckTemplate) ? parsed.fastCheckTemplate : undefined;
  const {
    statementHash: _statementHash,
    problemContract: _problemContract,
    fastCheck: _fastCheck,
    alignmentCheck: _alignmentCheck,
    routeCards: _routeCards,
    routeSelection: _routeSelection,
    routeProbeReceipt: _routeProbeReceipt,
    ...leadOwnedInput
  } = input;
  return {
    ...leadOwnedInput,
    statementHash,
    problemContract: parsed.problemContract,
    ...(trustedFastCheck || contractFastCheck
      ? {
          fastCheck: {
            ...(trustedFastCheck ?? contractFastCheck),
            statementHash,
            checkedAt: normalizePreferredMathCheckedAt((trustedFastCheck ?? contractFastCheck)?.checkedAt),
          },
        }
      : {}),
    alignmentCheck: {
      ...parsed.alignmentTemplate,
      contractCommit: baseCommit,
      assessorSessionId: `${capability.teamId}:${capability.slotId}`,
    },
  };
}

/** Keep natural-language Lead labels from leaking into the typed alignment contract. */
function canonicalizePreferredAlignmentCheck(input: Record<string, unknown>): Record<string, unknown> {
  const verdict = String(input.verdict ?? '')
    .trim()
    .toLowerCase();
  const canonicalVerdict =
    verdict === 'equivalent' || verdict === 'exact_match' || verdict === 'matches' || verdict === 'aligned'
      ? 'exact'
      : input.verdict;
  return { ...input, verdict: canonicalVerdict };
}

function normalizePreferredMathCheckedAt(value: unknown): number {
  if (typeof value === 'number' && Number.isFinite(value) && value > 0) return value;
  if (typeof value === 'string') {
    const parsed = Date.parse(value);
    if (Number.isFinite(parsed) && parsed > 0) return parsed;
  }
  return Date.now();
}

function firstTaskLine(task: string): string {
  const line = task
    .split(/\r?\n/u)
    .map((value) => value.trim())
    .find(Boolean);
  if (!line) throw new Error('dispatch task must not be empty');
  return line.length <= 120 ? line : `${line.slice(0, 117)}...`;
}

function normalizeIntegrationBatch(
  values: readonly ResearchTeamIntegrationItemInput[] | undefined,
  capability: ResearchTeamToolCapability,
  projectGit?: ResearchTeamProjectGitDriver,
  readAssignmentForBatch?: ResearchTeamAssignmentReader,
  validateAssignmentForBatch?: ResearchTeamAssignmentValidator,
  validateResultForBatch?: ResearchTeamResultValidator
): NormalizedIntegrationBatch {
  if (!values?.length) throw new Error('integrate requires a non-empty deliveries list');
  if (values.length > capability.agentLimit) throw new Error('integrate deliveries exceed the Team Agent limit');
  const assignments = new Set<string>();
  const branches = new Set<string>();
  const targets = new Set<string>();
  const normalized = values.map((item) => {
    const target = requireWorker(capability, item.targetSlotId);
    const targetSlotId = target.slotId;
    const itemResult = resolveIntegrationResult(
      item,
      capability,
      target,
      projectGit,
      readAssignmentForBatch,
      validateAssignmentForBatch,
      validateResultForBatch
    );
    const branch = itemResult.git.branch;
    if (
      targets.has(targetSlotId) ||
      assignments.has(itemResult.assignmentId) ||
      (branch !== undefined && branches.has(branch))
    ) {
      throw new Error('integrate deliveries must use unique Worker targets, assignments, and branches');
    }
    targets.add(targetSlotId);
    assignments.add(itemResult.assignmentId);
    if (branch !== undefined) branches.add(branch);
    return Object.freeze({ targetSlotId, result: itemResult });
  });
  validateMathematicsIntegrationWave(normalized, capability);
  return Object.freeze(normalized);
}

function resolveIntegrationResult(
  item: ResearchTeamIntegrationItemInput,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  projectGit: ResearchTeamProjectGitDriver | undefined,
  readAssignmentForBatch?: ResearchTeamAssignmentReader,
  validateAssignmentForBatch?: ResearchTeamAssignmentValidator,
  validateResultForBatch?: ResearchTeamResultValidator
): ResearchTeamResult {
  const readAssignment =
    readAssignmentForBatch ?? memoizeResearchTeamAssignmentReader(projectGit?.readResearchTeamAssignment);
  const validateAssignmentOnce =
    validateAssignmentForBatch ?? memoizeResearchTeamAssignmentValidator(validateAssignment);
  const validateResultOnce =
    validateResultForBatch ??
    memoizeResearchTeamResultValidator((value, resultCapability, resultTarget) =>
      validateResult(value, resultCapability, resultTarget, readAssignment, validateAssignmentOnce)
    );
  const choices = [item.result !== undefined, item.deliveryId !== undefined, item.assignmentId !== undefined].filter(
    Boolean
  ).length;
  if (choices !== 1) {
    throw new Error('integrate delivery must provide exactly one of result, deliveryId, or assignmentId');
  }
  if (item.result !== undefined) {
    const hydrated = hydrateMathematicsWorkerResult(
      normalizeResearchTeamWireRecord(item.result, 'deliveries.result'),
      capability,
      target,
      readAssignment,
      validateAssignmentOnce,
      projectGit?.resolveCommit
    );
    const result = validateResultOnce(hydrated, capability, target);
    const durableReceipt = readAssignment?.({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: target.slotId,
      assignmentId: result.assignmentId,
    });
    if (durableReceipt?.delivery && !isDeepStrictEqual(durableReceipt.delivery.result, result)) {
      throw new Error(
        'integrate result conflicts with the durable Worker delivery; use deliveryId or assignmentId as the authority'
      );
    }
    return result;
  }
  if (!readAssignment) {
    throw new Error('integrate delivery references require durable Research Team assignment receipts');
  }
  const prefix = `${capability.teamId}:${target.slotId}:`;
  const assignmentId = item.deliveryId
    ? (() => {
        const deliveryId = String(item.deliveryId).trim();
        if (!deliveryId.startsWith(prefix) || deliveryId.length === prefix.length) {
          throw new Error('integrate deliveryId does not match the Team and Worker slot');
        }
        return stableId(deliveryId.slice(prefix.length), 'delivery assignment_id');
      })()
    : stableId(String(item.assignmentId), 'assignment_id');
  const receipt = readAssignment({
    workspace: capability.projectRoot,
    teamId: capability.teamId,
    slotId: target.slotId,
    assignmentId,
  });
  if (!receipt) throw new Error('integrate delivery receipt is missing');
  if (
    receipt.teamId !== capability.teamId ||
    receipt.slotId !== target.slotId ||
    receipt.assignmentId !== assignmentId
  ) {
    throw new Error('integrate assignment receipt identity does not match the Team, Worker, and assignment');
  }
  if (!receipt.delivery) throw new Error('integrate assignment receipt has no persisted Worker delivery');
  const expectedDeliveryId = createProjectGitResearchTeamDeliveryId(capability.teamId, target.slotId, assignmentId);
  if (
    receipt.delivery.deliveryId !== expectedDeliveryId ||
    (item.deliveryId && receipt.delivery.deliveryId !== item.deliveryId.trim())
  ) {
    throw new Error('integrate deliveryId does not match the persisted Worker delivery');
  }
  if (!isRecord(receipt.delivery.result)) {
    throw new Error('integrate delivery receipt contains a malformed Worker result');
  }
  const hydrated = hydrateMathematicsWorkerResult(
    receipt.delivery.result,
    capability,
    target,
    readAssignment,
    validateAssignmentOnce
  );
  const result = validateResultOnce(hydrated, capability, target);
  if (result.assignmentId !== assignmentId) {
    throw new Error('integrate delivery receipt result does not match its assignment identity');
  }
  return result;
}

function memoizeResearchTeamAssignmentReader(
  readAssignment: ResearchTeamAssignmentReader | undefined
): ResearchTeamAssignmentReader | undefined {
  if (!readAssignment) return undefined;
  const receipts = new Map<string, ProjectGitResearchTeamAssignmentReceipt | undefined>();
  return (request) => {
    const key = `${request.workspace}\0${request.teamId}\0${request.slotId}\0${request.assignmentId}`;
    if (receipts.has(key)) return receipts.get(key);
    const receipt = readAssignment(request);
    receipts.set(key, receipt);
    return receipt;
  };
}

function memoizeResearchTeamAssignmentListReader(
  listAssignments: ResearchTeamAssignmentListReader | undefined
): ResearchTeamAssignmentListReader | undefined {
  if (!listAssignments) return undefined;
  const receipts = new Map<string, readonly ProjectGitResearchTeamAssignmentReceipt[]>();
  return (request) => {
    const key = `${request.workspace}\0${request.teamId}\0${request.states?.join('\0') ?? ''}`;
    if (receipts.has(key)) return receipts.get(key)!;
    const value = listAssignments(request);
    receipts.set(key, value);
    return value;
  };
}

function memoizeResearchTeamAssignmentValidator(
  validate: ResearchTeamAssignmentValidator,
  readPortfolio: ResearchTeamPortfolioReader = memoizeResearchTeamPortfolioReader(readCanonicalMathematicsPortfolio)
): ResearchTeamAssignmentValidator {
  const assignments = new WeakMap<object, Readonly<{ context: string; assignment: ResearchTeamAssignment }>>();
  return (value, capability, target) => {
    if (!isRecord(value)) return validate(value, capability, target);
    const context = `${capability.workflowId}\0${target.slotId}`;
    const cached = assignments.get(value);
    if (cached?.context === context) return cached.assignment;
    const assignment = validate(value, capability, target, readPortfolio);
    const cachedAssignment = { context, assignment };
    assignments.set(value, cachedAssignment);
    assignments.set(assignment, cachedAssignment);
    return assignment;
  };
}

function memoizeResearchTeamResultValidator(validate: ResearchTeamResultValidator): ResearchTeamResultValidator {
  const results = new WeakMap<object, Readonly<{ context: string; result: ResearchTeamResult }>>();
  return (value, capability, target) => {
    const context = `${capability.workflowId}\0${target.slotId}`;
    const cached = results.get(value);
    if (cached?.context === context) return cached.result;
    const result = validate(value, capability, target);
    const cachedResult = { context, result };
    results.set(value, cachedResult);
    results.set(result, cachedResult);
    return result;
  };
}

function memoizeResearchTeamPortfolioReader(readPortfolio: ResearchTeamPortfolioReader): ResearchTeamPortfolioReader {
  const portfolios = new Map<string, MathematicsPortfolio | undefined>();
  return (capability) => {
    const key = capability.projectRoot;
    if (portfolios.has(key)) return portfolios.get(key);
    const portfolio = readPortfolio(capability);
    portfolios.set(key, portfolio);
    return portfolio;
  };
}

/**
 * Resolve the route's model labels against the model statically bound to the
 * target Core slot. Core does not expose per-turn model switching, so this is
 * deliberately an observation and receipt step rather than a selection API.
 * An unavailable observation leaves dispatch usable while making the missing
 * runtime fact explicit in the durable execution policy.
 */
async function bindMathematicsExecutionModel(
  assignment: ResearchTeamAssignment,
  target: ResearchTeamRosterMember,
  teamId: string,
  client: ResearchCoreTeamClient,
  signal?: AbortSignal
): Promise<ResearchTeamAssignment> {
  const policy = assignment.math?.executionPolicy;
  if (!policy) return assignment;

  let observedModel: string | undefined;
  let observationError: string | undefined;
  if (client.readAgentModel) {
    try {
      const observation = await client.readAgentModel(teamId, target.slotId, signal);
      observedModel = observation?.model?.trim() || undefined;
    } catch (error) {
      observationError = error instanceof Error ? error.message : String(error);
    }
  } else {
    observationError = 'The Core client does not expose the statically bound Worker model.';
  }
  if (observedModel && observedModel.length > 128) {
    observationError = 'Core returned a model identifier longer than the assignment contract permits';
    observedModel = undefined;
  }

  // Core binds one model to a slot for the lifetime of the session. Once that
  // binding is observed, keep only the executable model in the policy. Leaving
  // conceptual route labels (for example an algebra specialist) in the
  // cursor makes the proof loop record retries that it cannot actually run.
  const requested = policy.modelPriority[0];
  const executablePolicy = observedModel
    ? Object.freeze({ ...policy, modelPriority: Object.freeze([observedModel]) })
    : policy;
  const modelReceipt = observedModel
    ? observedModel === requested
      ? Object.freeze({
          status: 'selected' as const,
          ...(requested ? { requested } : {}),
          selected: observedModel,
          reason: 'The statically bound Core Worker model matches the route priority.',
        })
      : Object.freeze({
          status: 'fallback' as const,
          ...(requested ? { requested } : {}),
          selected: observedModel,
          reason: policy.modelPriority.includes(observedModel)
            ? 'Core binds a lower-priority route model and cannot switch from the requested model.'
            : 'Core binds one static Worker model outside the route priority; using that observed model.',
        })
    : Object.freeze({
        status: 'unavailable' as const,
        ...(requested ? { requested } : {}),
        reason: observationError
          ? `The Core Worker model could not be observed: ${observationError.slice(0, 400)}`
          : 'The Core client does not expose the statically bound Worker model.',
      });
  const nextPolicy = normalizeMathExecutionPolicy({ ...executablePolicy, modelReceipt });
  return Object.freeze({
    ...assignment,
    math: Object.freeze({ ...assignment.math, executionPolicy: nextPolicy }),
  });
}

function validateMathematicsIntegrationWave(
  items: readonly IntegrationRequest[],
  capability: ResearchTeamToolCapability
): void {
  if (capability.profileId !== 'mathematics-research-team' || !items.length) return;
  const concrete: NonNullable<ResearchTeamResult['assignmentBinding']>[] = [];
  const stages = new Set<NonNullable<ResearchTeamResult['assignmentBinding']>['stage']>();
  const routes: (string | undefined)[] = [];
  const statements = new Set<string>();
  const commits = new Set<string>();
  const artifactPaths: string[] = [];
  for (const item of items) {
    const binding = item.result.assignmentBinding;
    if (!binding) throw new Error('Mathematics integration requires assignmentBinding on every Worker result');
    concrete.push(binding);
    stages.add(binding.stage);
    routes.push(binding.routeFingerprint);
    statements.add(binding.statementHash);
    commits.add(binding.baseCommit);
    artifactPaths.push(...item.result.artifactPaths);
  }
  if (stages.has(undefined) || stages.size !== 1) {
    throw new Error('Mathematics integration batch must contain one proof stage');
  }
  const [stage] = [...stages];
  if (statements.size !== 1 || commits.size !== 1) {
    throw new Error('Mathematics integration batch must share one statement hash and base commit');
  }
  // Integration must accept every wave that dispatch admits.  A narrower
  // limit here strands valid deliveries after the Lead has already paid for
  // them and creates a false "retry" path.
  validateMathematicsWaveLimits({
    stage,
    count: items.length,
    reasoningConcurrency: capability.reasoningConcurrency,
    routes,
    artifactPaths,
    requireDistinctRoutes: false,
    phase: 'integration',
  });
  if (stage === 'formalize' && items.length > 1) {
    const missingCompletionReceipt = items.some((item) => {
      const result = item.result;
      if (result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt) return false;
      // Direct declaration-cluster results may omit a Worker receipt because
      // whole-problem acceptance belongs to the external evaluator. Require a
      // real branch delta before treating such a result as completed.
      return !(
        result.math?.routeDisposition === 'advance' &&
        result.math.openGoalCountBefore > 0 &&
        result.math.openGoalCountAfter === 0 &&
        Boolean(result.git.headCommit) &&
        result.git.headCommit !== result.git.baseCommit
      );
    });
    if (missingCompletionReceipt) {
      throw new Error('Parallel FORMALIZE integration requires a kernel receipt or a new-commit solver completion');
    }
    const nodeIds = new Set<string>();
    for (const binding of concrete) {
      if (!binding.activePlanNodeId) {
        throw new Error('Parallel FORMALIZE integration requires distinct active plan nodes');
      }
      nodeIds.add(binding.activePlanNodeId);
    }
    if (nodeIds.size !== concrete.length) {
      throw new Error('Parallel FORMALIZE integration requires distinct active plan nodes');
    }
  }
}

function normalizeStatusTargets(
  values: readonly string[] | undefined,
  capability: ResearchTeamToolCapability
): readonly string[] {
  if (!values?.length) {
    return Object.freeze(
      capability.roster.filter((member) => member.roleKind === 'worker').map((member) => member.slotId)
    );
  }
  const normalized = [...new Set(values.map((value) => requireWorker(capability, value).slotId))];
  return Object.freeze(normalized);
}

function validateAssignment(
  value: Record<string, unknown> | ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  readPortfolio: ResearchTeamPortfolioReader = readCanonicalMathematicsPortfolio
): ResearchTeamAssignment {
  if (!isRecord(value) || value.schema !== RESEARCH_TEAM_ASSIGNMENT_SCHEMA) {
    throw new Error(`assignment must use ${RESEARCH_TEAM_ASSIGNMENT_SCHEMA}`);
  }
  if (!isRecord(value.git) || !path.isAbsolute(String(value.git.projectRoot ?? ''))) {
    throw new Error('assignment git.projectRoot must be absolute');
  }
  const assignment = createResearchTeamAssignment(value as unknown as CreateResearchTeamAssignmentInput);
  if (
    assignment.workflowId !== capability.workflowId ||
    assignment.laneId !== target.laneId ||
    path.resolve(assignment.git.projectRoot) !== path.resolve(capability.projectRoot)
  ) {
    throw new Error('assignment identity does not match the target Worker capability');
  }
  if (assignment.roleKind && !['xalpha', 'generic'].includes(assignment.roleKind)) {
    throw new Error('assignment roleKind must be xalpha or generic');
  }
  if (assignment.roleInstructions && assignment.roleInstructions.length > 4000) {
    throw new Error('assignment roleInstructions must be at most 4000 characters');
  }
  if (assignment.git.branch || assignment.git.worktreePath || assignment.git.headCommit) {
    throw new Error('dispatch assignment Git delivery fields must be empty before worktree preparation');
  }
  validateMathematicsAssignment(assignment, capability, target, readPortfolio);
  return assignment;
}

function enrichMathematicsAssignmentRuntimeState(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  slotId: string,
  readAssignment: ResearchTeamAssignmentReader | undefined,
  listAssignments: ResearchTeamAssignmentListReader | undefined
): ResearchTeamAssignment {
  let math = assignment.math;
  // Recover only episode-level scheduler state after a Lead restart.
  const durableReceipt =
    math && readAssignment
      ? readAssignment({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId,
          assignmentId: assignment.assignmentId,
        })
      : undefined;
  let durableProgress = durableReceipt?.mathProgress;
  const proposesCandidateRoute = Boolean(
    math && ['diversify', 'replan'].includes(math.stage) && math.routeProposalMode === 'candidate'
  );
  const needsAssignmentHistory = Boolean(
    math &&
    listAssignments &&
    (proposesCandidateRoute ||
      (assignment.executionMode === 'advisory' &&
        ['diversify', 'replan'].includes(math.stage) &&
        math.routeProposalMode !== 'candidate') ||
      math.stage === 'formalize' ||
      Boolean(math.sessionContinuation))
  );
  const assignmentHistory = needsAssignmentHistory
    ? listAssignments?.({ workspace: capability.projectRoot, teamId: capability.teamId })
    : undefined;
  const exploresRoutes = proposesCandidateRoute;
  const currentRouteCard = exploresRoutes
    ? math?.routeCards?.find((card) => card.routeFingerprint === math.routeFingerprint)
    : undefined;
  const currentRouteStructure = currentRouteCard
    ? mathRouteStructureSignatureFromNormalized(currentRouteCard)
    : undefined;
  let exactDuplicateFound = false;
  let structuralDuplicateFound = false;
  const historicalRouteFingerprints = new Set<string>();
  const historicalRouteStructures = new Set<string>();
  let latestDurableProgress: MathDurableProgressCheckpoint | undefined;
  if (assignmentHistory) {
    for (const receipt of assignmentHistory) {
      if (receipt.assignmentId === assignment.assignmentId) continue;
      // A prepared receipt is only a write-ahead reservation and may be left
      // behind by a dispatch that never reached Core. A superseded receipt is
      // terminal history. Neither represents a route that was actually
      // attempted, so neither may block a later constructive replan.
      if (!['accepted', 'integrated'].includes(receipt.state)) continue;
      const rawAssignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
      const rawMath = rawAssignment && isRecord(rawAssignment.math) ? rawAssignment.math : undefined;
      const rawGit = rawAssignment && isRecord(rawAssignment.git) ? rawAssignment.git : undefined;
      // Route history is scoped to the immutable theorem statement and Git
      // base. A receipt from another problem or rebased workspace must not
      // make a valid route look like a replay.
      if (math && (rawMath?.statementHash !== math.statementHash || rawGit?.baseCommit !== assignment.git.baseCommit)) {
        continue;
      }
      if (!durableProgress && math && receipt.mathProgress) {
        const progress = receipt.mathProgress;
        if (
          progress.statementHash === math.statementHash &&
          progress.routeFingerprint === math.routeFingerprint &&
          (!latestDurableProgress || progress.updatedAt > latestDurableProgress.updatedAt)
        ) {
          latestDurableProgress = progress;
        }
      }
      if (!math || !exploresRoutes) continue;
      const raw = rawMath;
      if (!raw || typeof raw.routeFingerprint !== 'string') continue;
      const rawRouteFingerprint = normalizeMathRouteFingerprint(raw.routeFingerprint);
      const durableRouteAttempt = Boolean(
        raw.statementHash === math.statementHash &&
        ['accepted', 'integrated'].includes(receipt.state) &&
        receipt.delivery
      );
      if (durableRouteAttempt) historicalRouteFingerprints.add(rawRouteFingerprint);
      if (rawRouteFingerprint === math.routeFingerprint) {
        exactDuplicateFound = true;
      }
      const rawCard = Array.isArray(raw.routeCards)
        ? raw.routeCards.find(
            (candidate) =>
              isRecord(candidate) &&
              typeof candidate.routeFingerprint === 'string' &&
              normalizeMathRouteFingerprint(candidate.routeFingerprint) === rawRouteFingerprint
          )
        : undefined;
      let structureSignature: string | undefined;
      if (rawCard) {
        try {
          const card = normalizeMathRouteCard(rawCard as never);
          structureSignature = mathRouteStructureSignatureFromNormalized(card);
        } catch {
          // Legacy receipts without a valid route card retain fingerprint-only protection.
        }
      }
      // A route card can be persisted only with the Worker delivery result in
      // older receipts. Keep structural duplicate protection active across
      // that representation as well; otherwise a fresh route label can evade
      // the candidate-route guard merely by omitting routeCards from the
      // durable assignment payload.
      if (!structureSignature) {
        const delivered = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
        const deliveredCard = delivered && isRecord(delivered.mathRouteCard) ? delivered.mathRouteCard : undefined;
        if (deliveredCard) {
          try {
            structureSignature = mathRouteStructureSignatureFromNormalized(
              normalizeMathRouteCard(deliveredCard as never)
            );
          } catch {
            // Invalid legacy delivery cards cannot establish structural identity.
          }
        }
      }
      if (durableRouteAttempt && structureSignature) historicalRouteStructures.add(structureSignature);
      structuralDuplicateFound ||= Boolean(currentRouteStructure && structureSignature === currentRouteStructure);
    }
    if (!durableProgress) durableProgress = latestDurableProgress;
  }
  if (assignmentHistory) {
    assertNoConcurrentDuplicateMathematicsResearch(assignment, assignmentHistory, capability);
    if (mathematicsRouteTombstoned(assignment, assignmentHistory)) {
      throw new Error(
        'Mathematics route is tombstoned by a durable semantic refutation; select a structurally new route before dispatching it again'
      );
    }
  }
  if (
    math &&
    assignmentHistory &&
    math.stage === 'formalize' &&
    (!math.researchContract || isBoundImoMathematicsWorkspace(capability))
  ) {
    const researchContract = reconstructIntegratedMathematicsResearchContract(assignment, assignmentHistory);
    if (researchContract) math = Object.freeze({ ...math, researchContract });
  }
  // Proof-mainline direct formalization deliberately has no advisory
  // prerequisite.  The Lead owns the initial route plan and the Lean Worker
  // is the first executable step; requiring a separate advisory delivery here
  // recreates the idle handoff that the mainline protocol is designed to remove.
  if (math && assignmentHistory && math.stage === 'formalize') {
    math = materializeLatestExpandedMathematicsPlan(math, assignmentHistory);
  }
  if (math && proposesCandidateRoute && (historicalRouteFingerprints.size || historicalRouteStructures.size)) {
    const existingLedger = math.failureLedger;
    const triedRoutes = Object.freeze([
      ...new Set([...(existingLedger?.triedRoutes ?? []), ...historicalRouteFingerprints, math.routeFingerprint]),
    ]);
    const triedRouteStructureSignatures = Object.freeze([
      ...new Set([...(existingLedger?.triedRouteStructureSignatures ?? []), ...historicalRouteStructures]),
    ]);
    math = Object.freeze({
      ...math,
      failureLedger: Object.freeze({
        ...(existingLedger ?? {
          stage: math.stage,
          statementHash: math.statementHash,
          activeRoute: math.routeFingerprint,
          nextSingleObjective: assignment.objective,
          failureCategory: 'stalled' as const,
          doNotRepeatRefs: assignment.doNotRepeat,
        }),
        triedRoutes,
        ...(triedRouteStructureSignatures.length ? { triedRouteStructureSignatures } : {}),
      }),
    });
  }
  if (math && durableProgress) {
    // A Lead restart may reconstruct the assignment from an older compact
    // payload while the WAL already contains the latest solver cursor. Restore
    // it only for the exact statement/route and never override a newer policy
    // explicitly supplied by the Lead.
    if (
      math.executionPolicy === undefined &&
      durableProgress.executionPolicy &&
      durableProgress.statementHash === math.statementHash &&
      normalizeMathRouteFingerprint(durableProgress.routeFingerprint) ===
        normalizeMathRouteFingerprint(math.routeFingerprint)
    ) {
      math = Object.freeze({ ...math, executionPolicy: durableProgress.executionPolicy });
    }
    if (
      math.previousConsecutiveStalls !== undefined &&
      durableProgress.outcome === 'stalled' &&
      math.previousConsecutiveStalls < durableProgress.consecutiveStalls
    ) {
      throw new Error('Mathematics assignment previousConsecutiveStalls cannot regress durable stalled progress');
    }
    if (math.previousConsecutiveStalls === undefined) {
      math = Object.freeze({ ...math, previousConsecutiveStalls: durableProgress.consecutiveStalls });
    }
    if (
      durableProgress.outcome === 'stalled' &&
      durableProgress.progressFingerprint &&
      math.stage === 'formalize' &&
      math.routeFingerprint === durableProgress.routeFingerprint
    ) {
      const existingLedger = math.failureLedger;
      const failureLedger = existingLedger
        ? Object.freeze({
            ...existingLedger,
            progressFingerprint: existingLedger.progressFingerprint ?? durableProgress.progressFingerprint,
          })
        : Object.freeze({
            stage: math.stage,
            statementHash: math.statementHash,
            activeRoute: math.routeFingerprint,
            triedRoutes: Object.freeze([math.routeFingerprint]),
            progressFingerprint: durableProgress.progressFingerprint,
            nextSingleObjective: 'Switch to a structurally distinct proof route.',
            failureCategory: 'stalled' as const,
            doNotRepeatRefs: Object.freeze([]),
          });
      math = Object.freeze({ ...math, failureLedger });
    }
    if (
      math.failureLedger &&
      durableProgress.proofStateFingerprint &&
      durableProgress.activePlanNodeId === math.activePlanNodeId &&
      math.failureLedger.proofStateFingerprint !== durableProgress.proofStateFingerprint
    ) {
      math = Object.freeze({
        ...math,
        failureLedger: Object.freeze({
          ...math.failureLedger,
          proofStateFingerprint: durableProgress.proofStateFingerprint,
        }),
      });
    }
  }
  if (math !== assignment.math) assignment = Object.freeze({ ...assignment, math });
  const continuation = assignment.math?.sessionContinuation;
  if (continuation) {
    const source = assignmentHistory?.find((receipt) => receipt.assignmentId === continuation.sourceAssignmentId);
    if (!source) {
      throw new Error(
        `Mathematics session continuation source assignment ${continuation.sourceAssignmentId} is not durable`
      );
    }
    if (!['accepted', 'integrated'].includes(source.state)) {
      throw new Error('Mathematics session continuation source assignment is not resumable');
    }
    const sourceAssignment = isRecord(source.assignment) ? source.assignment : undefined;
    const sourceMath = sourceAssignment && isRecord(sourceAssignment.math) ? sourceAssignment.math : undefined;
    if (!sourceMath || sourceMath.statementHash !== assignment.math?.statementHash) {
      throw new Error('Mathematics session continuation must preserve the source statement');
    }
    const sourceRoute = normalizeMathRouteFingerprint(String(sourceMath.routeFingerprint || ''));
    const sameRoute = sourceRoute === assignment.math?.routeFingerprint;
    if (continuation.purpose === 'alternate_route' ? sameRoute : !sameRoute) {
      throw new Error(
        continuation.purpose === 'alternate_route'
          ? 'Mathematics alternate-route continuation must change route fingerprint'
          : 'Mathematics candidate repair, Critic, and bottleneck helper must preserve the source route fingerprint'
      );
    }
    const sameSlot = source.slotId === slotId;
    if (continuation.mode === 'reuse_source_slot' && !sameSlot) {
      throw new Error('Mathematics session continuation must target the source Worker slot');
    }
    if (continuation.mode === 'fresh_slot' && sameSlot) {
      throw new Error('Mathematics fresh session continuation must target a different Worker slot');
    }
  }
  if (exactDuplicateFound) {
    throw new Error('Mathematics route was already attempted in durable assignment history');
  }
  if (currentRouteStructure && structuralDuplicateFound) {
    throw new Error('Mathematics route is structurally duplicated in durable assignment history');
  }
  return assignment;
}

function reconstructIntegratedMathematicsResearchContract(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[]
): MathResearchProblemContract | undefined {
  const math = assignment.math;
  const problemId = math?.problemContract?.problemId;
  if (!math || !problemId) return undefined;
  const findings = integratedMathematicsResearchFindings(assignment, assignmentHistory);
  if (!findings.length) return undefined;
  let contract = normalizeMathResearchProblemContract({
    problemId,
    objective: assignment.objective,
    context: 'Runtime-reconstructed context from integrated advisory findings for this exact theorem statement.',
  });
  for (const { finding, sourceTeamId, sourceAssignmentId } of findings) {
    contract = applyMathResearchFinding(
      contract,
      finding,
      readTrustedMathResearchEvidence(finding, { teamId: sourceTeamId, assignmentId: sourceAssignmentId })
    );
  }
  // Normalize once more at the dispatch boundary. This is deliberately not a
  // recovery path: an invalid reconstructed contract must never reach Core.
  return normalizeMathResearchProblemContract({
    ...contract,
    objective: assignment.objective,
    nextAction: assignment.objective,
  });
}

function isBoundImoMathematicsWorkspace(capability: ResearchTeamToolCapability): boolean {
  if (capability.profileId !== 'mathematics-research-team') return false;
  if (fs.existsSync(path.join(capability.projectRoot, 'active-problem.json'))) {
    if (readBoundImo2026Receipt(capability)) return true;
    return Boolean(readBoundLeanEvalReceipt(capability));
  }
  return fs.existsSync(boundMathematicsContractPath(capability));
}

function readBoundImo2026Receipt(capability: ResearchTeamToolCapability) {
  if (capability.profileId !== 'mathematics-research-team') return undefined;
  const receiptPath = path.join(capability.projectRoot, 'active-problem.json');
  if (!fs.existsSync(receiptPath)) return undefined;
  let raw: unknown;
  try {
    raw = JSON.parse(fs.readFileSync(receiptPath, 'utf8')) as unknown;
  } catch (error) {
    throw new Error(`IMO2026 bootstrap receipt is invalid: ${error instanceof Error ? error.message : String(error)}`);
  }
  if (!isRecord(raw) || raw.schema !== IMO2026_BOOTSTRAP_SCHEMA) return undefined;
  try {
    const receipt = readImo2026BootstrapReceipt(receiptPath);
    verifyImo2026BootstrapReceipt(receipt);
    if (path.resolve(receipt.workspaceRoot) !== path.resolve(capability.projectRoot)) {
      throw new Error('IMO2026 receipt workspaceRoot does not match the Research Team project root');
    }
    return receipt;
  } catch (error) {
    throw new Error(`IMO2026 bootstrap receipt is invalid: ${error instanceof Error ? error.message : String(error)}`);
  }
}

function boundMathematicsContractPath(capability: ResearchTeamToolCapability): string {
  const receiptPath = path.join(capability.projectRoot, 'active-problem.json');
  if (fs.existsSync(receiptPath)) {
    try {
      const raw = JSON.parse(fs.readFileSync(receiptPath, 'utf8')) as unknown;
      if (isRecord(raw) && typeof raw.projectRoot === 'string' && path.isAbsolute(raw.projectRoot)) {
        return path.join(raw.projectRoot, 'docs', 'humanize', 'math-contract.json');
      }
    } catch {
      // The receipt reader reports the authoritative error when this is a bound workspace.
    }
  }
  return path.join(capability.projectRoot, 'docs', 'humanize', 'math-contract.json');
}

function readBoundLeanEvalReceipt(capability: ResearchTeamToolCapability) {
  if (capability.profileId !== 'mathematics-research-team') return undefined;
  const receiptPath = path.join(capability.projectRoot, 'active-problem.json');
  if (!fs.existsSync(receiptPath)) return undefined;
  try {
    const raw = JSON.parse(fs.readFileSync(receiptPath, 'utf8')) as unknown;
    if (isRecord(raw) && raw.schema === IMO2026_BOOTSTRAP_SCHEMA) return undefined;
  } catch (error) {
    throw new Error(
      `Lean-Eval bootstrap receipt is invalid: ${error instanceof Error ? error.message : String(error)}`
    );
  }
  try {
    const receipt = readLeanEvalBootstrapReceipt(receiptPath);
    if (path.resolve(receipt.workspaceRoot) !== path.resolve(capability.projectRoot)) {
      throw new Error('Lean-Eval receipt workspaceRoot does not match the Research Team project root');
    }
    return receipt;
  } catch (error) {
    throw new Error(
      `Lean-Eval bootstrap receipt is invalid: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

function assertBoundImoFormalizationProvenance(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[],
  capability: ResearchTeamToolCapability
): void {
  const math = assignment.math;
  if (
    !math ||
    math.stage !== 'formalize' ||
    math.directAttempt === true ||
    !isBoundImoMathematicsWorkspace(capability)
  ) {
    return;
  }
  const card = math.routeCards?.find((candidate) => candidate.routeFingerprint === math.routeFingerprint);
  const expectedAssessorSessionId = `${capability.teamId}:${capability.slotId}:route-selection`;
  if (!card?.assessment || card.assessment.assessorSessionId !== expectedAssessorSessionId) {
    throw new Error('Bound IMO routed FORMALIZE requires the current Lead assessment on its selected route');
  }
  const { assessment: _assessment, ...selectedRouteProposal } = card;
  const hasDurableProposal = assignmentHistory.some((receipt) => {
    if (
      receipt.state !== 'integrated' ||
      !isRecord(receipt.assignment) ||
      receipt.assignment.laneId !== 'strategy-exploration' ||
      !isRecord(receipt.assignment.math) ||
      !isRecord(receipt.assignment.git) ||
      receipt.assignment.math.statementHash !== math.statementHash ||
      receipt.assignment.git.baseCommit !== assignment.git.baseCommit
    ) {
      return false;
    }
    const result = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
    if (!result || !isRecord(result.mathRouteCard)) return false;
    try {
      const delivered = normalizeMathRouteCard(result.mathRouteCard as MathRouteCard);
      const { assessment: _deliveredAssessment, ...deliveredProposal } = delivered;
      return (
        delivered.routeFingerprint === math.routeFingerprint &&
        isDeepStrictEqual(deliveredProposal, selectedRouteProposal)
      );
    } catch {
      return false;
    }
  });
  if (!hasDurableProposal) {
    throw new Error('Bound IMO routed FORMALIZE route must match an integrated Strategy Worker delivery');
  }
}

function assertRuntimeRouteProbeReceipt(
  receipt: MathRouteProbeReceipt,
  assignment: ResearchTeamAssignment,
  card: MathRouteCard
): void {
  const math = assignment.math;
  const binding = receipt.runtimeBinding;
  const secret = readMathematicsReceiptSecret();
  const hasVerifiedDependencyEvidence =
    receipt.outcome === 'kernel_verified' &&
    (receipt.verificationMode === undefined || receipt.verificationMode === 'verified_dependencies');
  if (
    !math?.problemContract ||
    !hasVerifiedDependencyEvidence ||
    !binding ||
    !secret ||
    !verifyMathRouteProbeReceipt(receipt, secret)
  ) {
    throw new Error('Mathematics FORMALIZE requires an authentic route preflight with verified dependencies');
  }
  const expectedStructureHash = crypto
    .createHash('sha256')
    .update(mathRouteStructureSignatureFromNormalized(card))
    .digest('hex');
  const expectedSourceHash = crypto.createHash('sha256').update(math.problemContract.formalStatement).digest('hex');
  const expectedHarnessHash = crypto
    .createHash('sha256')
    .update(createMathematicsRoutePreflightHarness(math.problemContract, card))
    .digest('hex');
  const expectedRouteBrief = {
    routeFingerprint: card.routeFingerprint,
    structuralCommitment: card.structuralCommitment,
    decisiveLemma: card.decisiveLemma,
    decisiveTest: card.decisiveTest,
    falsificationSignal: card.falsificationSignal,
    expectedInformationGain: card.expectedInformationGain,
    estimatedCost: card.estimatedCost,
    formalizationRisk: card.formalizationRisk,
  };
  if (
    receipt.statementHash !== math.statementHash ||
    receipt.routeFingerprint !== math.routeFingerprint ||
    receipt.proposerSessionId !== card.proposerSessionId ||
    receipt.assessorSessionId !== card.assessment?.assessorSessionId ||
    !isDeepStrictEqual(receipt.routeBrief, expectedRouteBrief) ||
    binding.targetCommit !== assignment.git.baseCommit ||
    binding.routeStructureHash !== expectedStructureHash ||
    binding.sourceHash !== expectedSourceHash ||
    binding.harnessHash !== expectedHarnessHash
  ) {
    throw new Error('Mathematics runtime route preflight receipt is stale or bound to a different route environment');
  }
}

async function attachBoundImoRoutePreflight(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  preflight: ResearchTeamToolContext['preflightMathematicsRoute'],
  signal?: AbortSignal
): Promise<ResearchTeamAssignment> {
  const math = assignment.math;
  if (
    !math ||
    math.stage !== 'formalize' ||
    math.directAttempt === true ||
    !isBoundImoMathematicsWorkspace(capability)
  ) {
    return assignment;
  }
  const card = math.routeCards?.find((candidate) => candidate.routeFingerprint === math.routeFingerprint);
  if (!math.problemContract || !math.routeSelection || !card) {
    throw new ResearchTeamOrchestrationError(
      'mathematics_route_preflight_missing',
      'Bound IMO FORMALIZE requires a selected route card before runtime route preflight.',
      false
    );
  }
  if (math.routeProbeReceipt) {
    try {
      assertRuntimeRouteProbeReceipt(math.routeProbeReceipt, assignment, card);
      const currentEnvironment = mathematicsRoutePreflightEnvironmentFingerprint(capability.projectRoot);
      if (math.routeProbeReceipt.runtimeBinding?.environmentFingerprint === currentEnvironment) return assignment;
    } catch {
      // A stale receipt must go through a fresh verifier-owned preflight below.
    }
  }
  if (!preflight) {
    throw new ResearchTeamOrchestrationError(
      'mathematics_route_preflight_unavailable',
      'Bound IMO FORMALIZE cannot start because the verifier-owned route preflight is unavailable.',
      true
    );
  }
  const result = await preflight({
    workspaceRoot: capability.projectRoot,
    targetCommit: assignment.git.baseCommit,
    problemContract: math.problemContract,
    routeCard: card,
    ...(signal ? { signal } : {}),
  });
  if (result.status !== 'passed' || !result.receipt) {
    throw new ResearchTeamOrchestrationError(
      result.status === 'unavailable'
        ? 'mathematics_route_preflight_unavailable'
        : 'mathematics_route_preflight_failed',
      `Bound IMO route preflight ${result.status}: ${result.diagnostics || 'the route did not compose'}`,
      result.status === 'unavailable'
    );
  }
  assertRuntimeRouteProbeReceipt(result.receipt, assignment, card);
  return Object.freeze({
    ...assignment,
    math: Object.freeze({ ...math, routeProbeReceipt: result.receipt }),
  });
}

function isActionableDirectFormalizationBrief(contract: MathResearchProblemContract | undefined): boolean {
  if (!contract?.nextAction) return false;
  const usefulStateChanges = (contract.probeSummary ?? []).reduce((total, summary) => total + summary.usefulChanges, 0);
  return usefulStateChanges > 0 && (Boolean(contract.solutionSketchRef) || Boolean(contract.establishedClaims?.length));
}

function isActionableIntegratedFormalizationFinding(
  entry: IntegratedMathematicsResearchFinding,
  assignment: ResearchTeamAssignment
): boolean {
  const math = assignment.math;
  return Boolean(
    math &&
    entry.sourceStage &&
    entry.sourceBaseCommit === assignment.git.baseCommit &&
    entry.sourceRouteFingerprint === normalizeMathRouteFingerprint(math.routeFingerprint) &&
    entry.sourceRouteDisposition === 'advance' &&
    entry.finding.mainlineImpact === 'mainline_advanced' &&
    entry.finding.mechanism &&
    (entry.finding.solutionSketchRef || entry.finding.establishedClaims.length > 0) &&
    entry.finding.evidenceRefs.length > 0 &&
    entry.finding.nextAction
  );
}

function materializeLatestExpandedMathematicsPlan(
  math: NonNullable<ResearchTeamAssignment['math']>,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[]
): NonNullable<ResearchTeamAssignment['math']> {
  const activeRoute = math.routeCards?.find((card) => card.routeFingerprint === math.routeFingerprint);
  if (!activeRoute) return math;
  let latestPlan: ReturnType<typeof normalizeMathPlanSnapshot> | undefined;
  for (let index = assignmentHistory.length - 1; index >= 0; index -= 1) {
    const receipt = assignmentHistory[index];
    if (receipt.state !== 'accepted' && receipt.state !== 'integrated') continue;
    const result = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
    const progress = result && isRecord(result.math) ? result.math : undefined;
    if (
      progress?.statementHash !== math.statementHash ||
      progress.routeFingerprint !== math.routeFingerprint ||
      !isRecord(progress.planAfter)
    ) {
      continue;
    }
    try {
      latestPlan = normalizeMathPlanSnapshot(progress.planAfter as never);
      break;
    } catch {
      // Invalid historical projections never replace the frozen route card.
    }
  }
  if (!latestPlan) return math;
  const coverageByNodeId = new Map(activeRoute.premiseBundle.coverage.map((entry) => [entry.planNodeId, entry]));
  const premiseBundle = Object.freeze({
    ...activeRoute.premiseBundle,
    coverage: Object.freeze(
      latestPlan.planNodes.map(
        (node) =>
          coverageByNodeId.get(node.id) ??
          Object.freeze({ planNodeId: node.id, premiseDeclarationNames: Object.freeze([]), selfContained: true })
      )
    ),
  });
  const expandedRoute = normalizeMathRouteCard({
    ...activeRoute,
    premiseBundle,
    planNodes: latestPlan.planNodes,
    rootNodeId: latestPlan.rootNodeId,
    ...(latestPlan.bottleneckNodeId ? { bottleneckNodeId: latestPlan.bottleneckNodeId } : {}),
    openFrontierNodeIds: latestPlan.openFrontierNodeIds,
    ...(latestPlan.planNodes.length > 7 && !activeRoute.extendedPlanReason
      ? { extendedPlanReason: 'Runtime-validated hierarchical expansion of a retained route milestone.' }
      : {}),
  });
  const { activePlanNodeId: _staleActivePlanNodeId, ...mathWithoutStaleActiveNode } = math;
  return Object.freeze({
    ...mathWithoutStaleActiveNode,
    routeCards: Object.freeze(
      math.routeCards?.map((card) => (card.routeFingerprint === math.routeFingerprint ? expandedRoute : card)) ?? [
        expandedRoute,
      ]
    ),
    ...(latestPlan.bottleneckNodeId ? { activePlanNodeId: latestPlan.bottleneckNodeId } : {}),
  });
}

type IntegratedMathematicsResearchFinding = Readonly<{
  sourceTeamId: string;
  sourceAssignmentId: string;
  sourceObjective: string;
  sourceStage: string;
  sourceBaseCommit: string;
  sourceRouteFingerprint: string;
  sourceRouteDisposition?: string;
  deliveredAt: number;
  deliveredAtIso: string;
  finding: MathResearchFinding;
}>;

function integratedMathematicsResearchFindings(
  assignment: ResearchTeamAssignment,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[]
): readonly IntegratedMathematicsResearchFinding[] {
  const math = assignment.math;
  if (!math) return Object.freeze([]);
  const findings: IntegratedMathematicsResearchFinding[] = [];
  for (const receipt of assignmentHistory) {
    if (receipt.state !== 'integrated' || receipt.assignmentId === assignment.assignmentId) continue;
    const sourceAssignment = isRecord(receipt.assignment) ? receipt.assignment : undefined;
    const sourceMath = sourceAssignment && isRecord(sourceAssignment.math) ? sourceAssignment.math : undefined;
    const sourceGit = sourceAssignment && isRecord(sourceAssignment.git) ? sourceAssignment.git : undefined;
    const deliveryResult = isRecord(receipt.delivery?.result) ? receipt.delivery.result : undefined;
    const deliveryMath = deliveryResult && isRecord(deliveryResult.math) ? deliveryResult.math : undefined;
    if (
      sourceAssignment?.executionMode !== 'advisory' ||
      !['diversify', 'replan'].includes(String(sourceMath?.stage)) ||
      sourceMath?.statementHash !== math.statementHash ||
      sourceGit?.baseCommit !== assignment.git.baseCommit ||
      !isRecord(receipt.delivery?.result) ||
      !isRecord(receipt.delivery.result.mathResearchFinding)
    ) {
      continue;
    }
    try {
      const deliveredAtIso = receipt.delivery.deliveredAt || receipt.updatedAt;
      findings.push({
        sourceTeamId: receipt.teamId,
        sourceAssignmentId: receipt.assignmentId,
        sourceObjective:
          typeof sourceAssignment.objective === 'string' ? sourceAssignment.objective.trim() : receipt.assignmentId,
        sourceStage: String(sourceMath.stage),
        sourceBaseCommit: String(sourceGit.baseCommit),
        sourceRouteFingerprint: normalizeMathRouteFingerprint(
          String(deliveryMath?.routeFingerprint ?? sourceMath.routeFingerprint ?? '')
        ),
        ...(typeof deliveryMath?.routeDisposition === 'string'
          ? { sourceRouteDisposition: deliveryMath.routeDisposition }
          : {}),
        deliveredAt: Date.parse(deliveredAtIso) || 0,
        deliveredAtIso,
        finding: normalizeMathResearchFinding(
          receipt.delivery.result.mathResearchFinding as unknown as MathResearchFinding
        ),
      });
    } catch {
      // Durable legacy or corrupt findings must not enter a new Worker assignment.
    }
  }
  return Object.freeze(findings.toSorted((left, right) => left.deliveredAt - right.deliveredAt));
}

const MATHEMATICS_RESEARCH_HANDOFF_SCHEMA = 'deepscientist.math.research-handoff.v1' as const;
const MATHEMATICS_RESEARCH_HANDOFF_MAX_FINDINGS = 4;
const MATHEMATICS_RESEARCH_HANDOFF_MAX_BYTES = 64 * 1024;

function materializeIntegratedMathematicsResearchHandoff(
  assignment: ResearchTeamAssignment,
  listAssignments: ResearchTeamAssignmentListReader | undefined,
  capability: ResearchTeamToolCapability,
  workspace: string
): ResearchTeamAssignment {
  const math = assignment.math;
  const contract = math?.researchContract;
  if (
    capability.profileId !== 'mathematics-research-team' ||
    math?.stage !== 'formalize' ||
    !contract ||
    !listAssignments
  ) {
    return assignment;
  }
  const findings = integratedMathematicsResearchFindings(
    assignment,
    listAssignments({ workspace: capability.projectRoot, teamId: capability.teamId })
  );
  const selected = selectMathematicsResearchHandoffFindings(assignment, findings);
  if (!selected.length) {
    if (contract.solutionSketchRef) {
      copyMathematicsResearchHandoffArtifact(capability.projectRoot, workspace, contract.solutionSketchRef);
    }
    return assignment;
  }

  const materializedArtifactRefs = selected.flatMap((entry) => {
    const artifactRef = entry.finding.solutionSketchRef;
    if (!artifactRef) return [];
    copyMathematicsResearchHandoffArtifact(capability.projectRoot, workspace, artifactRef);
    const compileReceiptRef = artifactRef.endsWith('.lean') ? `${artifactRef}.compile.json` : undefined;
    if (
      compileReceiptRef &&
      fs.existsSync(resolveMathematicsResearchHandoffArtifact(capability.projectRoot, compileReceiptRef))
    ) {
      copyMathematicsResearchHandoffArtifact(capability.projectRoot, workspace, compileReceiptRef);
      return [artifactRef, compileReceiptRef];
    }
    return [artifactRef];
  });

  const handoffKey = crypto
    .createHash('sha256')
    .update(`${math.statementHash}\0${assignment.assignmentId}`, 'utf8')
    .digest('hex')
    .slice(0, 24);
  const solutionSketchRef = path.posix.join(
    '.deepscientist',
    'science-artifacts',
    'math-research-handoffs',
    `${handoffKey}.json`
  );
  const handoffPath = path.join(workspace, ...solutionSketchRef.split('/'));
  fs.mkdirSync(path.dirname(handoffPath), { recursive: true });
  fs.writeFileSync(
    handoffPath,
    `${JSON.stringify(
      {
        schema: MATHEMATICS_RESEARCH_HANDOFF_SCHEMA,
        statementHash: math.statementHash,
        formalizationAssignmentId: assignment.assignmentId,
        formalizationObjective: assignment.objective,
        materializedArtifactRefs,
        findings: selected.map((entry) => ({
          sourceAssignmentId: entry.sourceAssignmentId,
          sourceObjective: entry.sourceObjective,
          deliveredAt: entry.deliveredAtIso,
          finding: entry.finding,
        })),
      },
      null,
      2
    )}\n`,
    { encoding: 'utf8', mode: 0o600 }
  );
  return Object.freeze({
    ...assignment,
    math: Object.freeze({
      ...math,
      researchContract: normalizeMathResearchProblemContract({ ...contract, solutionSketchRef }),
    }),
  });
}

function selectMathematicsResearchHandoffFindings(
  assignment: ResearchTeamAssignment,
  findings: readonly IntegratedMathematicsResearchFinding[]
): readonly IntegratedMathematicsResearchFinding[] {
  const query = [assignment.objective, assignment.math?.routeFingerprint ?? '', assignment.math?.activePlanNodeId ?? '']
    .join(' ')
    .toLowerCase();
  const queryTokens = mathematicsResearchHandoffTokens(query);
  const ranked = findings
    .map((entry) => {
      const body =
        `${entry.sourceAssignmentId} ${entry.sourceObjective} ${JSON.stringify(entry.finding)}`.toLowerCase();
      const overlap = [...mathematicsResearchHandoffTokens(body)].filter((token) => queryTokens.has(token)).length;
      const explicitlyNamed = query.includes(entry.sourceAssignmentId.toLowerCase());
      return { entry, score: overlap + (explicitlyNamed ? 1_000 : 0) };
    })
    .toSorted((left, right) => right.score - left.score || right.entry.deliveredAt - left.entry.deliveredAt);
  const selected: IntegratedMathematicsResearchFinding[] = [];
  let usedBytes = 0;
  for (const { entry } of ranked) {
    const bytes = Buffer.byteLength(JSON.stringify(entry), 'utf8');
    if (selected.length && usedBytes + bytes > MATHEMATICS_RESEARCH_HANDOFF_MAX_BYTES) continue;
    selected.push(entry);
    usedBytes += bytes;
    if (selected.length >= MATHEMATICS_RESEARCH_HANDOFF_MAX_FINDINGS) break;
  }
  return Object.freeze(selected.toSorted((left, right) => left.deliveredAt - right.deliveredAt));
}

function mathematicsResearchHandoffTokens(value: string): ReadonlySet<string> {
  return new Set(
    value
      .split(/[^a-z0-9_]+/gu)
      .map((token) => token.trim())
      .filter((token) => token.length >= 3)
  );
}

function resolveMathematicsResearchHandoffArtifact(root: string, artifactRef: string): string {
  const normalized = artifactRef.replace(/\\/gu, '/');
  if (
    path.isAbsolute(artifactRef) ||
    normalized !== path.posix.normalize(normalized) ||
    !normalized.startsWith(`${MATHEMATICS_RESEARCH_HANDOFF_ROOT}/`)
  ) {
    throw new Error(`Mathematics research handoff must stay under ${MATHEMATICS_RESEARCH_HANDOFF_ROOT}/`);
  }
  const rootPath = path.resolve(root);
  const artifactPath = path.resolve(rootPath, ...normalized.split('/'));
  const relative = path.relative(rootPath, artifactPath);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error('Mathematics research handoff escapes the project workspace');
  }
  return artifactPath;
}

function assertMathematicsResearchHandoffArtifact(root: string, artifactRef: string): string {
  const artifactPath = resolveMathematicsResearchHandoffArtifact(root, artifactRef);
  let metadata: fs.Stats;
  try {
    metadata = fs.statSync(artifactPath);
  } catch {
    throw new Error('Mathematics research handoff artifact does not exist');
  }
  if (!metadata.isFile() || metadata.size === 0 || metadata.size > 256 * 1024) {
    throw new Error('Mathematics research handoff artifact must be a non-empty file of at most 256 KB');
  }
  const rootPath = fs.realpathSync(path.resolve(root));
  const realArtifactPath = fs.realpathSync(artifactPath);
  const relative = path.relative(rootPath, realArtifactPath);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error('Mathematics research handoff artifact resolves outside the project workspace');
  }
  return realArtifactPath;
}

function copyMathematicsResearchHandoffArtifact(
  projectRoot: string,
  destinationRoot: string,
  artifactRef: string
): void {
  const sourcePath = assertMathematicsResearchHandoffArtifact(projectRoot, artifactRef);
  const destinationPath = resolveMathematicsResearchHandoffArtifact(destinationRoot, artifactRef);
  fs.mkdirSync(path.dirname(destinationPath), { recursive: true });
  fs.copyFileSync(sourcePath, destinationPath);
}

function assertRequiredMathematicsExactLeanHandoff(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined,
  teamId?: string
): void {
  if (!assignment) return;
  const finding = result.mathResearchFinding;
  if (
    finding &&
    teamId &&
    ['counterexample', 'example', 'computation'].includes(finding.kind) &&
    readTrustedMathResearchEvidence(finding, { teamId, assignmentId: assignment.assignmentId }).length
  )
    return;
  const findingText = [finding?.summary, ...(finding?.establishedClaims ?? []), ...(finding?.evidenceRefs ?? [])]
    .filter(Boolean)
    .join(' ');
  const hasAffirmativeLeanValidationClaim = (text: string): boolean => {
    const validationClaim =
      /(?:\b(?:lean|compiler|kernel)[- ]checked\b|\b(?:compile[sd]?|compiled) (?:locally|successfully|without|in lean)\b|\b(?:lemma|helper|proof|source) (?:compile[sd]?|was compiled)\b)/giu;
    for (const validationMatch of text.matchAll(validationClaim)) {
      if (validationMatch.index === undefined) continue;
      // Strategy findings often document the boundary explicitly (for example,
      // "plausible but not kernel-checked"). A local negation immediately before
      // the matched phrase means the finding is reporting an unverified route,
      // rather than claiming compiler or kernel authority.
      const before = text.slice(Math.max(0, validationMatch.index - 96), validationMatch.index);
      const locallyNegated =
        /(?:\b(?:not|never|no)\b(?:\s+(?:yet|be|been|currently|actually))*|\b(?:cannot|can't|couldn't|wasn't|isn't|hasn't|haven't|hadn't)\b(?:\s+(?:be|been))?|\b(?:did|does|do|could|would|was|is|has|have|had)\s+not\b(?:\s+(?:be|been))?|\b(?:failed|fails|unable)\s+to\b)\s*$/iu.test(
          before
        );
      if (!locallyNegated) return true;
    }
    return false;
  };
  const claimsSuccessfulLeanCheck =
    assignment.laneId === 'strategy-exploration' &&
    assignment.executionMode === 'advisory' &&
    Boolean(
      (finding?.evidenceRefs.some((ref) =>
        /^(?:lean|compile):.*(?:exit[-_ ]?0|success|pass|check|compil)/iu.test(ref)
      ) ??
        false) ||
      hasAffirmativeLeanValidationClaim(findingText)
    );
  // Signed sampled observations are permitted above; free-form text cannot confer proof authority.
  if (claimsSuccessfulLeanCheck) {
    throw new Error(
      'Mathematics Strategy findings cannot claim successful Lean/compiler validation; return the symbolic finding and dispatch a Lean Engineer for executable work.'
    );
  }
}

/**
 * A FORMALIZE delivery is an episode boundary, not a compiler transcript.
 * In particular, an unchanged first error after one tactic attempt must not
 * wake the Lead and consume a new assignment.  Reject it at the Worker edge
 * so the same Core-managed conversation can continue repairing its candidate.
 * The same gate applies to routed FORMALIZE nodes. A node boundary is useful
 * only when it carries a receipt, frontier change, or an explicit structural
 * failure; otherwise it merely creates another identical Lead wake-up.
 */
function assertMeaningfulDirectMathematicsFormalizeEpisode(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment | undefined,
  preparedGit?: ProjectGitResearchTeamPreparedGit
): void {
  if (!assignment || assignment.laneId !== 'lean-engineering' || assignment.math?.stage !== 'formalize') {
    return;
  }

  const math = result.math;
  if (!math) return;

  const hasKernelReceipt = Boolean(result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt);
  const reducedGoals = math.openGoalCountAfter < math.openGoalCountBefore;
  const goalFingerprintChanged =
    math.openGoalFingerprintBefore !== undefined &&
    math.openGoalFingerprintAfter !== undefined &&
    math.openGoalFingerprintBefore !== math.openGoalFingerprintAfter;
  const firstErrorResolved = math.firstLeanErrorBefore !== undefined && math.firstLeanErrorAfter === undefined;
  const firstErrorMoved =
    math.firstLeanErrorOffsetBefore !== undefined &&
    math.firstLeanErrorOffsetAfter !== undefined &&
    math.firstLeanErrorOffsetAfter > math.firstLeanErrorOffsetBefore;
  const runtimeCheckedRouteRefutation =
    math.routeDisposition === 'reject' &&
    math.evidenceDelta.some((item) => item.kind === 'route_refutation') &&
    math.evidenceDelta.some((item) => item.kind === 'counterexample_probe');
  const planFrontierChanged = Boolean(
    math.planExpansion ||
    (math.planBefore &&
      math.planAfter &&
      (math.verifiedPlanNodeIdsAdded?.length ||
        math.planBefore.openFrontierNodeIds.join('\u0000') !== math.planAfter.openFrontierNodeIds.join('\u0000')))
  );
  // The adapter rebuilds planAfter from trusted receipts. A Worker-supplied
  // planExpansion without one is only prose and must stay inside the current
  // solver episode instead of waking the Lead for another dispatch.
  const trustedPlanFrontierChanged = hasKernelReceipt && planFrontierChanged;
  const structuralFailure =
    ['actual_proof_failure', 'missing_hole', 'declaration_rejected', 'termination_failed'].includes(
      math.failureCategory ?? ''
    ) ||
    ['declaration_rejected', 'termination_failed', 'timeout_or_resource'].includes(
      math.wholeProofProbe?.failureKind ??
        (math.firstLeanErrorAfter ? classifyMathLeanFailure(math.firstLeanErrorAfter) : '')
    );
  const exactInfrastructureFailure =
    math.infraStatus !== 'ready' &&
    result.disposition === 'blocked' &&
    (result.mathCheckpoint?.ledger.failureCategory === 'infra' ||
      result.mathCheckpoint?.ledger.failureCategory === 'toolchain');
  const sourceDeclarationChanged = Boolean(math.sourceProgress?.changedDeclarationNames.length);
  // A prepared Worker commit is itself durable evidence when the adapter could
  // not rehydrate sourceProgress (for example while a proof-session patch is
  // being rebound). Verify that an authorized Lean artifact changed between
  // the assignment base and the committed head before accepting it as an
  // episode boundary; this avoids forcing the Worker to manufacture a failed
  // compiler probe just to wake the Lead.
  const committedAuthorizedSourceChanged = hasCommittedAuthorizedMathSourceDelta(result, assignment, preparedGit);
  const structuredBlockedFormalRoute =
    result.disposition === 'blocked' &&
    math.routeDisposition === 'reject' &&
    math.infraStatus === 'ready' &&
    math.openGoalCountBefore > 0 &&
    math.openGoalCountAfter > 0 &&
    Boolean(math.openGoalAfter?.trim()) &&
    Boolean(math.nextSingleObjective?.trim());

  const meaningfulEpisode =
    hasKernelReceipt ||
    reducedGoals ||
    goalFingerprintChanged ||
    firstErrorResolved ||
    firstErrorMoved ||
    runtimeCheckedRouteRefutation ||
    exactInfrastructureFailure ||
    trustedPlanFrontierChanged ||
    structuralFailure ||
    sourceDeclarationChanged ||
    committedAuthorizedSourceChanged ||
    structuredBlockedFormalRoute;

  if (meaningfulEpisode) {
    return;
  }

  throw new Error(
    `${assignment.math.directAttempt === true ? 'Direct' : 'Routed'} Mathematics FORMALIZE delivery has no meaningful episode progress. Continue the same solver episode and deliver again only after a kernel/helper receipt, a runtime-verified declaration source change, a strictly smaller goal, a changed proof-state fingerprint, a later or resolved first Lean error, a kernel-backed plan-frontier change, a runtime-checked counterexample, or an exact infrastructure failure; a missing library declaration, unsupported route-refutation claim, or one unchanged compiler error is not an assignment boundary.`
  );
}

function hasCommittedAuthorizedMathSourceDelta(
  result: ResearchTeamResult,
  assignment: ResearchTeamAssignment,
  preparedGit?: ProjectGitResearchTeamPreparedGit
): boolean {
  const git = result.git;
  const baseCommit = preparedGit?.progressBaseCommit?.trim() || assignment.git.baseCommit.trim();
  const headCommit = typeof git.headCommit === 'string' ? git.headCommit.trim() : '';
  if (!baseCommit || !headCommit || baseCommit === headCommit) return false;
  const worktreePath =
    preparedGit?.worktreePath && path.isAbsolute(preparedGit.worktreePath)
      ? preparedGit.worktreePath
      : typeof git.worktreePath === 'string' && path.isAbsolute(git.worktreePath)
        ? git.worktreePath
        : typeof assignment.git.worktreePath === 'string' && path.isAbsolute(assignment.git.worktreePath)
          ? assignment.git.worktreePath
          : '';
  if (!worktreePath) return false;
  const solverProjectRoot = preparedGit?.solverProjectRoot || worktreePath;
  const solverPrefix = path.relative(worktreePath, solverProjectRoot);
  if (solverPrefix.startsWith('..') || path.isAbsolute(solverPrefix)) return false;
  const declaredArtifacts = assignmentArtifactPaths(assignment, result.artifactPaths);
  let artifacts = declaredArtifacts;
  if (!artifacts.length) {
    try {
      const bootstrap = readLeanEvalBootstrapReceipt(path.join(worktreePath, 'active-problem.json'));
      artifacts = bootstrap.solverOwnedFiles;
    } catch {
      // Non-Lean assignments have no bootstrap receipt to expand their artifact list.
    }
  }
  for (const artifact of artifacts) {
    const relativePath = projectRelativeLeanArtifactPath(solverProjectRoot, artifact);
    if (!relativePath) continue;
    const repositoryRelativePath = path.join(solverPrefix, relativePath).replaceAll(path.sep, '/');
    try {
      const changed = execFileSync(
        'git',
        ['diff', '--name-only', `${baseCommit}..${headCommit}`, '--', repositoryRelativePath],
        {
          cwd: worktreePath,
          encoding: 'utf8',
          stdio: ['ignore', 'pipe', 'ignore'],
          maxBuffer: 64 * 1024,
        }
      ).trim();
      if (changed.split('\n').some((entry) => entry.trim() === repositoryRelativePath)) return true;
    } catch {
      // Missing Git objects or a removed worktree are not progress evidence.
    }
  }
  return false;
}

function validateResult(
  value: Record<string, unknown> | ResearchTeamResult,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  readAssignment?: ResearchTeamAssignmentReader,
  validateAssignmentForResult: ResearchTeamAssignmentValidator = validateAssignment
): ResearchTeamResult {
  if (!isRecord(value) || value.schema !== RESEARCH_TEAM_RESULT_SCHEMA) {
    throw new Error(`result must use ${RESEARCH_TEAM_RESULT_SCHEMA}`);
  }
  validateResultEnums(value);
  if (!isRecord(value.git) || !path.isAbsolute(String(value.git.projectRoot ?? ''))) {
    throw new Error('result git.projectRoot must be absolute');
  }
  if (capability.profileId === 'mathematics-research-team' && isRecord(value.mathRouteCard)) {
    const premiseBundle = isRecord(value.mathRouteCard.premiseBundle) ? value.mathRouteCard.premiseBundle : undefined;
    if (!Array.isArray(premiseBundle?.coverage)) {
      throw new Error('Mathematics Strategy Explorer result requires premise coverage for every plan node');
    }
  }
  const resultValue = createResearchTeamResult(value as unknown as CreateResearchTeamResultInput);
  if (
    resultValue.workflowId !== capability.workflowId ||
    resultValue.laneId !== target.laneId ||
    path.resolve(resultValue.git.projectRoot) !== path.resolve(capability.projectRoot)
  ) {
    throw new Error('result identity does not match the Worker capability');
  }
  if (
    resultValue.executionMode !== 'advisory' &&
    !resultValue.git.branch?.startsWith(workerBranchPrefix(capability, target))
  ) {
    throw new Error('result branch does not belong to the delivering Worker');
  }
  validateMathematicsResult(resultValue, capability, target, readAssignment, validateAssignmentForResult);
  return resultValue;
}

function persistResearchTeamAssignment(
  projectGit: ResearchTeamProjectGitDriver,
  capability: ResearchTeamToolCapability,
  assignment: ResearchTeamAssignment,
  target: ResearchTeamRosterMember,
  state: 'prepared' | 'accepted',
  usageBaseline?: ResearchCoreAgentUsage,
  teamRunId?: string,
  preparedGit?: ProjectGitResearchTeamPreparedGit
): ProjectGitResearchTeamAssignmentReceipt | undefined {
  return projectGit.recordResearchTeamAssignment?.({
    workspace: capability.projectRoot,
    teamId: capability.teamId,
    slotId: target.slotId,
    assignmentId: assignment.assignmentId,
    assignment,
    state,
    ...(usageBaseline ? { usageBaseline: usageBaseline as ProjectGitResearchTeamUsageBaseline } : {}),
    ...(teamRunId ? { teamRunId } : {}),
    ...(preparedGit ? { preparedGit } : {}),
  });
}

function assertAssignmentBindingMatches(
  binding: ResearchTeamAssignmentBinding | undefined,
  assignment: ResearchTeamAssignment
): void {
  if (!binding) throw new Error('Research Team result requires assignmentBinding from the dispatched assignment');
  const expected = expectedResearchTeamAssignmentBinding(assignment);
  for (const key of Object.keys(expected) as (keyof ResearchTeamAssignmentBinding)[]) {
    if (
      key === 'workflowStage' &&
      expected.workflowStage === 'candidate' &&
      binding.workflowStage === 'exploration' &&
      (binding.stage === 'diversify' || binding.stage === 'replan')
    ) {
      continue;
    }
    if (binding[key] !== expected[key]) {
      throw new Error(`Research Team assignmentBinding.${key} does not match the dispatched assignment`);
    }
  }
}

function assertIntegratedReceiptMatchesResult(
  receipt: ProjectGitResearchTeamAssignmentReceipt,
  result: ResearchTeamResult
): void {
  const integration = receipt.integration;
  const executionMode = result.executionMode ?? 'artifact';
  if (!integration || integration.executionMode !== executionMode) {
    throw new Error('Research Team integrated receipt execution mode does not match the repeated delivery');
  }
  if (receipt.delivery && !isDeepStrictEqual(receipt.delivery.result, result)) {
    throw new Error('Research Team integrated receipt result does not match the persisted Worker delivery');
  }
  if (
    executionMode === 'artifact' &&
    (integration.branch !== result.git.branch || integration.headCommit !== result.git.headCommit)
  ) {
    throw new Error('Research Team integrated receipt branch or headCommit does not match the repeated delivery');
  }
}

function validateMathematicsAssignment(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  readPortfolio: ResearchTeamPortfolioReader
): void {
  if (capability.profileId !== 'mathematics-research-team') return;
  if (!assignment.math) throw new Error('Mathematics assignment requires math stage and route identity');
  if (assignment.math.routeProposalMode === 'candidate') {
    if (
      !assignment.math.fastCheck ||
      !assignment.math.problemContract ||
      assignment.math.alignmentCheck?.verdict !== 'exact'
    ) {
      throw new Error(
        'Mathematics route candidate requires FAST_CHECK, a frozen formal problemContract, and exact alignment'
      );
    }
  }
  if (['audit', 'select', 'local_gate', 'official_gate', 'done'].includes(assignment.math.stage)) {
    throw new Error(`Mathematics ${assignment.math.stage.toUpperCase()} is Lead-owned and cannot dispatch Workers`);
  }
  const explorationStage = assignment.math.stage === 'diversify' || assignment.math.stage === 'replan';
  if (assignment.math.sessionContinuation?.sourceAssignmentId === assignment.assignmentId) {
    throw new Error('Mathematics session continuation must reference an earlier assignment');
  }
  if (
    ['critic', 'bottleneck_helper'].includes(assignment.math.sessionContinuation?.purpose ?? '') &&
    !explorationStage
  ) {
    throw new Error('Mathematics Critic and bottleneck helper must use an advisory exploration stage');
  }
  if (!assignment.math.fastCheck && !explorationStage) {
    throw new Error('Mathematics Worker dispatch requires a completed FAST_CHECK decision');
  }
  if (
    assignment.math.fastCheck?.candidateClaim === 'negation' &&
    (!assignment.math.problemContract?.formalNegationStatement || !assignment.math.problemContract.leanNegationHash)
  ) {
    throw new Error('Mathematics negation work requires a canonical formal negation and hash');
  }
  const mode = assignment.executionMode ?? 'artifact';
  const artifactLane = target.laneId === 'lean-engineering';
  if ((artifactLane && mode !== 'artifact') || (!artifactLane && mode !== 'advisory')) {
    throw new Error(
      artifactLane
        ? 'Mathematics Lean Engineer assignments must use executionMode=artifact'
        : 'Mathematics strategy and review assignments must use executionMode=advisory'
    );
  }
  if (target.laneId === 'strategy-exploration' && mathematicsAdvisoryRequestsExecutableLeanWork(assignment)) {
    throw new Error(
      'Mathematics advisory Strategy assignments must return a structured mathResearchFinding; move Lean source generation or compiler validation to a Lean Engineer FORMALIZE assignment.'
    );
  }
  if (artifactLane && assignment.math.stage !== 'formalize') {
    throw new Error('Mathematics Lean Engineer artifact work is allowed only in formalize');
  }
  if (artifactLane && mathematicsFormalizationPrejudgesFailure(assignment)) {
    throw new Error(
      'Mathematics Lean Engineer assignments must pursue the original theorem constructively; do not predeclare missing library support, prohibit a complete proof attempt, or make reconnaissance/blocked output the primary deliverable before Worker evidence.'
    );
  }
  if (target.laneId === 'independent-review' && assignment.math.stage !== 'review') {
    throw new Error('Mathematics Independent Reviewer starts only in the review stage');
  }
  if (
    assignment.math.problemContract &&
    assignment.math.problemContract.statementHash !== assignment.math.statementHash
  ) {
    throw new Error('Mathematics problemContract.statementHash must match math.statementHash');
  }
  if (explorationStage && !assignment.math.problemContract && !assignment.math.researchContract) {
    throw new Error('Mathematics exploration assignments require a researchContract or problemContract');
  }
  if (assignment.math.problemContract) {
    const payloads = canonicalMathProblemStatementPayloads(assignment.math.problemContract);
    const expectedStatementHash = crypto.createHash('sha256').update(payloads.informal).digest('hex');
    const expectedLeanStatementHash = crypto.createHash('sha256').update(payloads.lean).digest('hex');
    if (
      assignment.math.problemContract.statementHash !== expectedStatementHash ||
      assignment.math.problemContract.leanStatementHash !== expectedLeanStatementHash
    ) {
      throw new Error(
        'Mathematics problemContract statement hashes must be runtime-derived from the canonical informal and Lean statements.'
      );
    }
  }
  assertMathematicsTeamPlanNodeBounds(assignment.math.routeCards);
  if (assignment.math.failureLedger) {
    if (assignment.math.failureLedger.statementHash !== assignment.math.statementHash) {
      throw new Error('Mathematics failureLedger.statementHash must match math.statementHash');
    }
    if (assignment.math.failureLedger.activeRoute !== assignment.math.routeFingerprint) {
      throw new Error('Mathematics failureLedger.activeRoute must match math.routeFingerprint');
    }
    if (assignment.math.failureLedger.stage !== assignment.math.stage) {
      throw new Error('Mathematics failureLedger.stage must match math.stage');
    }
    if (
      assignment.math.failureLedger.activePlanNodeId &&
      assignment.math.failureLedger.activePlanNodeId !== assignment.math.activePlanNodeId
    ) {
      throw new Error('Mathematics failureLedger.activePlanNodeId must match math.activePlanNodeId');
    }
    if (assignment.math.stage === 'replan') {
      let routeOccurrences = 0;
      for (const route of assignment.math.failureLedger.triedRoutes) {
        if (route === assignment.math.routeFingerprint) routeOccurrences += 1;
      }
      if (routeOccurrences > 1) {
        throw new Error('Mathematics replan cannot reactivate a previously attempted route fingerprint');
      }
      const routeCard = assignment.math.routeCards?.find(
        (card) => card.routeFingerprint === assignment.math?.routeFingerprint
      );
      if (
        routeCard &&
        assignment.math.failureLedger.triedRouteStructureSignatures?.includes(
          mathRouteStructureSignatureFromNormalized(routeCard)
        )
      ) {
        throw new Error('Mathematics replan cannot reactivate a structurally duplicated route');
      }
    }
  }
  if (assignment.math.alignmentCheck && assignment.math.alignmentCheck.contractCommit !== assignment.git.baseCommit) {
    throw new Error('Mathematics alignmentCheck must target the assignment base commit');
  }
  // Bound IMO direct formalization is allowed after the runtime has integrated
  // an actionable advisory handoff.  The handoff check lives in
  // enrichMathematicsAssignmentRuntimeState, which has the durable assignment
  // history; keeping a second FAST_CHECK-only gate here rejected the intended
  // inconclusive-FAST_CHECK -> advisory-route -> direct-proof path.
  if (
    assignment.math.routeSelection &&
    assignment.math.routeSelection.selectionCommit !== assignment.git.baseCommit &&
    !(
      assignment.math.routeSelection.rebasedFromCommit &&
      assignment.math.routeSelection.revalidatedAtCommit === assignment.git.baseCommit
    )
  ) {
    throw new Error(
      'Mathematics routeSelection must target the assignment base commit or carry a re-materialization marker'
    );
  }
  if (assignment.math.routeProbeReceipt) {
    const card = assignment.math.routeCards?.find(
      (candidate) => candidate.routeFingerprint === assignment.math?.routeFingerprint
    );
    if (!card) throw new Error('Mathematics route preflight receipt requires its selected route card');
    assertRuntimeRouteProbeReceipt(assignment.math.routeProbeReceipt, assignment, card);
  }
  if (['formalize', 'review'].includes(assignment.math.stage)) {
    if (!assignment.math.problemContract) {
      throw new Error('Mathematics proof and review assignments require an immutable problemContract');
    }
    if (!assignment.math.alignmentCheck) {
      throw new Error('Mathematics proof and review assignments require an alignmentCheck');
    }
    if (assignment.math.alignmentCheck.verdict !== 'exact') {
      throw new Error('Mathematics non-exact alignment blocks proof-producing stages');
    }
    if (!assignment.math.directAttempt && !assignment.math.routeSelection) {
      throw new Error('Mathematics proof and review assignments require a frozen routeSelection');
    }
    if (
      !assignment.math.directAttempt &&
      assignment.math.routeSelection.primaryFingerprint !== assignment.math.routeFingerprint &&
      assignment.math.routeSelection.reserveFingerprint !== assignment.math.routeFingerprint
    ) {
      throw new Error('Mathematics proof-stage route must be the frozen primary or reserve route');
    }
  }
  if (assignment.math.stage === 'formalize' && !assignment.math.activePlanNodeId) {
    throw new Error('Mathematics FORMALIZE requires one dependency-ready activePlanNodeId');
  }
  if (assignment.math.stage === 'review') {
    if (!assignment.math.localGateReceipt) {
      throw new Error(`Mathematics ${assignment.math.stage.toUpperCase()} requires a frozen LOCAL_GATE receipt`);
    }
    assertLocalGateReceiptMatches(
      assignment.math.localGateReceipt,
      assignment.math.statementHash,
      assignment.math.routeFingerprint,
      assignment.git.baseCommit
    );
  }
  if (assignment.math.applicableLessons) {
    assertMathLessonsApplied(
      assignment.math.routeFingerprint,
      assignment.math.applicableLessons,
      assignment.doNotRepeat,
      assignment.math.routePattern
    );
  }
  const preflight = evaluateMathWorkflowPreflight({
    stage: assignment.math.stage,
    ...(assignment.math.fastCheck ? { fastCheck: assignment.math.fastCheck } : {}),
    ...(assignment.math.problemContract ? { problemContract: assignment.math.problemContract } : {}),
    ...(assignment.math.researchContract ? { researchContract: assignment.math.researchContract } : {}),
    ...(assignment.math.alignmentCheck ? { alignmentCheck: assignment.math.alignmentCheck } : {}),
    ...(assignment.math.directAttempt !== undefined ? { directAttempt: assignment.math.directAttempt } : {}),
    ...(assignment.math.routeSelection ? { routeSelection: assignment.math.routeSelection } : {}),
    ...(assignment.math.activePlanNodeId ? { activePlanNodeId: assignment.math.activePlanNodeId } : {}),
    ...(assignment.math.localGateReceipt ? { localGateReceipt: assignment.math.localGateReceipt } : {}),
  });
  if (!preflight.ok) {
    throw new Error(preflight.issues[0]?.message || 'Mathematics workflow preflight failed');
  }
  assertMathematicsPortfolioBinding(assignment, capability, readPortfolio);
}

/**
 * The Team assignment is a projection of the canonical mathematics portfolio,
 * not a second problem/state database.  Keep compatibility with legacy unit
 * fixtures that have no project mirror yet, but fail closed whenever a mirror
 * exists and disagrees with the immutable assignment.
 */
function assertMathematicsPortfolioBinding(
  assignment: ResearchTeamAssignment,
  capability: ResearchTeamToolCapability,
  readPortfolio: ResearchTeamPortfolioReader = readCanonicalMathematicsPortfolio
): void {
  const portfolio = readPortfolio(capability);
  if (!portfolio) return;
  const math = assignment.math;
  const contract = math?.problemContract;
  if (!contract) return;
  const problem = portfolio.problems.find((candidate) => candidate.id === contract.problemId);
  if (!problem)
    throw new Error(`Mathematics assignment problem ${contract.problemId} is absent from the canonical portfolio.`);
  if (
    problem.statementHash !== contract.statementHash ||
    problem.problemContract?.leanStatementHash !== contract.leanStatementHash ||
    problem.problemContract?.formalStatement !== contract.formalStatement
  ) {
    throw new Error('Mathematics Team assignment does not match the canonical portfolio problem contract.');
  }
  if (problem.fastCheck && !isDeepStrictEqual(problem.fastCheck, math.fastCheck)) {
    throw new Error('Mathematics Team assignment does not match the canonical portfolio FAST_CHECK decision.');
  }
  // Team stages are an execution projection, not a second portfolio state
  // machine. Contract and frozen-commit identity below remain authoritative.
  const frozenCommit = problem.routeSelection?.selectionCommit || problem.alignmentCheck?.contractCommit;
  if (frozenCommit && frozenCommit !== assignment.git.baseCommit) {
    // REVIEW is intentionally dispatched after artifact integration. A merge
    // (or a reverified merge) can advance the canonical commit while the
    // portfolio still records the proof route's original selection commit.
    // The review assignment remains safe because its alignment and LOCAL_GATE
    // receipt are both rebound to the exact reviewed commit before validation.
    if (
      assignment.math?.stage === 'review' &&
      assignment.math.localGateReceipt?.targetCommit === assignment.git.baseCommit
    ) {
      return;
    }
    throw new Error('Mathematics Team assignment baseCommit does not match the canonical portfolio frozen commit.');
  }
}

function readCanonicalMathematicsPortfolio(capability: ResearchTeamToolCapability): MathematicsPortfolio | undefined {
  const projectRoot = canonicalBoundProjectRoot(capability.projectRoot);
  const portfolioPath = assertBoundPortfolioPath(projectRoot);
  if (!fs.existsSync(portfolioPath)) return undefined;
  try {
    const portfolio = readMathematicsPortfolio({ mathematics: JSON.parse(fs.readFileSync(portfolioPath, 'utf8')) });
    if (!portfolio) throw new Error('invalid');
    return portfolio;
  } catch {
    throw new Error(`${MATHEMATICS_PORTFOLIO_PATH} is invalid; repair the canonical portfolio before dispatch.`);
  }
}

/**
 * Portfolio state is security-sensitive canonical state.  Resolve the bound
 * root once, reject symlink traversal for every path component, and require
 * the final real path to remain under that root.  This keeps a symlinked
 * portfolio (or parent directory) from bypassing the Team/project binding.
 */
function canonicalBoundProjectRoot(projectRoot: string): string {
  const resolved = path.resolve(projectRoot);
  const canonical = fs.realpathSync(resolved);
  if (!fs.statSync(canonical).isDirectory()) throw new Error('The bound mathematics project root must be a directory.');
  return canonical;
}

function assertBoundProjectPath(canonicalRoot: string, relativePath: string, label: string): string {
  const lexical = path.join(canonicalRoot, relativePath);
  const relative = path.relative(canonicalRoot, lexical);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must remain inside the bound project root.`);
  }
  let cursor = canonicalRoot;
  for (const segment of relative.split(path.sep).filter(Boolean)) {
    cursor = path.join(cursor, segment);
    try {
      if (fs.lstatSync(cursor).isSymbolicLink()) {
        throw new Error(`${label} must not traverse a symbolic link.`);
      }
    } catch (error) {
      if (error instanceof Error && error.message.includes('must not traverse')) throw error;
      // The portfolio may legitimately not exist yet. Existing components
      // are still checked above; the caller handles the missing final file.
      if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
      break;
    }
  }
  if (!fs.existsSync(lexical)) return lexical;
  const canonicalTarget = fs.realpathSync(lexical);
  const targetRelative = path.relative(canonicalRoot, canonicalTarget);
  if (targetRelative.startsWith('..') || path.isAbsolute(targetRelative)) {
    throw new Error(`${label} must resolve inside the bound project root.`);
  }
  return canonicalTarget;
}

function assertBoundPortfolioPath(canonicalRoot: string): string {
  return assertBoundProjectPath(canonicalRoot, MATHEMATICS_PORTFOLIO_PATH, MATHEMATICS_PORTFOLIO_PATH);
}

function withMathematicsPortfolioLock<T>(canonicalRoot: string, operation: () => T): T {
  const lockPath = assertBoundProjectPath(
    canonicalRoot,
    path.join('.deepscientist', 'mathematics', 'portfolio.lock'),
    'Mathematics portfolio lock'
  );
  fs.mkdirSync(path.dirname(lockPath), { recursive: true });
  const token = crypto.randomUUID();
  const temporaryPath = `${lockPath}.${process.pid}.${token}.tmp`;
  let descriptor: number | undefined;
  let acquired = false;
  try {
    // Write the owner record completely before publishing the lock path. A
    // hard-link is the atomic exclusive publish primitive available on the
    // local filesystems used by both Electron processes; this removes the
    // crash window where an empty lock could otherwise become permanent.
    const metadataDescriptor = fs.openSync(temporaryPath, 'w', 0o600);
    try {
      fs.writeFileSync(
        metadataDescriptor,
        `${JSON.stringify({ ...lockOwnerRecord(), token, createdAt: Date.now() })}\n`,
        'utf8'
      );
      fs.fsyncSync(metadataDescriptor);
    } finally {
      fs.closeSync(metadataDescriptor);
    }
    for (;;) {
      try {
        fs.linkSync(temporaryPath, lockPath);
        acquired = true;
        break;
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'EEXIST') throw error;
        let owner: 'alive' | 'dead' | 'unknown' = 'unknown';
        try {
          const metadata = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as Record<string, unknown>;
          owner =
            typeof metadata.pid === 'number' && Number.isSafeInteger(metadata.pid)
              ? lockOwnerState(metadata)
              : 'unknown';
        } catch {
          // Incomplete metadata (older versions, or a writer from another PID
          // namespace) is only recovered once the lock is clearly stale.
        }
        if (owner === 'alive' || (owner === 'unknown' && lockIsFresh(lockPath))) {
          throw new Error('Another mathematics portfolio writer is active; retry the integration.');
        }
        fs.rmSync(lockPath, { force: true });
      }
    }
    fs.rmSync(temporaryPath, { force: true });
    descriptor = fs.openSync(lockPath, 'r+');
    return operation();
  } finally {
    fs.rmSync(temporaryPath, { force: true });
    if (descriptor !== undefined) {
      fs.closeSync(descriptor);
    }
    if (acquired) {
      try {
        const owner = JSON.parse(fs.readFileSync(lockPath, 'utf8')) as { token?: string };
        if (owner.token === token) fs.rmSync(lockPath, { force: true });
      } catch {
        // Preserve a lock whose ownership cannot be established; a later
        // reconciliation can inspect the PID and recover it safely.
      }
    }
  }
}

function writeMathematicsProjectPortfolio(
  canonicalRoot: string,
  portfolio: MathematicsPortfolio,
  expectedRawHash: string
): void {
  const portfolioPath = assertBoundPortfolioPath(canonicalRoot);
  const currentRawHash = crypto.createHash('sha256').update(fs.readFileSync(portfolioPath, 'utf8')).digest('hex');
  if (currentRawHash !== expectedRawHash) {
    throw new Error('Mathematics portfolio changed concurrently; retry the integration.');
  }
  const temporaryPath = `${portfolioPath}.${process.pid}.${crypto.randomBytes(4).toString('hex')}.tmp`;
  try {
    const descriptor = fs.openSync(temporaryPath, 'w', 0o600);
    try {
      fs.writeFileSync(descriptor, `${JSON.stringify(portfolio, null, 2)}\n`, 'utf8');
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    fs.renameSync(temporaryPath, portfolioPath);
  } finally {
    fs.rmSync(temporaryPath, { force: true });
  }
}

function updateMathematicsResearchContract(request: {
  workspace: string;
  contract: MathResearchProblemContract;
  finding: MathResearchFinding;
  trustedEvidence?: readonly MathResearchEvidence[];
}): { updated: boolean; researchContract?: MathResearchProblemContract } {
  return mutateMathematicsResearchContract({
    workspace: request.workspace,
    contract: request.contract,
    update: (baseContract) => applyMathResearchFinding(baseContract, request.finding, request.trustedEvidence),
  });
}

function mutateMathematicsResearchContract(request: {
  workspace: string;
  contract: MathResearchProblemContract;
  update: (baseContract: MathResearchProblemContract) => MathResearchProblemContract;
}): { updated: boolean; researchContract?: MathResearchProblemContract } {
  const canonicalRoot = canonicalBoundProjectRoot(request.workspace);
  const portfolioPath = assertBoundPortfolioPath(canonicalRoot);
  if (!fs.existsSync(portfolioPath)) return { updated: false };
  return withMathematicsPortfolioLock(canonicalRoot, () => {
    const contents = fs.readFileSync(portfolioPath, 'utf8');
    const rawHash = crypto.createHash('sha256').update(contents).digest('hex');
    const snapshot = readMathematicsPortfolio({ mathematics: JSON.parse(contents) });
    if (!snapshot) return { updated: false };
    if (['done', 'verified', 'refuted'].includes(snapshot.stage) || ['verified', 'refuted'].includes(snapshot.status)) {
      throw new Error('Mathematics research findings cannot mutate a terminal portfolio.');
    }
    const problem = snapshot.problems.find((candidate) => candidate.id === request.contract.problemId);
    if (!problem) return { updated: false };
    const baseContract = problem.researchContract ?? request.contract;
    if (baseContract.problemId !== request.contract.problemId) {
      throw new Error('Mathematics research finding does not match the canonical portfolio problem.');
    }
    const researchContract = request.update(baseContract);
    if (problem.researchContract && isDeepStrictEqual(problem.researchContract, researchContract)) {
      return { updated: false, researchContract };
    }
    const candidate: MathematicsPortfolio = {
      ...snapshot,
      problems: snapshot.problems.map((entry) =>
        entry.id === problem.id ? { ...entry, researchContract, updatedAt: Date.now() } : entry
      ),
      updatedAt: Date.now(),
    };
    const validation = validateMathematicsPortfolio(candidate);
    if (!validation.ok) {
      throw new Error(`Mathematics research finding update failed validation: ${validation.errors.join(' ')}`);
    }
    writeMathematicsProjectPortfolio(canonicalRoot, candidate, rawHash);
    return { updated: true, researchContract };
  });
}

function assertLocalGateReceiptMatches(
  value: MathLocalGateReceipt,
  statementHash: string,
  routeFingerprint: string,
  targetCommit: string
): void {
  const receipt = normalizeMathLocalGateReceipt(value);
  const normalizedRouteFingerprint = normalizeMathRouteFingerprint(routeFingerprint);
  if (
    receipt.statementHash !== statementHash ||
    receipt.routeFingerprint !== normalizedRouteFingerprint ||
    receipt.targetCommit !== targetCommit
  ) {
    throw new Error('Mathematics LOCAL_GATE receipt does not match the frozen statement, route, and commit');
  }
}

/**
 * When the immutable formal statement names its theorem, bind the kernel
 * receipt to that declaration instead of accepting an arbitrary theorem from
 * the same proof file.  Official manifests remain the authority for
 * statement bodies that are represented as a bare proposition.
 */
function assertReceiptTheoremMatchesContract(
  receipt: MathLocalGateReceipt,
  contract: MathProblemContract | undefined,
  expectedClaim?: 'statement' | 'negation'
): void {
  if (!contract || typeof contract !== 'object' || typeof contract.formalStatement !== 'string') return;
  const claim = receipt.claim === 'negation' ? 'negation' : 'statement';
  if (expectedClaim && claim !== expectedClaim) {
    throw new Error(`Mathematics kernel receipt claim ${claim} does not match FAST_CHECK claim ${expectedClaim}`);
  }
  const formalStatement = claim === 'negation' ? contract.formalNegationStatement : contract.formalStatement;
  const leanStatementHash = claim === 'negation' ? contract.leanNegationHash : contract.leanStatementHash;
  if (!formalStatement || !leanStatementHash) {
    throw new Error('Mathematics negation receipt requires an immutable formal negation contract');
  }
  if (receipt.leanStatementHash !== leanStatementHash) {
    throw new Error('Mathematics kernel receipt leanStatementHash does not match the immutable problem contract');
  }
  const match = /\b(?:theorem|lemma|example)\s+([A-Za-z_][A-Za-z0-9_'.]*)/u.exec(formalStatement.trim());
  if (!match) return;
  const expected = match[1];
  const actual = receipt.theoremName.trim();
  if (actual !== expected && actual.split('.').at(-1) !== expected.split('.').at(-1)) {
    throw new Error(`Mathematics kernel receipt theorem ${actual} does not match contract declaration ${expected}`);
  }
  const expectedDeclarationHash = hashMathFormalSourceDeclaration(formalStatement, actual);
  if (!expectedDeclarationHash || receipt.sourceDeclarationHash !== expectedDeclarationHash) {
    throw new Error('Mathematics kernel receipt source declaration does not match the immutable problem contract');
  }
}

function assertMathNodeReceiptMatches(
  value: MathNodeProofReceipt,
  statementHash: string,
  routeFingerprint: string,
  planNodeId: string,
  targetCommit: string,
  assignment: ResearchTeamAssignment | undefined
): void {
  const receipt = normalizeMathNodeProofReceipt(value);
  const normalizedRouteFingerprint = normalizeMathRouteFingerprint(routeFingerprint);
  if (
    receipt.statementHash !== statementHash ||
    receipt.routeFingerprint !== normalizedRouteFingerprint ||
    receipt.planNodeId !== planNodeId ||
    receipt.targetCommit !== targetCommit
  ) {
    throw new Error('Mathematics node proof receipt does not match the frozen statement, route, node, and commit');
  }
  const route = assignment?.math?.routeCards?.find((card) => card.routeFingerprint === normalizedRouteFingerprint);
  const node = route?.planNodes.find((candidate) => candidate.id === planNodeId);
  if (!node) {
    throw new Error('Mathematics node proof receipt has no frozen route-DAG declaration');
  }
  const expectedDeclarationHash = hashMathFormalSourceDeclaration(node.provisionalLeanStatement, receipt.theoremName);
  if (!expectedDeclarationHash) {
    throw new Error('Mathematics node proof receipt theorem does not match the frozen plan-node declaration');
  }
  if (receipt.sourceDeclarationHash !== expectedDeclarationHash) {
    throw new Error(
      'Mathematics node proof receipt source declaration does not match the frozen plan-node declaration'
    );
  }
}

function assertMathHelperReceiptMatches(
  value: MathHelperReceipt,
  result: ResearchTeamResult,
  targetCommit: string
): void {
  const receipt = normalizeMathHelperReceipt(value);
  if (
    receipt.statementHash !== result.math?.statementHash ||
    receipt.routeFingerprint !== result.math?.routeFingerprint ||
    receipt.targetCommit !== targetCommit
  ) {
    throw new Error('Mathematics helper receipt does not match the frozen statement, route, and commit');
  }
  const expansion = result.math?.planExpansion;
  const node = result.math?.planAfter?.planNodes.find((candidate) => candidate.id === receipt.helperPlanNodeId);
  if (
    !expansion ||
    !node ||
    !expansion.addedNodes.some((candidate) => candidate.id === receipt.helperPlanNodeId) ||
    node.parentNodeId !== receipt.parentPlanNodeId
  ) {
    throw new Error('Mathematics helper receipt must bind a node introduced by the validated plan expansion');
  }
  const expectedDeclarationHash = hashMathFormalSourceDeclaration(
    node.provisionalLeanStatement,
    receipt.declarationName
  );
  if (!expectedDeclarationHash || receipt.sourceDeclarationHash !== expectedDeclarationHash) {
    throw new Error('Mathematics helper receipt source declaration does not match the expanded helper node');
  }
}

function validateMathematicsResult(
  result: ResearchTeamResult,
  capability: ResearchTeamToolCapability,
  target: ResearchTeamRosterMember,
  readAssignment?: ResearchTeamAssignmentReader,
  validateAssignmentForResult: ResearchTeamAssignmentValidator = validateAssignment
): void {
  if (capability.profileId !== 'mathematics-research-team') return;
  if (!result.math) throw new Error('Mathematics result requires MathProgressDelta');
  if (!result.assignmentBinding) {
    throw new Error('Mathematics result requires assignmentBinding from the dispatched assignment');
  }
  if (
    result.assignmentBinding.workflowId !== capability.workflowId ||
    result.assignmentBinding.laneId !== target.laneId
  ) {
    throw new Error('Mathematics assignmentBinding does not match the Worker capability');
  }
  if (result.assignmentBinding.statementHash !== result.math.statementHash) {
    throw new Error('Mathematics assignmentBinding.statementHash must match MathProgressDelta.statementHash');
  }
  if (result.assignmentBinding.routeFingerprint !== result.math.routeFingerprint) {
    throw new Error('Mathematics assignmentBinding.routeFingerprint must match MathProgressDelta.routeFingerprint');
  }
  if (result.assignmentBinding.activePlanNodeId !== result.math.activePlanNodeId) {
    throw new Error('Mathematics assignmentBinding.activePlanNodeId must match MathProgressDelta.activePlanNodeId');
  }
  if (result.assignmentId !== result.assignmentBinding.assignmentId) {
    throw new Error('Mathematics result.assignmentId must match assignmentBinding.assignmentId');
  }
  if (result.workflowId !== result.assignmentBinding.workflowId || result.laneId !== result.assignmentBinding.laneId) {
    throw new Error('Mathematics result identity must match assignmentBinding');
  }
  if (result.git.baseCommit !== result.assignmentBinding.baseCommit) {
    throw new Error('Mathematics result git.baseCommit must match assignmentBinding.baseCommit');
  }
  if (result.assignmentBinding.stage === undefined) {
    throw new Error('Mathematics assignmentBinding.stage is required');
  }
  let sourceAssignment = dispatchedAssignments.get(`${capability.teamId}:${result.assignmentId}`);
  let durableReceipt: ProjectGitResearchTeamAssignmentReceipt | undefined;
  if (readAssignment) {
    durableReceipt = readAssignment({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: target.slotId,
      assignmentId: result.assignmentId,
    });
  }
  if (sourceAssignment) {
    sourceAssignment = resolveMathematicsResearchAssignment(
      sourceAssignment,
      capability,
      target,
      durableReceipt?.assignment ?? sourceAssignment
    );
    assertAssignmentBindingMatches(result.assignmentBinding, sourceAssignment);
  }
  if (!sourceAssignment && readAssignment) {
    if (!durableReceipt || !['prepared', 'accepted', 'integrated'].includes(durableReceipt.state)) {
      throw new Error('Mathematics result has no durable assignment receipt after Lead restart');
    }
    const stored = validateDurableResearchTeamAssignment(
      durableReceipt.assignment,
      capability,
      target,
      validateAssignmentForResult
    );
    sourceAssignment = resolveMathematicsResearchAssignment(stored, capability, target, durableReceipt.assignment);
    assertAssignmentBindingMatches(result.assignmentBinding, sourceAssignment);
  }
  assertRequiredMathematicsExactLeanHandoff(result, sourceAssignment, capability.teamId);
  assertMathExecutionPolicyProgress(result, sourceAssignment);
  const allowedStages =
    target.laneId === 'lean-engineering'
      ? ['formalize']
      : target.laneId === 'independent-review'
        ? ['review']
        : ['diversify', 'replan'];
  if (!allowedStages.includes(result.assignmentBinding.stage)) {
    throw new Error(`Mathematics assignmentBinding.stage is incompatible with Worker lane ${target.laneId}`);
  }
  if (sourceAssignment?.math?.artifactPaths) {
    const declared = new Set(sourceAssignment.math.artifactPaths);
    if (result.artifactPaths.some((artifactPath) => !declared.has(artifactPath))) {
      throw new Error('Mathematics Worker delivered an artifact path outside its declared assignment ownership');
    }
  }
  const artifactLane = target.laneId === 'lean-engineering';
  if ((artifactLane && result.executionMode === 'advisory') || (!artifactLane && result.executionMode !== 'advisory')) {
    throw new Error('Mathematics result executionMode does not match the Worker lane');
  }
  if (target.laneId === 'independent-review' && !result.mathReview) {
    throw new Error('Mathematics Independent Reviewer result requires mathReview');
  }
  if (target.laneId !== 'independent-review' && result.mathReview) {
    throw new Error('Mathematics CandidateReview is only valid on the independent-review lane');
  }
  if (result.mathResearchFinding && target.laneId !== 'strategy-exploration') {
    throw new Error('Mathematics research findings are only valid on the discovery lane');
  }
  if (result.mathResearchFinding && !['diversify', 'replan'].includes(result.assignmentBinding.stage)) {
    throw new Error('Mathematics research findings are valid only during discovery stages');
  }
  if (result.mathResearchFinding) {
    const routeRefuted = result.mathResearchFinding.mainlineImpact === 'route_refuted';
    if (routeRefuted !== (result.disposition === 'refuted' && result.math.routeDisposition === 'reject')) {
      throw new Error('Mathematics research finding disposition must match mainlineImpact');
    }
  }
  if (target.laneId === 'independent-review' && result.mathReview) {
    const sound = result.mathReview.verdict === 'sound';
    if (result.disposition !== (sound ? 'accepted' : 'inconclusive')) {
      throw new Error('Mathematics Reviewer disposition must match the review verdict');
    }
    if (result.math.routeDisposition !== (sound ? 'advance' : 'reject')) {
      throw new Error('Mathematics Reviewer routeDisposition must match the review verdict');
    }
  }
  const directAttempt = sourceAssignment?.math?.directAttempt === true;
  const helperOnlyDirect =
    directAttempt && Boolean(result.mathHelperReceipt) && !result.localGateReceipt && !result.mathNodeReceipt;
  if (helperOnlyDirect) {
    if (result.math.routeDisposition !== 'blocked') {
      throw new Error('Direct Mathematics helper progress must keep routeDisposition=blocked');
    }
    if (result.math.openGoalCountBefore < 1 || result.math.openGoalCountAfter < 1) {
      throw new Error('Direct Mathematics helper progress must keep the whole-problem goal open');
    }
    if (result.disposition !== 'accepted' && result.disposition !== 'inconclusive') {
      throw new Error('Direct Mathematics helper progress cannot be terminal');
    }
  }
  if (
    result.assignmentBinding.stage === 'formalize' &&
    !directAttempt &&
    (!result.math.planBefore || !result.math.planAfter)
  ) {
    throw new Error('Mathematics FORMALIZE result requires planBefore and planAfter DAG snapshots');
  }
  if (result.assignmentBinding.stage === 'formalize' && result.math.routeDisposition === 'advance') {
    if (!result.git.headCommit) throw new Error('Mathematics advancing FORMALIZE result requires a head commit');
    if (directAttempt) {
      if (result.math.openGoalCountAfter !== 0) {
        throw new Error('Mathematics advancing direct FORMALIZE result must report zero remaining goals');
      }
      if (result.localGateReceipt) {
        assertLocalGateReceiptMatches(
          result.localGateReceipt,
          result.math.statementHash,
          result.math.routeFingerprint,
          result.git.headCommit
        );
        assertReceiptTheoremMatchesContract(
          result.localGateReceipt,
          sourceAssignment?.math?.problemContract,
          sourceAssignment?.math?.fastCheck?.candidateClaim
        );
      } else if (result.math.openGoalCountBefore < 1) {
        throw new Error('Mathematics solver-complete direct FORMALIZE result must report a positive prior goal count');
      }
    }
    const completedRoot = result.math.planAfter?.planNodes.some(
      (node) => node.id === result.math?.planAfter?.rootNodeId && node.status === 'kernel_verified'
    );
    const verifiedActiveNode = Boolean(
      result.math.activePlanNodeId && result.math.verifiedPlanNodeIdsAdded?.includes(result.math.activePlanNodeId)
    );
    if (directAttempt) {
      // A direct attempt advances only by closing the immutable whole-problem statement above.
    } else if (completedRoot) {
      if (!result.localGateReceipt) {
        throw new Error('Mathematics advancing FORMALIZE result requires a kernel-verified localGateReceipt');
      }
      assertLocalGateReceiptMatches(
        result.localGateReceipt,
        result.math.statementHash,
        result.math.routeFingerprint,
        result.git.headCommit
      );
      assertReceiptTheoremMatchesContract(
        result.localGateReceipt,
        sourceAssignment?.math?.problemContract,
        sourceAssignment?.math?.fastCheck?.candidateClaim
      );
    } else if (verifiedActiveNode) {
      if (!result.mathNodeReceipt) {
        throw new Error('Mathematics verified plan-node result requires mathNodeReceipt');
      }
    }
    const activeRouteNode = sourceAssignment?.math?.routeCards
      ?.find((card) => card.routeFingerprint === result.math.routeFingerprint)
      ?.planNodes.find((node) => node.id === result.math.activePlanNodeId);
    const expandedHelperNode =
      activeRouteNode?.kind === 'ported_helper' &&
      result.math.planExpansion?.addedNodes.some((node) => node.id === result.math.activePlanNodeId);
    if (!directAttempt && expandedHelperNode && !result.mathHelperReceipt) {
      throw new Error('Mathematics ported_helper FORMALIZE advancement requires a kernel-verified mathHelperReceipt');
    }
  }
  if (result.mathNodeReceipt) {
    if (!result.git.headCommit || !result.math.activePlanNodeId) {
      throw new Error('Mathematics mathNodeReceipt requires a committed active plan node');
    }
    assertMathNodeReceiptMatches(
      result.mathNodeReceipt,
      result.math.statementHash,
      result.math.routeFingerprint,
      result.math.activePlanNodeId,
      result.git.headCommit,
      sourceAssignment
    );
  }
  if (result.mathHelperReceipt) {
    if (!result.git.headCommit) {
      throw new Error('Mathematics mathHelperReceipt requires a committed helper');
    }
    assertMathHelperReceiptMatches(result.mathHelperReceipt, result, result.git.headCommit);
  }
  if (result.assignmentBinding.stage === 'review') {
    if (!result.localGateReceipt) {
      throw new Error('Mathematics REVIEW result must echo the frozen LOCAL_GATE receipt');
    }
    assertLocalGateReceiptMatches(
      result.localGateReceipt,
      result.math.statementHash,
      result.math.routeFingerprint,
      result.git.baseCommit
    );
    assertReceiptTheoremMatchesContract(
      result.localGateReceipt,
      sourceAssignment?.math?.problemContract,
      sourceAssignment?.math?.fastCheck?.candidateClaim
    );
    if (result.mathReview?.localGateReceiptId !== result.localGateReceipt.receiptId) {
      throw new Error('Mathematics CandidateReview must reference the echoed LOCAL_GATE receipt');
    }
    const replayFields = [
      result.mathReview.replayReceiptId,
      result.mathReview.replayTheoremName,
      result.mathReview.replayProofHash,
      result.mathReview.replayTheoremDeclarationHash,
      result.mathReview.replaySourceDeclarationHash,
    ];
    if (replayFields.some(Boolean)) {
      if (replayFields.slice(0, 4).some((value) => !value)) {
        throw new Error('Mathematics CandidateReview optional Lean replay metadata must be complete');
      }
      if (result.mathReview.replayReceiptId === result.localGateReceipt.receiptId) {
        throw new Error('Mathematics CandidateReview replay receipt must be distinct from the LOCAL_GATE receipt');
      }
      if (
        result.mathReview.replayTheoremName !== result.localGateReceipt.theoremName ||
        result.mathReview.replayProofHash !== result.localGateReceipt.proofHash ||
        result.mathReview.replayTheoremDeclarationHash !== result.localGateReceipt.theoremDeclarationHash ||
        result.mathReview.replaySourceDeclarationHash !== result.localGateReceipt.sourceDeclarationHash
      ) {
        throw new Error('Mathematics CandidateReview replay must match the exact LOCAL_GATE theorem and proof');
      }
      if (!result.mathReview.evidenceRefs.includes(`lean-receipt:${result.mathReview.replayReceiptId}`)) {
        throw new Error('Mathematics CandidateReview must include an exact evidence reference to its replay receipt');
      }
    }
    if (result.assignmentBinding.localGateReceiptId !== result.localGateReceipt.receiptId) {
      throw new Error('Mathematics REVIEW result must use the dispatched LOCAL_GATE receipt');
    }
  }
  if (
    result.mathRouteCard &&
    (result.mathRouteCard.statementHash !== result.math.statementHash ||
      result.mathRouteCard.routeFingerprint !== result.math.routeFingerprint)
  ) {
    throw new Error('Mathematics mathRouteCard must match MathProgressDelta statement and route identity');
  }
  const routeProposalMode = sourceAssignment?.math?.routeProposalMode;
  if (
    target.laneId !== 'lean-engineering' &&
    target.laneId !== 'independent-review' &&
    result.math.routeDisposition === 'advance' &&
    !result.mathRouteCard &&
    !result.mathResearchFinding
  ) {
    throw new Error('Mathematics discovery delivery requires mathResearchFinding or mathRouteCard');
  }
  if (routeProposalMode && result.mathResearchFinding) {
    throw new Error('Mathematics route-proposal assignments cannot return a generic research finding');
  }
  if (routeProposalMode === 'candidate' && result.math.routeDisposition === 'advance' && !result.mathRouteCard) {
    throw new Error('Mathematics route-candidate assignment requires mathRouteCard');
  }
  if (routeProposalMode === 'candidate' && result.mathRouteCard) {
    assertMathematicsTeamPlanNodeBounds([result.mathRouteCard]);
    const hasProbeEvidence = result.mathRouteCard.planNodes.some(
      (node) => node.status !== 'proposed' && node.evidenceRefs.length > 0
    );
    if (!hasProbeEvidence) {
      throw new Error('Mathematics route candidate must retain evidence from its decisive probe');
    }
    const triedStructures = sourceAssignment?.math?.failureLedger?.triedRouteStructureSignatures ?? [];
    if (triedStructures.includes(mathRouteStructureSignatureFromNormalized(result.mathRouteCard))) {
      throw new Error('Mathematics route candidate duplicates a structurally attempted route');
    }
  }
  if (target.laneId === 'strategy-exploration' && result.mathRouteCard?.assessment) {
    throw new Error('Mathematics Strategy Explorer must leave route assessment to a fresh Lead session');
  }
  if (
    target.laneId === 'strategy-exploration' &&
    result.mathRouteCard?.planNodes.some((node) => node.status === 'kernel_verified')
  ) {
    throw new Error('Mathematics Strategy Explorer cannot self-report kernel_verified plan nodes');
  }
  if (result.mathLessons) {
    const deliveredCommit = result.executionMode === 'advisory' ? result.git.baseCommit : result.git.headCommit;
    if (result.mathLessons.some((lesson) => lesson.sourceCommit !== deliveredCommit)) {
      throw new Error('Mathematics lessons must reference the delivered commit');
    }
    const receiptRefs = new Set<string>([
      ...(result.localGateReceipt ? [`lean-receipt:${result.localGateReceipt.receiptId}`] : []),
      ...(result.mathNodeReceipt ? [`lean-receipt:${result.mathNodeReceipt.receiptId}`] : []),
      ...(result.mathHelperReceipt ? [`lean-receipt:${result.mathHelperReceipt.receiptId}`] : []),
      ...(result.mathReview?.replayReceiptId ? [`lean-receipt:${result.mathReview.replayReceiptId}`] : []),
      ...(result.mathCheckpoint ? [`math-checkpoint:${result.mathCheckpoint.checkpointId}`] : []),
    ]);
    if (result.mathLessons.some((lesson) => !lesson.evidenceRefs.some((ref) => receiptRefs.has(ref)))) {
      throw new Error('Mathematics lessons must bind at least one evidenceRef to a receipt from this delivery');
    }
  }
  if (result.mathReview) {
    if (
      !sourceAssignment?.math?.problemContract ||
      result.mathReview.problemId !== sourceAssignment.math.problemContract.problemId
    ) {
      throw new Error('Mathematics mathReview.problemId must match the immutable assignment problemContract');
    }
    if (result.mathReview.statementHash !== result.math.statementHash) {
      throw new Error('Mathematics mathReview.statementHash must match MathProgressDelta.statementHash');
    }
    if (result.executionMode === 'advisory' && result.mathReview.targetCommit !== result.git.baseCommit) {
      throw new Error('Mathematics mathReview.targetCommit must match the reviewed base commit');
    }
  }
  if (result.mathCheckpoint) {
    if (result.mathCheckpoint.ledger.statementHash !== result.math.statementHash) {
      throw new Error('Mathematics recovery checkpoint statementHash must match MathProgressDelta.statementHash');
    }
    if (result.mathCheckpoint.ledger.activeRoute !== result.math.routeFingerprint) {
      throw new Error('Mathematics recovery checkpoint route must match MathProgressDelta.routeFingerprint');
    }
    const deliveredCommit = result.executionMode === 'advisory' ? result.git.baseCommit : result.git.headCommit;
    if (result.mathCheckpoint.targetCommit !== deliveredCommit) {
      throw new Error('Mathematics recovery checkpoint must target the delivered commit');
    }
    validateMathematicsCheckpointStage(target, result.mathCheckpoint);
    validateMathematicsCheckpointReason(result.math, result.mathCheckpoint);
  }
  const claimsKernelProgress =
    result.math.checkedDeclarationsAdded > 0 ||
    Boolean(result.math.verifiedPlanNodeIdsAdded?.length) ||
    result.math.evidenceDelta.some((item) => ['kernel_declaration', 'helper_declaration'].includes(item.kind));
  if (
    claimsKernelProgress &&
    target.laneId === 'lean-engineering' &&
    !result.localGateReceipt &&
    !result.mathNodeReceipt &&
    !result.mathHelperReceipt
  ) {
    throw new Error(
      'Mathematics Lean progress must be bound to a stored kernel receipt; Worker-reported declaration counts alone are not progress'
    );
  }
}

function assertMathExecutionPolicyProgress(
  result: ResearchTeamResult,
  sourceAssignment: ResearchTeamAssignment | undefined
): void {
  const previous = sourceAssignment?.math?.executionPolicy;
  const current = result.math?.executionPolicy;
  if (!previous) {
    if (current) {
      throw new Error('Mathematics Worker cannot introduce an executionPolicy that was not bound to its assignment');
    }
    return;
  }
  if (!current) {
    throw new Error('Mathematics Worker result must preserve the runtime-owned executionPolicy');
  }
  if (
    !isDeepStrictEqual(previous.modelPriority, current.modelPriority) ||
    !isDeepStrictEqual(previous.tacticLadder, current.tacticLadder) ||
    !isDeepStrictEqual(previous.premiseQueries, current.premiseQueries)
  ) {
    throw new Error('Mathematics Worker cannot rewrite the executionPolicy route or tactic ladder');
  }
  if (current.tacticIndex < previous.tacticIndex) {
    throw new Error('Mathematics executionPolicy.tacticIndex cannot regress');
  }
  if (current.premiseQueryIndex < previous.premiseQueryIndex) {
    throw new Error('Mathematics executionPolicy.premiseQueryIndex cannot regress');
  }
  const assertAppendOnly = (before: readonly string[], after: readonly string[], field: string): void => {
    if (after.length < before.length || before.some((value, index) => after[index] !== value)) {
      throw new Error(`Mathematics executionPolicy.${field} must be append-only`);
    }
  };
  assertAppendOnly(previous.attemptedModels, current.attemptedModels, 'attemptedModels');
  assertAppendOnly(previous.attemptedTactics, current.attemptedTactics, 'attemptedTactics');
  assertAppendOnly(previous.attemptedPremiseQueries, current.attemptedPremiseQueries, 'attemptedPremiseQueries');
  if (!isDeepStrictEqual(previous.modelReceipt, current.modelReceipt)) {
    throw new Error('Mathematics Worker cannot rewrite the runtime-owned modelReceipt');
  }
}

function assertMathematicsTeamPlanNodeBounds(cards: readonly MathRouteCard[] | undefined): void {
  if (!cards) return;
  for (const card of cards) {
    if (card.planNodes.length > 7 && !card.extendedPlanReason) {
      throw new Error('Mathematics Team route cards above 7 plan nodes require extendedPlanReason');
    }
  }
}

function validateMathematicsCheckpointReason(
  progress: NonNullable<ResearchTeamResult['math']>,
  checkpoint: NonNullable<ResearchTeamResult['mathCheckpoint']>
): void {
  const category = checkpoint.ledger.failureCategory;
  const outcome = classifyMathProgress(progress);
  if ((outcome !== 'advanced' || progress.routeDisposition !== 'advance') && category === 'none') {
    throw new Error('Mathematics recovery checkpoint for a stalled or failed result requires failureCategory');
  }
  if (progress.infraStatus !== 'ready' && !['infra', 'toolchain'].includes(category)) {
    throw new Error('Mathematics infrastructure failure checkpoint must use failureCategory=infra or toolchain');
  }
  if (progress.routeDisposition === 'duplicate' && category !== 'duplicate_route') {
    throw new Error('Mathematics duplicate route checkpoint must use failureCategory=duplicate_route');
  }
  if (
    checkpoint.ledger.stage === 'formalize' &&
    checkpoint.ledger.verifiedPlanNodeIds?.length &&
    !checkpoint.ledger.semiProofCheckpoint
  ) {
    throw new Error('Mathematics FORMALIZE checkpoint with verified nodes requires a semiProofCheckpoint');
  }
}

function validateMathematicsCheckpointStage(
  target: ResearchTeamRosterMember,
  checkpoint: NonNullable<ResearchTeamResult['mathCheckpoint']>
): void {
  const stage = checkpoint.ledger.stage;
  const allowedStages =
    target.laneId === 'lean-engineering'
      ? ['formalize']
      : target.laneId === 'independent-review'
        ? ['review']
        : ['diversify', 'replan'];
  if (!allowedStages.includes(stage)) {
    throw new Error(`Mathematics recovery checkpoint stage ${stage} is incompatible with Worker lane ${target.laneId}`);
  }
}

function validateResultEnums(value: Record<string, unknown>): void {
  if (!['accepted', 'refuted', 'inconclusive', 'blocked'].includes(String(value.disposition))) {
    throw new Error('result disposition is invalid');
  }
  if (value.evidence !== undefined && !Array.isArray(value.evidence))
    throw new Error('result evidence must be an array');
  for (const [index, evidence] of (Array.isArray(value.evidence) ? value.evidence : []).entries()) {
    if (!isRecord(evidence)) throw new Error(`result evidence[${index}] must be an object`);
    if (!['measurement', 'source', 'code', 'review', 'artifact'].includes(String(evidence.kind))) {
      throw new Error(`result evidence[${index}].kind is invalid`);
    }
    if (typeof evidence.supports !== 'boolean') {
      throw new Error(`result evidence[${index}].supports must be boolean`);
    }
  }
  if (value.falsification !== undefined) {
    if (
      !isRecord(value.falsification) ||
      !['survived', 'refuted', 'inconclusive', 'not_run'].includes(String(value.falsification.outcome))
    ) {
      throw new Error('result falsification outcome is invalid');
    }
  }
  if (value.verification !== undefined && !Array.isArray(value.verification))
    throw new Error('result verification must be an array');
  for (const [index, item] of (Array.isArray(value.verification) ? value.verification : []).entries()) {
    if (!isRecord(item)) throw new Error(`result verification[${index}] must be an object`);
    if (!['passed', 'failed', 'not_run'].includes(String(item.status))) {
      throw new Error(`result verification[${index}].status is invalid`);
    }
  }
}

async function compensateAcceptedAssignmentReceiptFailure(
  assignment: ResearchTeamAssignment,
  targetSlotId: string,
  teamRunId: string,
  runtime: ResearchTeamRuntime<RuntimeContext>,
  cause: unknown,
  preparedGit?: Readonly<{ branch?: string; worktreePath?: string }>
): Promise<never> {
  const capability = runtime.context.capability;
  const cancellation = {
    status: 'pending' as const,
    teamRunId,
  };
  try {
    runtime.context.projectGit.recordResearchTeamBudgetCancellation?.({
      workspace: assignment.git.projectRoot,
      teamId: capability.teamId,
      slotId: targetSlotId,
      assignmentId: assignment.assignmentId,
      assignment,
      budgetCancellation: cancellation,
    });
  } catch (persistError) {
    console.warn(`[ResearchTeam] unable to persist ACK compensation state: ${String(persistError)}`);
  }
  try {
    await cancelAssignmentTurn(
      runtime.client,
      capability.teamId,
      teamRunId,
      targetSlotId,
      `Mathematics assignment ${assignment.assignmentId} was accepted by Core but its durable receipt could not be persisted`
    );
    let cancellationPersisted = false;
    try {
      const persistCancellation = runtime.context.projectGit.recordResearchTeamBudgetCancellation;
      if (!persistCancellation) throw new Error('Durable budget cancellation persistence is unavailable');
      persistCancellation({
        workspace: assignment.git.projectRoot,
        teamId: capability.teamId,
        slotId: targetSlotId,
        assignmentId: assignment.assignmentId,
        assignment,
        budgetCancellation: { status: 'succeeded', teamRunId },
      });
      cancellationPersisted = true;
    } catch (persistError) {
      console.warn(`[ResearchTeam] unable to persist ACK compensation completion: ${String(persistError)}`);
    }
    if (!cancellationPersisted) {
      throw new ResearchTeamOrchestrationError(
        'assignment_receipt_persist_failed',
        `Core cancelled assignment ${assignment.assignmentId}, but durable cancellation state could not be persisted`,
        true
      );
    }
    try {
      const discarded = runtime.context.projectGit.discardAgentWorktree?.({
        workspace: capability.projectRoot,
        teamId: capability.teamId,
        slotId: targetSlotId,
        assignmentId: assignment.assignmentId,
        ...(preparedGit?.branch ? { branch: preparedGit.branch } : {}),
        ...(preparedGit?.worktreePath ? { worktreePath: preparedGit.worktreePath } : {}),
      });
      if (discarded && !discarded.ok && !discarded.preserved) {
        console.warn(
          `[ResearchTeam] unable to clean ACK-compensated assignment: ${discarded.error || 'cleanup failed'}`
        );
      }
    } catch (cleanupError) {
      // Cancellation is authoritative; preserve the receipt when cleanup is
      // blocked so a later reconciliation can protect any Worker evidence.
      console.warn(`[ResearchTeam] unable to clean ACK-compensated assignment: ${String(cleanupError)}`);
    }
  } catch (cancelError) {
    throw new ResearchTeamOrchestrationError(
      'assignment_receipt_persist_failed',
      `Core accepted the assignment, but its durable receipt failed and cancellation also failed: ${
        cancelError instanceof Error ? cancelError.message : String(cancelError)
      }`,
      true
    );
  }
  throw new ResearchTeamOrchestrationError(
    'assignment_receipt_persist_failed',
    `Core accepted the assignment, but its durable receipt failed: ${cause instanceof Error ? cause.message : String(cause)}`,
    true
  );
}

async function presentEvent(
  event: OrchestrationEvent,
  runtime: ResearchTeamRuntime<RuntimeContext>
): Promise<ItemResult> {
  const capability = runtime.context.capability;
  switch (event.kind) {
    case 'dispatch.accepted': {
      try {
        persistResearchTeamAssignment(
          runtime.context.projectGit,
          capability,
          // Keep the immutable assignment free of ephemeral Git delivery
          // fields; those are retained separately as preparedGit below.
          event.prepared.detail.receiptAssignment,
          event.prepared.detail.target,
          'accepted',
          event.prepared.detail.usageBaseline,
          event.acknowledgement.team_run_id,
          event.prepared.detail.advisory
            ? undefined
            : {
                ...(event.prepared.detail.preparedGit || {
                  branch: event.prepared.detail.branch?.name,
                  worktreePath: event.prepared.detail.workspace,
                  baseCommit: event.prepared.detail.branch?.baseCommit,
                }),
              }
        );
      } catch (error) {
        if (capability.profileId !== 'mathematics-research-team') {
          throw error;
        }
        // The prepared receipt is a write-ahead record.  Core has already
        // accepted the assignment, so a failure while promoting that record
        // must not cancel a valid Worker or turn it into a solver retry.  If
        // the WAL still matches the exact assignment sent to Core, let the
        // Worker delivery/status reconciliation promote it to `accepted`.
        try {
          const receipt = runtime.context.readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: event.request.targetSlotId,
            assignmentId: event.prepared.detail.receiptAssignment.assignmentId,
          });
          if (
            receipt?.state === 'prepared' &&
            isDeepStrictEqual(receipt.assignment, event.prepared.detail.receiptAssignment)
          ) {
            rememberDispatchedAssignment(
              `${capability.teamId}:${event.prepared.detail.assignment.assignmentId}`,
              event.prepared.detail.assignment,
              event.prepared.detail.usageBaseline
            );
            return Object.freeze({
              status: 'accepted',
              accepted: true,
              retryable: false,
              receipt_reconciliation_pending: true,
              target_slot_id: event.request.targetSlotId,
              target_role_id: event.prepared.detail.target.roleId,
              lane_id: event.prepared.detail.target.laneId,
              assignment_id: event.prepared.detail.assignment.assignmentId,
              assignment_binding: expectedResearchTeamAssignmentBinding(event.prepared.detail.assignment),
              team_run_id: event.acknowledgement.team_run_id,
              enqueue_status: event.acknowledgement.enqueue_status ?? 'accepted',
              message_id: event.acknowledgement.message_id ?? null,
              execution_mode: event.prepared.detail.assignment.executionMode ?? 'artifact',
              ...(event.prepared.detail.projectionEfficiency
                ? { efficiency: event.prepared.detail.projectionEfficiency }
                : {}),
              ...(event.prepared.detail.advisory
                ? { git_base_commit: event.prepared.detail.assignment.git.baseCommit }
                : {
                    git_branch: event.prepared.detail.branch?.name,
                    git_worktree: event.prepared.detail.workspace,
                    git_base_commit: event.prepared.detail.branch?.baseCommit,
                  }),
            });
          }
        } catch {
          // If the WAL cannot be read, cancellation below is the only safe
          // fallback because Core acceptance cannot be reconciled locally.
        }
        return compensateAcceptedAssignmentReceiptFailure(
          event.prepared.detail.receiptAssignment,
          event.request.targetSlotId,
          event.acknowledgement.team_run_id,
          runtime,
          error,
          event.prepared.detail.advisory
            ? undefined
            : {
                branch: event.prepared.detail.branch?.name,
                worktreePath: event.prepared.detail.workspace,
              }
        );
      }
      rememberDispatchedAssignment(
        `${capability.teamId}:${event.prepared.detail.assignment.assignmentId}`,
        event.prepared.detail.assignment,
        event.prepared.detail.usageBaseline
      );
      return Object.freeze({
        status: 'accepted',
        accepted: true,
        retryable: false,
        target_slot_id: event.request.targetSlotId,
        target_role_id: event.prepared.detail.target.roleId,
        lane_id: event.prepared.detail.target.laneId,
        assignment_id: event.prepared.detail.assignment.assignmentId,
        assignment_binding: expectedResearchTeamAssignmentBinding(event.prepared.detail.assignment),
        team_run_id: event.acknowledgement.team_run_id,
        enqueue_status: event.acknowledgement.enqueue_status ?? 'accepted',
        message_id: event.acknowledgement.message_id ?? null,
        execution_mode: event.prepared.detail.assignment.executionMode ?? 'artifact',
        ...(event.prepared.detail.projectionEfficiency
          ? { efficiency: event.prepared.detail.projectionEfficiency }
          : {}),
        ...(event.prepared.detail.advisory
          ? { git_base_commit: event.prepared.detail.assignment.git.baseCommit }
          : {
              git_branch: event.prepared.detail.branch?.name,
              git_worktree: event.prepared.detail.workspace,
              git_base_commit: event.prepared.detail.branch?.baseCommit,
            }),
      });
    }
    case 'dispatch.target-busy':
      return Object.freeze({
        status: 'target_busy',
        accepted: false,
        retryable: true,
        target_slot_id: event.request.targetSlotId,
        assignment_id: event.validated.assignment.assignmentId,
      });
    case 'dispatch.capacity':
      return Object.freeze({
        status: 'capacity',
        accepted: false,
        retryable: true,
        target_slot_id: event.request.targetSlotId,
        assignment_id: event.validated.assignment.assignmentId,
        reasoning_concurrency: capability.reasoningConcurrency,
        active_worker_slots: event.activeWorkerSlotIds,
        instruction: 'End this Lead turn; resume after a real Worker state transition or delivery.',
      });
    case 'dispatch.error':
      return Object.freeze({
        status: 'unavailable',
        accepted: false,
        retryable: event.retryable,
        target_slot_id: event.request.targetSlotId,
        error: Object.freeze({ code: event.code, message: event.message }),
        ...runInputsIntegrityDetails(event.code),
      });
    case 'status.observed': {
      let recoveryReceipts: readonly ProjectGitResearchTeamAssignmentReceipt[] | undefined;
      if (capability.profileId === 'mathematics-research-team' && runtime.context.listAssignments) {
        try {
          recoveryReceipts = runtime.context.listAssignments({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
          });
        } catch {
          // Individual recovery consumers retain their existing read fallback.
        }
      }
      const supersededAssignmentIds = new Set<string>();
      const supersessionNeedsRefresh = Boolean(
        recoveryReceipts?.some((receipt) => receipt.state === 'accepted' && receipt.supersessionPending)
      );
      const supersessionWarnings = await restorePendingResearchTeamSupersessions(
        capability,
        runtime.context.projectGit,
        runtime.client,
        recoveryReceipts,
        supersededAssignmentIds
      );
      // Supersession recovery may have changed accepted receipts on disk.
      // Refresh before the next reconciliation phase so a stale snapshot
      // cannot re-promote an assignment that was just superseded.
      if (supersessionNeedsRefresh && runtime.context.listAssignments) {
        try {
          recoveryReceipts = runtime.context.listAssignments({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
          });
        } catch {
          // Keep the earlier snapshot; the individual recovery helper will
          // surface an actionable warning if it cannot proceed safely.
        }
      }
      const preparedWarnings = await reconcilePreparedResearchTeamAssignments(
        capability,
        runtime.context.projectGit,
        runtime.client,
        event.state,
        runtime.context.validateAssignment,
        recoveryReceipts
      );
      const preparedNeedsRefresh = Boolean(recoveryReceipts?.some((receipt) => receipt.state === 'prepared'));
      if (preparedNeedsRefresh && runtime.context.listAssignments) {
        try {
          recoveryReceipts = runtime.context.listAssignments({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
          });
        } catch {
          // Preserve the last known snapshot for a best-effort status report.
        }
      }
      const pendingIntegrationWarnings = reconcilePendingResearchTeamIntegrations(
        capability,
        runtime.context.projectGit,
        recoveryReceipts
      );
      const selected = event.state.slots.filter((slot) => event.selectedSlotIds.includes(slot.slotId));
      const activeWorkerSlots = selected.filter((slot) => event.state.activeSlotIds.includes(slot.slotId));
      const observedAt = new Date().toISOString();
      return Object.freeze({
        status: 'observed',
        changed: event.changed,
        wait_seconds: event.request.waitSeconds ?? 0,
        wait_level: teamWaitLevelForSeconds(event.request.waitSeconds ?? 0) ?? null,
        observed_at: observedAt,
        slots: Object.freeze(
          selected.map((slot) =>
            Object.freeze({
              slot_id: slot.slotId,
              state: slot.state,
              queued_foreground_count: slot.queuedForegroundCount,
              queued_background_count: slot.queuedBackgroundCount,
              pending_wake_count: slot.pendingWakeCount,
              heartbeat: Object.freeze({
                status: researchTeamHeartbeatStatus(slot),
                observed_at: observedAt,
                active_turn_id: slot.activeTurnId ?? null,
                active_turn_started_at_ms: slot.activeTurnStartedAtMs ?? null,
                active_turn_elapsed_ms: slot.activeTurnElapsedMs ?? null,
                slow: slot.activeTurnSlow ?? false,
                runtime_health: slot.runtimeHealth ?? 'healthy',
                blocked_reason: slot.blockedReason ?? null,
              }),
            })
          )
        ),
        active_worker_slots: Object.freeze(activeWorkerSlots.map((slot) => slot.slotId)),
        ...(event.structuralStallSlotIds?.length
          ? {
              structural_stall: Object.freeze({
                slot_ids: Object.freeze([...event.structuralStallSlotIds]),
                action: 'dispatch_independent_formalize_or_strategy_lane',
                instruction:
                  'A Worker has produced no model or tool activity for the slow-turn threshold. Dispatch an independent dependency-ready FORMALIZE node or a structurally distinct strategy/Lean lane now; do not wait for this turn to finish.',
              }),
            }
          : {}),
        ...(supersessionWarnings.length || preparedWarnings.length || pendingIntegrationWarnings.length
          ? {
              supersession_warnings: Object.freeze([
                ...supersessionWarnings,
                ...preparedWarnings,
                ...pendingIntegrationWarnings,
              ]),
            }
          : {}),
        should_end_turn: activeWorkerSlots.length > 0,
        instruction:
          'This is a real Core snapshot. Do not poll repeatedly; Worker delivery wakes the Lead through Core messaging.',
      });
    }
    case 'status.error':
      return Object.freeze({
        status: 'unavailable',
        retryable: event.retryable,
        error: Object.freeze({ code: event.code, message: event.message }),
        ...runInputsIntegrityDetails(event.code),
      });
    case 'integration.accepted': {
      const mathProgressControl = event.integration.mathProgressControl;
      const efficiency = deriveIntegratedMathEfficiency(event.integration.result, mathProgressControl);
      const criticContinuation =
        event.integration.sourceAssignment?.math?.sessionContinuation?.purpose === 'critic'
          ? event.integration.sourceAssignment.math.sessionContinuation
          : undefined;
      const criticSourceReceipt = criticContinuation
        ? runtime.context
            .listAssignments?.({ workspace: capability.projectRoot, teamId: capability.teamId })
            .find((receipt) => receipt.assignmentId === criticContinuation.sourceAssignmentId)
        : undefined;
      if (criticContinuation && !criticSourceReceipt) {
        throw new Error('Mathematics Critic feedback lost its durable source assignment');
      }
      const criticSourceTarget = criticSourceReceipt
        ? capability.roster.find((member) => member.slotId === criticSourceReceipt.slotId)
        : undefined;
      if (criticSourceReceipt && !criticSourceTarget) {
        throw new Error('Mathematics Critic feedback source Worker is no longer in the roster');
      }
      const criticSourceAssignment =
        criticSourceReceipt && criticSourceTarget
          ? validateDurableResearchTeamAssignment(
              criticSourceReceipt.assignment,
              capability,
              criticSourceTarget,
              runtime.context.validateAssignment
            )
          : undefined;
      const mathRecoveryAction = deriveMathRecoveryAction(
        event.integration.result,
        mathProgressControl,
        capability,
        event.integration.researchContractUpdate?.researchContract,
        event.integration.target.slotId,
        event.integration.sourceAssignment,
        criticSourceReceipt?.slotId,
        criticSourceAssignment,
        deriveMathRouteWaveWidth(capability, [event.integration.target.slotId]),
        deriveMathBottleneckMicroWaveWidth(capability, [event.integration.target.slotId])
      );
      const supersessionWarnings: string[] = [];
      const mathematicsBatchReverification = runtime.context.mathematicsBatchReverification;
      const deferBatchReceiptCompletion = Boolean(
        mathematicsBatchReverification?.expectedAssignmentIds.has(event.integration.result.assignmentId) &&
        mathematicsBatchReverification.entries.size < mathematicsBatchReverification.expectedAssignmentIds.size
      );
      if (runtime.context.projectGit.completeResearchTeamAssignment && !deferBatchReceiptCompletion) {
        const durableMathProgress = mathProgressControl
          ? deriveDurableMathProgressCheckpoint(event.integration.result, mathProgressControl)
          : undefined;
        const durableIntegration = event.integration.advisory
          ? ({ executionMode: 'advisory' } as const)
          : event.integration.retainedWithoutMerge
            ? ({
                executionMode: 'artifact',
                branch: event.integration.result.git.branch,
                headCommit: event.integration.deliveredHeadCommit || event.integration.result.git.headCommit,
                retainedWithoutMerge: true,
              } as const)
            : ({
                executionMode: 'artifact',
                branch: event.integration.result.git.branch,
                headCommit: event.integration.deliveredHeadCommit || event.integration.result.git.headCommit,
                mergedCommit: event.integration.mergedCommit,
                ...(event.integration.reverificationRequired ? { reverificationRequired: true } : {}),
                ...(event.integration.reverifiedReceipts
                  ? { reverifiedReceipts: event.integration.reverifiedReceipts }
                  : {}),
                ...(event.integration.solverReadyReceipt
                  ? { solverReadyReceipt: event.integration.solverReadyReceipt }
                  : {}),
              } as const);
        const completionRequest = {
          workspace: capability.projectRoot,
          teamId: capability.teamId,
          slotId: event.integration.target.slotId,
          assignmentId: event.integration.result.assignmentId,
          integration: durableIntegration,
          ...(durableMathProgress ? { mathProgress: durableMathProgress } : {}),
        };
        try {
          runtime.context.projectGit.completeResearchTeamAssignment(completionRequest);
        } catch (error) {
          // The branch may already be merged when receipt persistence fails.
          // Preserve the exact integration payload on the accepted receipt so
          // the next status observation can promote it without redispatching.
          const durableAssignment = runtime.context.readAssignment?.({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: event.integration.target.slotId,
            assignmentId: event.integration.result.assignmentId,
          })?.assignment;
          if (!durableAssignment || !runtime.context.projectGit.recordResearchTeamAssignment) throw error;
          runtime.context.projectGit.recordResearchTeamAssignment({
            workspace: capability.projectRoot,
            teamId: capability.teamId,
            slotId: event.integration.target.slotId,
            assignmentId: event.integration.result.assignmentId,
            assignment: durableAssignment,
            state: 'accepted',
            integration: durableIntegration,
            ...(durableMathProgress ? { mathProgress: durableMathProgress } : {}),
          });
          console.warn(
            `[ResearchTeam] integration receipt promotion deferred for ${event.integration.result.assignmentId}: ${String(error)}`
          );
        }
        if (
          event.integration.integrationEffectId &&
          event.integration.mergedCommit &&
          runtime.context.mathIntegrationJournal
        ) {
          await runtime.context.mathIntegrationJournal.commit(
            event.integration.integrationEffectId,
            event.integration.mergedCommit
          );
        }
      }
      if (
        !event.integration.advisory &&
        event.integration.result.assignmentBinding?.stage === 'formalize' &&
        event.integration.result.assignmentBinding.activePlanNodeId &&
        runtime.context.listAssignments &&
        runtime.context.projectGit.supersedeResearchTeamAssignment &&
        (!event.integration.sourceAssignment?.math?.directAttempt ||
          isSolverCompleteDirectResult(event.integration.result, event.integration.sourceAssignment) ||
          isDirectDeclarationClusterCompleteResult(event.integration.result, event.integration.sourceAssignment))
      ) {
        const winner = event.integration.result;
        for (const receipt of runtime.context.listAssignments({
          workspace: capability.projectRoot,
          teamId: capability.teamId,
        })) {
          if (receipt.state !== 'accepted') continue;
          if (receipt.assignmentId === winner.assignmentId) continue;
          const target = capability.roster.find(
            (member) => member.roleKind === 'worker' && member.slotId === receipt.slotId
          );
          if (!target) continue;
          let competing: ResearchTeamAssignment;
          try {
            competing = validateDurableResearchTeamAssignment(
              receipt.assignment,
              capability,
              target,
              runtime.context.validateAssignment
            );
          } catch {
            continue;
          }
          const sameDirectCompetition =
            event.integration.sourceAssignment?.math?.directAttempt === true &&
            competing.math?.directAttempt === true &&
            competing.math?.stage === 'formalize' &&
            competing.math.statementHash === winner.math?.statementHash &&
            competing.math.activePlanNodeId === winner.math?.activePlanNodeId;
          const sameRoutedNode =
            event.integration.sourceAssignment?.math?.directAttempt !== true &&
            competing.math?.stage === 'formalize' &&
            competing.math.statementHash === winner.math?.statementHash &&
            competing.math.routeFingerprint === winner.math.routeFingerprint &&
            competing.math.activePlanNodeId === winner.math?.activePlanNodeId;
          if (!sameDirectCompetition && !sameRoutedNode) {
            continue;
          }
          const supersession = {
            winnerAssignmentId: winner.assignmentId,
            reason: 'A competing branch for the same proof node was selected and integrated.',
          };
          try {
            runtime.context.projectGit.recordResearchTeamSupersessionPending?.({
              workspace: capability.projectRoot,
              teamId: capability.teamId,
              slotId: receipt.slotId,
              assignmentId: receipt.assignmentId,
              supersessionPending: supersession,
            });
            if (receipt.teamRunId) {
              await cancelAssignmentTurn(
                runtime.client,
                capability.teamId,
                receipt.teamRunId,
                receipt.slotId,
                `Mathematics assignment ${receipt.assignmentId} was superseded by ${winner.assignmentId}`
              );
            } else {
              throw new Error(
                'Competing assignment has no durable teamRunId for safe cancellation; retry reconciliation.'
              );
            }
            runtime.context.projectGit.supersedeResearchTeamAssignment({
              workspace: capability.projectRoot,
              teamId: capability.teamId,
              slotId: receipt.slotId,
              assignmentId: receipt.assignmentId,
              supersession,
            });
            forgetDispatchedAssignment(`${capability.teamId}:${receipt.assignmentId}`);
          } catch (error) {
            const warning = `Unable to supersede competing assignment ${receipt.assignmentId}: ${
              error instanceof Error ? error.message : String(error)
            }`;
            supersessionWarnings.push(warning);
            console.warn(`[ResearchTeam] ${warning}`);
          }
        }
      }
      forgetDispatchedAssignment(`${capability.teamId}:${event.integration.result.assignmentId}`);
      if (event.integration.advisory) {
        return Object.freeze({
          status: 'advisory_accepted',
          accepted: true,
          target_slot_id: event.integration.target.slotId,
          target_role_id: event.integration.target.roleId,
          lane_id: event.integration.target.laneId,
          assignment_id: event.integration.result.assignmentId,
          disposition: event.integration.result.disposition,
          execution_mode: 'advisory',
          ...(event.integration.result.mathRouteCard
            ? { math_route_card: event.integration.result.mathRouteCard }
            : {}),
          ...(event.integration.result.mathReview ? { math_review: event.integration.result.mathReview } : {}),
          ...(event.integration.researchContractUpdate
            ? {
                research_contract: event.integration.researchContractUpdate.researchContract,
                research_state_persisted: event.integration.researchContractUpdate.persisted,
              }
            : {}),
          ...(mathProgressControl ? { math_progress_control: mathProgressControl } : {}),
          ...(mathRecoveryAction ? { next_assignment: mathRecoveryAction } : {}),
          ...(efficiency ? { efficiency } : {}),
        });
      }
      return Object.freeze({
        status: event.integration.retainedWithoutMerge
          ? event.integration.alreadyIntegrated
            ? 'already_retained_unmerged'
            : 'retained_unmerged'
          : event.integration.alreadyIntegrated
            ? 'already_integrated'
            : 'integrated',
        accepted: true,
        target_slot_id: event.integration.target.slotId,
        target_role_id: event.integration.target.roleId,
        lane_id: event.integration.target.laneId,
        assignment_id: event.integration.result.assignmentId,
        disposition: event.integration.result.disposition,
        branch: event.integration.branch?.name ?? event.integration.result.git.branch,
        delivered_commit:
          event.integration.branch?.head ??
          event.integration.deliveredHeadCommit ??
          event.integration.result.git.headCommit,
        ...(event.integration.mergedCommit ? { merged_commit: event.integration.mergedCommit } : {}),
        ...(event.integration.retainedWithoutMerge
          ? {
              merged: false,
              next_action:
                'The solver episode is closed and its incomplete branch remains unmerged. Follow math_progress_control or next_assignment.',
            }
          : {}),
        ...(supersessionWarnings.length ? { supersession_warnings: Object.freeze(supersessionWarnings) } : {}),
        ...(event.integration.reverified ? { reverified: true } : {}),
        ...(event.integration.reverifiedReceipts
          ? {
              merged_commit_receipts: Object.freeze({
                ...(event.integration.reverifiedReceipts?.localGateReceipt
                  ? { local_gate_receipt: event.integration.reverifiedReceipts.localGateReceipt }
                  : {}),
                ...(event.integration.reverifiedReceipts?.mathNodeReceipt
                  ? { math_node_receipt: event.integration.reverifiedReceipts.mathNodeReceipt }
                  : {}),
                ...(event.integration.reverifiedReceipts?.mathHelperReceipt
                  ? { math_helper_receipt: event.integration.reverifiedReceipts.mathHelperReceipt }
                  : {}),
              }),
            }
          : {}),
        ...(event.integration.solverReadyReceipt ? { solver_ready_receipt: event.integration.solverReadyReceipt } : {}),
        ...(mathProgressControl?.solver_declared_complete === true && !event.integration.solverReadyReceipt
          ? { solver_ready_receipt_pending: true }
          : {}),
        ...(event.integration.reverificationRequired
          ? {
              reverification_required: true,
              ...(event.integration.reverificationError
                ? { reverification_error: event.integration.reverificationError }
                : {}),
              next_action:
                'Re-run lean_workspace(certify) on merged_commit and use the new receipt before REVIEW or OFFICIAL_GATE.',
            }
          : {}),
        merged_into: event.integration.branch?.mergedInto,
        merged_at: event.integration.branch?.mergedAt,
        ...(event.integration.researchContractUpdate
          ? {
              research_contract: event.integration.researchContractUpdate.researchContract,
              research_state_persisted: event.integration.researchContractUpdate.persisted,
            }
          : {}),
        ...(mathProgressControl ? { math_progress_control: mathProgressControl } : {}),
        ...(mathRecoveryAction ? { next_assignment: mathRecoveryAction } : {}),
        ...(efficiency ? { efficiency } : {}),
      });
    }
    case 'integration.error': {
      const batch = runtime.context.mathematicsBatchReverification;
      const recoveryWarnings: string[] = [];
      // Artifact integrations are serialized. If a later branch fails after
      // an earlier branch was merged, do not leave that earlier receipt in
      // `accepted` forever. Persist its own merged commit with an explicit
      // reverification gate; a subsequent retry can then finish the wave.
      if (batch?.entries.size && runtime.context.projectGit.completeResearchTeamAssignment) {
        for (const entry of batch.entries.values()) {
          try {
            runtime.context.projectGit.completeResearchTeamAssignment({
              workspace: capability.projectRoot,
              teamId: capability.teamId,
              slotId: entry.targetSlotId,
              assignmentId: entry.result.assignmentId,
              integration: {
                executionMode: 'artifact',
                branch: entry.result.git.branch,
                headCommit: entry.result.git.headCommit,
                mergedCommit: entry.mergedCommit,
                reverificationRequired: true,
              },
            });
            if (entry.integrationEffectId && runtime.context.mathIntegrationJournal) {
              await runtime.context.mathIntegrationJournal.commit(entry.integrationEffectId, entry.mergedCommit);
            }
          } catch (error) {
            recoveryWarnings.push(
              `Unable to persist pending reverification for ${entry.result.assignmentId}: ${
                error instanceof Error ? error.message : String(error)
              }`
            );
          }
        }
      }
      return Object.freeze({
        status: 'unavailable',
        accepted: false,
        retryable: event.retryable,
        error: Object.freeze({ code: event.code, message: event.message }),
        ...(batch?.entries.size ? { batch_reverification_pending: true } : {}),
        ...runInputsIntegrityDetails(event.code),
        ...(recoveryWarnings.length ? { recovery_warnings: Object.freeze(recoveryWarnings) } : {}),
      });
    }
  }
}

type MathLeanRecoveryPolicy = Readonly<{
  strategy: string;
  candidateScope: 'same_candidate' | 'route_restructure';
  requiredActions: readonly string[];
  prohibitedActions: readonly string[];
  premiseQueryStrategy?: string;
  targetProbeMode?: 'exact' | 'apply';
}>;

const MATH_LEAN_RECOVERY_POLICIES: Readonly<Partial<Record<MathLeanFailureKind, MathLeanRecoveryPolicy>>> =
  Object.freeze({
    unknown_identifier: Object.freeze({
      strategy: 'resolve_name_or_import',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Search the current import closure for the fully qualified declaration and defining module.',
        'Validate the selected name with #check and against the live target before editing the proof.',
      ]),
      prohibitedActions: Object.freeze(['Do not guess namespace prefixes or add broad imports speculatively.']),
      premiseQueryStrategy: 'name_module_or_equivalent_declaration',
      targetProbeMode: 'exact',
    }),
    type_mismatch: Object.freeze({
      strategy: 'unify_expected_type',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Compare the inferred expression type with the live expected target.',
        'Try a ranked declaration with an apply probe, then repair only the first generated subgoal.',
      ]),
      prohibitedActions: Object.freeze(['Do not add casts or simp rules without checking the resulting target.']),
      premiseQueryStrategy: 'target_type_unification',
      targetProbeMode: 'apply',
    }),
    instance_synthesis_failed: Object.freeze({
      strategy: 'resolve_typeclass_instance',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Identify the exact missing typeclass and inspect local instances before changing the proof.',
        'Search for the defining instance, constructor, or narrow module import and validate it locally.',
      ]),
      prohibitedActions: Object.freeze([
        'Do not introduce an arbitrary local instance that changes theorem semantics.',
      ]),
      premiseQueryStrategy: 'instance_constructor_or_import',
      targetProbeMode: 'apply',
    }),
    unsolved_goals: Object.freeze({
      strategy: 'close_live_goal',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Work from the first live goal rather than the original theorem statement.',
        'Test ranked exact/apply/rewrite candidates and retain only a strictly smaller proof state.',
      ]),
      prohibitedActions: Object.freeze(['Do not rerun the same automation on an unchanged proof state.']),
      premiseQueryStrategy: 'remaining_goal_conclusion',
      targetProbeMode: 'exact',
    }),
    tactic_failed: Object.freeze({
      strategy: 'switch_tactic_family',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Replace the failed tactic family with a direct exact/apply/rewrite step or a smaller helper.',
        'Accept the repair only when the proof-state fingerprint changes or the goal closes.',
      ]),
      prohibitedActions: Object.freeze(['Do not retry equivalent automation with cosmetic parameter changes.']),
      premiseQueryStrategy: 'direct_lemma_before_alternate_tactic',
      targetProbeMode: 'exact',
    }),
    termination_failed: Object.freeze({
      strategy: 'restructure_termination_argument',
      candidateScope: 'route_restructure',
      requiredActions: Object.freeze([
        'Expose a structurally decreasing argument or an explicit well-founded measure.',
        'Prefer an existing non-recursive theorem or separate recursive definition from the proof.',
      ]),
      prohibitedActions: Object.freeze([
        'Do not run ordinary premise search against an unchanged recursive declaration.',
      ]),
    }),
    timeout_or_resource: Object.freeze({
      strategy: 'reduce_elaboration_cost',
      candidateScope: 'same_candidate',
      requiredActions: Object.freeze([
        'Replace broad automation with bounded deterministic steps or a typed intermediate helper.',
        'Reduce term size and search branching before retrying the same live goal once.',
      ]),
      prohibitedActions: Object.freeze([
        'Do not classify a Lean heartbeat or recursion-depth diagnostic as unavailable infrastructure.',
        'Do not increase resource limits before simplifying the candidate.',
      ]),
    }),
  });

const MATH_PREMISE_RETRIEVAL_FAILURE_KINDS = Object.freeze([
  'unknown_identifier',
  'type_mismatch',
  'instance_synthesis_failed',
  'unsolved_goals',
  'tactic_failed',
] as const);

const isMathPremiseRetrievalFailure = (
  value: MathLeanFailureKind | undefined
): value is (typeof MATH_PREMISE_RETRIEVAL_FAILURE_KINDS)[number] =>
  value !== undefined && (MATH_PREMISE_RETRIEVAL_FAILURE_KINDS as readonly string[]).includes(value);

/**
 * Turn the classified directive into a machine-readable next-dispatch
 * contract. The Lead may choose the target slot, while route and stall
 * decisions remain runtime-owned.
 */
function deriveMathRecoveryAction(
  result: ResearchTeamResult,
  control: Readonly<Record<string, unknown>> | undefined,
  capability: ResearchTeamToolCapability,
  updatedResearchContract?: MathResearchProblemContract,
  sourceSlotId?: string,
  sourceAssignment?: ResearchTeamAssignment,
  criticSourceSlotId?: string,
  criticSourceAssignment?: ResearchTeamAssignment,
  routeWaveWidth = 1,
  microWaveWidth = 1
): Readonly<Record<string, unknown>> | undefined {
  if (!result.math || !control) return undefined;
  if (control.completion_deferred === true) return undefined;
  // A completed direct declaration cluster has already been integrated into
  // the Lead branch. Do not redispatch that closed cluster as a solver repair;
  // the Lead will select the next dependency-ready declaration explicitly.
  if (isDirectDeclarationClusterCompleteResult(result, sourceAssignment)) return undefined;
  // A fresh semantic review is a Humanize-style control boundary. Keep the
  // reviewer verdict separate from the generic progress directive so a gap
  // repairs the same candidate while a wrong route opens a distinct route.
  if (result.assignmentBinding?.stage === 'review' && result.math.reviewAction) {
    const reviewAction = result.math.reviewAction;
    const action: Record<string, unknown> = {
      kind:
        reviewAction === 'advance'
          ? 'proceed_official_gate'
          : reviewAction === 'repair'
            ? 'repair_reviewed_candidate'
            : 'dispatch_new_route',
      review_action: reviewAction.toUpperCase(),
      source_assignment_id: result.assignmentId,
      stage: result.assignmentBinding.stage,
      workflow_stage: result.assignmentBinding.workflowStage,
      statement_hash: result.math.statementHash,
      route_fingerprint: result.math.routeFingerprint,
      next_objective: result.math.nextSingleObjective,
      progress_contract: Object.freeze({
        schema: 'deepscientist.mathematics.review-action-contract.v1',
        preserveCandidate: reviewAction !== 'reject',
        requireOfficialGate: reviewAction === 'advance',
        requireDistinctRoute: reviewAction === 'reject',
        evidenceRequired: Object.freeze(
          reviewAction === 'advance'
            ? ['unchanged_reviewed_commit', 'official_comparator_receipt']
            : reviewAction === 'repair'
              ? ['review_finding_evidence', 'new_kernel_or_goal_progress']
              : ['review_finding_evidence', 'new_route_fingerprint', 'new_route_mechanism']
        ),
      }),
    };
    if (reviewAction === 'reject') {
      action.forbid_route_fingerprint = result.math.routeFingerprint;
      Object.assign(
        action,
        deriveMathStrategyContinuation({
          capability,
          sourceAssignmentId: result.assignmentId,
          sourceSlotId,
          forbiddenTargetSlotIds: sourceSlotId ? [sourceSlotId] : [],
          purpose: 'alternate_route',
        })
      );
    }
    return Object.freeze(action);
  }
  // A repeated proof frontier is a high-confidence duplicate signal. Two
  // genuinely different routes are enough to recover; launching the full
  // strategy roster here only multiplies identical model calls.
  const effectiveRouteWaveWidth = control.repeated_proof_state === true ? Math.min(routeWaveWidth, 2) : routeWaveWidth;
  const directive = String(control.directive || '');
  if (
    ![
      'continue_research',
      'continue_node',
      'switch_node',
      'expand_node',
      'promote_helper',
      'port_upstream',
      're_decompose',
      'retry_infrastructure',
    ].includes(directive)
  ) {
    return undefined;
  }
  const action: Record<string, unknown> = {
    directive,
    source_assignment_id: result.assignmentId,
    stage: result.assignmentBinding?.stage,
    workflow_stage: result.assignmentBinding?.workflowStage,
    statement_hash: result.math.statementHash,
    route_fingerprint: result.math.routeFingerprint,
    progress_contract: Object.freeze({
      schema: 'deepscientist.mathematics.next-action-contract.v1',
      expectedChange:
        result.assignmentBinding?.stage === 'formalize'
          ? 'close the active goal, reduce the proof frontier, or retain a kernel-verified helper/node receipt'
          : 'add trusted evidence, narrow/resolve the active bottleneck, or produce a route-level falsification',
      rejectUnchangedState: true,
      evidenceRequired:
        result.assignmentBinding?.stage === 'formalize'
          ? Object.freeze(['open_goal_fingerprint_change', 'kernel_receipt', 'route_refutation'])
          : Object.freeze(['trusted_evidence_ref', 'bottleneck_change', 'route_refutation']),
      failureTransition:
        'Use the latest diagnostic or finding to change the tactic, premise, proof node, probe kind, or route. Do not resend an unchanged assignment.',
    }),
  };
  if (result.math.executionPolicy) {
    action.execution_policy = result.math.executionPolicy;
    action.policy_cursor = Object.freeze({
      tactic_index: result.math.executionPolicy.tacticIndex,
      premise_query_index: result.math.executionPolicy.premiseQueryIndex,
      current_tactic: result.math.executionPolicy.tacticLadder[result.math.executionPolicy.tacticIndex]?.tactic ?? null,
      current_premise_query:
        result.math.executionPolicy.premiseQueries[result.math.executionPolicy.premiseQueryIndex] ?? null,
      model_receipt: result.math.executionPolicy.modelReceipt ?? null,
    });
  }
  const findingObjective =
    result.mathResearchFinding?.bottleneckUpdate?.repair ?? result.mathResearchFinding?.nextAction;
  const helperRequest = result.mathResearchFinding?.helperRequest;
  if (directive === 'continue_research') {
    const criticSourceAssignmentId =
      sourceAssignment?.math?.sessionContinuation?.purpose === 'critic'
        ? sourceAssignment.math.sessionContinuation.sourceAssignmentId
        : undefined;
    const helperFeedback = sourceAssignment?.math?.sessionContinuation?.purpose === 'bottleneck_helper';
    if (helperFeedback) {
      action.kind = 'return_bottleneck_helper_result';
      action.helper_result = true;
      action.next_objective = findingObjective ?? result.math.nextSingleObjective;
    } else if (criticSourceAssignmentId) {
      action.kind = 'dispatch_same_candidate_repair';
      action.source_assignment_id = criticSourceAssignmentId;
      action.feedback_assignment_id = result.assignmentId;
      action.stage = criticSourceAssignment?.math?.stage ?? action.stage;
      action.workflow_stage = criticSourceAssignment?.math?.workflowStage ?? action.workflow_stage;
      action.statement_hash = criticSourceAssignment?.math?.statementHash ?? action.statement_hash;
      action.route_fingerprint = criticSourceAssignment?.math?.routeFingerprint ?? action.route_fingerprint;
      if (criticSourceAssignment?.math?.activePlanNodeId) {
        action.active_plan_node_id = criticSourceAssignment.math.activePlanNodeId;
      }
      action.next_objective = findingObjective ?? result.math.nextSingleObjective;
      action.session_continuation = {
        sourceAssignmentId: criticSourceAssignmentId,
        mode: 'reuse_source_slot',
        purpose: 'candidate_repair',
      };
      if (criticSourceSlotId) action.required_target_slot_id = criticSourceSlotId;
    } else if (control.critic_required === true) {
      Object.assign(
        action,
        deriveMathCriticFollowUp({
          capability,
          sourceAssignmentId: result.assignmentId,
          sourceSlotId,
          forbiddenTargetSlotIds: sourceSlotId ? [sourceSlotId] : [],
          nextObjective: findingObjective ?? result.math.nextSingleObjective,
        })
      );
    } else if (helperRequest && result.mathResearchFinding) {
      Object.assign(
        action,
        deriveMathBottleneckFollowUp({
          finding: result.mathResearchFinding,
          sourceAssignmentId: result.assignmentId,
          sourceSlotId,
          forbiddenTargetSlotIds: sourceSlotId ? [sourceSlotId] : [],
          primaryObjective: findingObjective ?? result.math.nextSingleObjective,
          primaryProbeKind: inferMathResearchProbeKind(result.mathResearchFinding),
          microWaveWidth,
        })
      );
    } else {
      action.kind = 'dispatch_next_research_action';
      action.next_objective = findingObjective ?? result.math.nextSingleObjective;
      action.session_continuation = {
        sourceAssignmentId: result.assignmentId,
        mode: 'reuse_source_slot',
        purpose: 'candidate_repair',
      };
      if (sourceSlotId) action.required_target_slot_id = sourceSlotId;
    }
    if (result.mathResearchFinding) {
      const recommendedProbeKind =
        isRecord(control.probe_roi) && typeof control.probe_roi.recommended_probe_kind === 'string'
          ? control.probe_roi.recommended_probe_kind
          : undefined;
      action.next_probe_kind = recommendedProbeKind ?? inferMathResearchProbeKind(result.mathResearchFinding);
    }
    action.research_finding_kind = result.mathResearchFinding?.kind ?? null;
    action.research_finding_impact = control.research_finding_impact ?? null;
    if (control.probe_roi) action.probe_roi = control.probe_roi;
    if (control.next_previous_consecutive_stalls !== undefined) {
      action.next_previous_consecutive_stalls = control.next_previous_consecutive_stalls;
    }
    if (updatedResearchContract) action.research_contract = updatedResearchContract;
    else if (isRecord(control.research_contract)) action.research_contract = control.research_contract;
  } else if (['expand_node', 'promote_helper', 'port_upstream'].includes(directive)) {
    action.kind =
      directive === 'promote_helper'
        ? 'promote_verified_helper'
        : directive === 'port_upstream'
          ? 'dispatch_upstream_port'
          : result.math.planExpansion
            ? 'continue_expanded_frontier'
            : 'dispatch_node_expansion';
    action.next_objective = result.math.nextSingleObjective;
    action.preferred_plan_node_id = result.math.planAfter?.bottleneckNodeId ?? result.math.activePlanNodeId ?? null;
    if (result.math.planAfter) action.plan_snapshot = result.math.planAfter;
    action.session_continuation = {
      sourceAssignmentId: result.assignmentId,
      mode: 'reuse_source_slot',
      purpose: 'candidate_repair',
    };
    if (sourceSlotId) action.required_target_slot_id = sourceSlotId;
  } else if (directive === 'retry_infrastructure') {
    action.kind = 'redispatch_infrastructure_retry';
    action.same_proof_state = result.math.openGoalFingerprintBefore ?? null;
  } else if (directive === 'switch_node') {
    action.kind = 'dispatch_alternate_frontier';
    action.preferred_plan_node_id = control.recommended_plan_node_id ?? null;
    action.session_continuation = {
      sourceAssignmentId: result.assignmentId,
      mode: 'reuse_source_slot',
      purpose: 'candidate_repair',
    };
    if (sourceSlotId) action.required_target_slot_id = sourceSlotId;
  } else if (directive === 're_decompose') {
    action.kind = effectiveRouteWaveWidth > 1 ? 'dispatch_route_wave' : 'dispatch_new_route';
    action.forbid_route_fingerprint = result.math.routeFingerprint;
    action.next_objective = result.math.nextSingleObjective;
    if (effectiveRouteWaveWidth > 1) {
      action.recommended_parallelism = effectiveRouteWaveWidth;
      action.route_proposal_mode = 'candidate';
      action.require_distinct_route_fingerprints = true;
      action.require_distinct_route_mechanisms = true;
      action.require_decisive_test_per_route = true;
    }
    Object.assign(
      action,
      deriveMathStrategyContinuation({
        capability,
        sourceAssignmentId: result.assignmentId,
        sourceSlotId,
        forbiddenTargetSlotIds: sourceSlotId ? [sourceSlotId] : [],
        purpose: 'alternate_route',
      })
    );
  } else {
    action.kind =
      control.critic_required === true
        ? 'dispatch_candidate_critic'
        : control.same_candidate_repair === true
          ? 'dispatch_same_candidate_repair'
          : 'continue_solver_episode';
    if (control.critic_required === true) {
      Object.assign(
        action,
        deriveMathCriticFollowUp({
          capability,
          sourceAssignmentId: result.assignmentId,
          sourceSlotId,
          forbiddenTargetSlotIds: sourceSlotId ? [sourceSlotId] : [],
          nextObjective: result.math.nextSingleObjective,
        })
      );
    } else {
      action.session_continuation = {
        sourceAssignmentId: result.assignmentId,
        mode: 'reuse_source_slot',
        purpose: 'candidate_repair',
      };
      if (sourceSlotId) action.required_target_slot_id = sourceSlotId;
    }
    action.proof_state_fingerprint =
      result.math.openGoalFingerprintAfter ?? result.math.openGoalFingerprintBefore ?? null;
  }
  if (!action.research_contract) {
    if (updatedResearchContract) action.research_contract = updatedResearchContract;
    else if (isRecord(control.research_contract)) action.research_contract = control.research_contract;
  }
  const failedProbe = result.math.wholeProofProbe?.outcome === 'lean_failed' ? result.math.wholeProofProbe : undefined;
  const observedFailureKind =
    failedProbe?.failureKind ??
    (result.math.firstLeanErrorAfter ? classifyMathLeanFailure(result.math.firstLeanErrorAfter) : undefined);
  const failureDiagnostic = failedProbe?.firstLeanError ?? result.math.firstLeanErrorAfter;
  const recoveryPolicy = observedFailureKind ? MATH_LEAN_RECOVERY_POLICIES[observedFailureKind] : undefined;
  if (recoveryPolicy) {
    action.lean_failure_recovery = Object.freeze({
      failure_kind: observedFailureKind,
      strategy: recoveryPolicy.strategy,
      candidate_scope: recoveryPolicy.candidateScope,
      required_actions: recoveryPolicy.requiredActions,
      prohibited_actions: recoveryPolicy.prohibitedActions,
      completion_signal: 'lean_goal_closed_or_strictly_new_proof_state',
    });
  }
  const premiseRetrievalTrigger = isMathPremiseRetrievalFailure(observedFailureKind)
    ? observedFailureKind
    : (!observedFailureKind || observedFailureKind === 'unknown') &&
        control.outcome === 'stalled' &&
        result.math.openGoalCountAfter > 0
      ? 'proof_stall'
      : undefined;
  const activePlanNodeId = result.math.activePlanNodeId;
  const problemId =
    sourceAssignment?.math?.problemContract?.problemId ?? sourceAssignment?.math?.researchContract?.problemId;
  if (
    premiseRetrievalTrigger &&
    activePlanNodeId &&
    problemId &&
    result.math.openGoalAfter &&
    directive !== 're_decompose'
  ) {
    const proofStateFingerprint = result.math.openGoalFingerprintAfter ?? result.math.openGoalFingerprintBefore;
    action.premise_retrieval = Object.freeze({
      trigger: premiseRetrievalTrigger,
      tool: 'math_portfolio',
      action: 'get',
      goal_source: 'live_lean_goal',
      import_modules_source: 'current_lean_file',
      retrieval_scope: recoveryPolicy?.premiseQueryStrategy ?? 'live_goal_local_premises',
      validation_modes: recoveryPolicy?.targetProbeMode
        ? Object.freeze(['check', recoveryPolicy.targetProbeMode])
        : Object.freeze(['check', 'exact', 'apply']),
      ...(proofStateFingerprint ? { cache_key: proofStateFingerprint, refresh_when_proof_state_changes: true } : {}),
      prompt_query: Object.freeze({
        problemId,
        routeFingerprint: result.math.routeFingerprint,
        planNodeId: activePlanNodeId,
        goal: result.math.openGoalAfter,
        ...(proofStateFingerprint ? { proofStateFingerprint } : {}),
        ...(isMathPremiseRetrievalFailure(observedFailureKind) ? { failureKind: observedFailureKind } : {}),
        ...(failureDiagnostic ? { failureDiagnostic } : {}),
        ...(recoveryPolicy?.targetProbeMode ? { targetProbeMode: recoveryPolicy.targetProbeMode } : {}),
        ...(result.math.executionPolicy
          ? {
              policyQueryIndex: result.math.executionPolicy.premiseQueryIndex,
              policyQuery:
                result.math.executionPolicy.premiseQueries[result.math.executionPolicy.premiseQueryIndex] ?? null,
            }
          : {}),
        ...(failedProbe?.sourceFile ? { sourceFile: failedProbe.sourceFile } : {}),
        premiseLimit: 4,
      }),
    });
  }
  if (failedProbe && directive !== 're_decompose') {
    const directDependentNodeIds = activePlanNodeId
      ? (result.math.planAfter?.planNodes ?? [])
          .filter((node) => node.dependsOn.includes(activePlanNodeId))
          .map((node) => node.id)
      : [];
    const solutionSketchRef = sourceAssignment?.math?.researchContract?.solutionSketchRef;
    const sketchKey = crypto
      .createHash('sha256')
      .update(
        [result.math.statementHash, result.math.routeFingerprint, activePlanNodeId ?? 'root'].join('\u0000'),
        'utf8'
      )
      .digest('hex')
      .slice(0, 24);
    action.sketch_revision = Object.freeze({
      source: solutionSketchRef ? 'artifact' : 'route_card',
      ...(solutionSketchRef ? { solution_sketch_ref: solutionSketchRef } : {}),
      ...(!solutionSketchRef
        ? {
            materialize_if_missing: true,
            artifact_path: `.deepscientist/math/solution-sketches/${sketchKey}.json`,
            artifact_schema: 'deepscientist.math.solution-sketch.v1',
          }
        : {}),
      ...(activePlanNodeId ? { active_plan_node_id: activePlanNodeId } : {}),
      affected_plan_node_ids: Object.freeze([
        ...new Set([activePlanNodeId, ...directDependentNodeIds].filter(Boolean)),
      ]),
      preserve_verified_plan_node_ids: Object.freeze([
        ...new Set([
          ...(sourceAssignment?.math?.failureLedger?.verifiedPlanNodeIds ?? []),
          ...(result.math.verifiedPlanNodeIdsAdded ?? []),
        ]),
      ]),
      ...(failedProbe.firstLeanError ? { diagnosis: failedProbe.firstLeanError } : {}),
      ...(failedProbe.repairObjective ? { repair_objective: failedProbe.repairObjective } : {}),
    });
  }
  const scheduleDecision = isRecord(control.schedule_decision) ? control.schedule_decision : undefined;
  const scheduledNodeIds =
    scheduleDecision && Array.isArray(scheduleDecision.selected_plan_node_ids)
      ? scheduleDecision.selected_plan_node_ids.filter(
          (value): value is string => typeof value === 'string' && value.trim().length > 0
        )
      : [];
  const scheduleTopology = typeof scheduleDecision?.topology === 'string' ? scheduleDecision.topology : undefined;
  const freshSupportSlotAvailable = hasCompatibleFreshWorkerSlot(
    capability,
    result.laneId,
    sourceSlotId ? [sourceSlotId] : []
  );
  if (scheduledNodeIds.length > 0 && scheduleTopology && scheduleTopology !== 'mainline' && freshSupportSlotAvailable) {
    action.kind = 'dispatch_support_frontier';
    action.support_lane = true;
    action.required_stage = 'formalize';
    action.execution_mode = 'artifact';
    action.selected_plan_node_ids = Object.freeze([...new Set(scheduledNodeIds)]);
    action.recommended_parallelism = Math.min(2, scheduledNodeIds.length);
    action.schedule_topology = scheduleTopology;
    action.schedule_reason = scheduleDecision.reason ?? null;
    delete action.session_continuation;
    delete action.required_target_slot_id;
    if (sourceSlotId) action.forbidden_target_slot_ids = [sourceSlotId];
  }
  return Object.freeze(action);
}

function deriveDurableMathProgressCheckpoint(
  result: ResearchTeamResult,
  control: Readonly<Record<string, unknown>>
): MathDurableProgressCheckpoint | undefined {
  if (!result.math || !result.assignmentBinding?.stage) return undefined;
  const outcome = control.outcome;
  const directive = control.directive;
  const nextStage = control.next_stage;
  const consecutiveStalls = control.consecutive_stalls;
  if (
    !['advanced', 'stalled', 'regressed', 'infra_failed'].includes(String(outcome)) ||
    ![
      'continue_node',
      'switch_node',
      'expand_node',
      'promote_helper',
      'port_upstream',
      're_decompose',
      'retry_infrastructure',
      'solver_complete',
    ].includes(String(directive)) ||
    !['audit', 'diversify', 'select', 'formalize', 'local_gate', 'review', 'official_gate', 'replan', 'done'].includes(
      String(nextStage)
    ) ||
    !Number.isSafeInteger(consecutiveStalls) ||
    Number(consecutiveStalls) < 0 ||
    (control.scaffold_only_streak !== undefined &&
      (!Number.isSafeInteger(control.scaffold_only_streak) || Number(control.scaffold_only_streak) < 0))
  ) {
    return undefined;
  }
  return normalizeMathDurableProgressCheckpoint({
    statementHash: result.math.statementHash,
    routeFingerprint: result.math.routeFingerprint,
    ...(result.math.executionPolicy ? { executionPolicy: result.math.executionPolicy } : {}),
    ...(result.math.progressFingerprint ? { progressFingerprint: result.math.progressFingerprint } : {}),
    ...(result.math.failureCategory ? { failureCategory: result.math.failureCategory } : {}),
    outcome: outcome as MathDurableProgressCheckpoint['outcome'],
    consecutiveStalls: Number(consecutiveStalls),
    directive: directive as MathDurableProgressCheckpoint['directive'],
    nextStage: nextStage as MathDurableProgressCheckpoint['nextStage'],
    ...(typeof control.progress_kind === 'string'
      ? { progressKind: control.progress_kind as MathDurableProgressCheckpoint['progressKind'] }
      : {}),
    ...(control.scaffold_only_streak !== undefined ? { scaffoldOnlyStreak: Number(control.scaffold_only_streak) } : {}),
    ...(Array.isArray(control.route_performance)
      ? { routePerformance: control.route_performance as MathDurableProgressCheckpoint['routePerformance'] }
      : {}),
    ...(Array.isArray(control.route_attempt_digests)
      ? { routeAttemptDigests: control.route_attempt_digests as MathDurableProgressCheckpoint['routeAttemptDigests'] }
      : {}),
    ...(result.math.activePlanNodeId ? { activePlanNodeId: result.math.activePlanNodeId } : {}),
    ...(result.math.openGoalFingerprintAfter ? { proofStateFingerprint: result.math.openGoalFingerprintAfter } : {}),
    updatedAt: Date.now(),
  });
}

function deriveIntegratedMathEfficiency(
  result: ResearchTeamResult,
  mathProgressControl: Readonly<Record<string, unknown>> | undefined
): Readonly<Record<string, unknown>> | undefined {
  if (!result.math) return undefined;
  return Object.freeze({
    assignment_elapsed_ms: mathProgressControl?.assignment_elapsed_ms ?? null,
    token_usage: mathProgressControl?.token_usage ?? null,
    lean_execution_count: mathProgressControl?.lean_execution_count ?? 0,
    worktree_count: (result.executionMode ?? 'artifact') === 'artifact' ? 1 : 0,
    integration_round_trip_count: 1,
  });
}

function inferMathScheduleEvidence(
  math: NonNullable<ResearchTeamResult['math']>
): Parameters<typeof selectMathSchedule>[0]['lastEvidence'] {
  if (math.firstLeanErrorAfter && classifyMathLeanFailure(math.firstLeanErrorAfter) === 'unknown_identifier') {
    return 'unknown_api';
  }
  if (math.evidenceDelta.some((item) => item.kind === 'counterexample_probe' || item.kind === 'route_refutation')) {
    return 'counterexample';
  }
  if (math.evidenceDelta.some((item) => item.kind === 'helper_declaration')) return 'scaffold_only';
  if (
    math.openGoalCountAfter === math.openGoalCountBefore &&
    math.openGoalFingerprintBefore === math.openGoalFingerprintAfter
  ) {
    return 'goal_unchanged';
  }
  if ((math.planAfter?.openFrontierNodeIds.length ?? 0) > 1) return 'independent_frontier';
  return undefined;
}

function inferMathRouteProgressClass(
  math: NonNullable<ResearchTeamResult['math']>,
  state: Readonly<{ progressKind?: string; scaffoldOnlyStreak?: number }>
): MathRouteProgressClass {
  if (math.infraStatus !== 'ready') return 'infra_failed';
  if (state.progressKind === 'foundation_progress' && (state.scaffoldOnlyStreak ?? 0) > 0) {
    return 'scaffold_progress';
  }
  if (
    math.openGoalCountAfter < math.openGoalCountBefore ||
    (math.firstLeanErrorBefore !== undefined && math.firstLeanErrorAfter === undefined)
  ) {
    return 'goal_progress';
  }
  if (math.checkedDeclarationsAdded > 0 || Boolean(math.verifiedPlanNodeIdsAdded?.length)) {
    return 'frontier_progress';
  }
  return 'stalled';
}

function compareMathResearchFindings(
  left: MathResearchFinding,
  leftImpact: string,
  leftFalsificationOutcome: string | undefined,
  leftPriorContract: MathResearchProblemContract | undefined,
  leftProgressRank: number | undefined,
  right: MathResearchFinding,
  rightImpact: string,
  rightFalsificationOutcome: string | undefined,
  rightPriorContract: MathResearchProblemContract | undefined,
  rightProgressRank: number | undefined,
  leftEvidence: ReturnType<typeof readTrustedMathResearchEvidence> = [],
  rightEvidence: ReturnType<typeof readTrustedMathResearchEvidence> = []
): number {
  const impactRank = (impact: string): number =>
    impact === 'route_refuted' ? 4 : impact === 'mainline_advanced' ? 3 : impact === 'supporting' ? 2 : 1;
  const falsificationRank = (outcome: string | undefined): number =>
    outcome === 'survived' ? 2 : outcome === 'inconclusive' ? 1 : 0;
  const leftProgress = classifyMathResearchFindingProgress(left, leftImpact, leftPriorContract, leftEvidence);
  const rightProgress = classifyMathResearchFindingProgress(right, rightImpact, rightPriorContract, rightEvidence);
  const leftRank = [
    leftProgressRank ?? leftProgress.rank,
    falsificationRank(leftFalsificationOutcome),
    impactRank(leftImpact),
    leftProgress.novelStateCount,
    -left.openObligations.length,
    left.evidenceRefs.length,
  ];
  const rightRank = [
    rightProgressRank ?? rightProgress.rank,
    falsificationRank(rightFalsificationOutcome),
    impactRank(rightImpact),
    rightProgress.novelStateCount,
    -right.openObligations.length,
    right.evidenceRefs.length,
  ];
  for (let index = 0; index < leftRank.length; index += 1) {
    if (leftRank[index] !== rightRank[index]) return leftRank[index] - rightRank[index];
  }
  return 0;
}

function inferMathResearchProbeKind(finding: MathResearchFinding): MathResearchProbeKind {
  const categoryProbeKind = mathResearchProbeKindForFailureCategory(finding.bottleneckUpdate?.category);
  if (categoryProbeKind) return categoryProbeKind;
  if (finding.nextProbeKind) return finding.nextProbeKind;
  switch (finding.kind) {
    case 'literature':
      return 'literature';
    case 'example':
      return 'example';
    case 'computation':
      return 'computation';
    case 'counterexample':
      return 'counterexample';
    case 'obstruction':
      return 'obstruction';
    case 'proof_step':
      return 'proof_step';
    case 'critique':
      return 'critique';
    case 'conjecture_update':
      return finding.openObligations.length ? 'proof_step' : 'critique';
  }
}

function mathResearchProbeKindForFailureCategory(category: string | undefined): MathResearchProbeKind | undefined {
  switch (category) {
    case 'wrong_statement':
    case 'counterexample':
      return 'counterexample';
    case 'lean_error':
    case 'stalled':
      return 'proof_step';
    case 'regression':
    case 'review_gap':
      return 'critique';
    default:
      return undefined;
  }
}

function selectBestMathResearchFinding(
  indices: readonly number[],
  findings: readonly MathResearchFinding[],
  impacts: readonly string[],
  falsificationOutcomes: readonly (string | undefined)[],
  priorContracts: readonly (MathResearchProblemContract | undefined)[] = [],
  progressRanks: readonly (number | undefined)[] = [],
  evidence: readonly ReturnType<typeof readTrustedMathResearchEvidence>[] = []
): number {
  return indices.reduce((best, index) =>
    compareMathResearchFindings(
      findings[index],
      impacts[index],
      falsificationOutcomes[index],
      priorContracts[index],
      progressRanks[index],
      findings[best],
      impacts[best],
      falsificationOutcomes[best],
      priorContracts[best],
      progressRanks[best],
      evidence[index],
      evidence[best]
    ) > 0
      ? index
      : best
  );
}

function selectMathObstructionFinding(
  findings: readonly MathResearchFinding[],
  impacts: readonly string[],
  falsificationOutcomes: readonly (string | undefined)[]
): MathResearchFinding | undefined {
  const obstructionIndices = findings
    .map((finding, index) => (finding.kind === 'obstruction' && impacts[index] !== 'route_refuted' ? index : -1))
    .filter((index): index is number => index >= 0);
  if (!obstructionIndices.length) return undefined;
  return findings[selectBestMathResearchFinding(obstructionIndices, findings, impacts, falsificationOutcomes)];
}

function deriveMathRouteWaveWidth(capability: ResearchTeamToolCapability, forbiddenSlotIds: readonly string[]): number {
  const forbidden = new Set(forbiddenSlotIds);
  const availableStrategySlots = capability.roster.filter(
    (member) =>
      member.roleKind === 'worker' && member.laneId === 'strategy-exploration' && !forbidden.has(member.slotId)
  ).length;
  return Math.max(1, Math.min(capability.reasoningConcurrency, availableStrategySlots));
}

function hasCompatibleFreshStrategySlot(
  capability: ResearchTeamToolCapability,
  sourceSlotIds: readonly string[]
): boolean {
  return hasCompatibleFreshWorkerSlot(capability, 'strategy-exploration', sourceSlotIds);
}

function hasCompatibleFreshWorkerSlot(
  capability: ResearchTeamToolCapability,
  laneId: string,
  sourceSlotIds: readonly string[]
): boolean {
  const sources = new Set(sourceSlotIds);
  return capability.roster.some(
    (member) => member.roleKind === 'worker' && member.laneId === laneId && !sources.has(member.slotId)
  );
}

function deriveMathStrategyContinuation(
  input: Readonly<{
    capability: ResearchTeamToolCapability;
    sourceAssignmentId: string;
    sourceSlotId?: string;
    forbiddenTargetSlotIds: readonly string[];
    purpose: 'alternate_route';
  }>
): Readonly<Record<string, unknown>> {
  if (input.sourceSlotId && !hasCompatibleFreshStrategySlot(input.capability, input.forbiddenTargetSlotIds)) {
    return Object.freeze({
      session_continuation: Object.freeze({
        sourceAssignmentId: input.sourceAssignmentId,
        mode: 'reuse_source_slot',
        purpose: input.purpose,
      }),
      required_target_slot_id: input.sourceSlotId,
    });
  }
  return Object.freeze({
    session_continuation: Object.freeze({
      sourceAssignmentId: input.sourceAssignmentId,
      mode: 'fresh_slot',
      purpose: input.purpose,
    }),
    forbidden_target_slot_ids: Object.freeze(input.forbiddenTargetSlotIds),
  });
}

function deriveMathCriticFollowUp(
  input: Readonly<{
    capability: ResearchTeamToolCapability;
    sourceAssignmentId: string;
    sourceSlotId?: string;
    forbiddenTargetSlotIds: readonly string[];
    nextObjective: string;
  }>
): Readonly<Record<string, unknown>> {
  if (input.sourceSlotId && !hasCompatibleFreshStrategySlot(input.capability, input.forbiddenTargetSlotIds)) {
    return Object.freeze({
      kind: 'dispatch_next_research_action',
      repair_same_candidate: true,
      critic_deferred: 'no_compatible_fresh_strategy_slot',
      next_objective: input.nextObjective,
      session_continuation: Object.freeze({
        sourceAssignmentId: input.sourceAssignmentId,
        mode: 'reuse_source_slot',
        purpose: 'candidate_repair',
      }),
      required_target_slot_id: input.sourceSlotId,
    });
  }
  return Object.freeze({
    kind: 'dispatch_candidate_critic',
    repair_same_candidate: true,
    critic_question: input.nextObjective,
    session_continuation: Object.freeze({
      sourceAssignmentId: input.sourceAssignmentId,
      mode: 'fresh_slot',
      purpose: 'critic',
    }),
    forbidden_target_slot_ids: Object.freeze(input.forbiddenTargetSlotIds),
  });
}

function deriveMathBottleneckMicroWaveWidth(
  capability: ResearchTeamToolCapability,
  sourceSlotIds: readonly string[]
): number {
  if (capability.reasoningConcurrency < 2) return 1;
  return hasCompatibleFreshStrategySlot(capability, sourceSlotIds) ? 2 : 1;
}

function deriveMathBottleneckFollowUp(
  input: Readonly<{
    finding: MathResearchFinding;
    sourceAssignmentId: string;
    sourceSlotId?: string;
    forbiddenTargetSlotIds: readonly string[];
    primaryObjective: string;
    primaryProbeKind: MathResearchProbeKind;
    microWaveWidth: number;
  }>
): Readonly<Record<string, unknown>> {
  const helper = input.finding.helperRequest;
  if (!helper) throw new Error('Mathematics bottleneck follow-up requires one helper request');
  if (input.microWaveWidth < 2) {
    return Object.freeze({
      kind: 'dispatch_bottleneck_helper',
      helper_request: helper,
      next_objective: helper.objective,
      max_parallelism: 1,
      session_continuation: {
        sourceAssignmentId: input.sourceAssignmentId,
        mode: input.sourceSlotId ? 'reuse_source_slot' : 'fresh_slot',
        purpose: 'bottleneck_helper',
      },
      ...(input.sourceSlotId
        ? { required_target_slot_id: input.sourceSlotId }
        : { forbidden_target_slot_ids: Object.freeze(input.forbiddenTargetSlotIds) }),
    });
  }
  return Object.freeze({
    kind: 'dispatch_bottleneck_micro_wave',
    active_bottleneck: helper.bottleneck,
    preserve_route: true,
    max_parallelism: 2,
    integrate_once_after_wave: true,
    probes: Object.freeze([
      Object.freeze({
        role: 'primary',
        probe_kind: input.primaryProbeKind,
        objective: input.primaryObjective,
        ...(input.sourceSlotId ? { required_target_slot_id: input.sourceSlotId } : {}),
        session_continuation: {
          sourceAssignmentId: input.sourceAssignmentId,
          mode: 'reuse_source_slot',
          purpose: 'candidate_repair',
        },
      }),
      Object.freeze({
        role: 'helper',
        probe_kind: helper.probeKind,
        objective: helper.objective,
        ...(helper.probeKind === 'problem_family'
          ? {
              problem_family_probe: Object.freeze({
                max_instances: 5,
                require_shared_mechanism: true,
                stop_on_counterexample: true,
              }),
            }
          : {}),
        forbidden_target_slot_ids: Object.freeze(input.forbiddenTargetSlotIds),
        session_continuation: {
          sourceAssignmentId: input.sourceAssignmentId,
          mode: 'fresh_slot',
          purpose: 'bottleneck_helper',
        },
      }),
    ]),
  });
}

function sharedResearchContractSeed(
  contracts: readonly MathResearchProblemContract[]
): MathResearchProblemContract | undefined {
  const first = contracts[0];
  if (!first) return undefined;
  if (
    contracts.some(
      (contract) =>
        contract.problemId !== first.problemId ||
        contract.objective !== first.objective ||
        contract.context !== first.context
    )
  ) {
    return undefined;
  }
  const shared = (
    key: keyof Pick<
      MathResearchProblemContract,
      'knownResults' | 'establishedClaims' | 'conjectures' | 'failedApproaches' | 'openObligations' | 'evidenceNotes'
    >
  ): readonly string[] | undefined => {
    const firstValues = first[key];
    if (!firstValues) return undefined;
    const present = new Set(firstValues);
    for (const contract of contracts.slice(1)) {
      const values = new Set(contract[key] ?? []);
      for (const value of present) {
        if (!values.has(value)) present.delete(value);
      }
    }
    return [...present];
  };
  const knownResults = shared('knownResults');
  const establishedClaims = shared('establishedClaims');
  const conjectures = shared('conjectures');
  const failedApproaches = shared('failedApproaches');
  const openObligations = shared('openObligations');
  const evidenceNotes = shared('evidenceNotes');
  const insights = contracts.every((contract) => isDeepStrictEqual(contract.insights, first.insights))
    ? first.insights
    : undefined;
  const probeSummary = MATH_RESEARCH_PROBE_KINDS.flatMap((probeKind) => {
    const entries = contracts.map((contract) => contract.probeSummary?.find((entry) => entry.probeKind === probeKind));
    if (entries.some((entry) => !entry)) return [];
    const present = entries as NonNullable<(typeof entries)[number]>[];
    const sharedBottlenecks = [
      ...new Set(present.flatMap((entry) => entry.bottleneckStats?.map((item) => item.bottleneck) ?? [])),
    ].filter((bottleneck) =>
      present.every((entry) => entry.bottleneckStats?.some((item) => item.bottleneck === bottleneck))
    );
    return [
      {
        probeKind,
        attempts: Math.min(...present.map((entry) => entry.attempts)),
        usefulChanges: Math.min(...present.map((entry) => entry.usefulChanges)),
        noChange: Math.min(...present.map((entry) => entry.noChange)),
        lastOutcome: present.every((entry) => entry.lastOutcome === present[0].lastOutcome)
          ? present[0].lastOutcome
          : ('no_state_change' as const),
        ...(sharedBottlenecks.length
          ? {
              bottleneckStats: sharedBottlenecks.map((bottleneck) => {
                const buckets = present.map(
                  (entry) => entry.bottleneckStats!.find((item) => item.bottleneck === bottleneck)!
                );
                return {
                  bottleneck,
                  attempts: Math.min(...buckets.map((entry) => entry.attempts)),
                  usefulChanges: Math.min(...buckets.map((entry) => entry.usefulChanges)),
                  noChange: Math.min(...buckets.map((entry) => entry.noChange)),
                  lastOutcome: buckets.every((entry) => entry.lastOutcome === buckets[0].lastOutcome)
                    ? buckets[0].lastOutcome
                    : ('no_state_change' as const),
                };
              }),
            }
          : {}),
      },
    ];
  });
  const activeBottleneck = contracts.every((contract) => contract.activeBottleneck === first.activeBottleneck)
    ? first.activeBottleneck
    : undefined;
  const bottleneckDiagnosis =
    activeBottleneck && contracts.every((contract) => contract.bottleneckDiagnosis === first.bottleneckDiagnosis)
      ? first.bottleneckDiagnosis
      : undefined;
  const solutionSketchRef = contracts.every((contract) => contract.solutionSketchRef === first.solutionSketchRef)
    ? first.solutionSketchRef
    : undefined;
  return normalizeMathResearchProblemContract({
    problemId: first.problemId,
    objective: first.objective,
    ...(first.context ? { context: first.context } : {}),
    ...(knownResults?.length ? { knownResults } : {}),
    ...(establishedClaims?.length ? { establishedClaims } : {}),
    ...(conjectures?.length ? { conjectures } : {}),
    ...(failedApproaches?.length ? { failedApproaches } : {}),
    ...(openObligations?.length ? { openObligations } : {}),
    ...(evidenceNotes?.length ? { evidenceNotes } : {}),
    ...(insights?.length ? { insights } : {}),
    ...(probeSummary?.length ? { probeSummary } : {}),
    consumedEvidenceKeys: [...new Set(contracts.flatMap((contract) => contract.consumedEvidenceKeys ?? []))],
    ...(activeBottleneck ? { activeBottleneck } : {}),
    ...(bottleneckDiagnosis ? { bottleneckDiagnosis } : {}),
    ...(solutionSketchRef ? { solutionSketchRef } : {}),
  });
}

function mergeMathResearchWaveContract(
  contracts: readonly MathResearchProblemContract[],
  findings: readonly MathResearchFinding[],
  selectedIndices: readonly number[],
  nextAction: string,
  evidence: readonly ReturnType<typeof readTrustedMathResearchEvidence>[] = []
): MathResearchProblemContract | undefined {
  const seed = sharedResearchContractSeed(contracts);
  if (!seed) return undefined;
  const selected = new Set(selectedIndices);
  let merged = seed;
  findings.forEach((finding, index) => {
    const effectiveFinding = selected.has(index)
      ? finding
      : Object.freeze({
          ...finding,
          // Non-winning routes contribute durable facts and evidence, but not
          // route-local conjectures or obligations.
          conjectureUpdates: Object.freeze([]),
          openObligations: Object.freeze([]),
          bottleneckUpdate: undefined,
          helperRequest: undefined,
          solutionSketchRef: undefined,
          nextAction,
        });
    merged = applyMathResearchFinding(merged, effectiveFinding, evidence[index]);
    if (!selected.has(index) && finding.mainlineImpact !== 'route_refuted') {
      merged = preserveSecondaryMathFinding(merged, finding);
    }
  });
  return normalizeMathResearchProblemContract({ ...merged, nextAction });
}

function preserveSecondaryMathFinding(
  contract: MathResearchProblemContract,
  finding: MathResearchFinding
): MathResearchProblemContract {
  if (!finding.evidenceRefs.length || (!finding.conjectureUpdates.length && !finding.openObligations.length)) {
    return contract;
  }
  const conditions = [finding.mechanism, ...finding.conjectureUpdates]
    .filter((value): value is string => Boolean(value))
    .slice(0, 4);
  const insight: MathResearchInsight = Object.freeze({
    claim: `Secondary route lead: ${finding.summary}`,
    conditions: Object.freeze(conditions),
    ...(finding.eliminatedApproaches[0] ? { failure: finding.eliminatedApproaches[0] } : {}),
    repair: finding.openObligations[0] ?? finding.nextAction,
    usableWhen: finding.bottleneckUpdate?.target ?? finding.nextAction,
    evidenceRefs: Object.freeze(finding.evidenceRefs.slice(0, 8)),
  });
  const insightKey = (value: MathResearchInsight): string => `${value.claim}\u0000${value.usableWhen}`;
  const insights = [
    ...(contract.insights ?? []).filter((value) => insightKey(value) !== insightKey(insight)),
    insight,
  ].slice(-8);
  return normalizeMathResearchProblemContract({ ...contract, insights });
}

function deriveMathResearchWaveSynthesis(
  batch: readonly IntegrationRequest[],
  outputs: readonly ItemResult[],
  capability: ResearchTeamToolCapability,
  workspace: string
): Readonly<Record<string, unknown>> | undefined {
  if (batch.length < 2) return undefined;
  const research = batch
    .map((request, index) => ({ request, output: outputs[index] }))
    .filter(
      ({ request, output }) =>
        request.result.laneId === 'strategy-exploration' &&
        Boolean(request.result.mathResearchFinding) &&
        ['advisory_accepted', 'integrated', 'already_integrated'].includes(String(output.status))
    );
  if (research.length === 1) {
    const contract = research[0].output.research_contract;
    if (isRecord(contract)) {
      mutateMathematicsResearchContract({
        workspace,
        contract: normalizeMathResearchProblemContract(contract as MathResearchProblemContract),
        update: (baseContract) =>
          applyMathResearchFinding(
            baseContract,
            research[0].request.result.mathResearchFinding!,
            readTrustedMathResearchEvidence(research[0].request.result.mathResearchFinding!, {
              teamId: capability.teamId,
              assignmentId: research[0].request.result.assignmentId,
            })
          ),
      });
    }
    return undefined;
  }
  if (research.length < 2) return undefined;

  const findings = research.map(({ request }) => request.result.mathResearchFinding!);
  const evidence = research.map(({ request }, index) =>
    readTrustedMathResearchEvidence(findings[index], {
      teamId: capability.teamId,
      assignmentId: request.result.assignmentId,
    })
  );
  const falsificationOutcomes = research.map(({ request }) => request.result.falsification?.outcome);
  const controls = research.map(({ output }) =>
    isRecord(output.math_progress_control) ? output.math_progress_control : undefined
  );
  const impacts = findings.map((finding, index) =>
    String(controls[index]?.research_finding_impact ?? finding.mainlineImpact ?? 'supporting')
  );
  const progressRanks = controls.map((control) =>
    Number.isFinite(control?.research_progress_rank) ? Number(control?.research_progress_rank) : undefined
  );
  const routeGroups = new Map<string, number[]>();
  research.forEach(({ request }, index) => {
    const routeFingerprint = normalizeMathRouteFingerprint(String(request.result.math?.routeFingerprint || ''));
    const indices = routeGroups.get(routeFingerprint) ?? [];
    indices.push(index);
    routeGroups.set(routeFingerprint, indices);
  });
  const routeDecisions = [...routeGroups].map(([routeFingerprint, indices]) => {
    const routeRefuted = indices.some((index) => impacts[index] === 'route_refuted');
    const advancingIndices = indices.filter((index) => impacts[index] === 'mainline_advanced');
    const advancingIndex = advancingIndices.length
      ? selectBestMathResearchFinding(
          advancingIndices,
          findings,
          impacts,
          falsificationOutcomes,
          [],
          progressRanks,
          evidence
        )
      : undefined;
    const primaryIndex = routeRefuted
      ? selectBestMathResearchFinding(
          indices.filter((index) => impacts[index] === 'route_refuted'),
          findings,
          impacts,
          falsificationOutcomes,
          [],
          progressRanks,
          evidence
        )
      : selectBestMathResearchFinding(indices, findings, impacts, falsificationOutcomes, [], progressRanks, evidence);
    const mechanismSignature = normalizeMathRouteFingerprint(findings[primaryIndex].mechanism ?? routeFingerprint);
    return Object.freeze({
      routeFingerprint,
      mechanismSignature,
      indices: Object.freeze(indices),
      routeRefuted,
      advancingIndex,
      primaryIndex,
    });
  });
  const mechanismGroups = new Map<string, (typeof routeDecisions)[number][]>();
  for (const route of routeDecisions.filter((candidate) => !candidate.routeRefuted)) {
    const group = mechanismGroups.get(route.mechanismSignature) ?? [];
    group.push(route);
    mechanismGroups.set(route.mechanismSignature, group);
  }
  const mechanismWinners = [...mechanismGroups.values()].map((routes) =>
    routes.reduce((best, route) =>
      compareMathResearchFindings(
        findings[route.primaryIndex],
        impacts[route.primaryIndex],
        falsificationOutcomes[route.primaryIndex],
        undefined,
        progressRanks[route.primaryIndex],
        findings[best.primaryIndex],
        impacts[best.primaryIndex],
        falsificationOutcomes[best.primaryIndex],
        undefined,
        progressRanks[best.primaryIndex],
        evidence[route.primaryIndex],
        evidence[best.primaryIndex]
      ) > 0
        ? route
        : best
    )
  );
  const selectedRoute = mechanismWinners.reduce<(typeof routeDecisions)[number] | undefined>((best, route) => {
    if (!best) return route;
    return compareMathResearchFindings(
      findings[route.primaryIndex],
      impacts[route.primaryIndex],
      falsificationOutcomes[route.primaryIndex],
      undefined,
      progressRanks[route.primaryIndex],
      findings[best.primaryIndex],
      impacts[best.primaryIndex],
      falsificationOutcomes[best.primaryIndex],
      undefined,
      progressRanks[best.primaryIndex],
      evidence[route.primaryIndex],
      evidence[best.primaryIndex]
    ) > 0
      ? route
      : best;
  }, undefined);
  const routeRefuted = selectedRoute === undefined;
  const selectedRouteDecision = selectedRoute ?? routeDecisions[0];
  const selectedIndices = selectedRouteDecision.indices;
  const primaryIndex = selectedRouteDecision.primaryIndex;
  const primaryProgressKind = String(
    controls[primaryIndex]?.research_progress_kind ??
      classifyMathResearchFindingProgress(
        findings[primaryIndex],
        impacts[primaryIndex],
        undefined,
        evidence[primaryIndex]
      ).kind
  ) as MathResearchFindingProgressClass;
  const mainlineAdvanced =
    !routeRefuted &&
    isMathResearchMainlineProgress(primaryProgressKind, findings[primaryIndex], evidence[primaryIndex]);
  const selectedControls = selectedIndices.map((index) => controls[index]);
  const replanRequired = Boolean(
    !routeRefuted &&
    !mainlineAdvanced &&
    selectedControls.some((control) => control?.directive === 're_decompose' || control?.next_stage === 'replan')
  );
  const obstructionFinding = selectMathObstructionFinding(findings, impacts, falsificationOutcomes);
  const obstructionRequired = Boolean(
    obstructionFinding &&
    !routeRefuted &&
    !mainlineAdvanced &&
    (mechanismGroups.size >= 2 || findings.filter((finding) => finding.kind === 'obstruction').length >= 2)
  );
  const routeChangeRequired = routeRefuted || (replanRequired && !obstructionRequired);
  const criticRequired =
    !routeRefuted &&
    !mainlineAdvanced &&
    !obstructionRequired &&
    !replanRequired &&
    selectedControls.some((control) => control?.critic_required === true);
  const nextPreviousStalls = Math.max(
    0,
    ...selectedControls.map((control) =>
      Number.isSafeInteger(control?.next_previous_consecutive_stalls)
        ? Number(control?.next_previous_consecutive_stalls)
        : 0
    )
  );
  const primaryFinding = findings[primaryIndex];
  const primaryProbeKind = inferMathResearchProbeKind(primaryFinding);
  const primaryResearch = research[primaryIndex];
  const sourceAssignmentId = primaryResearch.request.result.assignmentId;
  const sourceSlotIds = [...new Set(research.map(({ request }) => request.targetSlotId))];
  const freshStrategySlotAvailable = hasCompatibleFreshStrategySlot(capability, sourceSlotIds);
  const routeWaveWidth = deriveMathRouteWaveWidth(capability, [primaryResearch.request.targetSlotId]);
  const microWaveWidth = deriveMathBottleneckMicroWaveWidth(capability, sourceSlotIds);
  const nextObjective = routeChangeRequired
    ? routeRefuted
      ? 'Dispatch a structurally distinct route.'
      : 'Re-decompose the stalled route into a structurally distinct route.'
    : obstructionRequired
      ? `Synthesize the common obstruction before trying another route: ${obstructionFinding?.nextAction ?? 'Compare the failed routes and state the shared mechanism.'}`
      : criticRequired && freshStrategySlotAvailable
        ? 'Ask a fresh Critic to reconcile the wave against the active bottleneck.'
        : (primaryFinding.bottleneckUpdate?.repair ?? primaryFinding.nextAction);
  const obstructionAssignment = obstructionRequired
    ? Object.freeze({
        kind: 'dispatch_obstruction_synthesis',
        synthesize_obstruction: true,
        repair_same_candidate: true,
        next_probe_kind: 'obstruction',
        obstruction_summary: obstructionFinding?.summary ?? 'Compare the failed routes and state the shared mechanism.',
        ...(freshStrategySlotAvailable
          ? {
              critic_question: nextObjective,
              session_continuation: Object.freeze({
                sourceAssignmentId,
                mode: 'fresh_slot' as const,
                purpose: 'critic' as const,
              }),
              forbidden_target_slot_ids: Object.freeze(sourceSlotIds),
            }
          : {
              critic_deferred: 'no_compatible_fresh_strategy_slot',
              session_continuation: Object.freeze({
                sourceAssignmentId,
                mode: 'reuse_source_slot' as const,
                purpose: 'candidate_repair' as const,
              }),
              required_target_slot_id: primaryResearch.request.targetSlotId,
            }),
        ...(nextPreviousStalls ? { next_previous_consecutive_stalls: nextPreviousStalls } : {}),
      })
    : undefined;
  const bottleneckFollowUp = primaryFinding.helperRequest
    ? deriveMathBottleneckFollowUp({
        finding: primaryFinding,
        sourceAssignmentId,
        sourceSlotId: primaryResearch.request.targetSlotId,
        forbiddenTargetSlotIds: sourceSlotIds,
        primaryObjective: nextObjective,
        primaryProbeKind,
        microWaveWidth,
      })
    : undefined;
  const nextAssignment = routeChangeRequired
    ? Object.freeze({
        kind: routeWaveWidth > 1 ? 'dispatch_route_wave' : 'dispatch_new_route',
        next_objective: nextObjective,
        ...(primaryResearch.request.result.math?.routeFingerprint
          ? { forbid_route_fingerprint: primaryResearch.request.result.math.routeFingerprint }
          : {}),
        ...(routeWaveWidth > 1
          ? {
              recommended_parallelism: routeWaveWidth,
              route_proposal_mode: 'candidate',
              require_distinct_route_fingerprints: true,
              require_distinct_route_mechanisms: true,
              require_decisive_test_per_route: true,
            }
          : {}),
        ...deriveMathStrategyContinuation({
          capability,
          sourceAssignmentId,
          sourceSlotId: primaryResearch.request.targetSlotId,
          forbiddenTargetSlotIds: [primaryResearch.request.targetSlotId],
          purpose: 'alternate_route',
        }),
      })
    : criticRequired
      ? Object.freeze({
          ...deriveMathCriticFollowUp({
            capability,
            sourceAssignmentId,
            sourceSlotId: primaryResearch.request.targetSlotId,
            forbiddenTargetSlotIds: sourceSlotIds,
            nextObjective,
          }),
          next_probe_kind: freshStrategySlotAvailable ? 'critique' : primaryProbeKind,
          ...(nextPreviousStalls ? { next_previous_consecutive_stalls: nextPreviousStalls } : {}),
        })
      : (obstructionAssignment ??
        bottleneckFollowUp ??
        Object.freeze({
          kind: 'dispatch_next_research_action',
          next_objective: nextObjective,
          next_probe_kind: primaryProbeKind,
          session_continuation: {
            sourceAssignmentId,
            mode: 'reuse_source_slot',
            purpose: 'candidate_repair',
          },
          required_target_slot_id: primaryResearch.request.targetSlotId,
          ...(nextPreviousStalls ? { next_previous_consecutive_stalls: nextPreviousStalls } : {}),
        }));
  const outputContracts = research
    .map(({ output }) => output.research_contract)
    .filter((value): value is Record<string, unknown> => isRecord(value))
    .map((value) => normalizeMathResearchProblemContract(value as MathResearchProblemContract));
  const fallbackResearchContract = mergeMathResearchWaveContract(
    outputContracts,
    findings,
    selectedIndices,
    nextObjective,
    evidence
  );
  const seedContract = sharedResearchContractSeed(outputContracts);
  const persisted = seedContract
    ? mutateMathematicsResearchContract({
        workspace,
        contract: seedContract,
        update: (baseContract) =>
          mergeMathResearchWaveContract([baseContract], findings, selectedIndices, nextObjective, evidence) ??
          baseContract,
      })
    : undefined;
  const researchContract = persisted?.researchContract ?? fallbackResearchContract;
  return Object.freeze({
    kind: 'math_research_wave_synthesis',
    stage: research[0].request.result.assignmentBinding?.stage,
    source_assignment_ids: Object.freeze(research.map(({ request }) => request.result.assignmentId)),
    selected_assignment_id: sourceAssignmentId,
    route_fingerprints: Object.freeze([
      ...new Set(research.map(({ request }) => request.result.math?.routeFingerprint).filter(Boolean)),
    ]),
    route_mechanisms: Object.freeze(
      routeDecisions.map((route) =>
        Object.freeze({
          route_fingerprint: route.routeFingerprint,
          mechanism: route.mechanismSignature,
        })
      )
    ),
    duplicate_mechanism_route_fingerprints: Object.freeze(
      routeDecisions
        .filter((route) => !route.routeRefuted && !mechanismWinners.includes(route))
        .map((route) => route.routeFingerprint)
    ),
    ...(selectedRoute ? { selected_route_fingerprint: selectedRoute.routeFingerprint } : {}),
    refuted_route_fingerprints: Object.freeze(
      routeDecisions.filter((route) => route.routeRefuted).map((route) => route.routeFingerprint)
    ),
    finding_count: findings.length,
    finding_kinds: Object.freeze([...new Set(findings.map((finding) => finding.kind))]),
    impacts: Object.freeze(impacts),
    selected_progress_kind: primaryProgressKind,
    mainline_decision: routeRefuted
      ? 'route_refuted'
      : mainlineAdvanced
        ? 'mainline_advanced'
        : obstructionRequired
          ? 'obstruction_synthesis'
          : replanRequired
            ? 'route_replan'
            : criticRequired && freshStrategySlotAvailable
              ? 'critic_required'
              : 'continue_research',
    next_objective: nextObjective,
    next_probe_kind: routeChangeRequired
      ? null
      : obstructionRequired
        ? 'obstruction'
        : criticRequired && freshStrategySlotAvailable
          ? 'critique'
          : primaryProbeKind,
    next_assignment: nextAssignment,
    ...(obstructionFinding
      ? {
          obstruction_evidence_refs: Object.freeze(obstructionFinding.evidenceRefs),
          obstruction_summary: obstructionFinding.summary,
        }
      : {}),
    evidence_refs: Object.freeze([...new Set(findings.flatMap((finding) => finding.evidenceRefs))]),
    ...(researchContract?.activeBottleneck ? { active_bottleneck: researchContract.activeBottleneck } : {}),
    ...(researchContract ? { research_contract: researchContract } : {}),
    ...(criticRequired && !freshStrategySlotAvailable ? { critic_deferred: 'no_compatible_fresh_strategy_slot' } : {}),
    ...(persisted?.researchContract ? { research_state_persisted: true } : {}),
  });
}

function deriveAssignmentAgentUsage(
  baseline: ResearchCoreAgentUsage | undefined,
  current: ResearchCoreAgentUsage | undefined
): ResearchCoreAgentUsage | undefined {
  if (!baseline || !current || baseline.measurement !== current.measurement) return undefined;
  if (baseline.measurement !== 'token_totals') return undefined;
  if (current.totalTokens < baseline.totalTokens) return undefined;
  const subtract = (after: number, before: number): number => Math.max(0, after - before);
  const cost =
    current.cost !== undefined && baseline.cost !== undefined && current.cost >= baseline.cost
      ? current.cost - baseline.cost
      : undefined;
  return Object.freeze({
    measurement: current.measurement,
    inputTokens: subtract(current.inputTokens, baseline.inputTokens),
    cachedInputTokens: subtract(current.cachedInputTokens, baseline.cachedInputTokens),
    outputTokens: subtract(current.outputTokens, baseline.outputTokens),
    reasoningOutputTokens: subtract(current.reasoningOutputTokens, baseline.reasoningOutputTokens),
    totalTokens: subtract(current.totalTokens, baseline.totalTokens),
    ...(current.contextWindowSize !== undefined ? { contextWindowSize: current.contextWindowSize } : {}),
    ...(cost !== undefined ? { cost } : {}),
  });
}

function shouldReadMathAgentUsage(
  result: ResearchTeamResult,
  sourceAssignment: ResearchTeamAssignment | undefined
): boolean {
  if (!result.math) return false;
  const stage = sourceAssignment?.math?.stage ?? result.assignmentBinding?.stage;
  // Formal proof progress is decided by the branch delta and kernel receipts;
  // token telemetry cannot change that decision. Avoid a Core metadata plus
  // usage round trip on every Lean episode, which otherwise sits directly on
  // the critical path before integration/reverification.
  if (stage === 'formalize') return false;
  if (!result.mathResearchFinding) return true;
  if (stage !== 'diversify') return true;
  const continuationPurpose = sourceAssignment?.math?.sessionContinuation?.purpose;
  return Boolean(continuationPurpose);
}

function latestMathematicsRoutePerformance(
  durableReceipt: ProjectGitResearchTeamAssignmentReceipt | undefined,
  statementHash: string | undefined,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[]
): NonNullable<MathDurableProgressCheckpoint['routePerformance']> {
  if (!statementHash) return Object.freeze([]);
  if (durableReceipt?.state === 'integrated') {
    return durableReceipt.mathProgress?.routePerformance ?? Object.freeze([]);
  }
  let latest = durableReceipt?.mathProgress?.statementHash === statementHash ? durableReceipt.mathProgress : undefined;
  for (const receipt of assignmentHistory) {
    const progress = receipt.mathProgress;
    if (
      receipt.assignmentId === durableReceipt?.assignmentId ||
      receipt.state !== 'integrated' ||
      progress?.statementHash !== statementHash ||
      (latest && progress.updatedAt <= latest.updatedAt)
    ) {
      continue;
    }
    latest = progress;
  }
  return latest?.routePerformance ?? Object.freeze([]);
}

function deriveIntegratedMathProgressControl(
  result: ResearchTeamResult,
  dispatchedAssignment: ResearchTeamAssignment | undefined,
  durableReceipt: ProjectGitResearchTeamAssignmentReceipt | undefined,
  assignmentElapsedMs: number | undefined,
  assignmentUsage: ResearchCoreAgentUsage | undefined,
  agentUsageSnapshot: ResearchCoreAgentUsage | undefined,
  outstandingAssignmentCount = 0,
  assignmentHistory: readonly ProjectGitResearchTeamAssignmentReceipt[] = []
): Readonly<Record<string, unknown>> | undefined {
  const math = result.math;
  const stage = result.assignmentBinding?.stage;
  if (!math || !stage) return undefined;
  const progressRequirements = (): Readonly<Record<string, unknown>> =>
    Object.freeze({
      schema: 'deepscientist.mathematics.progress-requirements.v1',
      requiredForAdvance:
        stage === 'formalize'
          ? Object.freeze([
              'close the active Lean goal or produce a strictly smaller proof frontier',
              'retain a kernel-checked helper/node receipt when only a dependency milestone closes',
            ])
          : Object.freeze([
              'add a trusted evidence reference, narrow or resolve the active bottleneck, or refute the route',
            ]),
      rootClosureRequired: true,
      helperOrScaffoldIsNotRootClosure: stage === 'formalize',
      onNoStateChange: 'change tactic, premise, proof node, or route; do not repeat an unchanged state',
    });
  const durableMath =
    isRecord(durableReceipt?.assignment) && isRecord(durableReceipt.assignment.math)
      ? durableReceipt.assignment.math
      : undefined;
  const durablePreviousStalls =
    Number.isSafeInteger(durableMath?.previousConsecutiveStalls) && Number(durableMath?.previousConsecutiveStalls) >= 0
      ? Number(durableMath?.previousConsecutiveStalls)
      : durableReceipt?.mathProgress && durableReceipt.mathProgress.outcome === 'stalled'
        ? durableReceipt.mathProgress.consecutiveStalls
        : undefined;
  const durablePreviousScaffoldOnlyStreak =
    durableReceipt?.mathProgress && Number.isSafeInteger(durableReceipt.mathProgress.scaffoldOnlyStreak)
      ? Number(durableReceipt.mathProgress.scaffoldOnlyStreak)
      : 0;
  if (result.mathResearchFinding) {
    const finding = normalizeMathResearchFinding(result.mathResearchFinding);
    const priorContract = dispatchedAssignment?.math?.researchContract;
    const trustedEvidence = durableReceipt ? readTrustedAssignmentMathEvidence(finding, durableReceipt) : [];
    const researchContract = priorContract
      ? applyMathResearchFinding(priorContract, finding, trustedEvidence)
      : undefined;
    const findingProgress = classifyMathResearchFindingProgress(
      finding,
      finding.mainlineImpact ?? 'stalled',
      priorContract,
      trustedEvidence
    );
    const mainlineProgressEligible = isMathResearchMainlineProgress(findingProgress.kind, finding, trustedEvidence);
    const inferredImpact =
      findingProgress.kind === 'route_refuted'
        ? 'route_refuted'
        : mainlineProgressEligible
          ? 'mainline_advanced'
          : findingProgress.kind === 'no_state_change'
            ? 'stalled'
            : 'supporting';
    const previousStalls = dispatchedAssignment?.math?.previousConsecutiveStalls ?? durablePreviousStalls ?? 0;
    const criticFeedback = dispatchedAssignment?.math?.sessionContinuation?.purpose === 'critic';
    const noMainlineProgress = inferredImpact === 'supporting' || inferredImpact === 'stalled';
    const routeRefuted = inferredImpact === 'route_refuted';
    const researchCostPressure = classifyMathResearchCostPressure(assignmentElapsedMs, assignmentUsage?.totalTokens);
    const stalledForControl = noMainlineProgress;
    const consecutiveStalls = stalledForControl
      ? criticFeedback && !routeRefuted
        ? previousStalls
        : previousStalls + 1
      : 0;
    const directive = routeRefuted ? 're_decompose' : 'continue_research';
    return Object.freeze({
      outcome: routeRefuted ? 'advanced' : stalledForControl ? 'stalled' : 'advanced',
      consecutive_stalls: consecutiveStalls,
      directive,
      next_stage: stage,
      workflow_stage: result.assignmentBinding?.workflowStage,
      next_objective: finding.bottleneckUpdate?.repair ?? finding.nextAction,
      next_probe_kind: inferMathResearchProbeKind(finding),
      research_finding_kind: finding.kind,
      research_finding_impact: inferredImpact,
      research_progress_kind: findingProgress.kind,
      research_progress_rank: findingProgress.rank,
      progress_signal: hasMathResearchProgressSignal(finding, trustedEvidence) ? 'present' : 'missing',
      ...(findingProgress.kind !== 'no_state_change' && !mainlineProgressEligible
        ? { progress_gate: 'supporting_without_evidence_or_bottleneck_change' }
        : {}),
      cost_pressure: researchCostPressure,
      probe_roi: deriveMathResearchProbeRoi({
        finding,
        priorContract,
        progressRank: findingProgress.rank,
        assignmentElapsedMs,
        tokensUsed: assignmentUsage?.totalTokens,
        consecutiveStalls,
        routeRefuted,
        novelStateCount: findingProgress.novelStateCount,
      }),
      ...(finding.bottleneckUpdate ? { bottleneck_update: finding.bottleneckUpdate } : {}),
      ...(researchContract?.activeBottleneck ? { active_bottleneck: researchContract.activeBottleneck } : {}),
      ...(criticFeedback && !routeRefuted ? { critic_feedback_ready: true } : {}),
      ...(stalledForControl && directive === 'continue_research'
        ? { next_previous_consecutive_stalls: consecutiveStalls }
        : {}),
      ...(researchContract ? { research_contract: researchContract } : {}),
      progress_requirements: progressRequirements(),
    });
  }
  const leanExecutionCount = math.wholeProofProbe ? 1 : 0;
  const baseState = updateMathProgressState(
    stage,
    dispatchedAssignment?.math?.previousConsecutiveStalls ?? durablePreviousStalls ?? 0,
    math,
    {
      ...(assignmentElapsedMs !== undefined ? { assignmentElapsedMs } : {}),
      ...(assignmentUsage ? { tokensUsed: assignmentUsage.totalTokens } : {}),
      leanExecutionCount,
    },
    {
      kernelReceiptBound:
        result.laneId !== 'lean-engineering' ||
        Boolean(result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt),
      requireKernelReceiptForPlanExpansion: result.laneId === 'lean-engineering',
      previousScaffoldOnlyStreak: durablePreviousScaffoldOnlyStreak,
    }
  );
  const previousProgressFingerprint =
    dispatchedAssignment?.math?.failureLedger?.progressFingerprint ?? durableReceipt?.mathProgress?.progressFingerprint;
  const repeatedProofState =
    math.routeDisposition === 'blocked' &&
    Boolean(math.progressFingerprint) &&
    math.progressFingerprint === previousProgressFingerprint;
  const state = repeatedProofState
    ? Object.freeze({
        ...baseState,
        outcome: 'stalled' as const,
        directive: 're_decompose' as const,
        nextStage: 'replan' as const,
        repeated_proof_state: true,
      })
    : baseState.outcome === 'stalled' &&
        baseState.progressKind !== 'foundation_progress' &&
        classifyResearchTeamMathProgress(result) === 'advanced'
      ? Object.freeze({
          ...baseState,
          outcome: 'advanced' as const,
          consecutiveStalls: 0,
          directive: 'continue_node' as const,
          nextStage: stage,
        })
      : baseState;
  const schedulePlan = math.planAfter ?? math.planBefore;
  const researchContextFingerprint = crypto
    .createHash('sha256')
    .update(
      JSON.stringify({
        source: math.sourceProgress?.candidateSourceHash,
        dependencies: schedulePlan?.planNodes
          .map((node) => ({
            id: node.id,
            status: node.status,
            dependsOn: [...node.dependsOn].sort(),
            evidence: [...node.evidenceRefs].sort(),
          }))
          .sort((a, b) => a.id.localeCompare(b.id)),
        evidence: math.evidenceDelta,
        research: dispatchedAssignment?.math?.researchContract,
        baseCommit: result.assignmentBinding?.baseCommit,
      })
    )
    .digest('hex');
  // Reconstruct one event per assignment. Summing persisted cumulative snapshots
  // would count earlier assignments repeatedly after each integration.
  let priorRoutePerformance: Parameters<typeof updateMathRoutePerformanceLedger>[0] = [];
  const routeAttemptDigests = new Set<string>();
  const seenAssignments = new Set<string>();
  for (const receipt of [...assignmentHistory].sort(
    (a, b) => (a.mathProgress?.updatedAt ?? 0) - (b.mathProgress?.updatedAt ?? 0)
  )) {
    const checkpoint = receipt.mathProgress;
    const delivered = receipt.delivery?.result as ResearchTeamResult | undefined;
    const eventMath = delivered?.math;
    if (
      receipt.assignmentId === result.assignmentId ||
      seenAssignments.has(receipt.assignmentId) ||
      receipt.state !== 'integrated' ||
      !checkpoint ||
      checkpoint.statementHash !== math.statementHash
    )
      continue;
    seenAssignments.add(receipt.assignmentId);
    for (const digest of checkpoint.routeAttemptDigests ?? []) routeAttemptDigests.add(digest);
    if (!eventMath) {
      for (const prior of checkpoint.routePerformance ?? []) {
        priorRoutePerformance = updateMathRoutePerformanceLedger(priorRoutePerformance, {
          routeFingerprint: prior.routeFingerprint,
          planNodeId: prior.planNodeId,
          progressClass:
            prior.goalProgressCount > 0
              ? 'goal_progress'
              : prior.frontierProgressCount > 0
                ? 'frontier_progress'
                : prior.scaffoldOnlyCount > 0
                  ? 'scaffold_progress'
                  : 'stalled',
          proofStateFingerprint: prior.bestProofStateFingerprint,
          researchContextFingerprint: prior.researchContextFingerprint,
        });
      }
      continue;
    }
    const nodeId = checkpoint.activePlanNodeId ?? 'root';
    const record = checkpoint.routePerformance?.find(
      (item) => item.routeFingerprint === checkpoint.routeFingerprint && item.planNodeId === nodeId
    );
    priorRoutePerformance = updateMathRoutePerformanceLedger(priorRoutePerformance, {
      routeFingerprint: checkpoint.routeFingerprint,
      planNodeId: nodeId,
      progressClass: inferMathRouteProgressClass(eventMath, checkpoint),
      proofStateFingerprint: checkpoint.proofStateFingerprint,
      failureCategory: checkpoint.failureCategory,
      researchContextFingerprint: record?.researchContextFingerprint,
    });
  }
  const routePerformance =
    durableReceipt?.state === 'integrated'
      ? (durableReceipt.mathProgress?.routePerformance ?? [])
      : updateMathRoutePerformanceLedger(priorRoutePerformance, {
          routeFingerprint: math.routeFingerprint,
          planNodeId: math.activePlanNodeId ?? 'root',
          progressClass: inferMathRouteProgressClass(math, state),
          researchContextFingerprint,
          ...(math.openGoalFingerprintAfter ? { proofStateFingerprint: math.openGoalFingerprintAfter } : {}),
          ...(math.failureCategory ? { failureCategory: math.failureCategory } : {}),
        });
  const routeAttemptDigest = mathAssignmentDuplicateDigest({
    statementHash: math.statementHash,
    planNodeId: math.activePlanNodeId ?? 'root',
    sourceHash: math.sourceProgress?.candidateSourceHash,
    goalFingerprint: math.openGoalFingerprintAfter,
    researchContextFingerprint,
  });
  for (const digest of durableReceipt?.mathProgress?.routeAttemptDigests ?? []) routeAttemptDigests.add(digest);
  routeAttemptDigests.add(routeAttemptDigest);
  const durableRouteAttemptDigests = [...routeAttemptDigests].slice(-512);
  const scheduleDecision = schedulePlan
    ? selectMathSchedule({
        plan: schedulePlan,
        statementHash: math.statementHash,
        routeFingerprint: math.routeFingerprint,
        sourceHash: math.sourceProgress?.candidateSourceHash,
        goalFingerprint: math.openGoalFingerprintAfter,
        researchContextFingerprint,
        activeAssignments: math.activePlanNodeId
          ? [
              {
                planNodeId: math.activePlanNodeId,
                statementHash: math.statementHash,
                sourceHash: math.sourceProgress?.candidateSourceHash,
                goalFingerprint: math.openGoalFingerprintAfter,
                status: 'running',
              },
            ]
          : [],
        progress: {
          ...(state.progressKind ? { progressKind: state.progressKind } : {}),
          ...(state.scaffoldOnlyStreak !== undefined ? { scaffoldOnlyStreak: state.scaffoldOnlyStreak } : {}),
        },
        routePerformance,
        completedAssignmentDigests: durableRouteAttemptDigests,
        lastEvidence: inferMathScheduleEvidence(math),
        availableSlots: Math.min(2, Math.max(1, schedulePlan.openFrontierNodeIds.length)),
      })
    : undefined;
  const effectiveDirective = state.directive;
  const effectiveNextStage = state.nextStage;
  const directAttempt = dispatchedAssignment?.math?.directAttempt === true || durableMath?.directAttempt === true;
  const directDeclarationClusterComplete =
    directAttempt && isDirectDeclarationClusterCompleteResult(result, dispatchedAssignment);
  const assignmentDeclaredComplete =
    directAttempt &&
    isSolverCompleteDirectResult(result, dispatchedAssignment) &&
    result.git.headCommit !== result.git.baseCommit &&
    Boolean(result.localGateReceipt || result.mathNodeReceipt || result.mathHelperReceipt);
  const completionDeferred = assignmentDeclaredComplete && outstandingAssignmentCount > 0;
  const solverDeclaredComplete = assignmentDeclaredComplete && !completionDeferred;
  const directRouteBlocked =
    directAttempt && result.disposition === 'blocked' && math.infraStatus === 'ready' && state.outcome === 'stalled';
  const resolvedDirective = solverDeclaredComplete
    ? 'solver_complete'
    : directRouteBlocked
      ? 're_decompose'
      : effectiveDirective;
  const resolvedNextStage = solverDeclaredComplete ? 'done' : directRouteBlocked ? 'replan' : effectiveNextStage;
  const sameCandidateRepair =
    directAttempt && !completionDeferred && !directDeclarationClusterComplete && resolvedDirective === 'continue_node';
  const tokenUsage = assignmentUsage
    ? Object.freeze({
        scope: 'assignment_delta',
        measurement: assignmentUsage.measurement,
        input_tokens: assignmentUsage.inputTokens,
        cached_input_tokens: assignmentUsage.cachedInputTokens,
        output_tokens: assignmentUsage.outputTokens,
        reasoning_output_tokens: assignmentUsage.reasoningOutputTokens,
        total_tokens: assignmentUsage.totalTokens,
        ...(assignmentUsage.cost !== undefined ? { cost: assignmentUsage.cost } : {}),
      })
    : undefined;
  const usageSnapshot = agentUsageSnapshot
    ? Object.freeze({
        measurement: agentUsageSnapshot.measurement,
        used: agentUsageSnapshot.totalTokens,
        ...(agentUsageSnapshot.contextWindowSize !== undefined ? { size: agentUsageSnapshot.contextWindowSize } : {}),
        ...(agentUsageSnapshot.cost !== undefined ? { cost: agentUsageSnapshot.cost } : {}),
      })
    : undefined;

  return Object.freeze({
    outcome: assignmentDeclaredComplete ? 'advanced' : state.outcome,
    consecutive_stalls: assignmentDeclaredComplete ? 0 : state.consecutiveStalls,
    directive: resolvedDirective,
    cost_pressure: state.costPressure,
    ...(state.progressKind ? { progress_kind: state.progressKind } : {}),
    ...(state.scaffoldOnlyStreak !== undefined ? { scaffold_only_streak: state.scaffoldOnlyStreak } : {}),
    route_performance: routePerformance,
    route_attempt_digests: durableRouteAttemptDigests,
    ...(scheduleDecision
      ? {
          schedule_decision: Object.freeze({
            topology: scheduleDecision.topology,
            selected_plan_node_ids: scheduleDecision.selectedPlanNodeIds,
            ready_plan_node_ids: scheduleDecision.readyPlanNodeIds,
            expected_information_gain: scheduleDecision.expectedInformationGain,
            reason: scheduleDecision.reason,
            duplicate_keys: scheduleDecision.duplicateKeys,
          }),
        }
      : {}),
    next_stage: resolvedNextStage,
    workflow_stage: result.assignmentBinding?.workflowStage,
    ...(solverDeclaredComplete
      ? {
          solver_declared_complete: true,
          external_evaluation_required: true,
          next_objective:
            'Submit the integrated unchanged commit to the external evaluator without another solver assignment.',
          lead_instruction:
            'The runtime must produce solver_ready_receipt for merged_commit before the outer evaluator is invoked. Do not emit a completion marker; after receiving the receipt, end the turn without validating, reviewing, checkpointing, dispatching, or calling another project tool.',
          prohibited_lead_actions: Object.freeze([
            'solver_redispatch',
            'canonical_validation',
            'review',
            'project_checkpoint',
          ]),
        }
      : {}),
    ...(completionDeferred
      ? {
          assignment_declared_complete: true,
          completion_deferred: true,
          outstanding_assignment_count: outstandingAssignmentCount,
          next_objective:
            'Wait for and integrate every outstanding assignment before declaring the full problem solved.',
          lead_instruction:
            'This assignment is closed, but the full problem is not complete. Do not emit the completion marker and do not redispatch this closed assignment. Wait for the outstanding deliveries and integrate them.',
        }
      : {}),
    ...(directDeclarationClusterComplete
      ? {
          declaration_cluster_complete: true,
          next_objective:
            'This declaration cluster is integrated. Select and dispatch the next dependency-ready or declaration-disjoint proof node; do not redispatch this closed assignment.',
          lead_instruction:
            'The custom activePlanNodeId declaration cluster is closed and merged, but the whole problem is not complete. Do not emit the completion marker or redispatch this assignment; select the next actionable proof node.',
        }
      : {}),
    ...(sameCandidateRepair ? { same_candidate_repair: true } : {}),
    ...(math.executionPolicy ? { execution_policy: math.executionPolicy } : {}),
    ...(directRouteBlocked ? { route_readiness_failed: true } : {}),
    ...(repeatedProofState
      ? {
          repeated_proof_state: true,
          next_objective: 'Switch to a structurally distinct route; the same proof frontier produced no new evidence.',
        }
      : {}),
    ...(resolvedDirective === 'continue_node' && state.outcome === 'stalled'
      ? { next_previous_consecutive_stalls: state.consecutiveStalls }
      : {}),
    assignment_elapsed_ms: assignmentElapsedMs ?? null,
    tokens_used: assignmentUsage?.totalTokens ?? null,
    ...(tokenUsage ? { token_usage: tokenUsage } : {}),
    ...(usageSnapshot ? { conversation_usage_snapshot: usageSnapshot } : {}),
    lean_execution_count: leanExecutionCount,
    progress_requirements: progressRequirements(),
  });
}

function classifyMathResearchCostPressure(
  assignmentElapsedMs: number | undefined,
  tokensUsed: number | undefined
): 'low' | 'meaningful' | 'high' {
  const elapsed = assignmentElapsedMs ?? 0;
  const tokens = tokensUsed ?? 0;
  if (tokens >= 15_000 || elapsed >= 15 * 60_000) return 'high';
  if (tokens >= 8_000 || elapsed >= 5 * 60_000) return 'meaningful';
  return 'low';
}

function deriveMathResearchProbeRoi(
  input: Readonly<{
    finding: MathResearchFinding;
    priorContract: MathResearchProblemContract | undefined;
    progressRank: number;
    assignmentElapsedMs: number | undefined;
    tokensUsed: number | undefined;
    consecutiveStalls: number;
    routeRefuted: boolean;
    novelStateCount: number;
  }>
): Readonly<Record<string, unknown>> {
  const { finding } = input;
  const probeKind = researchProbeKindForFinding(finding);
  const activeBottleneck = input.priorContract?.activeBottleneck;
  const probeHistory = (kind: MathResearchProbeKind) => {
    const summary = input.priorContract?.probeSummary?.find((entry) => entry.probeKind === kind);
    if (!summary || !activeBottleneck) return summary;
    return (
      summary.bottleneckStats?.find((entry) => entry.bottleneck === activeBottleneck) ??
      (!summary.bottleneckStats?.length ? summary : undefined)
    );
  };
  const priorProbe = probeHistory(probeKind);
  const value = input.routeRefuted
    ? 'route_eliminated'
    : input.progressRank >= 7
      ? 'bottleneck_resolved'
      : input.progressRank >= 4
        ? 'useful_state_change'
        : input.progressRank === 2
          ? 'evidence_only'
          : 'no_state_change';
  const nextProbePriority = input.routeRefuted
    ? 'switch_route'
    : priorProbe?.lastOutcome === 'no_state_change'
      ? 'switch_probe'
      : 'continue_same_bottleneck';
  const candidates = (
    [
      'literature',
      'example',
      'computation',
      'counterexample',
      'problem_family',
      'proof_step',
      'obstruction',
      'critique',
    ] as const
  )
    .map((kind) => {
      const history = probeHistory(kind);
      const attempts = history?.attempts ?? 0;
      return {
        kind,
        attempts,
        usefulChanges: history?.usefulChanges ?? 0,
        estimatedUsefulness: ((history?.usefulChanges ?? 0) + 1) / (attempts + 2),
      };
    })
    .sort(
      (a, b) => b.estimatedUsefulness - a.estimatedUsefulness || a.attempts - b.attempts || a.kind.localeCompare(b.kind)
    );
  return Object.freeze({
    probe_kind: probeKind,
    recommended_probe_kind:
      priorProbe?.lastOutcome === 'no_state_change'
        ? candidates.find((entry) => entry.kind !== probeKind)?.kind
        : inferMathResearchProbeKind(finding),
    probe_candidates: candidates,
    recommendation_basis: activeBottleneck
      ? 'Smoothed useful-change frequency for the active bottleneck; a decision aid, not a stopping rule.'
      : 'Smoothed observed useful-change frequency; a decision aid, not a stopping rule.',
    prior_attempts: priorProbe?.attempts ?? 0,
    prior_useful_changes: priorProbe?.usefulChanges ?? 0,
    prior_no_change: priorProbe?.noChange ?? 0,
    value,
    next_probe_priority: nextProbePriority,
    progress_rank: input.progressRank,
    novel_state_count: input.novelStateCount,
    evidence_count: finding.evidenceRefs.length,
    assignment_elapsed_ms: input.assignmentElapsedMs ?? null,
    tokens_used: input.tokensUsed ?? null,
  });
}

function researchTeamHeartbeatStatus(slot: ResearchCoreSlotState): string {
  if (slot.runtimeHealth) return 'unhealthy';
  if (slot.state === 'blocked') return 'blocked';
  if (slot.state === 'paused') return 'paused';
  if (slot.state === 'running') return slot.activeTurnSlow ? 'slow' : 'working';
  if (slot.state === 'queued' || slot.state === 'starting') return 'starting';
  return 'idle';
}

function describeCapability(capability: ResearchTeamToolCapability): Record<string, unknown> {
  const callerAgentId = teamAgentIdForSlotId(capability.slotId, capability.roster);
  if (!callerAgentId) throw new Error('Research Team caller is outside the authenticated roster');
  const caller = requireRosterMember(capability, capability.slotId);
  const boundImoContract = isBoundImoMathematicsWorkspace(capability);
  const base = {
    schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
    action: 'describe',
    status: 'available',
    profile_id: capability.profileId,
    workflow_id: capability.workflowId,
    role_id: capability.roleId,
    role_kind: capability.roleKind,
    team_id: capability.teamId,
    agent_id: callerAgentId,
    allowed_actions: capability.allowedActions,
  };
  if (capability.profileId === 'mathematics-research-team' && isMathLiteRunEnvironment(process.env)) {
    return {
      ...base,
      interaction_profile: 'math-lite-v1',
      reasoning_concurrency: capability.reasoningConcurrency,
      roster: capability.roster.map((member) => ({
        agent_id: teamAgentIdForSlotId(member.slotId, capability.roster),
        role_kind: member.roleKind,
        lane_id: member.laneId ?? null,
        display_name: member.displayName,
      })),
      contracts: Object.fromEntries(
        capability.allowedActions
          .filter((action) => action !== 'describe')
          .map((action) => [action, createMathematicsProtocolHelp(action, capability)])
      ),
      constraints: [
        'Use only the fields in the lite tool schema. Identity, source scope, commits and verification targets are host-owned.',
        'A share or feedback read is provisional evidence, never final verification.',
        'Retain the same proof assignment; dispatch only useful independent research to an available Worker.',
      ],
    };
  }
  return capability.roleKind === 'lead'
    ? {
        ...base,
        member_count: capability.roster.length,
        agent_limit: capability.agentLimit,
        total_slots: capability.agentLimit + 1,
        available_slots: Math.max(0, capability.agentLimit + 1 - capability.roster.length),
        reasoning_concurrency: capability.reasoningConcurrency,
        contracts: {
          assignment: {
            schema: RESEARCH_TEAM_ASSIGNMENT_SCHEMA,
            ...(capability.profileId === 'mathematics-research-team'
              ? {
                  enums: {
                    math_stage: MATH_PROOF_STAGES,
                    math_workflow_stage: MATH_WORKFLOW_STAGES,
                  },
                  mathematics_templates: {
                    ...(boundImoContract
                      ? {
                          proof_mainline_formalize: {
                            execution_mode: 'artifact',
                            math: { stage: 'formalize', workflowStage: 'formalization', directAttempt: true },
                            prerequisite:
                              'The Lead supplies one dependency-aware route plan. Dispatch exactly one Lean Worker for the complete candidate; runtime owns the evaluator and continuation workspace.',
                            required_math_context: ['routeFingerprint'],
                            runtime_hydrated_math_context: [
                              'statementHash',
                              'fastCheck',
                              'problemContract',
                              'alignmentCheck',
                              'activePlanNodeId',
                            ],
                          },
                          routed_formalize: {
                            execution_mode: 'artifact',
                            math: { stage: 'formalize', workflowStage: 'formalization' },
                            prerequisite:
                              'Select an independently assessed route whose four semantic checks pass. The runtime compiles and signs its terminal-composition preflight before dispatch.',
                            required_math_context: ['routeFingerprint', 'activePlanNodeId', 'routeAssessment'],
                            runtime_hydrated_math_context: [
                              'statementHash',
                              'fastCheck',
                              'problemContract',
                              'alignmentCheck',
                              'routeCards',
                              'routeSelection',
                              'routeProbeReceipt',
                            ],
                          },
                        }
                      : {
                          direct_formalize: {
                            execution_mode: 'artifact',
                            math: {
                              stage: 'formalize',
                              workflowStage: 'formalization',
                              directAttempt: true,
                            },
                            required_math_context: [
                              'statementHash',
                              'routeFingerprint',
                              'fastCheck',
                              'problemContract',
                              'alignmentCheck',
                              'activePlanNodeId',
                            ],
                          },
                        }),
                    route_candidate_after_stall: {
                      execution_mode: 'advisory',
                      math: {
                        stage: 'replan',
                        workflowStage: 'candidate',
                        routeProposalMode: 'candidate',
                      },
                      required_math_context: ['statementHash', 'routeFingerprint'],
                      inherited_from_matching_durable_assignment: ['fastCheck', 'problemContract', 'alignmentCheck'],
                    },
                  },
                }
              : {}),
            preferred_dispatch: {
              required: ['target_slot_id', 'task', 'base_commit', 'idempotency_key'],
              optional: [
                'role_template_id',
                'role_kind=xalpha|generic',
                'role_label',
                'role_instructions',
                'execution_mode=advisory|artifact',
                'math.{stage (internal execution action),workflowStage? (validated canonical lifecycle),statementHash,routeFingerprint,executionPolicy?,fastCheck?,directAttempt?,routeProposalMode=candidate?,routeAssessment? (preferred Lead-only input),activePlanNodeId?,routePattern?,previousConsecutiveStalls?,sessionContinuation?,researchContract?,problemContract?,alignmentCheck?,routeCards?,routeSelection?,proofState?,applicableLessons?,failureLedger?}',
                'math.fastCheck={statementHash,checkedAt,method,checkedCaseCount,outcome=no_counterexample_found|counterexample_found|inconclusive,candidateClaim=statement|negation,directAttemptRecommended:boolean,summary,evidenceRefs[],runtimeProbe?={expression,precondition?,cases[],mode=proposition|boolean,imports[],timeoutMs}}',
                'acceptance_criteria[]',
                'failure_criteria[]',
                'expected_artifacts[]',
              ],
              notes: [
                'The runtime derives assignmentId, workflowId, laneId, title, projectRoot, and bounded defaults.',
                'math.fastCheck.runtimeProbe runs only in a host-owned Lean workspace; its bounded result is evidence, never a kernel verdict or formal refutation.',
                'runtimeProbe.precondition is an optional function-like proposition for legal-input filtering; skipped samples are excluded from witness search and an all-skipped sweep is inconclusive.',
                'The target Worker always keeps its system-preconfigured role and authority. Optional role fields only specialize this assignment.',
                ...(capability.profileId === 'mathematics-research-team'
                  ? [
                      ...(boundImoContract
                        ? [
                            'This bound IMO adapter owns immutable statement identity, FAST_CHECK metadata, alignment, base commit, and runtime route preflight. In proof-mainline mode dispatch directAttempt=true to the sole Lean Worker after the Lead plan; the runtime reuses the same slot and workspace for repairs. Routed FORMALIZE remains available only for explicit non-mainline compatibility callers.',
                          ]
                        : []),
                      'For a route candidate after a stalled direct proof, use stage=replan, workflowStage=candidate, and routeProposalMode=candidate. On the preferred task path, the runtime reuses matching immutable FAST_CHECK, problemContract, and alignmentCheck from durable Team assignment history.',
                    ]
                  : []),
              ],
            },
            required: [
              'assignmentId',
              'workflowId',
              'laneId',
              'title',
              'objective',
              'acceptanceCriteria[]',
              'failureCriteria[]',
              'evidenceRefs[]',
              'doNotRepeat[]',
              'expectedArtifacts[]',
              'falsificationPlan.{hypothesis,test,failureSignal}',
              'git.{projectRoot,baseCommit}',
            ],
            optional: [
              'roleTemplateId',
              'roleKind=xalpha|generic',
              'roleLabel',
              'roleInstructions (at most 4000 characters)',
              'executionMode=advisory|artifact; omission keeps the strict artifact default',
              'math.{stage (internal execution action),workflowStage? (validated canonical lifecycle),statementHash,routeFingerprint,executionPolicy?,fastCheck?,directAttempt?,routeProposalMode=candidate?,activePlanNodeId?,routePattern?,previousConsecutiveStalls?,sessionContinuation?,researchContract?,problemContract?,alignmentCheck?,routeCards?,routeSelection?,proofState?,applicableLessons?,failureLedger?}',
              'math.fastCheck={statementHash,checkedAt,method,checkedCaseCount,outcome=no_counterexample_found|counterexample_found|inconclusive,candidateClaim=statement|negation,directAttemptRecommended:boolean,summary,evidenceRefs[],runtimeProbe?={expression,precondition?,cases[],mode=proposition|boolean,imports[],timeoutMs}}',
              'git.{goalId,routeNodeId,roadmapRevision} only when these references already exist in committed project state',
            ],
            dispatch_forbidden: ['git.branch', 'git.worktreePath', 'git.headCommit'],
            notes: [
              'baseCommit must be a full 40- or 64-character Git object id.',
              'math.fastCheck.runtimeProbe is host-executed bounded evidence; a witness may trigger a canonical-negation follow-up but cannot by itself produce refuted status.',
              'runtimeProbe.precondition filters samples that violate the declared domain; it never turns a bounded sweep into a universal claim.',
              'For artifact work the tool creates branch and worktree identities; never invent them. Advisory work creates neither.',
              'Choose an injected domain roleTemplateId when it fits, or create a bounded generic role with roleKind=generic, roleLabel, and roleInstructions.',
            ],
          },
          result: createResearchTeamResultContract(capability),
        },
        roster: capability.roster.map((member) => ({
          agent_id: teamAgentIdForSlotId(member.slotId, capability.roster) ?? null,
          role_id: member.roleId,
          role_kind: member.roleKind,
          lane_id: member.laneId ?? null,
          display_name: member.displayName,
        })),
        usage: {
          dispatch: `Prefer {target_slot_id, task, base_commit, idempotency_key}. Use roster agent_id values and send at most ${capability.reasoningConcurrency} independent assignments, one per idle Worker. Optional role fields specialize the task without replacing the Worker's system role. The complete assignment object remains available for advanced callers.`,
          status:
            'Use agent_id values to read a selected Worker list once at a meaningful transition. The runtime-derived heartbeat reports working, slow, blocked, unhealthy, or idle without asking Workers to emit progress calls.',
          integrate:
            'Send one deliveries list. For each Mathematics delivery, copy its integration_item unchanged; it already contains target_slot_id and exactly one durable delivery_id selector. Never combine delivery_id, assignment_id, and result in one item. Exact unchanged ResearchTeamResult objects remain a compatibility path. Mathematics integration items return runtime-owned math_progress_control. completion_deferred means the current assignment is closed but other accepted work must still be integrated, so do not redispatch it or emit a completion marker. solver_complete is returned only after no outstanding assignment remains and then produces solver_ready_receipt; terminate immediately after receiving that receipt, with no validation, review, checkpoint, dispatch, or other project call.',
        },
        constraints: [
          'All dispatch inputs are validated before any Worker receives work.',
          'A fresh Git task requires the exact baseCommit; projectRoot and role identity are supplied by the authenticated runtime.',
          'Artifact Workers commit evidence on isolated Git worktrees. Advisory Workers are read-only and return structured analysis without a branch.',
          'Worker delivery is event-driven. Do not poll unchanged status or reread unchanged project state.',
          ...(capability.profileId === 'mathematics-research-team'
            ? [
                'The Lead chooses research and formalization work from the available lanes. Reuse the active Lean assignment and its worktree for local repairs; do not create duplicate full-problem assignments.',
              ]
            : [
                'The first wave should use at most one Worker per distinct lane. Keep duplicate-lane slots idle until a delivery identifies a disjoint follow-up.',
              ]),
          ...(capability.profileId === 'mathematics-research-team'
            ? [
                'The Lead plan, Worker proof episode, and external evaluator are separate stages. Before assembly, bind one bounded semantic viability check to the route. A directAttempt owns the complete whole-contract claim and stays on that candidate while math_progress_control returns continue_node. Distinct advisory research may inform the active route. Use typed routed-proof prerequisites when changing to a routed plan; do not duplicate an active proof assignment.',
                'Proof-producing mathematics assignments pass a typed preflight for contract, FAST_CHECK, exact alignment, route/direct-attempt identity, and stage-specific plan or LOCAL_GATE state before dispatch. Bound IMO routed FORMALIZE additionally requires a signed runtime Lean route-composition receipt before any worktree or Core turn is created.',
                'A mathematics recovery checkpoint is required only at a pause/resume, route-change, or infrastructure-failure boundary; ordinary local stalls use runtime-owned progress.',
              ]
            : []),
        ],
      }
    : {
        ...base,
        lane_id: caller.laneId ?? null,
        contracts: { result: createResearchTeamResultContract(capability) },
        usage: {
          deliver:
            'Send one compact ResearchTeamResult using the execution mode and lane contract. Omit assignmentBinding and all other runtime_supplied fields; the server binds them from the durable assignment receipt.',
        },
        constraints: [
          'Do not dispatch, poll Team state, integrate branches, run canonical evaluation, checkpoint, or publish.',
          caller.laneId === 'lean-engineering'
            ? 'Commit artifact work on the assigned branch and return its full head commit.'
            : 'Advisory work is read-only, uses executionMode=advisory, and contains no invented Git delivery identity.',
        ],
      };
}

function requireWorker(capability: ResearchTeamToolCapability, slotId: string): ResearchTeamRosterMember {
  const target = requireRosterMember(capability, stableId(slotId, 'target_slot_id'));
  if (target.roleKind !== 'worker' || !target.laneId) {
    throw new ResearchTeamOrchestrationError('foreign_or_lead_slot', 'The target slot is not a Worker in this Team.');
  }
  return target;
}

function requireRosterMember(capability: ResearchTeamToolCapability, slotId: string): ResearchTeamRosterMember {
  const canonicalSlotId = resolveTeamAgentSlotId(slotId, capability.roster);
  const member = capability.roster.find((candidate) => candidate.slotId === canonicalSlotId);
  if (!member) throw new Error('The selected slot is outside this Research Team roster');
  return member;
}

function requireAction(value: unknown): ResearchTeamMcpAction {
  if (!RESEARCH_TEAM_MCP_ACTIONS.includes(value as ResearchTeamMcpAction)) {
    throw new Error('Research Team action is invalid');
  }
  return value as ResearchTeamMcpAction;
}

function gitNamespace(capability: ResearchTeamToolCapability): string {
  return capability.profileId === 'financial-factor-research'
    ? FACTOR_RESEARCH_GIT_NAMESPACE
    : stableGitSegment(capability.profileId);
}

function workerBranchPrefix(capability: ResearchTeamToolCapability, target: ResearchTeamRosterMember): string {
  return `deepscientist/agents/${gitNamespace(capability)}/${stableGitSegment(capability.teamId)}/${stableGitSegment(target.roleId)}/`;
}

function stableGitSegment(value: string): string {
  const normalized = value
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/gu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 36);
  if (!normalized) throw new Error('Research Team profile cannot form a Git namespace');
  return normalized;
}

function stableId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) throw new Error(`${field} is invalid`);
  return normalized;
}

function requiredRecord(value: unknown, field: string): Record<string, unknown> {
  if (!isRecord(value)) throw new Error(`${field} is required`);
  return value;
}

/**
 * The successor starts in a fresh conversation. Without the predecessor's own
 * blocked summary it spent minutes rediscovering the same route and retrying
 * the same failing calls (run 23). Only the Worker's public delivery text is
 * carried; it remains provisional and never a proof receipt.
 */
export function formatBlockedPredecessorHandoff(result: unknown): string {
  const delivery = isRecord(result) && isRecord(result.delivery) ? result.delivery : undefined;
  if (!delivery || delivery.status !== 'blocked') return '';
  const clip = (value: unknown, limit: number) =>
    typeof value === 'string' ? value.replace(/\s+/gu, ' ').trim().slice(0, limit) : '';
  const summary = clip(delivery.summary, 1200);
  const blockers = Array.isArray(delivery.blockers)
    ? delivery.blockers
        .map((blocker) => clip(blocker, 300))
        .filter(Boolean)
        .slice(0, 4)
    : [];
  if (!summary && !blockers.length) return '';
  return [
    ' Predecessor handoff (its own provisional report, not verified):',
    summary ? ` Summary: ${summary}` : '',
    blockers.length ? ` Open blockers: ${blockers.join(' | ')}` : '',
    ' Its RESEARCH.md is carried into your assigned source directory; read it there first. Do not repeat its failed routes or tool calls; start with the independent lemmas it identified.',
  ].join('');
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

/** Normalize opaque MCP subcontracts after the ACP tool layer exposes camelCase fields as snake_case. */
function normalizeResearchTeamWireRecord(input: Record<string, unknown>, label: string): Record<string, unknown> {
  const normalized: Record<string, unknown> = {};
  for (const [wireKey, rawValue] of Object.entries(input)) {
    const key = wireKey.replace(/_([a-z0-9])/gu, (_match, character: string) => character.toUpperCase());
    if (Object.prototype.hasOwnProperty.call(normalized, key)) {
      throw new Error(`${label} contains conflicting field aliases for ${key}`);
    }
    normalized[key] = Array.isArray(rawValue)
      ? rawValue.map((value, index) =>
          isRecord(value) ? normalizeResearchTeamWireRecord(value, `${label}.${key}[${index}]`) : value
        )
      : isRecord(rawValue)
        ? normalizeResearchTeamWireRecord(rawValue, `${label}.${key}`)
        : rawValue;
  }
  return normalized;
}

function requireClient(value: ResearchCoreTeamClient | undefined): ResearchCoreTeamClient {
  if (!value) throw new Error('Local Core client is unavailable for Research Team orchestration');
  return value;
}

function result(payload: Record<string, unknown>): ToolResult {
  return { content: [{ type: 'text', text: JSON.stringify(payload, null, 2) }] };
}

function errorResult(action: unknown, error: unknown, capability: ResearchTeamToolCapability): ToolResult {
  const repairableDelivery = error instanceof RepairableResearchTeamDeliveryError;
  const liteRecovery = error instanceof MathLiteDeliveryRecoveryError ? error.recovery : undefined;
  const inputIntegrityFailure =
    error instanceof MathRunInputsIntegrityError ||
    (error instanceof ResearchTeamOrchestrationError && error.code === 'math_run_inputs_integrity_failed');
  const leanEvalRepairRequest = repairableDelivery ? error.repairRequest : undefined;
  const protocolHelp =
    !inputIntegrityFailure && RESEARCH_TEAM_MCP_ACTIONS.includes(action as ResearchTeamMcpAction)
      ? createMathematicsProtocolHelp(action as ResearchTeamMcpAction, capability)
      : undefined;
  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify(
          {
            schema: RESEARCH_TEAM_TOOL_RESULT_SCHEMA,
            action: typeof action === 'string' ? action : null,
            status: 'unavailable',
            accepted: false,
            ...(error instanceof MathematicsDispatchValidationError
              ? { errors: error.issues }
              : error instanceof MathWireValidationError
                ? {
                    errors: error.issues.map((issue) =>
                      action === 'read_artifact'
                        ? {
                            ...issue,
                            path:
                              (
                                { ref: 'artifact_ref', offsetBytes: 'offset_bytes', maxBytes: 'max_bytes' } as Record<
                                  string,
                                  string
                                >
                              )[issue.path] ?? issue.path,
                            message:
                              issue.path === 'maxBytes'
                                ? 'Use an integer from 1 to 2048, or omit max_bytes. Continue with offset_bytes set to the returned nextOffsetBytes.'
                                : issue.path === 'offsetBytes'
                                  ? 'Use a nonnegative safe integer from the returned nextOffsetBytes, or omit offset_bytes for the first page.'
                                  : issue.message,
                          }
                        : issue
                    ),
                  }
                : {}),
            ...runInputsIntegrityDetails(inputIntegrityFailure ? 'math_run_inputs_integrity_failed' : undefined),
            ...(protocolHelp ? { help: protocolHelp } : {}),
            error: {
              code:
                error instanceof MathRunInputsIntegrityError
                  ? 'math_run_inputs_integrity_failed'
                  : error instanceof ResearchTeamOrchestrationError
                    ? error.code
                    : leanEvalRepairRequest
                      ? 'lean_eval_repair_required'
                      : 'research_team_request_invalid',
              message: error instanceof Error ? error.message : String(error),
              retryable: error instanceof ResearchTeamOrchestrationError ? error.retryable : repairableDelivery,
            },
            ...(liteRecovery ? { recovery: liteRecovery } : {}),
            ...(repairableDelivery
              ? {
                  ...(leanEvalRepairRequest ? { repair_request: leanEvalRepairRequest } : {}),
                  ...(protocolHelp ? {} : { result_contract: createResearchTeamResultContract(capability) }),
                  recovery: {
                    action: 'deliver',
                    instruction: leanEvalRepairRequest
                      ? 'Keep the current Lean-Eval solver episode in this Worker conversation. Resolve the first diagnostic in repair_request without resubmitting a rejected candidate hash. When the diagnostic is forbidden proof markers in Submission.lean and the whole theorem is still open, revert Submission.lean to the retained baseline and commit only a new verified helper under Submission/**/*.lean so the helper checkpoint can be accepted; do not deliver a full candidate that still contains sorry/admit. If the same source bytes and the same first Lean diagnostic occur twice without a changed proof-state fingerprint, stop running probes and deliver one structured blocked boundary using disposition=blocked, action=refute_route, math.routeDisposition=reject, math.infraStatus=ready, positive openGoalCountBefore/openGoalCountAfter, openGoalAfter, nextSingleObjective, and math.evidenceDelta:[{kind:"route_refutation",ref:"<exact missing declaration or dependency>",summary:"<why this route is rejected and the next constructive dependency>"}]. Include the full committed git.headCommit. Do not send only action=refute_route or a prose summary. The runtime will wake the Lead only after valid progress, a blocked boundary, infrastructure failure, or cancellation.'
                      : 'Keep the current solver episode in this same Worker conversation. Make the stated correction or one concrete non-duplicate repair, then call deliver again; this is not an outer assignment retry and must not wake the Lead until the episode has a valid boundary. Stop only if the same validation error repeats after its stated correction or a non-retryable runtime error occurs.',
                  },
                }
              : {}),
          },
          null,
          2
        ),
      },
    ],
    isError: true,
  };
}

function runInputsIntegrityDetails(code: string | undefined) {
  return code === 'math_run_inputs_integrity_failed'
    ? {
        errors: [
          {
            path: '$',
            code: 'integrity',
            message: 'Run inputs changed. Stop this run; do not repair through model tool arguments.',
          },
        ],
      }
    : {};
}

const DEFAULT_PROJECT_GIT_DRIVER: ResearchTeamProjectGitDriver = Object.freeze({
  prepareAgentWorktree: prepareProjectGitAgentWorktree,
  resolveCommit: resolveProjectGitCommit,
  isCommitAncestor: isProjectGitCommitAncestor,
  discardAgentWorktree: discardProjectGitAgentWorktree,
  integrateAgentBranch: integrateProjectGitAgentBranch,
  recordResearchTeamAssignment: recordProjectGitResearchTeamAssignment,
  recordResearchTeamDelivery: recordProjectGitResearchTeamDelivery,
  recordResearchTeamBudgetCancellation: recordProjectGitResearchTeamBudgetCancellation,
  recordResearchTeamSupersessionPending: recordProjectGitResearchTeamSupersessionPending,
  readResearchTeamAssignment: readProjectGitResearchTeamAssignment,
  listResearchTeamAssignments: listProjectGitResearchTeamAssignments,
  completeResearchTeamAssignment: completeProjectGitResearchTeamAssignment,
  supersedeResearchTeamAssignment: supersedeProjectGitResearchTeamAssignment,
});
