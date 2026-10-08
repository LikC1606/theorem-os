import { createMathPortfolioToolInput, mathPortfolioToolActions } from "./mathPortfolioToolInput";
import { bindMathToolAssignment, withMathToolRecovery } from "../math/mathToolInteraction";
import { projectRuntimeMathAssignmentToExecutionView } from "../math/mathAssignmentExecutionAdapter";
import {
  mathSynthesisInputSchema,
  mathWorkspaceActions,
  mathWorkspaceActionContract,
} from "../common/chat/team/mathToolContract";
import { collectMathCheckedProofSupport } from "../math/mathProofEfficiencyExecution";
import { executeMathSynthesis } from "../math/mathConjectureSynthesisRuntime";
/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { compactMathLeanProbeResponse, enrichMathLeanCheckpoint } from "../math/mathLeanCheckpoint";
import { isMathPlanningSafetyError } from "../math/mathPlanningContext";
import { createMathToolTiming } from "../math/mathDiagnostics";
import { lockIsFresh, lockOwnerRecord, lockOwnerState } from "../shared/services/lockOwnerLiveness";
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { z } from 'zod';
import {
  PROJECT_WORKSPACE_ENV_KEYS,
  PROJECT_WORKSPACE_TOOL_NAME,
  requiresResearchStrategyForCheckpoint,
} from "../common/chat/projectWorkspace";
import { LOOP_GOAL_ENV_KEYS } from "../common/chat/loopGoal";
import {
  FINANCIAL_FACTOR_PORTFOLIO_PATH,
  FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID,
  readFinancialFactorPortfolio,
} from "../common/chat/financialFactor";
import {
  FINANCE_ARTIFACT_KINDS,
  FINANCE_TOOL_RECEIPT_SCHEMA,
  buildStructuredReportCardAuthoringGuide,
  financeArtifactMetadataSchema,
  financeCompletionManifestSchema,
  getFinanceTaskContract,
  materializeStructuredReportCardDrafts,
  preflightFinanceCompletion,
  readFinanceArtifactKind,
  readFinanceArtifactMetadata,
  validateStructuredReportCards,
  type FinanceCompletionManifest,
  type FinanceCompletionPreflightResult,
  type FinanceToolRequirementCondition,
  type FinanceToolReceipt,
  type StructuredReportCard,
  type StructuredReportCardDraftContext,
} from "../common/chat/finance/index";
import { normalizeProjectGitDirectionDecision, normalizeResearchStrategy } from "../common/chat/researchStrategy";
import {
  buildResearchRoutePresentation,
  readResearchRouteMap,
  reviewScienceReportVisuals,
  RESEARCH_ROUTE_ARTIFACT_ID,
  SCIENCE_REPORT_VISUAL_ROLES,
  SCIENCE_EVENT_SCHEMA,
  SCIENCE_PANEL_SCHEMA,
  validateResearchRouteBranchSelection,
  validateResearchRouteMap,
  type ResearchRouteMap,
  type ResearchRoutePresentation,
  type ScienceArtifact,
  type ScienceArtifactAction,
  type ScienceArtifactEvent,
  type ScienceArtifactGitRef,
  type ScienceArtifactMemoryEvent,
  type ScienceArtifactPage,
  type ScienceArtifactResourceKind,
  type ScienceArtifactSnapshotIncludePath,
  type ScienceOptimizationArtifactMetadata,
  type ScienceOptimizationCandidateQuality,
  type ScienceOptimizationDispatchDecision,
  type ScienceOptimizationDispatchTarget,
  type ScienceOptimizationFusionEvidence,
  type ScienceOptimizationFailureClass,
  type ScienceOptimizationLessonCapsule,
  type ScienceOptimizationMetric,
  type ScienceOptimizationRoute,
  type ScienceOptimizationStabilityAssessment,
  type ScienceOptimizationStrongestAlternative,
  type ScienceOptimizationTaskScope,
  type ScienceClaim,
  type ScienceClaimVerification,
  type ScienceEvidenceItem,
  type ScienceGraphWarning,
  type ScienceGitLineAnchor,
  type SciencePanelData,
  type ScienceProvenanceEdge,
  type ScienceProvenanceNode,
  type ScienceReportBlock,
  type ScienceReportVisualRole,
  type ScienceResultSummaryBlock,
  type ScienceResultSummaryFact,
  type ScienceResultSummaryMetric,
  type ScienceSkillUse,
  type ScienceSourceGitRef,
} from "../common/chat/science";
import {
  collectReportChartEvidenceIds,
  collectReportChartMarkCoverage,
  REPORT_CHART_SCHEMA_V1,
  REPORT_CHART_SCHEMA_V2,
  validateReportChartSpec,
} from "../common/chat/reportChart";
import type {
  ProjectGitDomain,
  ProjectGitMetricContext,
  ProjectGitPerformanceMetric,
  ProjectGitResearchStageReceipt,
  ProjectGitWorkspaceBinding,
} from "../common/types/office/preview";
import {
  inspectTargetDiscoveryPortfolio,
  readTargetDiscoveryPortfolio,
  summarizeTargetDiscoveryPortfolio,
  TARGET_DISCOVERY_PORTFOLIO_ARTIFACT_ID,
  TARGET_DISCOVERY_PORTFOLIO_PATH,
  type TargetDiscoveryPortfolio,
} from "../common/chat/targetDiscovery";
import {
  MATHEMATICS_EVENT_SCHEMA,
  MATHEMATICS_PORTFOLIO_ARTIFACT_ID,
  MATHEMATICS_PORTFOLIO_PATH,
  MATHEMATICS_PORTFOLIO_SCHEMA,
  MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
  MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH,
  MATHEMATICS_VERIFICATION_TRACE_PATH,
  MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
  buildInitialMathematicsPortfolio,
  deriveMathematicsFeasibilityRanking,
  deriveMathematicsPromptPack,
  deriveMathematicsReusablePremises,
  rankMathFeasibilityCandidates,
  getMathematicsTerminalGateReadiness,
  normalizeValidatedMathematicsPortfolio,
  readMathematicsPortfolio,
  readMathematicsVerificationTrace,
  validateMathematicsPortfolio,
  type MathematicsPortfolio,
  type MathematicsVerificationCapability,
  type MathematicsVerificationEvent,
  type MathematicsVerificationEventKind,
  type MathematicsVerificationEventPayloadMap,
  type MathematicsVerificationTrace,
} from "../common/chat/mathematics";
import { SCIENCE_ARTIFACT_ENV_KEYS } from "../common/config/scienceArtifactMcpEnv";
import {
  canonicalMathProblemNegationPayload,
  canonicalMathProblemStatementPayloads,
  isMathFoundationalLeanAxiom,
  normalizeMathLocalGateReceipt,
  normalizeMathOfficialGateReceipt,
  normalizeMathProblemContract,
  normalizeMathRouteFingerprint,
  normalizeMathRouteCard,
  type MathCandidateReview,
  type MathLocalGateReceipt,
  type MathOfficialProblemManifest,
  type MathOfficialGateReceipt,
  type MathProblemContract,
} from "../common/types/team/mathematicsTeam";
import {
  assertResearchTeamToolActionAuthorized,
  readResearchTeamToolPolicy,
  researchTeamAuthorizedToolActions,
} from "../common/types/team/researchTeamToolPolicy";
import { isPlausibleLocalFileReference } from "../common/utils/localFileReference";
import {
  commitScienceArtifactSnapshot,
  ensureScienceProject,
  readScienceArtifactGitLines,
  readScienceArtifactRunSnapshot,
  searchScienceArtifactEvidenceIndex,
} from "../shared/services/scienceArtifactGitStore";
import {
  commitLoadedTargetDiscoveryImport,
  loadTargetDiscoveryImport,
  readTargetDiscoveryProjectPortfolio,
  reconcileTargetDiscoveryProject,
} from "../shared/services/targetDiscoveryImport";
import { BUILTIN_SCIENCE_ARTIFACT_NAME } from "./constants";
import {
  PROJECT_WORKSPACE_TOOL_DESCRIPTION,
  SCIENCE_ARTIFACT_FULL_CONTRACT,
  SCIENCE_ARTIFACT_TOOL_DESCRIPTION,
  FORMAL_VERIFIER_TOOL_DESCRIPTION,
  LEAN_WORKSPACE_TOOL_DESCRIPTION,
  MATHEMATICS_PORTFOLIO_TOOL_DESCRIPTION,
} from "./scienceArtifactPrompt";
import {
  activateProjectGitResearchBranch,
  cloneProjectGit,
  compareProjectGitResearchBranches,
  createProjectGitCheckpoint,
  discoverProjectGit,
  getProjectGitBlob,
  getProjectGitWorkingTree,
  listProjectGitGraph,
  listProjectGitResearchFrontier,
  listProjectGitResearchTeamAssignments,
  prepareProjectGitResearchBranch,
} from "../project-git/index";
import {
  checkManyFormalVerifications,
  findCachedFormalVerificationReceipt,
  findCachedFormalVerificationReceipts,
  hashMathFormalSourceDeclaration,
  inspectLeanDeclarations,
  inspectFormalVerifierCapability,
  readMathematicsReceiptSecret,
  runFormalVerification,
  runOfficialComparator,
  signMathOfficialGateReceipt,
  verifyMathCandidateReview,
  verifyMathOfficialGateReceipt,
  type MathematicsVerifierBatchItem,
  type MathematicsVerifierBatchResult,
  type MathematicsVerifierResult,
} from "../math/index";
import {
  fetchLeanEvalLeaderboardCredits,
  findLeanEvalCatalogProblem,
  readLeanEvalCatalog,
  LEAN_EVAL_BENCHMARK_COMMIT,
  LEAN_EVAL_REPOSITORY_URL,
} from "../math/leanEvalCatalogAdapter";
import {
  analyzeLeanEvalProblem,
  runLeanEvalSandboxedElaborationProbe,
  runLeanEvalSandboxedCompileProbe,
} from "../math/leanEvalProblemAnalyzer";
import { runLeanEvalLeanProbe } from "../math/leanEvalLeanProbe";
import { runLeanEvalCounterexampleProbe } from "../math/leanEvalCounterexampleProbe";
import {
  materializeLeanEvalProblemBinding,
  prepareLeanEvalProblemBinding,
} from "../math/leanEvalAdapter";
import {
  rankUpstreamLeanPremises,
  retrieveLeanPremisesForFailure,
  searchUpstreamLeanPremises,
} from "../math/upstreamPremiseSearch";
import { validateLeanPremiseCandidates } from "../math/leanEvalPremiseValidation";
import {
  createLeanEvalIntakeReceipt,
  paginateLeanEvalAnalyses,
  persistLeanEvalIntakeReceipt,
  readCachedLeanEvalAnalysis,
  writeCachedLeanEvalAnalysis,
} from "../math/leanEvalIntake";
import { bootstrapLeanEvalProblem, runPersistedLeanEvalOfficialGate } from "../math/leanEvalBootstrap";
import { findLeanEvalTeamReceipt } from "../math/leanEvalTeamWorkspace";
import {
  readLeanEvalOutcomeLedgerRevision,
  readLeanEvalOutcomeSummary,
} from "../math/leanEvalOutcomeLedger";
import {
  readLeanProjectCompatibility,
  searchUpstreamLeanPackages,
} from "../math/upstreamPackageSearch";
import {
  adoptUpstreamLeanPackage,
  adoptUpstreamLeanPackages,
} from "../math/leanDependencyAdoption";
import {
  searchInstalledLeanPackagePremises,
  validateInstalledLeanPremiseHeaders,
} from "../math/installedPackageSearch";
import { searchMathRetrievalCorpus } from "../math/mathRetrievalCorpus";
import {
  isMathLiteRunEnvironment,
  MATH_RUN_INPUTS_ENV,
  readMathRunRetrievalCorpus,
  verifyMathRunInputs,
} from "../math/mathRunInputs";
import {
  isMathPathWithin,
  readMathRunBinding,
  resolveMathRunProjectPaths,
} from "../math/mathRunBinding";
import { isMathWorkerOwnedRoot, selectMathWorkerProbeScope } from "../math/mathWorkerProbeScope";
import { readMathRunHistoryIdentity } from "../math/mathRunHistory";
import { isAllowedMathProofSource } from "../math/mathProofSourcePolicy";
import { signMathResearchObservation } from "../math/mathResearchEvidence";
import {
  prepareMathRouteRefutationTarget,
  verifyMathRouteRefutation,
} from "../math/mathRouteRefutation";
import {
  resolveMathSearchPlan,
  runMathWorkerProofAction,
  type MathValidatedGoalView,
} from "../math/mathWorkerProofSession";
import { readMathResearchPolicy } from "../math/mathResearchPolicy";
import { assertMathMcpRunning, installMathMcpShutdown } from "../math/mathMcpShutdown";
import { leanSourceProbeInput, runLeanSourceProbe } from "../math/leanSourceProbe";
import {
  readMathResearchWorkflowState,
  updateMathResearchWorkflow,
} from "../math/mathResearchWorkflow";
import { canonicalMathJson, mathDigest } from "../math/mathRuntimeIo";
import {
  resolveMathAssignmentContext,
  resolveMathAssignmentProofSource,
  resolveMathAssignmentProbeSource,
  type MathAssignmentContext,
} from "../math/mathAssignmentContext";
import { resolveResearchTeamRuntimeCapability } from "../team/toolCapability";
import { mathExplorationInput, verifyMathExploration } from "../math/mathExploration";
import {
  assertMathRunPortfolioOrigin,
  assertMathRunPortfolioPremises,
  bindMathRunPortfolio,
} from "../math/mathRunPortfolio";
import {
  readFinanceReceiptSecret,
  signFinanceToolReceipt,
  verifiedFinanceReceiptIds,
} from "../shared/services/finance/receiptAttestation";

type JsonRecord = Record<string, unknown>;
type TargetRef = {
  kind?: ScienceArtifactResourceKind;
  id?: string;
  version?: number;
  pageId?: string;
};

type AnnotationRecord = {
  id: string;
  runId: string;
  artifactId?: string;
  pageId?: string;
  text: string;
  region?: JsonRecord;
  gitAnchor?: ScienceGitLineAnchor;
  status: 'open' | 'resolved';
  createdAt: number;
  revision: string;
};

type ScienceCommandReceipt = {
  id: string;
  requestHash: string;
  response: JsonRecord;
  createdAt: number;
};

export type ScienceRunState = {
  runId: string;
  conversationId?: string;
  messageId?: string;
  toolCallId?: string;
  projectRoot?: string;
  question: string;
  summary?: string;
  status: SciencePanelData['status'];
  report?: SciencePanelData['report'];
  /** Internal only: never expose the reason in report prose or the public panel. */
  visualWaiverReason?: string;
  cards: StructuredReportCard[];
  cardDiagnostics: string[];
  financeCompletion?: FinanceCompletionManifest;
  financePreflight?: SciencePanelData['financePreflight'];
  statsPatch?: Partial<SciencePanelData['stats']>;
  evidence: Map<string, ScienceEvidenceItem>;
  artifacts: Map<string, ScienceArtifact>;
  pages: Map<string, ScienceArtifactPage>;
  claims: Map<string, ScienceClaim>;
  provenance: Map<string, ScienceProvenanceNode>;
  edges: Map<string, ScienceProvenanceEdge>;
  graphWarnings: Map<string, ScienceGraphWarning>;
  usedSkills: Map<string, ScienceSkillUse>;
  annotations: Map<string, AnnotationRecord>;
  commandReceipts: Map<string, ScienceCommandReceipt>;
  memory: ScienceArtifactMemoryEvent[];
  events: ScienceArtifactEvent[];
  git?: ScienceArtifactGitRef;
  sourceGit?: ScienceSourceGitRef;
  mathematicsVerification?: MathematicsVerifierResult;
  mathematicsVerifications: MathematicsVerifierResult[];
  mathematicsVerificationEvents: MathematicsVerificationEvent[];
  mathematicsVerificationCapability?: MathematicsVerificationCapability;
  mathematicsOfficialGateReceipts: MathOfficialGateReceipt[];
  mathematicsReview?: JsonRecord;
  createdAt: number;
  updatedAt: number;
};

const runs = new Map<string, ScienceRunState>();

const jsonText = (value: unknown) => ({
  content: [{ type: 'text' as const, text: JSON.stringify(value, null, 2) }],
});

const jsonStructured = <T extends JsonRecord>(value: T) => ({
  content: [{ type: 'text' as const, text: JSON.stringify(value, null, 2) }],
  structuredContent: value,
});

const now = (): number => Date.now();
const revision = (): string => `rev_${Date.now().toString(36)}_${crypto.randomBytes(4).toString('hex')}`;
const eventId = (): string => `sci_evt_${Date.now().toString(36)}_${crypto.randomBytes(3).toString('hex')}`;
const runId = (): string => `sci_run_${Date.now().toString(36)}_${crypto.randomBytes(3).toString('hex')}`;
const makeId = (kind: ScienceArtifactResourceKind): string =>
  `sci_${kind}_${Date.now().toString(36)}_${crypto.randomBytes(3).toString('hex')}`;
const artifactKey = (id: string, version = 1): string => `${id}@${version}`;
const writeProjectManifest = (): boolean => process.env[SCIENCE_ARTIFACT_ENV_KEYS.writeProjectManifest] !== 'false';

const leanEvalCompileProbeLimit = (): number => {
  const configured = Number.parseInt(process.env.DEEPSCIENTIST_LEAN_EVAL_COMPILE_PROBE_LIMIT ?? '4', 10);
  return Number.isSafeInteger(configured) ? Math.max(0, Math.min(16, configured)) : 4;
};

const mapWithConcurrency = async <T, R>(
  values: readonly T[],
  limit: number,
  worker: (value: T, index: number) => Promise<R> | R
): Promise<readonly R[]> => {
  const results = Array<R>(values.length);
  let cursor = 0;
  const run = async (): Promise<void> => {
    while (true) {
      const index = cursor++;
      if (index >= values.length) return;
      results[index] = await worker(values[index]!, index);
    }
  };
  await Promise.all(Array.from({ length: Math.max(1, Math.min(limit, values.length || 1)) }, () => run()));
  return Object.freeze(results);
};

// Session bindings are process-local MCP context, not process-wide mutable
// environment state.  Keeping updates in this map prevents a future shared
// MCP runtime from leaking one conversation's workspace or loop-goal identity
// into another conversation.
const sessionContext = new Map<string, string>();
let sessionContextOwnerConversationId: string | undefined;

const sessionEnvValue = (key: string): string | undefined => {
  const value = (sessionContext.get(key) ?? process.env[key])?.trim();
  return value || undefined;
};

const setSessionEnvValue = (key: string, value: string | undefined): void => {
  const normalized = value?.trim();
  if (key === AIONUI_CONVERSATION_ID_ENV_KEY || key === PROJECT_WORKSPACE_ENV_KEYS.conversationId) {
    if (normalized && sessionContextOwnerConversationId && sessionContextOwnerConversationId !== normalized) {
      throw new Error(
        'This Science Artifact MCP process is already bound to another conversation; start a fresh process for a new workspace.'
      );
    }
    if (normalized) sessionContextOwnerConversationId = normalized;
  }
  if (normalized) sessionContext.set(key, normalized);
  else sessionContext.delete(key);
};

const AIONUI_BASE_URL_ENV_KEY = 'AIONUI_BASE_URL';
const AIONUI_CONVERSATION_ID_ENV_KEY = 'AIONUI_CONVERSATION_ID';

const provisionalConversationIdPattern = /^(?:lab_skill|loop_goal|target|math|lark_project|project)_[A-Za-z0-9_-]+$/u;

const normalizedPathIdentity = (value: string): string => {
  const resolved = path.resolve(value);
  return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
};

const resolveSessionProjectRoot = (requested?: string): string | undefined => {
  const bound = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectRoot);
  if (bound && requested && normalizedPathIdentity(bound) !== normalizedPathIdentity(requested)) {
    throw new Error('projectRoot does not match the workspace bound to this conversation.');
  }
  return bound || requested;
};

const runtimeOwnerConversationId = (): string | undefined =>
  sessionEnvValue(AIONUI_CONVERSATION_ID_ENV_KEY) || sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.conversationId);

const resolveSessionIdentifier = (requested: string | undefined, envKey: string, label: string): string | undefined => {
  const configured = sessionEnvValue(envKey);
  const runtimeOwner =
    envKey === PROJECT_WORKSPACE_ENV_KEYS.conversationId ? sessionEnvValue(AIONUI_CONVERSATION_ID_ENV_KEY) : undefined;
  const bound = runtimeOwner || configured;
  if (bound && requested && bound !== requested) {
    if (
      envKey === PROJECT_WORKSPACE_ENV_KEYS.conversationId &&
      provisionalConversationIdPattern.test(bound) &&
      !provisionalConversationIdPattern.test(requested)
    ) {
      return requested;
    }
    throw new Error(`${label} does not match the value bound to this conversation.`);
  }
  return bound || requested;
};

const projectBindingBackendBaseUrl = (): string | undefined => {
  const configured = sessionEnvValue(AIONUI_BASE_URL_ENV_KEY);
  if (configured) {
    let parsed: URL;
    try {
      parsed = new URL(configured);
    } catch {
      throw new Error('The runtime supplied an invalid Core base URL for project binding recovery.');
    }
    if (!['127.0.0.1', 'localhost', '[::1]'].includes(parsed.hostname)) {
      throw new Error('Project binding recovery only accepts a loopback Core endpoint.');
    }
    return parsed.origin;
  }
  const port =
    sessionEnvValue('DEEPSCIENTIST_BACKEND_PORT') ||
    sessionEnvValue('AIONUI_BACKEND_PORT') ||
    sessionEnvValue('BACKEND_PORT');
  return port && /^\d+$/u.test(port) ? `http://127.0.0.1:${port}` : undefined;
};

const readAuthoritativeConversation = async (conversationId: string): Promise<JsonRecord> => {
  const baseUrl = projectBindingBackendBaseUrl();
  if (!baseUrl) {
    throw new Error(
      'Project workspace binding is unavailable because this MCP process received neither a bound project root nor a Core endpoint.'
    );
  }
  let response: Response;
  try {
    response = await fetch(`${baseUrl}/api/conversations/${encodeURIComponent(conversationId)}`);
  } catch (error) {
    throw new Error(
      `Project workspace binding could not be recovered from Core: ${error instanceof Error ? error.message : String(error)}`
    );
  }
  if (!response.ok) {
    throw new Error(`Project workspace binding could not be recovered from Core (HTTP ${response.status}).`);
  }
  const parsed = (await response.json()) as unknown;
  const conversation = isRecord(parsed) && isRecord(parsed.data) ? parsed.data : parsed;
  if (!isRecord(conversation) || asString(conversation.id) !== conversationId) {
    throw new Error('Core returned an invalid conversation while recovering the project workspace binding.');
  }
  return conversation;
};

const persistProjectBindingToCore = async (
  conversationId: string,
  binding: ProjectGitWorkspaceBinding
): Promise<boolean> => {
  const baseUrl = projectBindingBackendBaseUrl();
  if (!baseUrl) return false;
  const response = await fetch(`${baseUrl}/api/conversations/${encodeURIComponent(conversationId)}`, {
    method: 'PATCH',
    headers: { 'content-type': 'application/json' },
    body: JSON.stringify({ extra: { project_git: binding }, merge_extra: true }),
  });
  if (!response.ok) {
    throw new Error(
      `The cloned workspace was created, but Core rejected the conversation binding (HTTP ${response.status}).`
    );
  }
  return true;
};

type RuntimeDiscoveryIdentity = {
  runId?: string;
  goalId?: string;
};

const runtimeDiscoveryIdentityFromEnv = (): RuntimeDiscoveryIdentity => {
  const goalId = sessionEnvValue(LOOP_GOAL_ENV_KEYS.goalId);
  return {
    runId: sessionEnvValue(LOOP_GOAL_ENV_KEYS.runId) || (goalId ? `discovery-${goalId}` : undefined),
    goalId,
  };
};

const resolveRuntimeDiscoveryIdentity = async (conversationId?: string): Promise<RuntimeDiscoveryIdentity> => {
  const configured = runtimeDiscoveryIdentityFromEnv();
  if ((configured.runId && configured.goalId) || !conversationId) return configured;

  try {
    const conversation = await readAuthoritativeConversation(conversationId);
    const extra = isRecord(conversation.extra) ? conversation.extra : undefined;
    const loopGoal = extra && isRecord(extra.loop_goal) ? extra.loop_goal : undefined;
    const goalId = configured.goalId || (loopGoal ? asString(loopGoal.id) : undefined);
    const runId =
      configured.runId ||
      (loopGoal ? asString(loopGoal.science_run_id) : undefined) ||
      (goalId ? `discovery-${goalId}` : undefined);
    setSessionEnvValue(LOOP_GOAL_ENV_KEYS.runId, runId);
    setSessionEnvValue(LOOP_GOAL_ENV_KEYS.goalId, goalId);
    return { runId, goalId };
  } catch {
    // Generic Science conversations do not have a Discovery identity. They
    // continue to use explicit run ids or create a new run as before.
    return configured;
  }
};

const resolveRuntimeDiscoveryRunId = (
  requestedRunId: string | undefined,
  identity: RuntimeDiscoveryIdentity
): string | undefined => {
  if (requestedRunId && identity.runId && requestedRunId !== identity.runId) {
    throw new Error('runId does not match the Discovery task bound to this conversation.');
  }
  return requestedRunId || identity.runId;
};

const bindRuntimeDiscoveryGoalId = (value: JsonRecord, identity: RuntimeDiscoveryIdentity): JsonRecord => {
  const requestedGoalId = asString(value.goalId || value.goal_id, '');
  if (requestedGoalId && identity.goalId && requestedGoalId !== identity.goalId) {
    throw new Error('goalId does not match the Discovery task bound to this conversation.');
  }
  return !requestedGoalId && identity.goalId ? { ...value, goalId: identity.goalId } : value;
};

const sessionMcpProfileEnv = (extra: JsonRecord): JsonRecord | undefined => {
  const candidates = [...asArray(extra.session_mcp_servers), ...asArray(extra.selected_session_mcp_servers)];
  for (const candidate of candidates) {
    if (!isRecord(candidate) || asString(candidate.name) !== BUILTIN_SCIENCE_ARTIFACT_NAME) continue;
    const transport = isRecord(candidate.transport) ? candidate.transport : undefined;
    if (transport && isRecord(transport.env)) return transport.env;
  }
  return undefined;
};

const hydrateProjectBindingFromCore = async (
  requestedProjectRoot?: string,
  requestedConversationId?: string
): Promise<string> => {
  const ownerConversationId = runtimeOwnerConversationId();
  if (!ownerConversationId) {
    throw new Error(
      'Project workspace binding is unavailable because this MCP process has no bound project root or owning conversation id.'
    );
  }
  if (requestedConversationId && requestedConversationId !== ownerConversationId) {
    throw new Error('conversationId does not match the conversation that owns this MCP process.');
  }

  const conversation = await readAuthoritativeConversation(ownerConversationId);
  const extra = isRecord(conversation.extra) ? conversation.extra : undefined;
  const binding = extra && isRecord(extra.project_git) ? extra.project_git : undefined;
  if (
    !binding ||
    asString(binding.schema) !== 'deepscientist.project_git.v1' ||
    asString(binding.strategy) === 'disabled'
  ) {
    throw new Error('Core reports that this conversation has no active project workspace binding.');
  }
  const projectRoot = asString(binding.workspaceRoot);
  if (!projectRoot) {
    throw new Error('Core returned a project workspace binding without a workspace root.');
  }
  if (requestedProjectRoot && normalizedPathIdentity(projectRoot) !== normalizedPathIdentity(requestedProjectRoot)) {
    throw new Error('projectRoot does not match the workspace bound to this conversation.');
  }

  const profileEnv = sessionMcpProfileEnv(extra);
  const profileProjectRoot = profileEnv && asString(profileEnv[PROJECT_WORKSPACE_ENV_KEYS.projectRoot]);
  if (profileProjectRoot && normalizedPathIdentity(profileProjectRoot) !== normalizedPathIdentity(projectRoot)) {
    throw new Error('Core returned conflicting project roots for this conversation.');
  }
  const projectId =
    asString(binding.projectId) || (profileEnv ? asString(profileEnv[PROJECT_WORKSPACE_ENV_KEYS.projectId]) : '');
  const profileProjectId = profileEnv && asString(profileEnv[PROJECT_WORKSPACE_ENV_KEYS.projectId]);
  if (projectId && profileProjectId && projectId !== profileProjectId) {
    throw new Error('Core returned conflicting project ids for this conversation.');
  }

  setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectRoot, projectRoot);
  setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.conversationId, ownerConversationId);
  setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectId, projectId);
  for (const key of [PROJECT_WORKSPACE_ENV_KEYS.domain, PROJECT_WORKSPACE_ENV_KEYS.checkpointStages]) {
    const value = profileEnv && asString(profileEnv[key]);
    setSessionEnvValue(key, value);
  }
  return projectRoot;
};

const requireBoundProjectRoot = async (
  requestedProjectRoot?: string,
  requestedConversationId?: string
): Promise<string> => {
  const bound = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectRoot);
  const runtimeOwner = sessionEnvValue(AIONUI_CONVERSATION_ID_ENV_KEY);
  const configuredConversationId = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.conversationId);
  if (bound && (!runtimeOwner || configuredConversationId === runtimeOwner)) {
    return resolveSessionProjectRoot(requestedProjectRoot) as string;
  }
  return hydrateProjectBindingFromCore(requestedProjectRoot, requestedConversationId);
};

const resolveModeProjectRoot = async (
  requestedProjectRoot?: string,
  requestedConversationId?: string
): Promise<string | undefined> => {
  const runtimeOwner = sessionEnvValue(AIONUI_CONVERSATION_ID_ENV_KEY);
  const configuredConversationId = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.conversationId);
  if (
    sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectRoot) &&
    (!runtimeOwner || configuredConversationId === runtimeOwner)
  ) {
    return resolveSessionProjectRoot(requestedProjectRoot);
  }
  if (runtimeOwnerConversationId()) {
    return requireBoundProjectRoot(requestedProjectRoot, requestedConversationId);
  }
  return requestedProjectRoot;
};

/**
 * Math-lite Team conversations carry their project root in the authenticated
 * Team capability, not in a Core project_git binding. Without this fallback
 * every lean_workspace call failed with "no active project workspace binding",
 * although the prompt directs Lean Workers to use the probe (run 23).
 */
const resolveLeanWorkspaceProjectRoot = async (
  requestedProjectRoot?: string,
  requestedConversationId?: string
): Promise<string | undefined> => {
  try {
    return await resolveModeProjectRoot(requestedProjectRoot, requestedConversationId);
  } catch (error) {
    if (!isMathLiteRunEnvironment(process.env)) throw error;
    const capability = await resolveResearchTeamRuntimeCapability(undefined);
    if (!capability) throw error;
    const capabilityRoot = fs.realpathSync(capability.projectRoot);
    if (
      requestedProjectRoot &&
      fs.realpathSync(path.resolve(requestedProjectRoot)) !== capabilityRoot &&
      // A Worker naturally names its own worktree; the Team root stays the
      // authority and assignment-bound calls still select that worktree.
      !isMathWorkerOwnedRoot({
        receipts: listProjectGitResearchTeamAssignments({
          workspace: capabilityRoot,
          teamId: capability.teamId,
          strict: true,
        }),
        slotId: capability.slotId,
        requestedRoot: requestedProjectRoot,
      })
    ) {
      throw new Error('projectRoot does not match the workspace bound to this Team capability.');
    }
    return capabilityRoot;
  }
};

const normalizeProjectDomain = (value: unknown, fallback: ProjectGitDomain = 'general'): ProjectGitDomain => {
  const candidate = asString(value, '').toLowerCase();
  return (
    [
      'general',
      'research',
      'medical_evidence',
      'knowledge_deposition',
      'financial',
      'financial_factor',
      'target_discovery',
      'mathematics',
      'challenge',
    ] as const
  ).includes(candidate as ProjectGitDomain)
    ? (candidate as ProjectGitDomain)
    : fallback;
};

const resolveBoundProjectDomain = (requested: unknown, fallback: ProjectGitDomain): ProjectGitDomain => {
  const boundValue = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain);
  if (!boundValue) {
    throw new Error('project_workspace checkpoint is unavailable because this session has no bound project domain.');
  }
  const bound = normalizeProjectDomain(boundValue, fallback);
  const candidate = asString(requested, '');
  if (bound !== boundValue.toLowerCase()) {
    throw new Error(`The session-bound project domain ${boundValue} is not supported.`);
  }
  if (candidate && candidate.toLowerCase() !== bound) {
    throw new Error(`Checkpoint domain must match the session-bound domain ${bound}.`);
  }
  return bound;
};

const resolveBoundCheckpointStage = (requested: unknown): string => {
  const stages = (sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.checkpointStages) || '')
    .split(',')
    .map((stage) => stage.trim())
    .filter(Boolean);
  if (stages.length === 0) {
    throw new Error('project_workspace checkpoint is unavailable because this session has no bound checkpoint stages.');
  }
  const stage = asString(requested, stages[0]);
  if (!stages.includes(stage)) {
    throw new Error(`Checkpoint stage ${stage} is not allowed for this mode. Allowed stages: ${stages.join(', ')}.`);
  }
  return stage;
};

const boundCheckpointStages = (): string[] =>
  (sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.checkpointStages) || '')
    .split(',')
    .map((stage) => stage.trim())
    .filter(Boolean);

const isRecord = (value: unknown): value is JsonRecord =>
  Boolean(value) && typeof value === 'object' && !Array.isArray(value);

const asString = (value: unknown, fallback = ''): string =>
  typeof value === 'string' && value.trim() ? value.trim() : fallback;

const asNumber = (value: unknown, fallback: number): number =>
  typeof value === 'number' && Number.isFinite(value) ? value : fallback;

const asArray = (value: unknown): unknown[] => (Array.isArray(value) ? value : []);

const asStringArray = (value: unknown): string[] =>
  asArray(value)
    .map((item) => asString(item))
    .filter(Boolean);

const asLocalPath = (value: unknown, field: string): string | undefined => {
  const candidate = asString(value, '');
  if (!candidate) return undefined;
  if (!isPlausibleLocalFileReference(candidate)) {
    throw new Error(
      `${field} must be a local file path, not a command, URL, control string, or parent-traversal path. ` +
        'Store shell text in execution.command and remote sources in evidence.url.'
    );
  }
  return candidate;
};

const asLocalPathArray = (value: unknown, field: string): string[] =>
  asArray(value)
    .filter((item): item is string => typeof item === 'string' && Boolean(item.trim()))
    .map((item, index) => asLocalPath(item, `${field}[${index}]`) as string);

const ARTIFACT_VIEWER_PATH_KEYS = [
  'configPath',
  'dataPath',
  'indexPath',
  'sourcePath',
  'tablePath',
  'modelPath',
  'logPath',
  'schemaPath',
  'codebookPath',
  'variableDictionaryPath',
  'dagPath',
  'mapPath',
] as const;

const normalizeArtifactViewer = (value: unknown): ScienceArtifact['viewer'] => {
  if (!isRecord(value)) return undefined;
  const viewer: JsonRecord = { ...value };
  const requestedKind = asString(value.kind, '');
  for (const key of ARTIFACT_VIEWER_PATH_KEYS) {
    const snakeKey = key.replace(/[A-Z]/gu, (letter) => `_${letter.toLowerCase()}`);
    const normalizedPath = asLocalPath(value[key] ?? value[snakeKey], `viewer.${key}`);
    delete viewer[snakeKey];
    if (normalizedPath) viewer[key] = normalizedPath;
    else delete viewer[key];
  }
  const rawChartSpec = value.chartSpec ?? value.chart_spec;
  delete viewer.chart_spec;
  if (requestedKind === 'proof_trace' && rawChartSpec !== undefined) {
    throw new Error('viewer.kind=proof_trace cannot also provide viewer.chartSpec. Use report_chart for chart specs.');
  }
  if (rawChartSpec !== undefined) {
    const chartValidation = validateReportChartSpec(rawChartSpec);
    if (!chartValidation.ok) {
      throw new Error(
        `viewer.chartSpec is not a valid ${REPORT_CHART_SCHEMA_V1} or ${REPORT_CHART_SCHEMA_V2}: ${chartValidation.issues
          .map((issue) => `${issue.path || '$'} ${issue.message}`)
          .join('; ')}`
      );
    }
    viewer.kind = 'report_chart';
    viewer.chartSpec = chartValidation.spec;
  }
  if (requestedKind === 'proof_trace' && !viewer.dataPath) {
    throw new Error('viewer.kind=proof_trace requires viewer.dataPath.');
  }
  if (requestedKind === 'proof_trace') viewer.kind = 'proof_trace';
  return viewer as ScienceArtifact['viewer'];
};

const PANEL_STATUSES: SciencePanelData['status'][] = ['completed', 'partial', 'blocked', 'failed', 'running', 'draft'];
const normalizePanelStatus = (
  value: unknown,
  fallback: SciencePanelData['status'],
  strict = false
): SciencePanelData['status'] => {
  if (value == null || value === '') return fallback;
  const status = asString(value) as SciencePanelData['status'];
  if (PANEL_STATUSES.includes(status)) return status;
  if (strict) throw new Error(`Unsupported Science run status: ${String(value)}.`);
  return fallback;
};

const clone = <T>(value: T): T => JSON.parse(JSON.stringify(value)) as T;

const normalizeRelativePath = (candidate: string, projectRoot?: string): string => {
  if (!candidate || path.isAbsolute(candidate) || !projectRoot) return candidate;
  return path.join(projectRoot, candidate);
};

const safeSegment = (value: string): string =>
  value
    .trim()
    .replace(/[^a-z0-9_.-]+/giu, '-')
    .replace(/^-+|-+$/gu, '')
    .slice(0, 120) || 'science-run';

const writeJson = (filePath: string, value: unknown): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const writeJsonAtomic = (filePath: string, value: unknown): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  const temporaryPath = `${filePath}.${process.pid}.${crypto.randomBytes(4).toString('hex')}.tmp`;
  try {
    const descriptor = fs.openSync(temporaryPath, 'w', 0o600);
    try {
      fs.writeFileSync(descriptor, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
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
      // Some filesystems do not allow opening directories. Rename remains
      // atomic; the durability boundary is best effort on those platforms.
    }
  } finally {
    if (fs.existsSync(temporaryPath)) fs.rmSync(temporaryPath, { force: true });
  }
};

/**
 * The Lean project inside a Worker's private worktree, from the frozen run
 * binding. The sealed proof environment records that project's configuration,
 * so Worker checks must run there rather than at the worktree top.
 */
export const workerSolverProjectRoot = (
  teamWorkspace: string,
  preparedGit: Readonly<{ worktreePath?: string; solverProjectRoot?: string }>
): string | undefined => {
  const encoded = process.env[MATH_RUN_INPUTS_ENV];
  if (!encoded || !preparedGit.worktreePath) return undefined;
  const paths = resolveMathRunProjectPaths(
    readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded))),
    teamWorkspace,
    preparedGit.worktreePath
  );
  if (preparedGit.solverProjectRoot && preparedGit.solverProjectRoot !== paths.solverProjectRoot)
    throw new Error('Worker proof project does not match its worktree binding.');
  return fs.realpathSync(paths.solverProjectRoot);
};

type MathematicsProjectPortfolioSnapshot =
  | { status: 'missing'; path: string; rawHash: string }
  | { status: 'invalid'; path: string; rawHash: string }
  | { status: 'ready'; path: string; rawHash: string; portfolio: MathematicsPortfolio };

type MathematicsPortfolioFileCacheEntry = Readonly<{
  metadata: string;
  snapshot: MathematicsProjectPortfolioSnapshot;
}>;

// Portfolio reads happen on every mathematics tool call.  Keep the parsed
// snapshot while the file identity is unchanged; ctime catches atomic
// replacements even when a writer preserves size and mtime.
const mathematicsPortfolioFileCache = new Map<string, MathematicsPortfolioFileCacheEntry>();

const cacheMathematicsPortfolioSnapshot = (
  filePath: string,
  metadata: string,
  snapshot: MathematicsProjectPortfolioSnapshot
): void => {
  mathematicsPortfolioFileCache.delete(filePath);
  mathematicsPortfolioFileCache.set(filePath, { metadata, snapshot });
  while (mathematicsPortfolioFileCache.size > 256) {
    const oldest = mathematicsPortfolioFileCache.keys().next().value;
    if (oldest === undefined) break;
    mathematicsPortfolioFileCache.delete(oldest);
  }
};

const latestMathematicsPortfolio = (artifacts: Iterable<ScienceArtifact>): MathematicsPortfolio | undefined => {
  let latest: MathematicsPortfolio | undefined;
  for (const artifact of artifacts) {
    const candidate = readMathematicsPortfolio(artifact.metadata);
    if (candidate && (!latest || candidate.updatedAt > latest.updatedAt)) latest = candidate;
  }
  return latest;
};

const readMathematicsProjectPortfolio = (projectRoot: string): MathematicsProjectPortfolioSnapshot => {
  const filePath = resolveProjectOwnedPath(projectRoot, MATHEMATICS_PORTFOLIO_PATH, 'mathematics portfolio path');
  let stat: fs.Stats;
  try {
    stat = fs.statSync(filePath);
    if (!stat.isFile()) throw new Error('portfolio path is not a file');
  } catch {
    const cachedMissing = mathematicsPortfolioFileCache.get(filePath);
    if (cachedMissing?.metadata === 'missing') {
      cacheMathematicsPortfolioSnapshot(filePath, cachedMissing.metadata, cachedMissing.snapshot);
      return cachedMissing.snapshot;
    }
    const snapshot: MathematicsProjectPortfolioSnapshot = {
      status: 'missing',
      path: MATHEMATICS_PORTFOLIO_PATH,
      rawHash: 'missing',
    };
    cacheMathematicsPortfolioSnapshot(filePath, 'missing', snapshot);
    return snapshot;
  }
  const metadata = [stat.dev, stat.ino, stat.size, stat.mtimeMs, stat.ctimeMs].join(':');
  const cached = mathematicsPortfolioFileCache.get(filePath);
  if (cached?.metadata === metadata) {
    cacheMathematicsPortfolioSnapshot(filePath, cached.metadata, cached.snapshot);
    return cached.snapshot;
  }
  let contents: string;
  try {
    contents = fs.readFileSync(filePath, 'utf8');
  } catch {
    const snapshot: MathematicsProjectPortfolioSnapshot = {
      status: 'invalid',
      path: MATHEMATICS_PORTFOLIO_PATH,
      rawHash: 'unreadable',
    };
    cacheMathematicsPortfolioSnapshot(filePath, metadata, snapshot);
    return snapshot;
  }
  const rawHash = crypto.createHash('sha256').update(contents, 'utf8').digest('hex');
  try {
    const parsed = JSON.parse(contents) as unknown;
    const portfolio = readMathematicsPortfolio(parsed) || readMathematicsPortfolio({ mathematics: parsed });
    const snapshot: MathematicsProjectPortfolioSnapshot = portfolio
      ? { status: 'ready', path: MATHEMATICS_PORTFOLIO_PATH, rawHash, portfolio }
      : { status: 'invalid', path: MATHEMATICS_PORTFOLIO_PATH, rawHash };
    cacheMathematicsPortfolioSnapshot(filePath, metadata, snapshot);
    return snapshot;
  } catch {
    const snapshot: MathematicsProjectPortfolioSnapshot = {
      status: 'invalid',
      path: MATHEMATICS_PORTFOLIO_PATH,
      rawHash,
    };
    cacheMathematicsPortfolioSnapshot(filePath, metadata, snapshot);
    return snapshot;
  }
};

const withMathematicsPortfolioLock = <T>(projectRoot: string, operation: () => T): T => {
  const lockPath = resolveProjectOwnedPath(
    projectRoot,
    path.join('.deepscientist', 'mathematics', 'portfolio.lock'),
    'mathematics portfolio lock path'
  );
  fs.mkdirSync(path.dirname(lockPath), { recursive: true });
  const token = crypto.randomUUID();
  const temporaryPath = `${lockPath}.${process.pid}.${token}.tmp`;
  let descriptor: number | undefined;
  let acquired = false;
  try {
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
          throw new Error('Another mathematics portfolio writer is active; retry the operation.');
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
      try {
        fs.closeSync(descriptor);
      } catch {
        // The descriptor may already have been closed by the filesystem.
      }
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
};

const writeMathematicsProjectPortfolio = (
  projectRoot: string,
  portfolio: MathematicsPortfolio,
  expectedRawHash?: string
): string => {
  const filePath = resolveProjectOwnedPath(projectRoot, MATHEMATICS_PORTFOLIO_PATH, 'mathematics portfolio path');
  assertProjectPathHasNoSymlinkEscape(projectRoot, filePath, 'mathematics portfolio path');
  if (expectedRawHash !== undefined) {
    const current = readMathematicsProjectPortfolio(projectRoot);
    if (current.rawHash !== expectedRawHash) {
      throw new Error('Mathematics portfolio changed concurrently; reload it and retry with its current revision.');
    }
  }
  mathematicsPortfolioFileCache.delete(filePath);
  writeJsonAtomic(filePath, portfolio);
  // The next read will repopulate the cache with the new inode/metadata.
  return MATHEMATICS_PORTFOLIO_PATH;
};

const isTerminalMathematicsPortfolio = (portfolio: MathematicsPortfolio): boolean =>
  ['verified', 'refuted'].includes(portfolio.stage) ||
  ['verified', 'refuted'].includes(portfolio.status) ||
  portfolio.problems.some((problem) => ['verified', 'refuted'].includes(problem.status));

const assertCurrentMathematicsPortfolioCommitted = (projectRoot: string, portfolio: MathematicsPortfolio): void => {
  const blob = getProjectGitBlob({ workspace: projectRoot, sha: 'HEAD', path: MATHEMATICS_PORTFOLIO_PATH });
  if (!blob.ok || blob.binary || blob.truncated || !blob.content) {
    throw new Error(`Terminal mathematics state must be committed at HEAD in ${MATHEMATICS_PORTFOLIO_PATH}.`);
  }
  let committed: MathematicsPortfolio | undefined;
  try {
    committed = readMathematicsPortfolio({ mathematics: JSON.parse(blob.content) });
  } catch {
    committed = undefined;
  }
  if (!committed || !isDeepStrictEqual(committed, portfolio)) {
    throw new Error(`Terminal mathematics state must match ${MATHEMATICS_PORTFOLIO_PATH} at HEAD.`);
  }
};

const assertTerminalMathematicsPortfolioCommitted = (
  projectRoot: string,
  targetCommit: string | undefined,
  portfolio: MathematicsPortfolio
): void => {
  if (!isTerminalMathematicsPortfolio(portfolio)) return;
  const commit = targetCommit?.trim().toLowerCase();
  if (!commit || !/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/u.test(commit)) {
    throw new Error('A terminal mathematics portfolio requires its exact committed Git revision.');
  }
  const blob = getProjectGitBlob({ workspace: projectRoot, sha: 'HEAD', path: MATHEMATICS_PORTFOLIO_PATH });
  if (!blob.ok || blob.sha?.toLowerCase() !== commit) {
    throw new Error('A terminal mathematics portfolio must target the current project HEAD.');
  }
  if (!blob.ok || blob.binary || blob.truncated || !blob.content) {
    throw new Error(`Terminal mathematics state must already exist in ${MATHEMATICS_PORTFOLIO_PATH} at HEAD.`);
  }
  let committed: MathematicsPortfolio | undefined;
  try {
    committed = readMathematicsPortfolio({ mathematics: JSON.parse(blob.content) });
  } catch {
    committed = undefined;
  }
  if (!committed || !isDeepStrictEqual(committed, portfolio)) {
    throw new Error(
      `Terminal mathematics state must be byte-semantically identical to ${MATHEMATICS_PORTFOLIO_PATH} at HEAD.`
    );
  }
};

const readMathematicsVerificationTraceAtPath = (
  projectRoot: string,
  relativePath: string
): MathematicsVerificationTrace | undefined => {
  const filePath = resolveProjectOwnedPath(projectRoot, relativePath, 'mathematics verification trace path');
  if (!fs.existsSync(filePath)) return undefined;
  const trace = readMathematicsVerificationTrace(readJson<unknown>(filePath, undefined));
  const runIdentity = readMathRunHistoryIdentity();
  return runIdentity && trace?.runIdentity !== runIdentity ? undefined : trace;
};

const readMathematicsProjectVerificationTrace = (projectRoot: string): MathematicsVerificationTrace | undefined =>
  readMathematicsVerificationTraceAtPath(projectRoot, MATHEMATICS_VERIFICATION_TRACE_PATH);

const writeMathematicsProofTraceSnapshot = (projectRoot: string, trace: MathematicsVerificationTrace): string => {
  const contents = `${JSON.stringify(trace, null, 2)}\n`;
  const digest = crypto.createHash('sha256').update(contents).digest('hex');
  const relativePath = `mathematics/report-traces/verification-${digest.slice(0, 20)}.json`;
  const filePath = resolveProjectOwnedPath(projectRoot, relativePath, 'mathematics report trace path');
  assertProjectPathHasNoSymlinkEscape(projectRoot, filePath, 'mathematics report trace path');
  if (fs.existsSync(filePath)) {
    if (!fs.statSync(filePath).isFile() || fs.readFileSync(filePath, 'utf8') !== contents) {
      throw new Error('The content-addressed mathematics report trace path contains different data.');
    }
    return relativePath;
  }
  writeJsonAtomic(filePath, trace);
  return relativePath;
};

const mathematicsProofTraceArtifactDraft = (tracePath: string) => ({
  type: 'figure' as const,
  title: 'Lean verification trace',
  primaryPath: tracePath,
  outputPaths: [tracePath],
  mimeType: 'application/vnd.deepscientist.mathematics.verification-trace+json',
  viewer: {
    kind: 'proof_trace' as const,
    dataPath: tracePath,
    savePolicy: 'read_only' as const,
  },
});

const areMathematicsVerificationEventsOrdered = (events: readonly MathematicsVerificationEvent[]): boolean => {
  for (let index = 1; index < events.length; index += 1) {
    if (events[index - 1].timestamp > events[index].timestamp) return false;
  }
  return true;
};

const writeMathematicsVerificationTraceAtPath = (
  projectRoot: string,
  relativePath: string,
  events: MathematicsVerificationEvent[],
  capability?: MathematicsVerificationCapability
): MathematicsVerificationTrace => {
  const previous = readMathematicsVerificationTraceAtPath(projectRoot, relativePath);
  const eventById = new Map<string, MathematicsVerificationEvent>();
  for (const event of previous?.events || []) eventById.set(event.eventId, event);
  for (const event of events) eventById.set(event.eventId, event);
  const retainedEvents = [...eventById.values()];
  if (!areMathematicsVerificationEventsOrdered(retainedEvents)) {
    retainedEvents.sort((left, right) => left.timestamp - right.timestamp);
  }
  if (retainedEvents.length > 2_000) retainedEvents.splice(0, retainedEvents.length - 2_000);
  const trace: MathematicsVerificationTrace = {
    schema: MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
    version: 1,
    runIdentity: readMathRunHistoryIdentity(),
    updatedAt: now(),
    ...(capability || previous?.capability ? { capability: capability || previous?.capability } : {}),
    events: retainedEvents,
  };
  const filePath = resolveProjectOwnedPath(projectRoot, relativePath, 'mathematics verification trace path');
  writeJsonAtomic(filePath, trace);
  return trace;
};

const writeMathematicsProjectVerificationTrace = (
  projectRoot: string,
  events: MathematicsVerificationEvent[],
  capability?: MathematicsVerificationCapability
): MathematicsVerificationTrace =>
  writeMathematicsVerificationTraceAtPath(projectRoot, MATHEMATICS_VERIFICATION_TRACE_PATH, events, capability);

const writeMathematicsLiveVerificationTrace = (
  projectRoot: string,
  events: MathematicsVerificationEvent[],
  capability?: MathematicsVerificationCapability
): MathematicsVerificationTrace =>
  writeMathematicsVerificationTraceAtPath(projectRoot, MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH, events, capability);

const createMathematicsLiveTraceWriter = (
  projectRoot: string,
  initialEventGroups: readonly (readonly MathematicsVerificationEvent[])[],
  initialCapability?: MathematicsVerificationCapability
) => {
  const previous = readMathematicsVerificationTraceAtPath(projectRoot, MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH);
  const eventById = new Map<string, MathematicsVerificationEvent>();
  for (const event of previous?.events || []) eventById.set(event.eventId, event);
  for (const events of initialEventGroups) {
    for (const event of events) eventById.set(event.eventId, event);
  }
  let capability = initialCapability || previous?.capability;
  let timer: NodeJS.Timeout | undefined;

  const flush = (nextCapability?: MathematicsVerificationCapability): MathematicsVerificationTrace => {
    if (nextCapability) capability = nextCapability;
    if (timer) clearTimeout(timer);
    timer = undefined;
    const retainedEvents = [...eventById.values()];
    const ordered = areMathematicsVerificationEventsOrdered(retainedEvents);
    if (!ordered) retainedEvents.sort((left, right) => left.timestamp - right.timestamp);
    if (retainedEvents.length > 2_000) retainedEvents.splice(0, retainedEvents.length - 2_000);
    if (!ordered || eventById.size > 2_000) {
      eventById.clear();
      for (const event of retainedEvents) eventById.set(event.eventId, event);
    }
    const trace: MathematicsVerificationTrace = {
      schema: MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
      version: 1,
      runIdentity: readMathRunHistoryIdentity(),
      updatedAt: now(),
      ...(capability ? { capability } : {}),
      events: retainedEvents,
    };
    const filePath = resolveProjectOwnedPath(
      projectRoot,
      MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH,
      'mathematics verification trace path'
    );
    writeJsonAtomic(filePath, trace);
    return trace;
  };

  return {
    append(event: MathematicsVerificationEvent): void {
      eventById.set(event.eventId, event);
      if (!timer) timer = setTimeout(() => flush(), 150);
    },
    flush,
    close(nextCapability?: MathematicsVerificationCapability): MathematicsVerificationTrace {
      return flush(nextCapability);
    },
  };
};

const resolveProjectOwnedPath = (projectRoot: string, candidate: string, field: string): string => {
  const resolvedRoot = path.resolve(projectRoot);
  const resolvedPath = path.resolve(normalizeRelativePath(candidate, resolvedRoot));
  const relative = path.relative(resolvedRoot, resolvedPath);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${field} must resolve inside the authorized project root.`);
  }
  assertProjectPathHasNoSymlinkEscape(projectRoot, resolvedPath, field);
  return resolvedPath;
};

const assertProjectPathHasNoSymlinkEscape = (projectRoot: string, targetPath: string, field: string): void => {
  const lexicalRoot = path.resolve(projectRoot);
  const realRoot = fs.realpathSync(lexicalRoot);
  const relative = path.relative(lexicalRoot, path.resolve(targetPath));
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${field} must resolve inside the authorized project root.`);
  }

  let cursor = lexicalRoot;
  for (const segment of relative.split(path.sep).filter(Boolean)) {
    cursor = path.join(cursor, segment);
    if (!fs.existsSync(cursor)) break;
    if (fs.lstatSync(cursor).isSymbolicLink()) {
      throw new Error(`${field} must not traverse a symbolic link.`);
    }
    const realCursor = fs.realpathSync(cursor);
    const realRelative = path.relative(realRoot, realCursor);
    if (realRelative.startsWith('..') || path.isAbsolute(realRelative)) {
      throw new Error(`${field} must resolve inside the authorized project root.`);
    }
  }
};

const isFactorPortfolioArtifactMutation = (action: string, body: JsonRecord): boolean => {
  if (!['create', 'patch', 'replace', 'version'].includes(action)) return false;
  const artifactType = asString(body.artifactType || body.artifact_type || body.type, '').toLowerCase();
  const candidatePath = asString(body.primaryPath || body.primary_path || body.path, '')
    .replaceAll('\\', '/')
    .replace(/^\.\//u, '');
  return (
    artifactType === 'factor_portfolio' ||
    artifactType === 'financial_factor_portfolio' ||
    candidatePath === FINANCIAL_FACTOR_PORTFOLIO_PATH
  );
};

const isMathematicsPortfolioArtifactMutation = (action: string, body: JsonRecord): boolean => {
  if (!['create', 'patch', 'replace', 'version'].includes(action)) return false;
  const artifactType = asString(body.artifactType || body.artifact_type || body.type, '').toLowerCase();
  const candidatePath = asString(body.primaryPath || body.primary_path || body.path, '')
    .replaceAll('\\', '/')
    .replace(/^\.\//u, '');
  return artifactType === 'mathematics_portfolio' || candidatePath === MATHEMATICS_PORTFOLIO_PATH;
};

const writeJsonl = (filePath: string, values: unknown[]): void => {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(
    filePath,
    values.map((value) => JSON.stringify(value)).join('\n') + (values.length ? '\n' : ''),
    'utf8'
  );
};

const readJson = <T>(filePath: string, fallback: T): T => {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8')) as T;
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') return fallback;
    throw error;
  }
};

const fileMeta = (
  candidate?: string,
  projectRoot?: string
): Pick<ScienceArtifact, 'status' | 'sizeBytes' | 'contentHash'> => {
  if (!candidate) return {};
  const resolved = normalizeRelativePath(candidate, projectRoot);
  if (!fs.existsSync(resolved)) return { status: 'missing' };
  const stat = fs.statSync(resolved);
  if (!stat.isFile()) return { status: 'available', sizeBytes: stat.size };
  const hash = crypto.createHash('sha256').update(fs.readFileSync(resolved)).digest('hex');
  return { status: 'available', sizeBytes: stat.size, contentHash: hash };
};

const deepMerge = (base: unknown, patch: unknown): unknown => {
  if (!isRecord(base) || !isRecord(patch)) return clone(patch);
  const next: JsonRecord = { ...clone(base) };
  for (const [key, value] of Object.entries(patch)) {
    if (value === null) {
      delete next[key];
      continue;
    }
    next[key] = isRecord(value) && isRecord(next[key]) ? deepMerge(next[key], value) : clone(value);
  }
  return next;
};

const contextValue = (payload: JsonRecord | undefined, key: string): unknown => {
  const context = isRecord(payload?.context) ? payload.context : undefined;
  const snakeKey = key.replace(/[A-Z]/gu, (letter) => `_${letter.toLowerCase()}`);
  return payload?.[key] || payload?.[snakeKey] || context?.[key] || context?.[snakeKey];
};

const applyRunContext = (
  run: ScienceRunState,
  payload?: JsonRecord,
  topLevel?: { conversationId?: string; messageId?: string; toolCallId?: string }
): void => {
  const conversationId = asString(
    topLevel?.conversationId || contextValue(payload, 'conversationId'),
    undefined as unknown as string
  );
  const messageId = asString(topLevel?.messageId || contextValue(payload, 'messageId'), undefined as unknown as string);
  const toolCallId = asString(
    topLevel?.toolCallId || contextValue(payload, 'toolCallId'),
    undefined as unknown as string
  );
  if (conversationId) run.conversationId = conversationId;
  if (messageId) run.messageId = messageId;
  if (toolCallId) run.toolCallId = toolCallId;
};

const ensureRun = (requestedRunId?: string, projectRoot?: string, payload?: JsonRecord): ScienceRunState => {
  const id = requestedRunId || asString(payload?.runId) || runId();
  const existing = runs.get(id);
  if (existing) {
    if (
      projectRoot &&
      existing.projectRoot &&
      normalizedPathIdentity(projectRoot) !== normalizedPathIdentity(existing.projectRoot)
    ) {
      throw new Error('runId is already bound to a different project root.');
    }
    if (projectRoot) {
      const hydrated = hydrateRun(id, projectRoot);
      if (hydrated && hydrated.updatedAt > existing.updatedAt) {
        runs.set(id, hydrated);
        return hydrated;
      }
    }
    if (projectRoot && !existing.projectRoot) existing.projectRoot = projectRoot;
    if (projectRoot) ensureScienceProject(projectRoot);
    existing.updatedAt = now();
    return existing;
  }
  const hydrated = hydrateRun(id, projectRoot);
  if (hydrated) {
    runs.set(id, hydrated);
    return hydrated;
  }
  const created: ScienceRunState = {
    runId: id,
    conversationId: asString(contextValue(payload, 'conversationId'), undefined as unknown as string),
    messageId: asString(contextValue(payload, 'messageId'), undefined as unknown as string),
    toolCallId: asString(contextValue(payload, 'toolCallId'), undefined as unknown as string),
    projectRoot,
    question: asString(payload?.question, ''),
    summary: asString(payload?.summary, undefined as unknown as string),
    status: normalizePanelStatus(payload?.status, 'draft'),
    visualWaiverReason: readVisualWaiverReason(payload) || readVisualWaiverReason(payload?.report),
    cards: [],
    cardDiagnostics: [],
    evidence: new Map(),
    artifacts: new Map(),
    pages: new Map(),
    claims: new Map(),
    provenance: new Map(),
    edges: new Map(),
    graphWarnings: new Map(),
    usedSkills: new Map(),
    annotations: new Map(),
    commandReceipts: new Map(),
    memory: [],
    events: [],
    mathematicsVerifications: [],
    mathematicsVerificationEvents: [],
    mathematicsOfficialGateReceipts: [],
    createdAt: now(),
    updatedAt: now(),
  };
  if (projectRoot) ensureScienceProject(projectRoot);
  runs.set(id, created);
  return created;
};

const hydrateMap = <T extends { id: string }>(items: unknown): Map<string, T> => {
  const map = new Map<string, T>();
  if (!Array.isArray(items)) return map;
  for (const item of items) {
    if (!isRecord(item)) continue;
    const id = asString(item.id, undefined as unknown as string);
    if (!id) continue;
    map.set(id, item as T);
  }
  return map;
};

const hydrateArtifacts = (items: unknown): Map<string, ScienceArtifact> => {
  const map = new Map<string, ScienceArtifact>();
  if (!Array.isArray(items)) return map;
  for (const item of items) {
    if (!isRecord(item)) continue;
    const id = asString(item.id, undefined as unknown as string);
    if (!id) continue;
    const version = asNumber(item.version, 1);
    map.set(artifactKey(id, version), item as unknown as ScienceArtifact);
  }
  return map;
};

const validateCardsAgainstResources = (
  value: unknown,
  artifacts: ReadonlyMap<string, ScienceArtifact>,
  evidence: ReadonlyMap<string, ScienceEvidenceItem>
) =>
  validateStructuredReportCards(value, {
    artifactRefs: new Set(artifacts.keys()),
    evidenceIds: new Set(evidence.keys()),
  });

const hydrateRun = (id: string, projectRoot?: string): ScienceRunState | undefined => {
  if (!projectRoot) return undefined;
  const snapshot = readScienceArtifactRunSnapshot({ projectRoot, runId: id });
  if (!snapshot) return undefined;
  const state = snapshot.state;
  const panel = (snapshot.panel || {}) as Partial<SciencePanelData> & JsonRecord;
  const events = snapshot.events;
  const rawReport = isRecord(state.report) ? state.report : isRecord(panel.report) ? panel.report : undefined;
  const visualWaiverReason = asDisplayString(state.visualWaiverReason) || readVisualWaiverReason(rawReport);
  const createdAt = asNumber(state.createdAt, now());
  const evidence = hydrateMap<ScienceEvidenceItem>(state.evidence);
  const artifacts = hydrateArtifacts(state.artifacts);
  const cards = validateCardsAgainstResources(state.cards ?? panel.cards ?? [], artifacts, evidence);
  const cardErrors = cards.ok === false ? cards.errors : [];
  const rawFinanceCompletion = state.financeCompletion ?? panel.financeCompletion;
  const financeCompletion = rawFinanceCompletion
    ? financeCompletionManifestSchema.safeParse(rawFinanceCompletion)
    : undefined;
  const persistedCardDiagnostics = stringArray(state.cardDiagnostics ?? panel.cardDiagnostics);
  const trustedMathematicsState = snapshot.source === 'git';
  const legacyMathematicsVerification =
    trustedMathematicsState && isRecord(state.mathematicsVerification)
      ? (state.mathematicsVerification as unknown as MathematicsVerifierResult)
      : undefined;
  const mathematicsVerifications: MathematicsVerifierResult[] = [];
  if (trustedMathematicsState && Array.isArray(state.mathematicsVerifications)) {
    for (const item of state.mathematicsVerifications) {
      if (isRecord(item)) mathematicsVerifications.push(item as unknown as MathematicsVerifierResult);
    }
  } else if (legacyMathematicsVerification) {
    mathematicsVerifications.push(legacyMathematicsVerification);
  }
  const mathematicsOfficialGateReceipts: MathOfficialGateReceipt[] = [];
  for (const item of trustedMathematicsState && Array.isArray(state.mathematicsOfficialGateReceipts)
    ? state.mathematicsOfficialGateReceipts
    : []) {
    if (!isRecord(item)) continue;
    try {
      mathematicsOfficialGateReceipts.push(
        normalizeMathOfficialGateReceipt(item as unknown as MathOfficialGateReceipt)
      );
    } catch {
      // Ignore one malformed historical receipt while hydrating the remaining run state.
    }
  }
  const persistedMathematicsTrace = readMathematicsVerificationTrace({
    schema: MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
    version: 1,
    updatedAt: asNumber(state.updatedAt, createdAt),
    capability: state.mathematicsVerificationCapability,
    events: Array.isArray(state.mathematicsVerificationEvents) ? state.mathematicsVerificationEvents : [],
  });
  const recoveredGit: ScienceArtifactGitRef | undefined =
    snapshot.source === 'git' && snapshot.commit
      ? {
          repoPath: path.join(projectRoot, '.deepscientist', 'artifact-repo'),
          commit: snapshot.commit,
          shortCommit: snapshot.commit.slice(0, 7),
          runPath: `runs/${safeSegment(id)}`,
          status: 'committed',
        }
      : undefined;
  return {
    runId: id,
    conversationId: asString(state.conversationId || panel.conversationId, undefined as unknown as string),
    messageId: asString(state.messageId, undefined as unknown as string),
    toolCallId: asString(state.toolCallId, undefined as unknown as string),
    projectRoot,
    question: asString(state.question, asString(panel.question, '')),
    summary: asString(state.summary, asString(panel.summary, undefined as unknown as string)),
    status: normalizePanelStatus(state.status, normalizePanelStatus(panel.status, 'draft')),
    report: rawReport ? normalizeReport(rawReport) : undefined,
    visualWaiverReason,
    cards: cards.cards,
    cardDiagnostics: [...new Set([...persistedCardDiagnostics, ...cardErrors])],
    financeCompletion: financeCompletion?.success ? (financeCompletion.data as FinanceCompletionManifest) : undefined,
    financePreflight: isRecord(state.financePreflight)
      ? (state.financePreflight as SciencePanelData['financePreflight'])
      : isRecord(panel.financePreflight)
        ? (panel.financePreflight as SciencePanelData['financePreflight'])
        : rawFinanceCompletion && financeCompletion?.success === false
          ? {
              status: 'blocked',
              gaps: financeCompletion.error.issues.map(
                (issue) => `financeCompletion.${issue.path.join('.') || 'manifest'}: ${issue.message}`
              ),
              verifiedAt: new Date(createdAt).toISOString(),
            }
          : undefined,
    statsPatch: isRecord(state.statsPatch) ? (state.statsPatch as Partial<SciencePanelData['stats']>) : undefined,
    evidence,
    artifacts,
    pages: hydrateMap<ScienceArtifactPage>(state.pages),
    claims: hydrateMap<ScienceClaim>(state.claims),
    provenance: hydrateMap<ScienceProvenanceNode>(state.provenance),
    edges: hydrateMap<ScienceProvenanceEdge>(state.edges),
    graphWarnings: hydrateMap<ScienceGraphWarning>(state.graphWarnings),
    usedSkills: hydrateMap<ScienceSkillUse>(state.usedSkills),
    annotations: hydrateMap<AnnotationRecord>(state.annotations),
    commandReceipts: hydrateMap<ScienceCommandReceipt>(state.commandReceipts),
    memory: Array.isArray(state.memory)
      ? state.memory.filter((item): item is ScienceArtifactMemoryEvent => Boolean(item && typeof item === 'object'))
      : [],
    events: Array.isArray(events) ? events : [],
    git: isRecord(state.git)
      ? (state.git as ScienceArtifactGitRef)
      : isRecord(panel.git)
        ? (panel.git as ScienceArtifactGitRef)
        : recoveredGit,
    sourceGit: isRecord(state.sourceGit)
      ? (state.sourceGit as unknown as ScienceSourceGitRef)
      : isRecord(panel.sourceGit)
        ? (panel.sourceGit as unknown as ScienceSourceGitRef)
        : undefined,
    mathematicsVerification: legacyMathematicsVerification,
    mathematicsVerifications,
    mathematicsVerificationEvents: persistedMathematicsTrace?.events || [],
    mathematicsVerificationCapability: persistedMathematicsTrace?.capability,
    mathematicsOfficialGateReceipts,
    mathematicsReview: isRecord(state.mathematicsReview) ? state.mathematicsReview : undefined,
    createdAt,
    updatedAt: asNumber(state.updatedAt, createdAt),
  };
};

const assertBaseRevision = (current: { revision?: string } | undefined, baseRevision?: string): void => {
  if (!current) return;
  if (!baseRevision) {
    throw new Error(
      'baseRevision is required before mutating an existing object. Reuse currentRevision/resultingRevision from the latest successful mutation. If no receipt is available, call math_portfolio(action="get") for mathematics, target_portfolio(action="get") for targets, factor_registry(action="get") for factors, or science_artifact(action="get") for other resources.'
    );
  }
  if (current.revision && current.revision !== baseRevision) {
    throw new Error(`baseRevision mismatch. Current revision is ${current.revision}.`);
  }
};

const FINANCE_PUBLICATION_INVALIDATING_ACTIONS = new Set<ScienceArtifactAction>([
  'transact',
  'create',
  'patch',
  'replace',
  'append',
  'version',
  'checkpoint',
  'prepare_branch',
  'activate_branch',
  'snapshot',
  'annotate',
]);

const invalidateFinancePublication = (
  run: ScienceRunState,
  action: ScienceArtifactAction,
  panel?: SciencePanelData
): void => {
  if (!run.financeCompletion || !FINANCE_PUBLICATION_INVALIDATING_ACTIONS.has(action)) return;
  const financePreflight: NonNullable<SciencePanelData['financePreflight']> = {
    status: 'partial',
    gaps: [...new Set([...(run.financePreflight?.gaps ?? []), `stale_after_mutation:${action}`])],
    verifiedAt: new Date(now()).toISOString(),
  };
  run.financePreflight = financePreflight;
  if (run.status === 'completed') run.status = 'partial';
  if (panel) {
    panel.financePreflight = financePreflight;
    if (panel.status === 'completed') panel.status = 'partial';
  }
};

export const eventFor = (
  run: ScienceRunState,
  action: ScienceArtifactAction,
  target?: TargetRef,
  extra?: Partial<ScienceArtifactEvent>,
  includePaths?: ScienceArtifactSnapshotIncludePath[]
): ScienceArtifactEvent => {
  invalidateFinancePublication(run, action, extra?.panel);
  const evt: ScienceArtifactEvent = {
    schema: SCIENCE_EVENT_SCHEMA,
    eventId: eventId(),
    runId: run.runId,
    action,
    timestamp: now(),
    conversationId: extra?.conversationId || run.conversationId,
    messageId: extra?.messageId || run.messageId,
    toolCallId: extra?.toolCallId || run.toolCallId,
    target,
    ...extra,
  };
  run.events.push(evt);
  run.updatedAt = evt.timestamp;
  const shouldRemember =
    target?.kind !== 'memory' && !['status', 'get', 'list', 'reserve_id', 'focus_page'].includes(action);
  const memory: ScienceArtifactMemoryEvent | undefined = shouldRemember
    ? {
        id: `memory_${evt.eventId}`,
        runId: run.runId,
        artifactId:
          target?.kind === 'artifact' ? target.id : extra?.artifactIds?.length ? extra.artifactIds[0] : undefined,
        artifactVersion: target?.kind === 'artifact' ? target.version : undefined,
        actor: 'agent',
        action,
        summary: `${action.replace(/_/gu, ' ')} ${target?.kind || 'run'}${target?.id ? ` ${target.id}` : ''}`,
        evidenceIds: extra?.evidenceIds,
        claimIds: extra?.claimIds,
        timestamp: evt.timestamp,
        hidden: true,
      }
    : undefined;
  if (memory) {
    run.memory.push(memory);
    evt.memoryId = memory.id;
  }
  const gitRef = persistRunSnapshot(run, evt, includePaths);
  if (gitRef) {
    run.git = gitRef;
    evt.git = gitRef;
    if (evt.panel) evt.panel.git = gitRef;
    if (evt.snapshot) evt.snapshot.files = gitRef.files;
    if (memory) memory.commit = gitRef.commit;
  }
  return evt;
};

const normalizeGitAnchor = (run: ScienceRunState, value: unknown): ScienceGitLineAnchor | undefined => {
  if (!isRecord(value)) return undefined;
  if (
    value.kind === 'git_lines' &&
    typeof value.commit === 'string' &&
    typeof value.repoRelativePath === 'string' &&
    typeof value.lineStart === 'number' &&
    typeof value.lineEnd === 'number'
  ) {
    return value as unknown as ScienceGitLineAnchor;
  }
  if (!run.projectRoot || value.kind !== 'git_lines') return undefined;
  const filePath = asString(value.filePath || value.file_path || value.path, undefined as unknown as string);
  if (!filePath) throw new Error('A git_lines anchor requires filePath.');
  const result = readScienceArtifactGitLines({
    projectRoot: run.projectRoot,
    anchor: {
      kind: 'git_lines',
      commit: asString(value.commit, undefined as unknown as string),
      filePath,
      lineStart: asNumber(value.lineStart || value.line_start, 1),
      lineEnd:
        value.lineEnd || value.line_end
          ? asNumber(value.lineEnd || value.line_end, asNumber(value.lineStart || value.line_start, 1))
          : undefined,
      side: value.side === 'parent' ? 'parent' : 'current',
    },
  });
  if (!result.ok || !result.anchor) throw new Error(result.error || 'The Git line anchor could not be resolved.');
  return result.anchor;
};

const normalizeEvidence = (run: ScienceRunState, value: JsonRecord): ScienceEvidenceItem => {
  const id = asString(value.id, makeId('evidence'));
  const regionRecord = isRecord(value.region) ? value.region : undefined;
  const region = regionRecord
    ? ({
        ...regionRecord,
        filePath: asLocalPath(regionRecord.filePath || regionRecord.file_path, 'evidence.region.filePath'),
      } as ScienceEvidenceItem['region'])
    : undefined;
  if (regionRecord && !region?.filePath) {
    throw new Error('evidence.region.filePath is required when evidence.region is provided.');
  }
  return {
    id,
    title: asString(value.title, id),
    sourceType:
      (asString(value.sourceType || value.source_type, 'dataset') as ScienceEvidenceItem['sourceType']) || 'dataset',
    claimType:
      value.claimType || value.claim_type
        ? (asString(value.claimType || value.claim_type) as ScienceEvidenceItem['claimType'])
        : undefined,
    confidence: (asString(value.confidence, 'moderate') as ScienceEvidenceItem['confidence']) || 'moderate',
    status: (asString(value.status, 'available') as ScienceEvidenceItem['status']) || 'available',
    summary: asString(value.summary, undefined as unknown as string),
    path: asLocalPath(value.path, 'evidence.path'),
    url: asString(value.url, undefined as unknown as string),
    virtualPath: asString(value.virtualPath || value.virtual_path, undefined as unknown as string),
    command: asString(value.command, undefined as unknown as string),
    lineStart: value.lineStart || value.line_start ? asNumber(value.lineStart || value.line_start, 0) : undefined,
    lineEnd: value.lineEnd || value.line_end ? asNumber(value.lineEnd || value.line_end, 0) : undefined,
    gitAnchor: normalizeGitAnchor(run, value.gitAnchor || value.git_anchor || value.anchor),
    artifactId: asString(value.artifactId || value.artifact_id, undefined as unknown as string),
    artifactVersion:
      value.artifactVersion || value.artifact_version
        ? asNumber(value.artifactVersion || value.artifact_version, 1)
        : undefined,
    nodeId: asString(value.nodeId || value.node_id, undefined as unknown as string),
    supportingEvidenceIds: asArray(value.supportingEvidenceIds || value.supporting_evidence_ids).filter(
      (item): item is string => typeof item === 'string'
    ),
    hash: asString(value.hash, undefined as unknown as string),
    version: value.version ? asNumber(value.version, 1) : undefined,
    skillUseId: asString(value.skillUseId || value.skill_use_id, undefined as unknown as string),
    connectorId: asString(value.connectorId || value.connector_id, undefined as unknown as string),
    database: isRecord(value.database) ? (value.database as ScienceEvidenceItem['database']) : undefined,
    region,
    createdAt: asNumber(value.createdAt || value.created_at, now()),
    revision: asString(value.revision, revision()),
  };
};

const normalizeArtifact = (run: ScienceRunState, value: JsonRecord): ScienceArtifact => {
  const id = asString(value.id, makeId('artifact'));
  const version = asNumber(value.version, 1);
  // Auto-infer primaryPath from fallback fields when agent omits it
  const rawPrimaryPath = asLocalPath(value.primaryPath || value.primary_path || value.path, 'primaryPath');
  const outputPaths = asLocalPathArray(value.outputPaths || value.output_paths, 'outputPaths');
  const codeRecord = isRecord(value.code) ? value.code : undefined;
  const executionRecord = isRecord(value.execution) ? value.execution : undefined;
  const codePath = asLocalPath(codeRecord?.path, 'code.path');
  const executionScriptPath = asLocalPath(
    executionRecord?.scriptPath || executionRecord?.script_path,
    'execution.scriptPath'
  );
  const primaryPath = rawPrimaryPath || outputPaths[0] || codePath || undefined;
  const meta = fileMeta(primaryPath, run.projectRoot);
  const metadata = isRecord(value.metadata) ? value.metadata : undefined;
  const hasTargetDiscoveryMetadata = Boolean(metadata && Object.hasOwn(metadata, 'targetDiscovery'));
  const hasFinancialFactorMetadata = Boolean(metadata && Object.hasOwn(metadata, 'financialFactor'));
  const hasResearchRouteMetadata = Boolean(metadata && Object.hasOwn(metadata, 'researchRoute'));
  const targetPortfolio = readTargetDiscoveryPortfolio(metadata);
  const factorPortfolio = readFinancialFactorPortfolio(metadata);
  const researchRouteValidation = hasResearchRouteMetadata
    ? validateResearchRouteMap(metadata?.researchRoute)
    : undefined;
  if (hasResearchRouteMetadata && id !== RESEARCH_ROUTE_ARTIFACT_ID) {
    throw new Error(`metadata.researchRoute must be stored on the stable ${RESEARCH_ROUTE_ARTIFACT_ID} artifact.`);
  }
  if (hasTargetDiscoveryMetadata && !targetPortfolio) {
    throw new Error(
      'metadata.targetDiscovery must be a complete deepscientist.target_discovery.portfolio.v1 object. Use schema and numeric version=1 plus title, stage, status, updatedAt, context, branches, candidates, sourceHealth, blockers, and nextActions; portfolioVersion or a status-only stub is not valid.'
    );
  }
  if (hasFinancialFactorMetadata && !factorPortfolio) {
    throw new Error(
      'metadata.financialFactor must be a complete deepscientist.financial_factor.portfolio.v1 object. Every factor requires id, name, expression, hypothesis, selectionReason, decisionReason, status, checks, evidenceIds, and updatedAt; measured metrics also require metricContext.'
    );
  }
  if (researchRouteValidation?.ok === false) {
    throw new Error(`metadata.researchRoute is invalid: ${researchRouteValidation.error}.`);
  }
  if (researchRouteValidation && 'value' in researchRouteValidation) {
    const disciplineIssues = validateResearchRoadmapDiscipline(researchRouteValidation.value);
    if (disciplineIssues.length) {
      throw new Error(
        `metadata.researchRoute violates stage discipline: ${disciplineIssues.join(' ')} Use research_roadmap(action="validate") before writing.`
      );
    }
  }
  const artifactRevision = asString(value.revision, revision());
  const artifactCreatedAt = asNumber(value.createdAt || value.created_at, now());
  const artifactEvidenceIds = asArray(value.evidenceIds || value.evidence_ids).filter(
    (item): item is string => typeof item === 'string'
  );
  const financeKind = metadata
    ? asString(
        (isRecord(metadata.finance) ? metadata.finance.kind : undefined) || metadata.financeKind || metadata.kind,
        ''
      )
    : '';
  const isFinanceArtifact = FINANCE_ARTIFACT_KINDS.includes(financeKind as (typeof FINANCE_ARTIFACT_KINDS)[number]);
  const inputFinanceMetadata = metadata && isRecord(metadata.finance) ? metadata.finance : metadata;
  const financeCurrencies = inputFinanceMetadata
    ? asArray(inputFinanceMetadata.currencies).filter((item): item is string => typeof item === 'string')
    : [];
  const financeEvidenceIds = inputFinanceMetadata
    ? asArray(inputFinanceMetadata.evidenceIds).filter((item): item is string => typeof item === 'string')
    : [];
  const normalizedFinanceDataMode = inputFinanceMetadata
    ? asString(inputFinanceMetadata.dataMode, financeKind === 'research_portfolio' ? 'SIMULATION' : 'HISTORICAL')
    : 'HISTORICAL';
  const normalizedFinanceMetadata =
    isFinanceArtifact && inputFinanceMetadata
      ? {
          schema: asString(inputFinanceMetadata.schema, 'deepscientist.finance.artifact.v1'),
          kind: financeKind,
          ...(inputFinanceMetadata.contractId ? { contractId: asString(inputFinanceMetadata.contractId) } : {}),
          ...(inputFinanceMetadata.contractVersion
            ? { contractVersion: asString(inputFinanceMetadata.contractVersion) }
            : {}),
          ...(inputFinanceMetadata.contractHash ? { contractHash: asString(inputFinanceMetadata.contractHash) } : {}),
          snapshotId: asString(inputFinanceMetadata.snapshotId, artifactRevision),
          asOf: asString(inputFinanceMetadata.asOf, new Date(artifactCreatedAt).toISOString()),
          refreshedAt: asString(
            inputFinanceMetadata.refreshedAt || inputFinanceMetadata.asOf,
            new Date(artifactCreatedAt).toISOString()
          ),
          timezone: asString(inputFinanceMetadata.timezone, 'UTC'),
          currency:
            asString(inputFinanceMetadata.currency, '') || financeCurrencies.find((currency) => currency.trim()),
          ...(financeCurrencies.length ? { currencies: financeCurrencies } : {}),
          dataMode: normalizedFinanceDataMode,
          tradeCapability: 'disabled',
          sopId: asString(inputFinanceMetadata.sopId || inputFinanceMetadata.contractId, `finance.${financeKind}`),
          sopVersion: asString(inputFinanceMetadata.sopVersion || inputFinanceMetadata.contractVersion, '1.0.0'),
          evidenceIds: financeEvidenceIds.length ? financeEvidenceIds : artifactEvidenceIds,
          ...(inputFinanceMetadata.status ? { status: asString(inputFinanceMetadata.status) } : {}),
          ...(inputFinanceMetadata.sourceManifestPath
            ? { sourceManifestPath: asString(inputFinanceMetadata.sourceManifestPath) }
            : {}),
          ...(inputFinanceMetadata.dataRevision ? { dataRevision: asString(inputFinanceMetadata.dataRevision) } : {}),
          ...(inputFinanceMetadata.contentSha256
            ? { contentSha256: asString(inputFinanceMetadata.contentSha256) }
            : {}),
          ...(isRecord(inputFinanceMetadata.simulation) ? { simulation: inputFinanceMetadata.simulation } : {}),
        }
      : undefined;
  if (normalizedFinanceMetadata) {
    const parsed = financeArtifactMetadataSchema.safeParse(normalizedFinanceMetadata);
    if (!parsed.success) {
      throw new Error(
        `metadata.finance is invalid: ${parsed.error.issues
          .map((issue) => `${issue.path.join('.') || 'finance'}: ${issue.message}`)
          .join(' | ')}`
      );
    }
  }
  const normalizedMetadata: JsonRecord | undefined = metadata
    ? {
        ...metadata,
        ...(normalizedFinanceMetadata ? { finance: normalizedFinanceMetadata } : {}),
        ...(researchRouteValidation?.ok ? { researchRoute: researchRouteValidation.value } : {}),
      }
    : undefined;
  const viewer = normalizeArtifactViewer(value.viewer);
  const code: ScienceArtifact['code'] = codeRecord
    ? {
        path: codePath,
        language: codeRecord.language as ScienceArtifact['code']['language'],
        entrypoint: asString(codeRecord.entrypoint, undefined as unknown as string),
        cellIds: asArray(codeRecord.cellIds || codeRecord.cell_ids).filter(
          (item): item is string => typeof item === 'string'
        ),
      }
    : undefined;
  const execution: ScienceArtifact['execution'] = executionRecord
    ? {
        command: asString(executionRecord.command, undefined as unknown as string),
        scriptPath: executionScriptPath,
        cwd: asLocalPath(executionRecord.cwd, 'execution.cwd'),
        logPath: asLocalPath(executionRecord.logPath || executionRecord.log_path, 'execution.logPath'),
        stdoutPreview: asString(
          executionRecord.stdoutPreview || executionRecord.stdout_preview,
          undefined as unknown as string
        ),
        stderrPreview: asString(
          executionRecord.stderrPreview || executionRecord.stderr_preview,
          undefined as unknown as string
        ),
        startedAt:
          executionRecord.startedAt || executionRecord.started_at
            ? asNumber(executionRecord.startedAt || executionRecord.started_at, 0)
            : undefined,
        endedAt:
          executionRecord.endedAt || executionRecord.ended_at
            ? asNumber(executionRecord.endedAt || executionRecord.ended_at, 0)
            : undefined,
        exitCode:
          executionRecord.exitCode != null || executionRecord.exit_code != null
            ? asNumber(executionRecord.exitCode ?? executionRecord.exit_code, 0)
            : undefined,
      }
    : undefined;
  const artifact: ScienceArtifact = {
    id,
    runId: run.runId,
    type: (asString(value.type, 'run_bundle') as ScienceArtifact['type']) || 'run_bundle',
    title: asString(value.title, id),
    version,
    versionGroupId: asString(value.versionGroupId || value.version_group_id, id),
    previousArtifactId: asString(
      value.previousArtifactId || value.previous_artifact_id,
      undefined as unknown as string
    ),
    previousVersion:
      value.previousVersion || value.previous_version
        ? asNumber(value.previousVersion || value.previous_version, version - 1)
        : undefined,
    revision: artifactRevision,
    changeSummary: asString(value.changeSummary || value.change_summary, undefined as unknown as string),
    status:
      (asString(value.status, meta.status || 'available') as ScienceArtifact['status']) || meta.status || 'available',
    primaryPath,
    previewPath: asLocalPath(value.previewPath || value.preview_path, 'previewPath'),
    thumbnailPath: asLocalPath(value.thumbnailPath || value.thumbnail_path, 'thumbnailPath'),
    sourcePaths: asLocalPathArray(value.sourcePaths || value.source_paths, 'sourcePaths'),
    inputPaths: asLocalPathArray(value.inputPaths || value.input_paths, 'inputPaths'),
    outputPaths,
    contentHash: asString(value.contentHash || value.content_hash, meta.contentHash),
    sizeBytes:
      value.sizeBytes || value.size_bytes
        ? asNumber(value.sizeBytes || value.size_bytes, meta.sizeBytes || 0)
        : meta.sizeBytes,
    mimeType: asString(value.mimeType || value.mime_type, undefined as unknown as string),
    code,
    execution,
    environment: isRecord(value.environment) ? (value.environment as ScienceArtifact['environment']) : undefined,
    inputs: Array.isArray(value.inputs) ? (value.inputs as ScienceArtifact['inputs']) : undefined,
    relatedMessageIds: asArray(value.relatedMessageIds || value.related_message_ids).filter(
      (item): item is string => typeof item === 'string'
    ),
    relatedToolCallIds: asArray(value.relatedToolCallIds || value.related_tool_call_ids).filter(
      (item): item is string => typeof item === 'string'
    ),
    defaultInspectorTab: asString(
      value.defaultInspectorTab || value.default_inspector_tab,
      undefined as unknown as string
    ) as ScienceArtifact['defaultInspectorTab'],
    availableTabs: Array.isArray(value.availableTabs || value.available_tabs)
      ? ((value.availableTabs || value.available_tabs) as ScienceArtifact['availableTabs'])
      : undefined,
    evidenceIds: artifactEvidenceIds,
    provenanceNodeIds: asArray(value.provenanceNodeIds || value.provenance_node_ids).filter(
      (item): item is string => typeof item === 'string'
    ),
    reviewStatus:
      (asString(value.reviewStatus || value.review_status, 'not_reviewed') as ScienceArtifact['reviewStatus']) ||
      'not_reviewed',
    viewer: targetPortfolio
      ? { ...(viewer || {}), kind: 'target_discovery' }
      : factorPortfolio
        ? { ...(viewer || {}), kind: 'financial_factor' }
        : isFinanceArtifact
          ? { ...(viewer || {}), kind: 'financial_research' }
          : viewer,
    metadata: normalizedMetadata,
    createdAt: artifactCreatedAt,
  };
  verifyReportChartArtifactHandoff(run, artifact);
  verifyMathematicsProofTraceArtifactHandoff(run, artifact);
  return artifact;
};

const normalizePage = (run: ScienceRunState, value: JsonRecord): ScienceArtifactPage => ({
  id: asString(value.id, makeId('page')),
  runId: run.runId,
  title: asString(value.title, 'Science Artifact Workspace'),
  kind: (asString(value.kind, 'artifact_workspace') as ScienceArtifactPage['kind']) || 'artifact_workspace',
  layout:
    (asString(value.layout, 'report_artifact_inspector') as ScienceArtifactPage['layout']) ||
    'report_artifact_inspector',
  panes: Array.isArray(value.panes) ? (value.panes as ScienceArtifactPage['panes']) : [],
  revision: asString(value.revision, revision()),
});

const normalizeClaim = (run: ScienceRunState, value: JsonRecord): ScienceClaim => ({
  id: asString(value.id, makeId('claim')),
  runId: run.runId,
  text: asString(value.text, 'Untitled Science claim'),
  claimType: (asString(value.claimType || value.claim_type, 'hypothesis') as ScienceClaim['claimType']) || 'hypothesis',
  status: (asString(value.status, 'hypothesis') as ScienceClaim['status']) || 'hypothesis',
  supportingEvidenceIds: asArray(
    value.supportingEvidenceIds || value.supporting_evidence_ids || value.evidenceIds || value.evidence_ids
  ).filter((item): item is string => typeof item === 'string'),
  artifactIds: asArray(value.artifactIds || value.artifact_ids).filter(
    (item): item is string => typeof item === 'string'
  ),
  provenanceNodeIds: asArray(value.provenanceNodeIds || value.provenance_node_ids).filter(
    (item): item is string => typeof item === 'string'
  ),
  limitations: asArray(value.limitations).filter((item): item is string => typeof item === 'string'),
  createdAt: asNumber(value.createdAt || value.created_at, now()),
  revision: asString(value.revision, revision()),
});

const normalizeNode = (run: ScienceRunState, value: JsonRecord): ScienceProvenanceNode => ({
  id: asString(value.id, makeId('provenance')),
  type: (asString(value.type, 'activity') as ScienceProvenanceNode['type']) || 'activity',
  label: asString(value.label, 'Science activity'),
  artifactId: asString(value.artifactId || value.artifact_id, undefined as unknown as string),
  evidenceIds: asArray(value.evidenceIds || value.evidence_ids).filter(
    (item): item is string => typeof item === 'string'
  ),
  parents: asArray(value.parents).filter((item): item is string => typeof item === 'string'),
  command: asString(value.command, undefined as unknown as string),
  path: asString(value.path, undefined as unknown as string),
  contentHash: asString(value.contentHash || value.content_hash, undefined as unknown as string),
  createdAt: asNumber(value.createdAt || value.created_at, now()),
  metadata: isRecord(value.metadata) ? value.metadata : undefined,
  revision: asString(value.revision, revision()),
});

const normalizeEdge = (run: ScienceRunState, value: JsonRecord): ScienceProvenanceEdge => ({
  id: asString(value.id, makeId('provenance')),
  runId: run.runId,
  from: (isRecord(value.from)
    ? value.from
    : { kind: 'node', id: asString(value.fromId || value.from_id, '') }) as ScienceProvenanceEdge['from'],
  to: (isRecord(value.to)
    ? value.to
    : { kind: 'node', id: asString(value.toId || value.to_id, '') }) as ScienceProvenanceEdge['to'],
  type: (asString(value.type, 'derived_from') as ScienceProvenanceEdge['type']) || 'derived_from',
  label: asString(value.label, undefined as unknown as string),
  confidence: (asString(value.confidence, 'declared') as ScienceProvenanceEdge['confidence']) || 'declared',
  createdAt: asNumber(value.createdAt || value.created_at, now()),
});

const normalizeSkillUse = (run: ScienceRunState, value: JsonRecord): ScienceSkillUse => ({
  id: asString(value.id, makeId('skill_use')),
  runId: run.runId,
  skillId: asString(value.skillId || value.skill_id, 'unknown-skill'),
  skillName: asString(value.skillName || value.skill_name, asString(value.skillId || value.skill_id, 'Unknown skill')),
  source: (asString(value.source, 'local') as ScienceSkillUse['source']) || 'local',
  sourceUrl: asString(value.sourceUrl || value.source_url, undefined as unknown as string),
  version: asString(value.version, undefined as unknown as string),
  purpose: (asString(value.purpose, 'routing') as ScienceSkillUse['purpose']) || 'routing',
  status: (asString(value.status, 'used') as ScienceSkillUse['status']) || 'used',
  triggeredBy: asString(value.triggeredBy || value.triggered_by, 'Science Mode'),
  selectedBecause: asString(value.selectedBecause || value.selected_because, undefined as unknown as string),
  limitations: asArray(value.limitations).filter((item): item is string => typeof item === 'string'),
  evidenceIds: asArray(value.evidenceIds || value.evidence_ids).filter(
    (item): item is string => typeof item === 'string'
  ),
  artifactIds: asArray(value.artifactIds || value.artifact_ids).filter(
    (item): item is string => typeof item === 'string'
  ),
  createdAt: asNumber(value.createdAt || value.created_at, now()),
  revision: asString(value.revision, revision()),
});

const stringArray = (value: unknown): string[] =>
  asArray(value).filter((item): item is string => typeof item === 'string');

const RESULT_SUMMARY_BASES = new Set<ScienceResultSummaryMetric['basis']>([
  'measured',
  'synthetic',
  'literature',
  'estimated',
  'pending',
]);
const RESULT_SUMMARY_ROLES = new Set<ScienceResultSummaryMetric['role']>(['primary', 'baseline', 'secondary']);
const RESULT_SUMMARY_DIRECTIONS = new Set<NonNullable<ScienceResultSummaryMetric['direction']>>([
  'maximize',
  'minimize',
]);
const RESULT_SUMMARY_FACT_KEYS = new Set<NonNullable<ScienceResultSummaryFact['key']>>([
  'system',
  'dataset',
  'sample_size',
  'replicates',
  'condition',
  'method',
  'comparator',
  'scope',
  'threshold',
  'environment',
  'endpoint',
  'participants',
  'events',
  'censoring',
  'validation',
  'data_release',
  'modalities',
  'other',
]);

const asDisplayString = (value: unknown): string | undefined => {
  if (typeof value === 'string' && value.trim()) return value.trim();
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  return undefined;
};

const normalizeResultSummaryInterval = (value: unknown, field: string): ScienceResultSummaryMetric['interval'] => {
  if (value == null) return undefined;
  if (!isRecord(value)) throw new Error(`result_summary.${field}.interval must be an object.`);
  const kind = asString(value.kind, 'confidence') as NonNullable<ScienceResultSummaryMetric['interval']>['kind'];
  if (!['confidence', 'credible', 'range'].includes(kind)) {
    throw new Error(`result_summary.${field}.interval.kind is not supported.`);
  }
  const lower = asNumber(value.lower, Number.NaN);
  const upper = asNumber(value.upper, Number.NaN);
  if (!Number.isFinite(lower) || !Number.isFinite(upper) || lower > upper) {
    throw new Error(`result_summary.${field}.interval requires finite lower <= upper.`);
  }
  const level = value.level == null ? undefined : asNumber(value.level, Number.NaN);
  if (level != null && (!Number.isFinite(level) || level <= 0 || level > 1)) {
    throw new Error(`result_summary.${field}.interval.level must be in (0, 1].`);
  }
  return {
    kind,
    lower,
    upper,
    level,
    method: asDisplayString(value.method),
  };
};

const normalizeResultSummaryMetric = (
  value: unknown,
  inheritedEvidenceIds: string[],
  field: string
): ScienceResultSummaryMetric => {
  if (!isRecord(value)) throw new Error(`result_summary.${field} must be an object.`);
  const key = asString(value.key || value.id);
  const label = asString(value.label || value.name);
  if (!key || !/^[a-z][a-z0-9_.-]*$/iu.test(key)) {
    throw new Error(`result_summary.${field}.key must be a stable machine key.`);
  }
  if (!label) throw new Error(`result_summary.${field}.label is required.`);
  const role = asString(value.role) as ScienceResultSummaryMetric['role'];
  if (!RESULT_SUMMARY_ROLES.has(role)) {
    throw new Error(`result_summary.${field}.role must be primary, baseline, or secondary.`);
  }
  const rawBasis = asString(value.basis, 'pending') as ScienceResultSummaryMetric['basis'];
  if (!RESULT_SUMMARY_BASES.has(rawBasis)) {
    throw new Error(`result_summary.${field}.basis must be measured, synthetic, literature, estimated, or pending.`);
  }
  const evidenceIds = stringArray(value.evidenceIds || value.evidence_ids);
  const metricEvidenceIds = evidenceIds.length ? evidenceIds : inheritedEvidenceIds;
  const metricValue = value.value == null ? undefined : asNumber(value.value, Number.NaN);
  if (metricValue != null && !Number.isFinite(metricValue)) {
    throw new Error(`result_summary.${field}.value must be a finite number.`);
  }
  const interval = normalizeResultSummaryInterval(
    value.interval || value.confidenceInterval || value.confidence_interval,
    field
  );
  if (rawBasis === 'pending' && (metricValue != null || interval)) {
    throw new Error(`result_summary.${field} with basis=pending must omit value and interval.`);
  }
  if (rawBasis !== 'pending' && metricValue == null && !interval) {
    throw new Error(`result_summary.${field} requires value or interval when basis=${rawBasis}.`);
  }
  if (['measured', 'synthetic', 'literature'].includes(rawBasis) && !metricEvidenceIds.length) {
    throw new Error(`result_summary.${field} with basis=${rawBasis} requires evidenceIds.`);
  }
  const rawDirection = asString(
    value.direction,
    undefined as unknown as string
  ) as ScienceResultSummaryMetric['direction'];
  if (rawDirection && !RESULT_SUMMARY_DIRECTIONS.has(rawDirection)) {
    throw new Error(`result_summary.${field}.direction must be maximize or minimize.`);
  }
  return {
    key,
    label,
    role,
    value: metricValue,
    unit: asDisplayString(value.unit),
    direction: rawDirection || undefined,
    interval,
    comparison: asDisplayString(value.comparison || value.delta),
    basis: rawBasis,
    evidenceIds: metricEvidenceIds.length ? metricEvidenceIds : undefined,
  };
};

const normalizeResultSummaryFact = (value: unknown, index: number): ScienceResultSummaryFact => {
  if (!isRecord(value)) throw new Error(`result_summary.facts[${index}] must be an object.`);
  const label = asString(value.label || value.name);
  const displayValue = asDisplayString(value.value ?? value.detail);
  if (!label || !displayValue) {
    throw new Error(`result_summary.facts[${index}] requires label and value.`);
  }
  const rawKey = asString(value.key, undefined as unknown as string) as ScienceResultSummaryFact['key'];
  if (rawKey && !RESULT_SUMMARY_FACT_KEYS.has(rawKey)) {
    throw new Error(`result_summary.facts[${index}].key is not supported.`);
  }
  const evidenceIds = stringArray(value.evidenceIds || value.evidence_ids);
  return {
    key: rawKey || undefined,
    label,
    value: displayValue,
    evidenceIds: evidenceIds.length ? evidenceIds : undefined,
  };
};

const normalizeResultSummaryBlock = (value: JsonRecord, inheritedEvidenceIds: string[]): ScienceResultSummaryBlock => {
  const evidenceIds = stringArray(value.evidenceIds || value.evidence_ids);
  const blockEvidenceIds = evidenceIds.length ? evidenceIds : inheritedEvidenceIds;
  const rawVariant = asString(value.variant, 'generic');
  if (!['generic', 'survival_prediction'].includes(rawVariant)) {
    throw new Error('result_summary.variant must be generic or survival_prediction.');
  }
  const rawMetrics = asArray(value.metrics);
  if (rawMetrics.length > 4) throw new Error('result_summary.metrics supports at most 4 metrics.');
  const metrics = rawMetrics.map((item, index) =>
    normalizeResultSummaryMetric(item, blockEvidenceIds, `metrics[${index}]`)
  );
  if (!metrics.length) throw new Error('result_summary.metrics must contain 1 to 4 metrics.');
  const metricKeys = new Set(metrics.map((metric) => metric.key));
  if (metricKeys.size !== metrics.length) throw new Error('result_summary metric keys must be unique.');
  const primaryMetrics = metrics.filter((metric) => metric.role === 'primary');
  if (primaryMetrics.length !== 1) throw new Error('result_summary requires exactly one primary metric.');
  const rawFacts = asArray(value.facts);
  if (rawFacts.length > 6) throw new Error('result_summary.facts supports at most 6 facts.');
  const facts = rawFacts.map((item, index) => normalizeResultSummaryFact(item, index));
  const stableFactKeys = facts.map((item) => item.key).filter((key): key is NonNullable<typeof key> => Boolean(key));
  if (new Set(stableFactKeys).size !== stableFactKeys.length) {
    throw new Error('result_summary fact keys must be unique.');
  }

  const primaryMetric = primaryMetrics[0];
  if (rawVariant === 'survival_prediction') {
    if (!['measured', 'pending'].includes(primaryMetric.basis)) {
      throw new Error(
        'survival_prediction primary metric must be measured or pending; put synthetic, literature, and estimated values in baseline or secondary metrics.'
      );
    }
    if (primaryMetric.basis === 'measured') {
      const factKeys = new Set(facts.map((item) => item.key));
      const missingKeys = ['endpoint', 'participants', 'events', 'validation'].filter(
        (key) => !factKeys.has(key as ScienceResultSummaryFact['key'])
      );
      if (!primaryMetric.interval || missingKeys.length) {
        throw new Error(
          `measured survival_prediction summaries require a confidence interval and endpoint, participants, events, and validation facts${
            missingKeys.length ? `; missing: ${missingKeys.join(', ')}` : ''
          }.`
        );
      }
    }
  }

  const takeaway = asString(value.takeaway || value.conclusion || value.summary);
  if (!takeaway) throw new Error('result_summary.takeaway is required.');
  return {
    type: 'result_summary',
    variant: rawVariant as ScienceResultSummaryBlock['variant'],
    title: asDisplayString(value.title),
    takeaway,
    metrics,
    facts: facts.length ? facts : undefined,
    note: asDisplayString(value.note || value.scopeNote || value.scope_note),
    evidenceIds: blockEvidenceIds.length ? blockEvidenceIds : undefined,
  };
};

const normalizeReportBlock = (value: unknown, inheritedEvidenceIds: string[] = []): ScienceReportBlock => {
  if (typeof value === 'string') {
    return { type: 'paragraph', text: value, evidenceIds: inheritedEvidenceIds };
  }

  if (!isRecord(value)) {
    return { type: 'paragraph', text: 'Science report item', evidenceIds: inheritedEvidenceIds };
  }

  const evidenceIds = stringArray(value.evidenceIds || value.evidence_ids);
  const blockEvidenceIds = evidenceIds.length ? evidenceIds : inheritedEvidenceIds;
  const type = asString(value.type, 'paragraph');

  if (type === 'result_summary') {
    return normalizeResultSummaryBlock(value, inheritedEvidenceIds);
  }

  if (type === 'bullet_list') {
    const items = asArray(value.items)
      .map((item) =>
        isRecord(item)
          ? {
              text: asString(item.text || item.content || item.label, 'Untitled item'),
              evidenceIds: stringArray(item.evidenceIds || item.evidence_ids),
              confidence: asString(item.confidence, undefined as unknown as string),
            }
          : { text: String(item), evidenceIds: blockEvidenceIds }
      )
      .filter((item) => item.text);
    return items.length
      ? { type: 'bullet_list', items }
      : {
          type: 'paragraph',
          text: asString(value.text || value.content, 'Science report item'),
          evidenceIds: blockEvidenceIds,
        };
  }

  if (type === 'checklist') {
    const items = asArray(value.items)
      .map((item) =>
        isRecord(item)
          ? {
              label: asString(item.label || item.text || item.content, 'Checklist item'),
              detail: asString(item.detail || item.description, undefined as unknown as string),
              status: asString(item.status, undefined as unknown as string),
              evidenceIds: stringArray(item.evidenceIds || item.evidence_ids),
            }
          : { label: String(item), evidenceIds: blockEvidenceIds }
      )
      .filter((item) => item.label);
    return items.length
      ? { type: 'checklist', items }
      : {
          type: 'paragraph',
          text: asString(value.text || value.content, 'Science report item'),
          evidenceIds: blockEvidenceIds,
        };
  }

  if (
    ['artifact_embed', 'figure_ref', 'table_ref', 'artifact_ref', 'code_ref'].includes(type) &&
    asString(value.artifactId || value.artifact_id)
  ) {
    const artifactId = asString(value.artifactId || value.artifact_id);
    if (type === 'artifact_embed') {
      return {
        type: 'artifact_embed',
        artifactId,
        display:
          (asString(value.display, undefined as unknown as string) as Extract<
            ScienceReportBlock,
            { type: 'artifact_embed' }
          >['display']) || undefined,
        renderer:
          (asString(value.renderer, undefined as unknown as string) as Extract<
            ScienceReportBlock,
            { type: 'artifact_embed' }
          >['renderer']) || undefined,
        caption: asString(value.caption, undefined as unknown as string),
        evidenceIds: blockEvidenceIds,
        showSource: typeof value.showSource === 'boolean' ? value.showSource : undefined,
        maxHeight: asNumber(value.maxHeight || value.max_height, undefined as unknown as number),
      };
    }
    return { type: type as 'figure_ref' | 'table_ref' | 'artifact_ref' | 'code_ref', artifactId };
  }

  if (type === 'card_ref' && asString(value.cardId || value.card_id)) {
    return { type: 'card_ref', cardId: asString(value.cardId || value.card_id) };
  }

  return {
    type: 'paragraph',
    text: asString(value.text || value.content || value.detail || value.label, 'Science report item'),
    evidenceIds: blockEvidenceIds,
  };
};

const SCIENCE_REPORT_VISUAL_ROLE_SET = new Set<string>(SCIENCE_REPORT_VISUAL_ROLES);

const normalizeReportVisualRole = (value: unknown): ScienceReportVisualRole | undefined => {
  const role = asString(value);
  return SCIENCE_REPORT_VISUAL_ROLE_SET.has(role) ? (role as ScienceReportVisualRole) : undefined;
};

const readVisualWaiverReason = (value: unknown): string | undefined => {
  if (!isRecord(value)) return undefined;
  return asDisplayString(
    value.internalVisualWaiverReason ||
      value.internal_visual_waiver_reason ||
      value.visualWaiverReason ||
      value.visual_waiver_reason
  );
};

const hasVisualWaiverReason = (value: unknown): boolean =>
  isRecord(value) &&
  ('internalVisualWaiverReason' in value ||
    'internal_visual_waiver_reason' in value ||
    'visualWaiverReason' in value ||
    'visual_waiver_reason' in value);

const publicScienceReport = (
  report: SciencePanelData['report'] | undefined
): SciencePanelData['report'] | undefined => {
  if (!report) return undefined;
  const visibleReport = clone(report) as SciencePanelData['report'] & JsonRecord;
  delete visibleReport.internalVisualWaiverReason;
  delete visibleReport.internal_visual_waiver_reason;
  delete visibleReport.visualWaiverReason;
  delete visibleReport.visual_waiver_reason;
  return visibleReport;
};

const normalizeReport = (value: JsonRecord): SciencePanelData['report'] => {
  const sections = asArray(value.sections)
    .map((section, index) => {
      const sectionRecord = isRecord(section) ? section : ({ content: String(section) } as JsonRecord);
      const evidenceIds = stringArray(sectionRecord.evidenceIds || sectionRecord.evidence_ids);
      const rawBlocks = asArray(sectionRecord.blocks);
      const blocks =
        rawBlocks.length > 0
          ? rawBlocks.map((block) => normalizeReportBlock(block, evidenceIds))
          : [
              normalizeReportBlock(
                {
                  type: 'paragraph',
                  text: asString(
                    sectionRecord.text || sectionRecord.content || sectionRecord.summary,
                    'Science report section'
                  ),
                  evidenceIds,
                },
                evidenceIds
              ),
            ];
      const visualRole = normalizeReportVisualRole(sectionRecord.visualRole || sectionRecord.visual_role);
      return {
        id: asString(sectionRecord.id, `section_${index + 1}`),
        role: asString(sectionRecord.role, undefined as unknown as string),
        ...(visualRole ? { visualRole } : {}),
        heading: asString(sectionRecord.heading || sectionRecord.title, `Section ${index + 1}`),
        blocks,
      };
    })
    .filter((section) => section.blocks.length > 0);

  const report = {
    title: asString(value.title, 'Science Artifact Report'),
    sections: sections.length
      ? sections
      : [
          {
            id: 'summary',
            heading: 'Summary',
            blocks: [
              normalizeReportBlock(asString(value.summary || value.content, 'Science report is being assembled.')),
            ],
          },
        ],
  } as SciencePanelData['report'] & JsonRecord;
  const resultSummaryCount = sections.reduce(
    (count, section) => count + section.blocks.filter((block) => block.type === 'result_summary').length,
    0
  );
  if (resultSummaryCount > 1) {
    throw new Error(
      'A Science report may contain at most one result_summary block. Update the existing block instead.'
    );
  }
  if (resultSummaryCount === 1 && sections[0]?.blocks[0]?.type !== 'result_summary') {
    throw new Error('The result_summary block must be the first block of the first report section.');
  }

  if (Array.isArray(value.evidence)) report.evidence = value.evidence as SciencePanelData['report']['evidence'];
  if (Array.isArray(value.claims)) report.claims = value.claims as SciencePanelData['report']['claims'];
  for (const key of ['language', 'summary', 'status', 'kind', 'revision']) {
    if (value[key] != null) report[key] = value[key];
  }
  return report;
};

const applyRunCards = (run: ScienceRunState, value: unknown): void => {
  const result = validateCardsAgainstResources(value, run.artifacts, run.evidence);
  if (result.ok === false) throw new Error(`Invalid report cards: ${result.errors.join(' | ')}`);
  run.cards = result.cards;
  run.cardDiagnostics = [];
};

const rawFinanceMetadata = (artifact: ScienceArtifact): JsonRecord | undefined => {
  if (!isRecord(artifact.metadata)) return undefined;
  return isRecord(artifact.metadata.finance) ? artifact.metadata.finance : artifact.metadata;
};

const financeCardDraftContext = (run: ScienceRunState): StructuredReportCardDraftContext => {
  const artifacts = [...run.artifacts.values()];
  const primaryRef = run.financeCompletion?.artifactRefs.find((ref) => ref.role === 'primary');
  const artifact =
    (primaryRef
      ? artifacts.find(
          (candidate) => candidate.id === primaryRef.artifactId && candidate.version === primaryRef.version
        )
      : undefined) ||
    artifacts
      .filter((candidate) => Boolean(readFinanceArtifactKind(candidate.metadata)))
      .toSorted((left, right) => right.createdAt - left.createdAt || right.version - left.version)[0];
  if (!artifact) {
    throw new Error('cardDrafts require a versioned financial Artifact registered in the same run.');
  }

  const parsedMetadata = readFinanceArtifactMetadata(artifact.metadata);
  const rawMetadata = rawFinanceMetadata(artifact);
  const rawMode = asString(rawMetadata?.dataMode, '');
  const dataMode =
    parsedMetadata?.dataMode ||
    (['HISTORICAL', 'SIMULATION', 'LIVE_READ_ONLY'].includes(rawMode)
      ? (rawMode as StructuredReportCardDraftContext['dataMode'])
      : readFinanceArtifactKind(artifact.metadata) === 'research_portfolio'
        ? 'SIMULATION'
        : 'HISTORICAL');
  const refreshedAt =
    parsedMetadata?.refreshedAt ||
    asString(rawMetadata?.refreshedAt || rawMetadata?.asOf, '') ||
    new Date(artifact.createdAt || now()).toISOString();
  const artifactRef = {
    artifactId: artifact.id,
    version: artifact.version,
    ...(artifact.revision ? { revision: artifact.revision } : {}),
    ...(artifact.contentHash ? { contentSha256: artifact.contentHash } : {}),
  };
  return {
    artifactRef,
    snapshotId:
      parsedMetadata?.snapshotId ||
      asString(rawMetadata?.snapshotId, '') ||
      artifact.revision ||
      `${artifact.id}@${artifact.version}`,
    refreshedAt,
    dataMode,
    completeness: run.status === 'completed' ? 'complete' : 'partial',
    evidence: [...run.evidence.values()].map((item) => ({
      evidenceId: item.id,
      title: item.title,
      source: item.database?.name || item.sourceType,
      asOf: new Date(item.createdAt || Date.parse(refreshedAt) || now()).toISOString(),
      ...(item.summary ? { detail: item.summary } : {}),
    })),
    ...(dataMode === 'SIMULATION' ? { simulationAssumptionsArtifactRef: artifactRef } : {}),
  };
};

const optionalFinanceCardDraftContext = (run: ScienceRunState): StructuredReportCardDraftContext | undefined => {
  try {
    return financeCardDraftContext(run);
  } catch {
    return undefined;
  }
};

const attachPlacedCardsToReport = (run: ScienceRunState): void => {
  if (!run.report) return;
  const referencedCardIds = new Set(
    run.report.sections.flatMap((section) =>
      section.blocks.flatMap((block) => (block.type === 'card_ref' ? [block.cardId] : []))
    )
  );
  for (const card of run.cards) {
    if (!card.reportSectionRole || referencedCardIds.has(card.id)) continue;
    const section = run.report.sections.find(
      (candidate) => (candidate.role || candidate.id) === card.reportSectionRole
    );
    if (!section) {
      run.cardDiagnostics.push(`card ${card.id}: report section role ${card.reportSectionRole} was not found`);
      continue;
    }
    section.blocks.push({ type: 'card_ref', cardId: card.id });
    referencedCardIds.add(card.id);
  }
};

const applyRunCardPayload = (run: ScienceRunState, payload: JsonRecord): void => {
  if (payload.cards !== undefined && payload.cardDrafts !== undefined) {
    throw new Error('Pass either payload.cards or payload.cardDrafts, not both.');
  }
  if (payload.cards !== undefined) {
    applyRunCards(run, payload.cards);
    attachPlacedCardsToReport(run);
    return;
  }
  if (payload.cardDrafts === undefined) {
    attachPlacedCardsToReport(run);
    return;
  }
  const result = materializeStructuredReportCardDrafts(payload.cardDrafts, financeCardDraftContext(run));
  if (result.ok === false) throw new Error(`Invalid financial cardDrafts: ${result.errors.join(' | ')}`);
  run.cards = result.cards;
  run.cardDiagnostics = [];
  attachPlacedCardsToReport(run);
};

const applyFinanceCompletion = (run: ScienceRunState, value: unknown): void => {
  const result = financeCompletionManifestSchema.safeParse(value);
  if (!result.success) {
    throw new Error(
      `Invalid Finance completion manifest: ${result.error.issues
        .map((issue) => `${issue.path.join('.') || 'manifest'}: ${issue.message}`)
        .join(' | ')}`
    );
  }
  run.financeCompletion = result.data as FinanceCompletionManifest;
};

const upsertEdge = (run: ScienceRunState, edge: ScienceProvenanceEdge): void => {
  if (!edge.from.id || !edge.to.id) return;
  run.edges.set(edge.id, edge);
};

const syncArtifactEdges = (run: ScienceRunState, artifact: ScienceArtifact): void => {
  for (const evidenceId of artifact.evidenceIds || []) {
    upsertEdge(run, {
      id: `edge_${evidenceId}_${artifact.id}_${artifact.version}`,
      runId: run.runId,
      from: { kind: 'evidence', id: evidenceId },
      to: { kind: 'artifact', id: artifact.id, version: artifact.version },
      type: 'supports',
      confidence: 'declared',
      createdAt: now(),
    });
  }
  for (const input of artifact.inputs || []) {
    if (input.evidenceId) {
      upsertEdge(run, {
        id: `edge_${input.evidenceId}_${artifact.id}_${artifact.version}_input`,
        runId: run.runId,
        from: { kind: 'evidence', id: input.evidenceId },
        to: { kind: 'artifact', id: artifact.id, version: artifact.version },
        type: 'uses_input',
        confidence: 'declared',
        createdAt: now(),
      });
    }
    if (input.artifactId) {
      upsertEdge(run, {
        id: `edge_${input.artifactId}_${artifact.id}_${artifact.version}_input`,
        runId: run.runId,
        from: { kind: 'artifact', id: input.artifactId },
        to: { kind: 'artifact', id: artifact.id, version: artifact.version },
        type: 'uses_input',
        confidence: 'declared',
        createdAt: now(),
      });
    }
  }
  if (artifact.previousArtifactId || artifact.previousVersion) {
    upsertEdge(run, {
      id: `edge_${artifact.id}_${artifact.previousVersion || 'prev'}_${artifact.version}`,
      runId: run.runId,
      from: { kind: 'artifact', id: artifact.previousArtifactId || artifact.id, version: artifact.previousVersion },
      to: { kind: 'artifact', id: artifact.id, version: artifact.version },
      type: 'supersedes',
      confidence: 'declared',
      createdAt: now(),
    });
  }
};

const syncEvidenceEdges = (run: ScienceRunState, evidence: ScienceEvidenceItem): void => {
  if (evidence.artifactId) {
    upsertEdge(run, {
      id: `edge_${evidence.artifactId}_${evidence.artifactVersion || 'latest'}_${evidence.id}_file_evidence`,
      runId: run.runId,
      from: { kind: 'artifact', id: evidence.artifactId, version: evidence.artifactVersion },
      to: { kind: 'evidence', id: evidence.id },
      type: 'supports',
      label: 'file evidence',
      confidence: 'declared',
      createdAt: now(),
    });
  }

  if (evidence.nodeId) {
    upsertEdge(run, {
      id: `edge_${evidence.nodeId}_${evidence.id}_generated`,
      runId: run.runId,
      from: { kind: 'node', id: evidence.nodeId },
      to: { kind: 'evidence', id: evidence.id },
      type: 'generated',
      confidence: 'declared',
      createdAt: now(),
    });
  }

  for (const supportingEvidenceId of evidence.supportingEvidenceIds || []) {
    upsertEdge(run, {
      id: `edge_${supportingEvidenceId}_${evidence.id}_supports_evidence`,
      runId: run.runId,
      from: { kind: 'evidence', id: supportingEvidenceId },
      to: { kind: 'evidence', id: evidence.id },
      type: 'supports',
      confidence: 'declared',
      createdAt: now(),
    });
  }
};

const syncClaimEdges = (run: ScienceRunState, claim: ScienceClaim): void => {
  for (const evidenceId of claim.supportingEvidenceIds || []) {
    upsertEdge(run, {
      id: `edge_${evidenceId}_${claim.id}`,
      runId: run.runId,
      from: { kind: 'evidence', id: evidenceId },
      to: { kind: 'claim', id: claim.id },
      type: claim.status === 'blocked' ? 'contradicts' : 'supports',
      confidence: 'declared',
      createdAt: now(),
    });
  }
  for (const artifactId of claim.artifactIds || []) {
    upsertEdge(run, {
      id: `edge_${artifactId}_${claim.id}`,
      runId: run.runId,
      from: { kind: 'artifact', id: artifactId },
      to: { kind: 'claim', id: claim.id },
      type: claim.status === 'blocked' ? 'contradicts' : 'supports',
      confidence: 'declared',
      createdAt: now(),
    });
  }
};

const syncReportResources = (run: ScienceRunState, report: unknown): void => {
  if (!isRecord(report)) return;

  for (const item of asArray(report.evidence)) {
    if (!isRecord(item)) continue;
    const evidence = normalizeEvidence(run, item);
    run.evidence.set(evidence.id, evidence);
    syncEvidenceEdges(run, evidence);
  }

  for (const item of asArray(report.claims)) {
    if (!isRecord(item)) continue;
    const claim = normalizeClaim(run, item);
    run.claims.set(claim.id, claim);
    syncClaimEdges(run, claim);
  }
};

const RESULT_SUMMARY_COMPUTED_EVIDENCE = new Set<ScienceEvidenceItem['sourceType']>([
  'command_log',
  'computational_run',
  'dataset_analysis',
  'parameter_sweep',
  'validation_result',
  'remote_job',
  'regression_output',
  'statistical_model',
]);
const RESULT_SUMMARY_LITERATURE_EVIDENCE = new Set<ScienceEvidenceItem['sourceType']>(['paper', 'database_record']);

const existingEvidencePath = (run: ScienceRunState, filePath?: string): boolean => {
  if (!filePath) return false;
  const resolved = normalizeRelativePath(filePath, run.projectRoot);
  if (!path.isAbsolute(resolved) || !fs.existsSync(resolved)) return false;
  try {
    const stat = fs.statSync(resolved);
    if (stat.isFile()) return stat.size > 0;
    if (stat.isDirectory()) return fs.readdirSync(resolved).length > 0;
  } catch {
    return false;
  }
  return false;
};

const evidenceArtifactHasOutput = (run: ScienceRunState, evidence: ScienceEvidenceItem): boolean => {
  if (!evidence.artifactId) return false;
  const hasOutput = (artifact: ScienceArtifact): boolean =>
    [artifact.primaryPath, artifact.previewPath, artifact.thumbnailPath, ...(artifact.outputPaths || [])].some(
      (filePath) => existingEvidencePath(run, filePath)
    );
  if (evidence.artifactVersion != null) {
    const artifact = run.artifacts.get(artifactKey(evidence.artifactId, evidence.artifactVersion));
    return Boolean(artifact && hasOutput(artifact));
  }
  for (const artifact of run.artifacts.values()) {
    if (artifact.id === evidence.artifactId && hasOutput(artifact)) return true;
  }
  return false;
};

const hasConcreteEvidenceSource = (run: ScienceRunState, evidence: ScienceEvidenceItem): boolean =>
  existingEvidencePath(run, evidence.path) ||
  evidenceArtifactHasOutput(run, evidence) ||
  Boolean(evidence.gitAnchor?.commit && evidence.gitAnchor.commit !== 'WORKTREE') ||
  Boolean(evidence.url || evidence.virtualPath || evidence.command || evidence.hash);

const hasDurableMathematicsEvidenceSource = (run: ScienceRunState, evidence: ScienceEvidenceItem): boolean =>
  existingEvidencePath(run, evidence.path) ||
  evidenceArtifactHasOutput(run, evidence) ||
  Boolean(evidence.gitAnchor?.commit && evidence.gitAnchor.commit !== 'WORKTREE') ||
  Boolean(evidence.url && evidence.hash) ||
  Boolean(evidence.virtualPath && evidence.hash) ||
  Boolean(evidence.command && evidence.hash);

const mathematicsEvidenceIds = (portfolio: MathematicsPortfolio): string[] => {
  const evidenceIds: string[] = [];
  const seenEvidenceIds = new Set<string>();
  for (const item of portfolio.evidence || []) {
    for (const evidenceId of item.evidenceIds) {
      if (seenEvidenceIds.has(evidenceId)) continue;
      seenEvidenceIds.add(evidenceId);
      evidenceIds.push(evidenceId);
    }
  }
  return evidenceIds;
};

/**
 * Enforce the boundary between a typed math conclusion and the shared
 * Science Evidence graph. Structural validation lives in common/chat; this
 * process-side check resolves the referenced evidence ids and verifies that
 * they still point to available, concrete sources in the bound run.
 */
const assertMathematicsEvidenceSources = (
  run: ScienceRunState,
  portfolio: MathematicsPortfolio,
  evidenceIds?: Set<string>
): ReadonlyMap<string, MathematicsPortfolio['evidence'][number][]> => {
  const evidenceByProblem = new Map<string, MathematicsPortfolio['evidence'][number][]>();
  const concreteSourceByEvidenceId = new Map<string, boolean>();
  for (const item of portfolio.evidence || []) {
    const records = evidenceByProblem.get(item.problemId);
    if (records) records.push(item);
    else evidenceByProblem.set(item.problemId, [item]);
    for (const evidenceId of item.evidenceIds) {
      evidenceIds?.add(evidenceId);
      const evidence = run.evidence.get(evidenceId);
      if (!evidence) {
        throw new Error(`Mathematics evidence ${item.id} references unknown Science evidence ${evidenceId}.`);
      }
      if (evidence.status && evidence.status !== 'available') {
        throw new Error(
          `Mathematics evidence ${item.id} references unavailable Science evidence ${evidenceId} (status=${evidence.status}).`
        );
      }
      let hasConcreteSource = concreteSourceByEvidenceId.get(evidenceId);
      if (hasConcreteSource === undefined) {
        hasConcreteSource = hasConcreteEvidenceSource(run, evidence);
        concreteSourceByEvidenceId.set(evidenceId, hasConcreteSource);
      }
      if (evidence.confidence === 'blocked' || !hasConcreteSource) {
        throw new Error(
          `Mathematics evidence ${item.id} references Science evidence ${evidenceId} without a concrete source.`
        );
      }
    }
  }
  return evidenceByProblem;
};

const verifiedMathematicsOfficialReceiptIds = (portfolio: MathematicsPortfolio): ReadonlySet<string> => {
  const verified = new Set<string>();
  const secret = readMathematicsReceiptSecret();
  if (!secret) return verified;
  for (const problem of portfolio.problems) {
    if (!problem.officialGateReceipt) continue;
    const receipt = verifyMathOfficialGateReceipt(problem.officialGateReceipt, secret);
    if (receipt) verified.add(receipt.receiptId);
  }
  return verified;
};

const assertMathematicsDecisionGate = (run: ScienceRunState, portfolio: MathematicsPortfolio) => {
  const evidenceIds = new Set<string>();
  const evidenceByProblem = assertMathematicsEvidenceSources(run, portfolio, evidenceIds);
  const readiness = getMathematicsTerminalGateReadiness(portfolio, portfolio.activeProblemId, {
    evidenceByProblem,
    evidenceIds,
    verifiedOfficialReceiptIds: verifiedMathematicsOfficialReceiptIds(portfolio),
  });
  const terminalProblems = portfolio.problems.filter(
    (problem) => problem.status === 'verified' || problem.status === 'refuted'
  );
  if (!terminalProblems.length && !['verified', 'refuted'].includes(portfolio.status)) return readiness;
  const durableSourceByEvidenceId = new Map<string, boolean>();
  const hasDurableSource = (evidenceId: string): boolean => {
    const cached = durableSourceByEvidenceId.get(evidenceId);
    if (cached !== undefined) return cached;
    const evidence = run.evidence.get(evidenceId);
    const durable = Boolean(evidence && hasDurableMathematicsEvidenceSource(run, evidence));
    durableSourceByEvidenceId.set(evidenceId, durable);
    return durable;
  };

  for (const problem of terminalProblems) {
    const statementHash = problem.statementHash;
    const polarity = problem.status === 'verified' ? 'supporting' : 'refuting';
    for (const item of evidenceByProblem.get(problem.id) || []) {
      if (
        item.problemId !== problem.id ||
        item.statementHash !== statementHash ||
        item.polarity !== polarity ||
        ![polarity, 'formal'].includes(item.strength) ||
        !['reproduced', 'independent', 'formal'].includes(item.reproducibility)
      ) {
        continue;
      }
      if (!item.evidenceIds.some(hasDurableSource)) {
        throw new Error(`Problem ${problem.id} ${polarity} evidence needs a durable result, hash, or Git anchor.`);
      }
    }
  }
  return readiness;
};

type MathematicsVerificationIndex = {
  byReceiptId: ReadonlyMap<string, readonly MathematicsVerifierResult[]>;
  kernelIdentityKeys: ReadonlySet<string>;
};

const indexMathematicsVerifications = (run: ScienceRunState): MathematicsVerificationIndex => {
  const byReceiptId = new Map<string, MathematicsVerifierResult[]>();
  const kernelIdentityKeys = new Set<string>();
  for (const result of run.mathematicsVerifications) {
    const matches = byReceiptId.get(result.receiptId);
    if (matches) matches.push(result);
    else byReceiptId.set(result.receiptId, [result]);
    if (result.status === 'kernel_verified' && result.theoremDeclarationHash) {
      kernelIdentityKeys.add(
        JSON.stringify([result.proofHash, result.targetCommit, result.statementHash, result.claim, result.theoremName])
      );
    }
  }
  return { byReceiptId, kernelIdentityKeys };
};

const storedVerificationForLocalReceipt = (
  receipt: MathLocalGateReceipt,
  verificationIndex: MathematicsVerificationIndex
): MathematicsVerifierResult | undefined =>
  verificationIndex.byReceiptId
    .get(receipt.receiptId)
    ?.find(
      (result) =>
        result.status === 'kernel_verified' &&
        result.verifier === 'lean-kernel' &&
        result.targetCommit === receipt.targetCommit &&
        result.statementHash === receipt.statementHash &&
        result.claim === (receipt.claim || 'statement') &&
        (!receipt.leanStatementHash || result.leanStatementHash === receipt.leanStatementHash) &&
        result.proofHash === receipt.proofHash &&
        result.theoremName === receipt.theoremName &&
        result.theoremDeclarationHash === receipt.theoremDeclarationHash &&
        result.sourceDeclarationHash === receipt.sourceDeclarationHash &&
        result.goalsRemaining === 0 &&
        result.sorryCount === 0 &&
        result.admitCount === 0 &&
        result.axioms.length === receipt.axioms.length &&
        result.axioms.every((axiom) => isMathFoundationalLeanAxiom(axiom) && receipt.axioms.includes(axiom))
    );

const storedSuccessfulVerificationForReceipt = (
  receiptId: string,
  targetCommit: string,
  statementHash: string,
  verificationIndex: MathematicsVerificationIndex
): MathematicsVerifierResult | undefined =>
  verificationIndex.byReceiptId
    .get(receiptId)
    ?.find(
      (result) =>
        result.status === 'kernel_verified' &&
        result.verifier === 'lean-kernel' &&
        result.targetCommit === targetCommit &&
        result.statementHash === statementHash &&
        result.goalsRemaining === 0 &&
        result.sorryCount === 0 &&
        result.admitCount === 0 &&
        result.axioms.every(isMathFoundationalLeanAxiom) &&
        Boolean(result.theoremName && result.theoremDeclarationHash)
    );

/**
 * Select the exact LOCAL_GATE result named by an official receipt.  A batch may
 * contain several holes, and the official comparator signs only the decisive
 * theorem; positional selection would bind the gate to an unrelated sibling.
 */
export const selectMathematicsOfficialGateLocalResult = (
  batch: MathematicsVerifierBatchResult,
  localGateReceiptId: string
): MathematicsVerifierResult | undefined =>
  batch.results.find(
    (result) =>
      result.status === 'kernel_verified' &&
      result.verifier === 'lean-kernel' &&
      result.receiptId === localGateReceiptId
  );

/**
 * Bind an official-comparison request to the exact LOCAL_GATE receipt frozen
 * on the portfolio problem.  A receipt id alone is insufficient because the
 * verifier cache is project-scoped and can contain multiple candidates for
 * the same statement.
 */
export const assertMathematicsOfficialCompareReceiptBinding = (
  localReceipt: MathLocalGateReceipt,
  localVerification: MathematicsVerifierResult,
  localGateReceiptId: string,
  routeFingerprint: string
): void => {
  const normalizedRoute = normalizeMathRouteFingerprint(routeFingerprint);
  const receiptClaim = localReceipt.claim || 'statement';
  const verificationClaim = localVerification.claim || 'statement';
  if (
    localReceipt.receiptId !== localGateReceiptId ||
    localReceipt.status !== 'kernel_verified' ||
    localReceipt.verifier !== 'lean-kernel' ||
    localReceipt.targetCommit !== localVerification.targetCommit ||
    localReceipt.statementHash !== localVerification.statementHash ||
    receiptClaim !== verificationClaim ||
    (localReceipt.leanStatementHash !== undefined &&
      localReceipt.leanStatementHash !== localVerification.leanStatementHash) ||
    localReceipt.routeFingerprint !== normalizedRoute ||
    localReceipt.theoremName !== localVerification.theoremName ||
    localReceipt.proofHash !== localVerification.proofHash ||
    localReceipt.theoremDeclarationHash !== localVerification.theoremDeclarationHash ||
    localReceipt.sourceDeclarationHash !== localVerification.sourceDeclarationHash
  ) {
    throw new Error(
      'official_compare receipt must match the problem LOCAL_GATE receipt, theorem identity, commit, claim, and route.'
    );
  }
};

const referencedMathematicsReviewIds = (portfolio: MathematicsPortfolio): ReadonlySet<string> => {
  const reviewIds = new Set<string>();
  for (const problem of portfolio.problems) {
    if (problem.reviewId) reviewIds.add(problem.reviewId);
    for (const reviewId of problem.reviewIds ?? []) reviewIds.add(reviewId);
  }
  return reviewIds;
};

const assertCandidateReviewEvidenceBinding = (
  run: ScienceRunState,
  portfolio: MathematicsPortfolio,
  problemId: string,
  review: MathCandidateReview,
  verificationIndex: MathematicsVerificationIndex | undefined,
  portfolioEvidenceIds: ReadonlySet<string>
): void => {
  if (review.problemId !== problemId) {
    throw new Error('Mathematics CandidateReview problemId must match its owner review.');
  }
  const ownerProblem = portfolio.problems.find((problem) => problem.id === problemId);
  const localGateReceipt = ownerProblem?.localGateReceipt;
  if (!localGateReceipt) {
    throw new Error('Mathematics CandidateReview owner problem has no LOCAL_GATE receipt.');
  }
  const local = normalizeMathLocalGateReceipt(localGateReceipt);
  if (local.receiptId !== review.localGateReceiptId) {
    throw new Error('Mathematics CandidateReview must reference its owner problem LOCAL_GATE receipt.');
  }
  if (local.targetCommit !== review.targetCommit || local.statementHash !== review.statementHash) {
    throw new Error('Mathematics CandidateReview must target the same commit and statement as its LOCAL_GATE receipt.');
  }
  if ((local.claim || 'statement') !== 'statement') {
    throw new Error('Mathematics CandidateReview can only advance a statement LOCAL_GATE receipt.');
  }
  const replayReceiptId = review.replayReceiptId?.trim();
  if (replayReceiptId) {
    if (replayReceiptId === review.localGateReceiptId) {
      throw new Error('Mathematics Reviewer replay receipt must be distinct from the proposer LOCAL_GATE receipt.');
    }
    const replay = storedSuccessfulVerificationForReceipt(
      replayReceiptId,
      review.targetCommit,
      review.statementHash,
      verificationIndex
    );
    if (!replay) {
      throw new Error('Mathematics CandidateReview replayReceiptId is not backed by a matching Reviewer Lean receipt.');
    }
    if (
      replay.claim !== 'statement' ||
      replay.theoremName !== local.theoremName ||
      replay.proofHash !== local.proofHash ||
      replay.theoremDeclarationHash !== local.theoremDeclarationHash ||
      replay.sourceDeclarationHash !== local.sourceDeclarationHash ||
      replay.theoremName !== review.replayTheoremName ||
      replay.proofHash !== review.replayProofHash ||
      replay.theoremDeclarationHash !== review.replayTheoremDeclarationHash ||
      replay.sourceDeclarationHash !== review.replaySourceDeclarationHash
    ) {
      throw new Error(
        'Mathematics CandidateReview replay must recheck the exact LOCAL_GATE statement, theorem, declaration, and proof.'
      );
    }
  }
  const isValidEvidenceRef = (reference: string): boolean => {
    const value = reference.trim();
    if (value === `lean-receipt:${local.receiptId}`) return true;
    if (replayReceiptId && value === `lean-receipt:${replayReceiptId}`) return true;
    const portfolioMatch = /^portfolio-evidence:([^:]+)$/u.exec(value);
    if (portfolioMatch) return portfolioEvidenceIds.has(portfolioMatch[1]);
    const scienceMatch = /^science-evidence:([^:]+)$/u.exec(value);
    if (scienceMatch) return run.evidence.has(scienceMatch[1]);
    return false;
  };
  const validRefs = review.evidenceRefs.every(isValidEvidenceRef);
  const invalidFinding = (review.findings ?? []).find(
    (finding) => !finding.evidenceRefs.length || !finding.evidenceRefs.every(isValidEvidenceRef)
  );
  if (!review.evidenceRefs.length || !validRefs || invalidFinding) {
    throw new Error(
      'Mathematics CandidateReview evidenceRefs and finding evidenceRefs must resolve to the frozen Lean receipt, optional replay, portfolio evidence, or Science evidence.'
    );
  }
};

const assertMathematicsRuntimeReceipts = (
  run: ScienceRunState,
  portfolio: MathematicsPortfolio,
  verificationIndex: MathematicsVerificationIndex
): void => {
  const secret = readMathematicsReceiptSecret();
  const portfolioEvidenceIds = new Set<string>();
  const referencedReviewIds = referencedMathematicsReviewIds(portfolio);
  for (const item of portfolio.evidence) portfolioEvidenceIds.add(item.id);
  for (const problem of portfolio.problems) {
    if (problem.problemContract) {
      const payloads = canonicalMathProblemStatementPayloads(problem.problemContract);
      const negationPayload = canonicalMathProblemNegationPayload(problem.problemContract);
      const expectedStatementHash = sha256(payloads.informal);
      const expectedLeanStatementHash = sha256(payloads.lean);
      const expectedLeanNegationHash = negationPayload ? sha256(negationPayload) : undefined;
      if (
        problem.problemContract.statementHash !== expectedStatementHash ||
        problem.problemContract.leanStatementHash !== expectedLeanStatementHash ||
        problem.problemContract.leanNegationHash !== expectedLeanNegationHash
      ) {
        throw new Error(
          `Problem ${problem.id} statement hashes were not derived from its canonical immutable statements.`
        );
      }
    }
    if (!problem.localGateReceipt && !problem.officialGateReceipt) continue;
    if (!problem.localGateReceipt) {
      throw new Error(`Problem ${problem.id} has an official receipt without a local Lean receipt.`);
    }
    const localReceipt = normalizeMathLocalGateReceipt(problem.localGateReceipt);
    if (problem.problemContract) {
      const claim = localReceipt.claim || 'statement';
      const expectedLeanHash =
        claim === 'negation' ? problem.problemContract.leanNegationHash : problem.problemContract.leanStatementHash;
      const terminal = problem.status === 'verified' || problem.status === 'refuted';
      if (
        !expectedLeanHash ||
        (terminal && localReceipt.leanStatementHash !== expectedLeanHash) ||
        (!terminal &&
          localReceipt.leanStatementHash !== undefined &&
          localReceipt.leanStatementHash !== expectedLeanHash)
      ) {
        throw new Error(
          `Problem ${problem.id} local gate claim/hash does not match its immutable MathProblemContract.`
        );
      }
      if (localReceipt.statementHash !== problem.problemContract.statementHash) {
        throw new Error(`Problem ${problem.id} local gate statementHash does not match its MathProblemContract.`);
      }
    }
    if (!storedVerificationForLocalReceipt(localReceipt, verificationIndex)) {
      throw new Error(
        `Problem ${problem.id} local gate is not backed by a stored successful Lean receipt for the same commit, theorem, declaration, and proof hash.`
      );
    }
    if (problem.officialGateReceipt) {
      const officialReceipt = secret ? verifyMathOfficialGateReceipt(problem.officialGateReceipt, secret) : undefined;
      if (!officialReceipt) {
        throw new Error(
          `Problem ${problem.id} official gate receipt was not issued by formal_verifier(action="official_compare").`
        );
      }
      if (
        (officialReceipt.claim || 'statement') !== (localReceipt.claim || 'statement') ||
        officialReceipt.targetCommit !== localReceipt.targetCommit ||
        officialReceipt.statementHash !== localReceipt.statementHash ||
        officialReceipt.routeFingerprint !== localReceipt.routeFingerprint ||
        officialReceipt.localGateReceiptId !== localReceipt.receiptId ||
        officialReceipt.theoremName !== localReceipt.theoremName ||
        officialReceipt.proofHash !== localReceipt.proofHash ||
        officialReceipt.theoremDeclarationHash !== localReceipt.theoremDeclarationHash ||
        (officialReceipt.sourceDeclarationHash !== undefined &&
          officialReceipt.sourceDeclarationHash !== localReceipt.sourceDeclarationHash)
      ) {
        throw new Error(`Problem ${problem.id} official gate receipt does not match its stored local Lean receipt.`);
      }
      if (
        officialReceipt.problemId !== problem.id ||
        officialReceipt.officialManifestId !== problem.problemContract.officialManifestId ||
        officialReceipt.officialManifestHash !== problem.problemContract.officialManifestHash ||
        officialReceipt.leanStatementHash !==
          ((officialReceipt.claim || 'statement') === 'negation'
            ? problem.problemContract.leanNegationHash
            : problem.problemContract.leanStatementHash)
      ) {
        throw new Error(`Problem ${problem.id} official gate receipt does not match its committed manifest identity.`);
      }
    }
  }
  for (const review of portfolio.reviews) {
    if (!referencedReviewIds.has(review.id) || !review.candidateReview) continue;
    if (!secret || !verifyMathCandidateReview(review.candidateReview, secret)) {
      throw new Error(
        `Review ${review.id} was not issued by an independent research_team(deliver) Reviewer assignment.`
      );
    }
    if (review.candidateReview.problemId !== review.problemId) {
      throw new Error(`Review ${review.id} CandidateReview does not match its owner problem.`);
    }
    assertCandidateReviewEvidenceBinding(
      run,
      portfolio,
      review.problemId,
      review.candidateReview,
      verificationIndex,
      portfolioEvidenceIds
    );
  }
};

const hasDurableComputedEvidence = (run: ScienceRunState, evidence: ScienceEvidenceItem): boolean =>
  existingEvidencePath(run, evidence.path) ||
  evidenceArtifactHasOutput(run, evidence) ||
  Boolean(evidence.url && evidence.hash) ||
  Boolean(evidence.command && evidence.hash);

const claimArtifacts = (run: ScienceRunState, claim: ScienceClaim): ScienceArtifact[] =>
  [...run.artifacts.values()].filter((artifact) => claim.artifactIds?.includes(artifact.id));

const hasDurableArtifactOutput = (run: ScienceRunState, artifact: ScienceArtifact): boolean =>
  [artifact.primaryPath, artifact.previewPath, artifact.thumbnailPath, ...(artifact.outputPaths || [])].some(
    (filePath) => existingEvidencePath(run, filePath)
  ) || Boolean(artifact.git?.commit && artifact.git.files?.length);

const assertResultSummaryEvidence = (run: ScienceRunState): void => {
  const summaryBlocks =
    run.report?.sections.flatMap((section) => section.blocks.filter((block) => block.type === 'result_summary')) || [];
  const block = summaryBlocks[0];
  if (!block || block.type !== 'result_summary') return;

  const assertEvidenceIds = (ids: string[] | undefined, field: string): ScienceEvidenceItem[] =>
    (ids || []).map((id) => {
      const evidence = run.evidence.get(id);
      if (!evidence) throw new Error(`${field} references unknown evidence id ${id}.`);
      if ((evidence.status && evidence.status !== 'available') || evidence.confidence === 'blocked') {
        throw new Error(
          `${field} evidence ${id} is not available for a result claim (status=${evidence.status || 'available'}, confidence=${evidence.confidence}).`
        );
      }
      if (!hasConcreteEvidenceSource(run, evidence)) {
        throw new Error(`${field} evidence ${id} has no path, URL, command, virtual path, or artifact.`);
      }
      return evidence;
    });

  assertEvidenceIds(block.evidenceIds, 'result_summary');
  block.facts?.forEach((fact) => assertEvidenceIds(fact.evidenceIds, `result_summary fact ${fact.key || fact.label}`));
  block.metrics.forEach((metric) => {
    const evidence = assertEvidenceIds(metric.evidenceIds, `result_summary metric ${metric.key}`);
    if (['measured', 'synthetic', 'literature'].includes(metric.basis) && !evidence.length) {
      throw new Error(`result_summary metric ${metric.key} with basis=${metric.basis} requires evidence.`);
    }
    if (
      ['measured', 'synthetic'].includes(metric.basis) &&
      !evidence.some(
        (item) => RESULT_SUMMARY_COMPUTED_EVIDENCE.has(item.sourceType) && hasDurableComputedEvidence(run, item)
      )
    ) {
      throw new Error(
        `result_summary metric ${metric.key} with basis=${metric.basis} requires an existing result file or artifact, or a hashed remote/command result.`
      );
    }
    if (
      metric.basis === 'literature' &&
      !evidence.some((item) => RESULT_SUMMARY_LITERATURE_EVIDENCE.has(item.sourceType))
    ) {
      throw new Error(`result_summary metric ${metric.key} with basis=literature requires paper or database evidence.`);
    }
  });

  const primaryMetric = block.metrics.find((metric) => metric.role === 'primary');
  if (primaryMetric?.basis === 'pending' && run.status === 'completed') {
    run.status = 'partial';
  }
};

const validateGraph = (run: ScienceRunState): ScienceGraphWarning[] => {
  const warnings: ScienceGraphWarning[] = [...run.graphWarnings.values()];
  for (const evidence of run.evidence.values()) {
    if (!evidence.path && !evidence.url && !evidence.virtualPath && !evidence.command && !evidence.artifactId) {
      warnings.push({
        id: `warn_missing_source_${evidence.id}`,
        runId: run.runId,
        severity: 'warning',
        code: 'missing_source',
        message: `Evidence ${evidence.id} has no path, url, virtualPath, command, or artifactId.`,
        target: { kind: 'evidence', id: evidence.id },
        createdAt: now(),
      });
    }
  }
  for (const artifact of run.artifacts.values()) {
    const hasInput = Boolean(
      artifact.evidenceIds?.length ||
      artifact.inputPaths?.length ||
      artifact.inputs?.length ||
      artifact.sourcePaths?.length ||
      artifact.code?.path
    );
    if (!hasInput) {
      warnings.push({
        id: `warn_untraced_artifact_${artifact.id}_${artifact.version}`,
        runId: run.runId,
        severity: 'warning',
        code: 'untraced_artifact',
        message: `Artifact ${artifact.id} v${artifact.version} has no declared inputs, sources, code, or evidence ids.`,
        target: { kind: 'artifact', id: artifact.id, version: artifact.version },
        createdAt: now(),
      });
    }
    if (
      [
        'figure',
        'table',
        'dataset',
        'notebook',
        'manuscript',
        'pdf',
        'latex',
        'regression_table',
        'model_diagnostic',
        'causal_dag',
        'survey_codebook',
        'geospatial_map',
        'qualitative_coding',
        'replication_package',
      ].includes(artifact.type) &&
      !artifact.execution?.logPath
    ) {
      warnings.push({
        id: `warn_missing_execution_log_${artifact.id}_${artifact.version}`,
        runId: run.runId,
        severity: 'info',
        code: 'missing_execution_log',
        message: `Artifact ${artifact.id} v${artifact.version} has no execution log path.`,
        target: { kind: 'artifact', id: artifact.id, version: artifact.version },
        createdAt: now(),
      });
    }
  }
  for (const claim of run.claims.values()) {
    if (claim.claimType === 'hypothesis' || claim.status === 'hypothesis') continue;

    const evidence = claim.supportingEvidenceIds
      .map((id) => run.evidence.get(id))
      .filter(Boolean) as ScienceEvidenceItem[];
    const artifacts = claimArtifacts(run, claim);
    const missingEvidenceIds = claim.supportingEvidenceIds.filter((id) => !run.evidence.has(id));
    const missingArtifactIds = (claim.artifactIds || []).filter(
      (id) => ![...run.artifacts.values()].some((artifact) => artifact.id === id)
    );
    const unavailableEvidence = evidence.filter(
      (item) => (item.status && item.status !== 'available') || item.confidence === 'blocked'
    );
    const sourceLessEvidence = evidence.filter((item) => !hasConcreteEvidenceSource(run, item));

    if (missingEvidenceIds.length || missingArtifactIds.length) {
      warnings.push({
        id: `warn_broken_claim_reference_${claim.id}`,
        runId: run.runId,
        severity: 'error',
        code: 'broken_reference',
        message: `Claim ${claim.id} references unknown resources: ${[
          ...missingEvidenceIds.map((id) => `evidence ${id}`),
          ...missingArtifactIds.map((id) => `artifact ${id}`),
        ].join(', ')}.`,
        target: { kind: 'claim', id: claim.id },
        blocking: true,
        createdAt: now(),
      });
    }
    if (unavailableEvidence.length) {
      warnings.push({
        id: `warn_unavailable_claim_evidence_${claim.id}`,
        runId: run.runId,
        severity: 'error',
        code: 'unopenable_evidence',
        message: `Claim ${claim.id} uses unavailable evidence: ${unavailableEvidence.map((item) => item.id).join(', ')}.`,
        target: { kind: 'claim', id: claim.id },
        blocking: true,
        createdAt: now(),
      });
    }
    if (sourceLessEvidence.length) {
      warnings.push({
        id: `warn_sourceless_claim_evidence_${claim.id}`,
        runId: run.runId,
        severity: 'error',
        code: 'missing_source',
        message: `Claim ${claim.id} uses evidence without a concrete source: ${sourceLessEvidence
          .map((item) => item.id)
          .join(', ')}.`,
        target: { kind: 'claim', id: claim.id },
        blocking: true,
        createdAt: now(),
      });
    }
    if (!claim.supportingEvidenceIds.length && !claim.artifactIds?.length) {
      warnings.push({
        id: `warn_unsupported_claim_${claim.id}`,
        runId: run.runId,
        severity: 'error',
        code: 'unsupported_claim',
        message: `Claim ${claim.id} is not marked as hypothesis but has no supporting evidence or artifact.`,
        target: { kind: 'claim', id: claim.id },
        blocking: true,
        createdAt: now(),
      });
    }
    if (
      claim.claimType === 'computed' &&
      !evidence.some(
        (item) => RESULT_SUMMARY_COMPUTED_EVIDENCE.has(item.sourceType) && hasDurableComputedEvidence(run, item)
      ) &&
      !artifacts.some((artifact) => hasDurableArtifactOutput(run, artifact))
    ) {
      warnings.push({
        id: `warn_non_durable_computed_claim_${claim.id}`,
        runId: run.runId,
        severity: 'error',
        code: 'unsupported_claim',
        message: `Computed claim ${claim.id} has no existing result artifact, output file, or hashed command/remote result.`,
        target: { kind: 'claim', id: claim.id },
        blocking: true,
        createdAt: now(),
      });
    }
    if (claim.status === 'partial' || claim.status === 'blocked') {
      warnings.push({
        id: `warn_incomplete_claim_${claim.id}`,
        runId: run.runId,
        severity: claim.status === 'blocked' ? 'error' : 'warning',
        code: 'unsupported_claim',
        message: `Claim ${claim.id} is ${claim.status}; the report must preserve that uncertainty.`,
        target: { kind: 'claim', id: claim.id },
        blocking: claim.status === 'blocked',
        createdAt: now(),
      });
    }
  }
  return Array.from(new Map(warnings.map((item) => [item.id, item])).values());
};

const buildClaimVerification = (claims: ScienceClaim[], warnings: ScienceGraphWarning[]): ScienceClaimVerification => {
  const blockingWarnings = warnings.filter((warning) => warning.blocking || warning.severity === 'error');
  const warnedClaimIds = new Set(
    warnings
      .filter((warning) => warning.target?.kind === 'claim' && warning.severity !== 'info')
      .map((warning) => warning.target?.id)
      .filter((id): id is string => Boolean(id))
  );
  const hypothesisClaims = claims.filter((claim) => claim.claimType === 'hypothesis' || claim.status === 'hypothesis');
  const unsupportedClaimIds = claims
    .filter((claim) => claim.status === 'partial' || claim.status === 'blocked' || warnedClaimIds.has(claim.id))
    .map((claim) => claim.id);
  const supportedClaims = claims.filter(
    (claim) => claim.status === 'supported' && claim.claimType !== 'hypothesis' && !warnedClaimIds.has(claim.id)
  ).length;

  return {
    state: blockingWarnings.length
      ? 'blocked'
      : unsupportedClaimIds.length || hypothesisClaims.length
        ? 'partial'
        : 'verified',
    totalClaims: claims.length,
    supportedClaims,
    hypothesisClaims: hypothesisClaims.length,
    unsupportedClaimIds,
    blockingWarningIds: blockingWarnings.map((warning) => warning.id),
  };
};

const fallbackBlocks = (run: ScienceRunState): ScienceReportBlock[] => {
  const artifacts = [...run.artifacts.values()].slice(0, 6);
  const claims = [...run.claims.values()].slice(0, 6);
  if (claims.length) {
    return [
      {
        type: 'bullet_list',
        items: claims.map((claim) => ({
          text: claim.text,
          evidenceIds: claim.supportingEvidenceIds,
          confidence: claim.status,
        })),
      },
    ];
  }
  if (artifacts.length) {
    return artifacts.map((artifact) =>
      ['figure', 'html', 'pdf', 'latex', 'table', 'regression_table', 'notebook'].includes(artifact.type)
        ? ({ type: 'artifact_embed', artifactId: artifact.id } satisfies ScienceReportBlock)
        : ({ type: 'artifact_ref', artifactId: artifact.id } satisfies ScienceReportBlock)
    );
  }
  return [{ type: 'paragraph', text: run.summary || 'Science artifact run is being assembled.' }];
};

const researchRouteForRun = (
  run: ScienceRunState,
  artifacts: ScienceArtifact[] = [...run.artifacts.values()]
): {
  artifact?: ScienceArtifact;
  map?: ResearchRouteMap;
  presentation?: ResearchRoutePresentation;
} => {
  const artifact = artifacts
    .filter((candidate) => candidate.id === RESEARCH_ROUTE_ARTIFACT_ID)
    .sort((left, right) => right.createdAt - left.createdAt || right.version - left.version)
    .find((candidate) => readResearchRouteMap(candidate.metadata));
  const map = artifact ? readResearchRouteMap(artifact.metadata) : undefined;
  return {
    artifact,
    map,
    presentation:
      artifact && map
        ? buildResearchRoutePresentation(map, {
            runId: run.runId,
            artifactId: artifact.id,
            version: artifact.version,
            baseRevision: artifact.revision || '',
          })
        : undefined,
  };
};

const requireAnsweredResearchRouteBranchSelection = (run: ScienceRunState | undefined, routeNodeId?: string) => {
  if (!run) throw new Error('Branch operations require an explicit runId with a persisted research route.');
  const route = researchRouteForRun(run).map;
  if (!route) throw new Error('The requested run does not contain a valid persisted research route map.');
  const selection = validateResearchRouteBranchSelection(route, routeNodeId);
  if (selection.ok === false) throw new Error(selection.error);
  if (route.decision?.status !== 'answered' || !selection.node) {
    throw new Error('Branch operations require an answered research route with an explicitly selected routeNodeId.');
  }
  return selection;
};

const financeEnvironmentSet = (name: string): Set<string> => {
  const raw = process.env[name]?.trim();
  if (!raw) return new Set();
  try {
    const parsed = JSON.parse(raw) as unknown;
    if (Array.isArray(parsed)) return new Set(parsed.filter((item): item is string => typeof item === 'string'));
  } catch {
    // A comma-delimited value is retained as a simple deployment fallback.
  }
  return new Set(
    raw
      .split(',')
      .map((item) => item.trim())
      .filter(Boolean)
  );
};

const projectWorkspaceStatusFinanceReceipt = (input: {
  runId?: string;
  conversationId?: string;
  projectId?: string;
  projectRoot: string;
  head?: string;
  branch?: string;
  dirtyPaths: string[];
}): FinanceToolReceipt | undefined => {
  const secret = readFinanceReceiptSecret(input.runId);
  if (!secret || !input.runId) return undefined;
  const issuedAt = new Date(now()).toISOString();
  const requestHash = crypto
    .createHash('sha256')
    .update(
      JSON.stringify({
        action: 'status',
        runId: input.runId,
        projectRoot: input.projectRoot,
        head: input.head,
        branch: input.branch,
        dirtyPaths: input.dirtyPaths,
      })
    )
    .digest('hex');
  return signFinanceToolReceipt(
    {
      schema: FINANCE_TOOL_RECEIPT_SCHEMA,
      receiptId: `finance_receipt_${crypto.randomUUID()}`,
      runId: input.runId,
      sessionId: input.conversationId || input.projectId || 'bound-project-session',
      callId: `project_status_${crypto.randomUUID()}`,
      toolName: 'project_workspace',
      status: 'succeeded',
      dataStatus: 'available',
      requestHash,
      evidenceIds: [],
      artifactRefs: [],
      capabilities: [],
      warnings: [],
      issuedAt,
    },
    secret
  );
};

const scienceArtifactFinanceReceipt = (
  run: ScienceRunState,
  action: string,
  toolName: FinanceToolReceipt['toolName'] = 'science_artifact',
  capabilities: string[] = ['science.artifact'],
  requestContext?: JsonRecord,
  outcome?: Pick<FinanceToolReceipt, 'status' | 'dataStatus' | 'warnings'>
): FinanceToolReceipt | undefined => {
  const secret = readFinanceReceiptSecret(run.runId);
  const boundDomain = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain);
  if (!secret || (boundDomain !== 'financial' && boundDomain !== 'financial_factor' && !run.financeCompletion)) {
    return undefined;
  }
  return signFinanceToolReceipt(
    {
      schema: FINANCE_TOOL_RECEIPT_SCHEMA,
      receiptId: `finance_receipt_${crypto.randomUUID()}`,
      runId: run.runId,
      sessionId: run.conversationId || 'finance-session',
      callId: run.toolCallId || `${toolName}_${crypto.randomUUID()}`,
      toolName,
      status: outcome?.status || 'succeeded',
      dataStatus: outcome?.dataStatus || 'available',
      requestHash: crypto
        .createHash('sha256')
        .update(
          JSON.stringify({
            action,
            runId: run.runId,
            updatedAt: run.updatedAt,
            artifactGit: run.git?.commit,
            ...(requestContext ? { requestContext } : {}),
          })
        )
        .digest('hex'),
      evidenceIds: [...run.evidence.keys()].slice(0, 100),
      artifactRefs: [...run.artifacts.values()]
        .slice(0, 100)
        .map((artifact) => ({ artifactId: artifact.id, version: artifact.version, revision: artifact.revision })),
      capabilities,
      warnings: outcome?.warnings || [],
      issuedAt: new Date(now()).toISOString(),
    },
    secret
  );
};

const stableMathematicsRunId = (
  requestedRunId: string | undefined,
  projectRoot: string | undefined,
  conversationId?: string
): string => {
  const runIdentity = readMathRunHistoryIdentity();
  if (runIdentity) {
    const prefix = `mathematics_${runIdentity}_`;
    if (requestedRunId?.startsWith(prefix)) return requestedRunId;
    return `${prefix}${sha256(JSON.stringify([projectRoot ? normalizedPathIdentity(projectRoot) : null, requestedRunId ?? null])).slice(0, 24)}`;
  }
  return (
    requestedRunId ||
    `mathematics_${crypto
      .createHash('sha256')
      .update(
        projectRoot
          ? `${normalizedPathIdentity(projectRoot)}\u0000mathematics-project`
          : `unbound\u0000${conversationId || 'math-session'}`
      )
      .digest('hex')
      .slice(0, 24)}`
  );
};

const collectCardDiagnostics = (
  report: SciencePanelData['report'],
  cards: readonly StructuredReportCard[]
): string[] => {
  const cardIds = new Set(cards.map((card) => card.id));
  const diagnostics: string[] = [];
  report.sections.forEach((section) => {
    section.blocks.forEach((block, blockIndex) => {
      if (block.type === 'card_ref' && !cardIds.has(block.cardId)) {
        diagnostics.push(`report.sections.${section.id}.blocks.${blockIndex}: unknown card ${block.cardId}`);
      }
    });
  });
  return diagnostics;
};

const financeArtifactKindsForRun = (run: ScienceRunState): Set<string> => {
  const kinds = new Set<string>();
  run.artifacts.forEach((artifact) => {
    const financeMetadata = isRecord(artifact.metadata?.finance) ? artifact.metadata.finance : undefined;
    const candidate = asString(financeMetadata?.kind || artifact.metadata?.financeKind || artifact.metadata?.kind);
    if (FINANCE_ARTIFACT_KINDS.includes(candidate as (typeof FINANCE_ARTIFACT_KINDS)[number])) kinds.add(candidate);
    if (artifact.id === FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID || artifact.viewer?.kind === 'financial_factor') {
      kinds.add('factor_research');
    }
  });
  return kinds;
};

const preflightRunFinanceCompletion = (
  run: ScienceRunState,
  report: SciencePanelData['report'],
  cards: readonly StructuredReportCard[]
): SciencePanelData['financePreflight'] => {
  const verifiedAt = new Date(now()).toISOString();
  const boundDomain = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain);
  const isFinancialRun =
    Boolean(run.financeCompletion) || boundDomain === 'financial' || boundDomain === 'financial_factor';
  if (!isFinancialRun) return undefined;
  if (!run.financeCompletion) {
    return { status: 'legacy_uncontracted', gaps: ['legacy_uncontracted'], verifiedAt };
  }

  const cardsById = new Map(cards.map((card) => [card.id, card]));
  const referencedCardIds = new Set(
    report.sections.flatMap((section) =>
      section.blocks.flatMap((block) => (block.type === 'card_ref' ? [block.cardId] : []))
    )
  );
  const referencedCards = [...referencedCardIds]
    .map((cardId) => cardsById.get(cardId))
    .filter((card): card is StructuredReportCard => Boolean(card));
  const verifiedReceiptIds = verifiedFinanceReceiptIds(
    run.financeCompletion.toolReceipts,
    readFinanceReceiptSecret(run.runId)
  );

  const result: FinanceCompletionPreflightResult = preflightFinanceCompletion(run.financeCompletion, {
    runId: run.runId,
    projectRoot: run.projectRoot,
    projectGitHead: run.sourceGit?.commit,
    artifactGitCommit: run.git?.commit,
    activeConditions: financeEnvironmentSet('DEEPSCIENTIST_FINANCE_CONDITIONS') as Set<FinanceToolRequirementCondition>,
    activeCapabilities: new Set([
      ...financeEnvironmentSet('DEEPSCIENTIST_FINANCE_CAPABILITIES'),
      ...run.financeCompletion.toolReceipts
        .filter((receipt) => receipt.status === 'succeeded' || receipt.status === 'partial')
        .flatMap((receipt) => receipt.capabilities),
    ]),
    verifiedReceiptIds,
    artifactKinds: financeArtifactKindsForRun(run),
    artifactRefs: new Set(run.artifacts.keys()),
    evidenceIds: new Set(run.evidence.keys()),
    cardIds: new Set(cards.map((card) => card.id)),
    referencedCardIds,
    cardKinds: new Set(referencedCards.map((card) => card.kind)),
    sectionIds: new Set(report.sections.map((section) => section.id)),
    sectionRoles: new Set(report.sections.map((section) => section.role || section.id)),
    hasResultSummary: report.sections.some((section) =>
      section.blocks.some((block) => block.type === 'result_summary')
    ),
    hasLimitations: report.sections.some((section) => (section.role || section.id) === 'limitations'),
    hasReviewableOutput:
      report.sections.some((section) => section.blocks.length > 0) || run.evidence.size > 0 || run.artifacts.size > 0,
  });
  const observedGaps = [
    ...(!run.sourceGit?.commit ? ['project_git_checkpoint_unobserved'] : []),
    ...(!run.git?.commit ? ['artifact_git_snapshot_unobserved'] : []),
  ];
  if (result.ok && !observedGaps.length) return { status: 'completed', gaps: [], verifiedAt };
  const resultGaps = result.ok === false ? result.gaps : [];
  const resultStatus = result.ok === false ? result.status : 'partial';
  const gaps = [...new Set([...resultGaps, ...observedGaps])];
  return {
    status: resultStatus,
    gaps,
    verifiedAt,
  };
};

const buildFinancePublicationGap = (preflight: SciencePanelData['financePreflight']): JsonRecord | undefined => {
  if (!preflight || preflight.status === 'completed') return undefined;
  const gaps = preflight.gaps || [];
  const suffixes = (prefixes: readonly string[]): string[] =>
    gaps
      .filter((gap) => prefixes.some((prefix) => gap.startsWith(prefix)))
      .map((gap) => gap.slice(gap.indexOf(':') + 1))
      .filter(Boolean);
  return {
    code: 'finance_publication_gap',
    status: preflight.status === 'blocked' ? 'blocked' : 'partial',
    missingSections: suffixes(['missing_section_role:']),
    missingCards: suffixes(['missing_card_kind:', 'unreferenced_report_card:', 'unknown_card:']),
    missingReceipts: suffixes([
      'missing_tool_receipt:',
      'failed_tool_receipt:',
      'partial_tool_receipt:',
      'unverified_tool_receipt:',
    ]),
    missingCapabilities: suffixes(['missing_capability:', 'provider_capability_unavailable:']),
    gaps,
    repairable: preflight.status !== 'blocked',
  };
};

const buildFinanceCompletionGuide = (value: unknown, run: ScienceRunState): JsonRecord | undefined => {
  const contractId = asString(value, '');
  if (!contractId) return undefined;
  const contract = getFinanceTaskContract(contractId);
  if (!contract) {
    throw new Error(
      `Unknown Finance task contract: ${contractId}. Use the exact id from Runtime Financial Task Route.`
    );
  }
  const availableReceipts = (run.financeCompletion?.toolReceipts || []).map((receipt) => ({
    receiptId: receipt.receiptId,
    toolName: receipt.toolName,
    status: receipt.status,
    dataStatus: receipt.dataStatus,
    capabilities: receipt.capabilities,
  }));
  const availableCapabilities = new Set([
    ...financeEnvironmentSet('DEEPSCIENTIST_FINANCE_CAPABILITIES'),
    ...availableReceipts
      .filter((receipt) => receipt.status === 'succeeded' || receipt.status === 'partial')
      .flatMap((receipt) => receipt.capabilities),
  ]);
  const publicationMode = run.financeCompletion
    ? run.financePreflight?.status === 'completed'
      ? 'complete'
      : run.financePreflight?.status === 'blocked'
        ? 'blocked'
        : 'partial'
    : 'pending';
  return {
    schema: 'deepscientist.finance.completion_guide.v1',
    reportProtocol: 'ScienceReportV1',
    domain: 'finance',
    publicationMode,
    taskKind: contract.taskKind,
    taskContract: {
      id: contract.id,
      version: contract.version,
      contractHash: contract.contractHash,
    },
    sopReference: contract.sopReference,
    requiredCapabilities: contract.requiredCapabilities,
    requiredTools: contract.requiredTools,
    requiredArtifactKinds: contract.requiredArtifactKinds,
    requiredReport: contract.requiredReport,
    requiredSections: contract.requiredReport.sectionRoles,
    requiredCardKinds: contract.requiredReport.cardKinds,
    availableReceipts,
    missingCapabilities: contract.requiredCapabilities.filter((capability) => !availableCapabilities.has(capability)),
    currentPublicationGap: buildFinancePublicationGap(run.financePreflight),
    cardAuthoring: buildStructuredReportCardAuthoringGuide(optionalFinanceCardDraftContext(run), contract.id),
    visualDelivery: {
      rule: 'When verified structured values support comparison, trend, distribution, interval, exposure, drawdown, or scenario analysis, provide one lead visual before completed status.',
      targetCount: { min: 1, max: 4 },
      composition:
        'Use two to four total visuals only for distinct reader questions; place the lead visual before long evidence and risk detail.',
      noDataFallback:
        'When no meaningful visual data exists, pass the concrete reason only as payload.internalVisualWaiverReason. It is private validation metadata and must never appear in the report, cards, limitations, data gaps, Evidence, or final reply.',
    },
    allowedPartialReasons: contract.allowedPartialReasons,
    publishPlacement: 'science_artifact.payload.financeCompletion',
    terminalPublication: {
      action: 'publish',
      displayIntent: 'open',
      target: { kind: 'report', id: 'report' },
      requiresExplicitReport: true,
      artifactAloneIsDelivery: false,
      exceptions: ['terminal_preflight_without_reviewable_data', 'monitor_no_change'],
    },
    researchWorkflow: {
      schema: 'deepscientist.finance.research_workflow.v1',
      stages: [
        { id: 'lock', output: 'raw_result_envelope_and_receipt' },
        { id: 'compute', output: 'derived_evidence_with_inputs' },
        { id: 'publish', output: 'selected_cards_and_one_reader_first_report' },
      ],
      decisionFrame: ['facts', 'interpretation', 'implication', 'triggers_or_risks', 'limitations'],
      rules: [
        'Use registered evidenceIds for every decision-bearing claim or card.',
        'Use Git-tracked project files or Science artifacts as the durable research record.',
        'Make the evidence-conditioned visual delivery decision before composing the final report.',
        'Do not force empty modules or duplicate one result as prose, a card, and a chart.',
      ],
    },
    requiredManifestFields: [
      'schema',
      'runId',
      'taskKind',
      'taskContract',
      'gate',
      'toolReceipts',
      'asOf',
      'evidenceIds',
      'artifactRefs',
      'report',
      'verifiedAt',
      'status',
      'reproducible',
      'gaps',
    ],
    manifestAuthoring: {
      runId: run.runId,
      schema: 'deepscientist.finance.completion.v1',
      taskContract: {
        requiredKeys: ['id', 'version', 'contractHash', 'routeSource'],
        fixedValues: {
          id: contract.id,
          version: contract.version,
          contractHash: contract.contractHash,
        },
        routeSourceValues: ['deterministic', 'agent_selected', 'user_confirmed'],
        rule: 'Copy routeSource from Runtime Financial Task Route. Do not add specialist or sopReference to taskContract.',
      },
      gate: {
        unboundReadOnlyShape: {
          kind: 'unbound_read_only',
          gateId: `unbound-${run.runId}`,
        },
        boundWriteRequiredKeys: ['kind="bound_write"', 'workspaceStatusReceiptId', 'workspace'],
        rule: 'Choose exactly one gate shape and include every key in that shape.',
      },
      toolReceipts: {
        sources: ['finance tool output .receipt', 'platform tool output .financeReceipt'],
        rule: 'Copy each complete receipt object byte-for-byte from the tool output. Never retype, shorten, repair, recompute, or summarize requestHash, attestation.value, receiptId, or any other receipt field.',
        validation:
          'requestHash and attestation.value are lowercase 64-character SHA-256 values. If a copied object does not satisfy that shape, return to the original tool output instead of editing the value.',
      },
      scalarFormats: {
        asOf: 'ISO-8601 datetime string copied from the selected evidence cutoff',
        verifiedAt: 'current ISO-8601 datetime string',
        reproducible: 'true only for completed; false for partial or blocked',
        gaps: 'empty array only for completed; explicit strings for partial or blocked',
      },
      report: {
        requiredKeys: ['panelId', 'sectionIds', 'cardIds'],
        rule: 'Use ids from the report and cards in the same publish payload. Do not put the report body or financeCompletion inside this reference object.',
      },
    },
    instructions: [
      'Copy routeSource from Runtime Financial Task Route; do not infer or recompute it.',
      'Use only attested receipts returned by tools in this run. Copy complete .receipt and .financeReceipt objects exactly; never hand-transcribe hashes or signatures.',
      'Pass the manifest directly as payload.financeCompletion, never inside payload.report or payload.completion.',
      'Checkpoint material project changes before composing the completion manifest.',
      'After reviewable data exists, publish exactly once with displayIntent=open and an explicit report, cardDrafts or exact cards, and financeCompletion. Creating an artifact alone is not delivery.',
      'Give every finance card draft a moduleId. The server links it into the module default report section; override reportSectionRole only with a role allowed by the module.',
      'Only cards actually referenced by report card_ref blocks satisfy completion requirements.',
      'When verified structured numeric data exists, put one lead chart or chart-card before long evidence detail; use two to four total visuals only for distinct questions. Otherwise pass payload.internalVisualWaiverReason as private validation metadata and do not repeat it in reader-facing content.',
      'For unbound_read_only, publish a partial non-reproducible report without invented Project Git or Artifact Git references.',
    ],
  };
};

const buildReportAuthoringGuide = (run: ScienceRunState): JsonRecord => {
  const boundDomain = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain);
  const isFinancial =
    Boolean(run.financeCompletion) || boundDomain === 'financial' || boundDomain === 'financial_factor';
  return {
    schema: 'deepscientist.report.authoring_guide.v1',
    reportProtocol: 'ScienceReportV1',
    recommendedSkills: isFinancial
      ? ['report-authoring', 'financial-report-research']
      : ['report-authoring', 'science'],
    optionalSkills: ['report-chart', 'ds-paper-plot', 'ds-nature-figure'],
    skillPolicy: {
      editorialGuidance: 'advisory',
      deliveryContract: 'science_artifact_mcp',
      rule: 'Read the shared authoring Skill for composition and examples. Use this MCP response for the current schema, evidence, visual, and publication requirements; do not copy the full Skill into the report.',
    },
    readerPath: [
      'direct_answer',
      'lead_visual_or_key_metrics',
      'interpretation',
      'limitations_and_next_action',
      'sources_and_method',
    ],
    natureFigurePolicy:
      'Use ds-nature-figure or ds-paper-plot only for a requested submission-grade figure or manuscript package. Ordinary reports should use the shortest evidence-bound visual that answers the question.',
    examples: {
      leadAnswer:
        'As of [date], [measured comparison] supports [bounded answer]; the conclusion would weaken if [observable invalidation condition].',
      visualCaption:
        '[Outcome] by [group] in [analysis set]; marks show [statistic] and intervals show [uncertainty]. [Observed contrast] is the main support for [answer].',
      partialReport:
        '[Provider] was unavailable, so [specific metric] is not covered. The report still answers [narrow question] from [remaining evidence]; [missing check] is the next action.',
    },
    editorialWarnings: [
      'The first answer-bearing block does not directly answer the user question.',
      'A decision-bearing visual is missing its unit, denominator, period, source, or nearby takeaway.',
      'Evidence, raw tool chronology, or risk detail appears before the answer without a reader reason.',
      'The report lacks an observable condition that would change the conclusion or a concrete next action.',
    ],
    hardValidationBoundary: [
      'schema_and_reference_integrity',
      'evidence_bound_decision_claims',
      'no_invented_values_or_sources',
      'successful_publication_receipt_before_completion',
    ],
  };
};

const buildPanel = (run: ScienceRunState): SciencePanelData => {
  const artifacts = [...run.artifacts.values()];
  const evidence = [...run.evidence.values()];
  const usedSkills = [...run.usedSkills.values()];
  const claims = [...run.claims.values()];
  const warnings = validateGraph(run);
  const verification = buildClaimVerification(claims, warnings);
  const researchRoute = researchRouteForRun(run, artifacts).presentation;

  const stats = {
    searches:
      run.statsPatch?.searches || evidence.filter((item) => item.sourceType === 'paper' || item.database).length,
    artifacts: artifacts.length,
    evidence: evidence.length,
    commands:
      run.statsPatch?.commands ||
      artifacts.filter((item) => item.execution?.command || item.execution?.scriptPath).length,
    validations:
      run.statsPatch?.validations || evidence.filter((item) => item.sourceType === 'validation_result').length,
    warnings: warnings.length,
  };
  const report =
    run.report ||
    ({
      title: run.question || 'Science Artifact Report',
      sections: [
        {
          id: 'summary',
          heading: 'Research Output',
          blocks: fallbackBlocks(run),
        },
      ],
    } satisfies SciencePanelData['report']);
  const visibleReport = publicScienceReport(report) || report;
  const validatedCards = validateCardsAgainstResources(run.cards, run.artifacts, run.evidence);
  const validationErrors = validatedCards.ok === false ? validatedCards.errors : [];
  const cards = validatedCards.cards;
  const cardDiagnostics = [
    ...new Set([...run.cardDiagnostics, ...validationErrors, ...collectCardDiagnostics(visibleReport, cards)]),
  ];
  stats.warnings += cardDiagnostics.length;
  const visualReview = reviewScienceReportVisuals(visibleReport, artifacts, run.status, cards, run.visualWaiverReason);
  const mathematicsPortfolio = latestMathematicsPortfolio(artifacts);
  let mathematics: SciencePanelData['mathematics'];
  if (mathematicsPortfolio) {
    const verifiedOfficialReceiptIds = [...verifiedMathematicsOfficialReceiptIds(mathematicsPortfolio)];
    let portfolioIntegrity: SciencePanelData['mathematics']['portfolioIntegrity'];
    if (isTerminalMathematicsPortfolio(mathematicsPortfolio)) {
      try {
        assertMathematicsRuntimeReceipts(run, mathematicsPortfolio, indexMathematicsVerifications(run));
        const readiness = assertMathematicsDecisionGate(run, mathematicsPortfolio);
        const expectedDisposition = mathematicsPortfolio.status;
        if (readiness.decision.disposition !== expectedDisposition) {
          throw new Error('Mathematics terminal decision is not ready.');
        }
        if (run.projectRoot) assertCurrentMathematicsPortfolioCommitted(run.projectRoot, mathematicsPortfolio);
        portfolioIntegrity = 'trusted';
      } catch {
        portfolioIntegrity = 'untrusted_terminal';
      }
    }
    mathematics = { verifiedOfficialReceiptIds, ...(portfolioIntegrity ? { portfolioIntegrity } : {}) };
  }

  return {
    schema: SCIENCE_PANEL_SCHEMA,
    runId: run.runId,
    conversationId: run.conversationId,
    projectRoot: run.projectRoot,
    question: run.question,
    generatedAt: now(),
    summary: run.summary,
    status: run.status,
    stats,
    report: visibleReport,
    evidence,
    artifacts,
    cards,
    cardDiagnostics: cardDiagnostics.length ? cardDiagnostics : undefined,
    visualReview,
    financeCompletion: run.financeCompletion,
    financePreflight: run.financePreflight,
    mathematics,
    pages: [...run.pages.values()],
    claims,
    verification,
    provenance: [...run.provenance.values()],
    edges: [...run.edges.values()],
    graphWarnings: warnings,
    usedSkills,
    methods: {
      queryPlan: undefined as string[] | undefined,
      commands: artifacts.map((item) => item.execution?.command).filter((item): item is string => Boolean(item)).length
        ? artifacts.map((item) => item.execution?.command).filter((item): item is string => Boolean(item))
        : undefined,
      environmentSummary:
        artifacts
          .map((item) => item.environment?.kind)
          .filter(Boolean)
          .join(', ') || undefined,
      limitations: warnings.filter((item) => item.severity !== 'info').map((item) => item.message).length
        ? warnings.filter((item) => item.severity !== 'info').map((item) => item.message)
        : undefined,
    },
    researchRoute,
    git: run.git,
    sourceGit: run.sourceGit,
  };
};

function persistRunSnapshot(
  run: ScienceRunState,
  triggerEvent?: ScienceArtifactEvent,
  includePaths?: ScienceArtifactSnapshotIncludePath[]
): ScienceArtifactGitRef | undefined {
  if (!writeProjectManifest() || !run.projectRoot) return undefined;
  try {
    const root = path.join(run.projectRoot, '.deepscientist', 'science-artifacts', 'runs', safeSegment(run.runId));
    const panel = buildPanel(run);
    const state = {
      runId: run.runId,
      conversationId: run.conversationId,
      messageId: run.messageId,
      toolCallId: run.toolCallId,
      projectRoot: run.projectRoot,
      question: run.question,
      summary: run.summary,
      status: run.status,
      report: publicScienceReport(run.report),
      visualWaiverReason: run.visualWaiverReason,
      cards: panel.cards,
      cardDiagnostics: panel.cardDiagnostics,
      financeCompletion: run.financeCompletion,
      financePreflight: run.financePreflight,
      statsPatch: run.statsPatch,
      createdAt: run.createdAt,
      updatedAt: run.updatedAt,
      evidence: panel.evidence,
      artifacts: panel.artifacts,
      pages: panel.pages,
      claims: panel.claims,
      provenance: panel.provenance,
      edges: panel.edges,
      graphWarnings: panel.graphWarnings,
      usedSkills: panel.usedSkills,
      annotations: [...run.annotations.values()],
      commandReceipts: [...run.commandReceipts.values()],
      memory: run.memory,
      git: run.git,
      sourceGit: run.sourceGit,
      mathematicsVerification: run.mathematicsVerification,
      mathematicsVerifications: run.mathematicsVerifications,
      mathematicsVerificationEvents: run.mathematicsVerificationEvents,
      mathematicsVerificationCapability: run.mathematicsVerificationCapability,
      mathematicsOfficialGateReceipts: run.mathematicsOfficialGateReceipts,
      mathematicsReview: run.mathematicsReview,
    };
    const gitRef = commitScienceArtifactSnapshot({
      projectRoot: run.projectRoot,
      panel,
      state,
      events: run.events,
      event: triggerEvent,
      target: triggerEvent?.target,
      includePaths,
    });
    if (gitRef.ok) {
      run.git = gitRef;
      panel.git = gitRef;
      state.git = gitRef;
      if (triggerEvent?.memoryId) {
        const memory = run.memory.find((item) => item.id === triggerEvent.memoryId);
        if (memory) memory.commit = gitRef.commit;
      }
      if (triggerEvent) {
        triggerEvent.git = gitRef;
        if (triggerEvent.snapshot) triggerEvent.snapshot.files = gitRef.files;
      }
    }
    writeJson(path.join(root, 'panel.json'), panel);
    writeJson(path.join(root, 'state.json'), state);
    writeJsonl(path.join(root, 'events.jsonl'), run.events);
    return gitRef;
  } catch (error) {
    console.warn('[ScienceArtifactMCP] Failed to write project manifest:', error);
    return {
      status: 'unavailable',
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

const getResource = (run: ScienceRunState, target?: TargetRef): unknown => {
  if (!target?.kind) return buildPanel(run);
  if (target.kind === 'run')
    return {
      runId: run.runId,
      projectRoot: run.projectRoot,
      question: run.question,
      summary: run.summary,
      status: run.status,
      cards: run.cards,
      cardDiagnostics: run.cardDiagnostics,
      financeCompletion: run.financeCompletion,
      financePreflight: run.financePreflight,
    };
  if (target.kind === 'report') return publicScienceReport(run.report);
  if (target.kind === 'artifact' && target.id) return run.artifacts.get(artifactKey(target.id, target.version || 1));
  if (target.kind === 'page' && (target.id || target.pageId)) return run.pages.get(target.id || target.pageId || '');
  if (target.kind === 'evidence' && target.id) return run.evidence.get(target.id);
  if (target.kind === 'claim' && target.id) return run.claims.get(target.id);
  if (target.kind === 'provenance' && target.id) return run.provenance.get(target.id) || run.edges.get(target.id);
  if (target.kind === 'skill_use' && target.id) return run.usedSkills.get(target.id);
  if (target.kind === 'annotation' && target.id) return run.annotations.get(target.id);
  if (target.kind === 'memory' && target.id) return run.memory.find((item) => item.id === target.id);
  return undefined;
};

const listResource = (run: ScienceRunState, kind?: ScienceArtifactResourceKind): unknown[] => {
  if (kind === 'artifact') return [...run.artifacts.values()];
  if (kind === 'page') return [...run.pages.values()];
  if (kind === 'evidence') return [...run.evidence.values()];
  if (kind === 'claim') return [...run.claims.values()];
  if (kind === 'provenance') return [...run.provenance.values(), ...run.edges.values()];
  if (kind === 'skill_use') return [...run.usedSkills.values()];
  if (kind === 'annotation') return [...run.annotations.values()];
  if (kind === 'memory') return run.memory;
  return [
    ...run.artifacts.values(),
    ...run.pages.values(),
    ...run.evidence.values(),
    ...run.claims.values(),
    ...run.provenance.values(),
    ...run.edges.values(),
    ...run.usedSkills.values(),
    ...run.annotations.values(),
    ...run.memory,
  ];
};

const scienceRunSnapshotVersion = (run: ScienceRunState): string => {
  const sortedValues = <T>(values: Map<string, T>): T[] =>
    [...values.entries()].toSorted(([left], [right]) => left.localeCompare(right)).map(([, value]) => value);
  const snapshot = {
    run: {
      runId: run.runId,
      projectRoot: run.projectRoot,
      question: run.question,
      summary: run.summary,
      status: run.status,
      cards: run.cards,
      cardDiagnostics: run.cardDiagnostics,
      financeCompletion: run.financeCompletion,
      financePreflight: run.financePreflight,
    },
    report: publicScienceReport(run.report),
    visualWaiverReason: run.visualWaiverReason,
    artifacts: sortedValues(run.artifacts),
    pages: sortedValues(run.pages),
    evidence: sortedValues(run.evidence),
    claims: sortedValues(run.claims),
    provenance: sortedValues(run.provenance),
    edges: sortedValues(run.edges),
    usedSkills: sortedValues(run.usedSkills),
    annotations: sortedValues(run.annotations),
    memory: run.memory,
  };
  return `sha256:${crypto.createHash('sha256').update(JSON.stringify(snapshot)).digest('hex')}`;
};

const normalizeIncludePaths = (value: unknown): ScienceArtifactSnapshotIncludePath[] => {
  const rawItems = Array.isArray(value) ? value : value ? [value] : [];
  return rawItems
    .map((item): ScienceArtifactSnapshotIncludePath | undefined => {
      if (typeof item === 'string') return { path: item, role: 'other', recursive: true };
      if (!isRecord(item)) return undefined;
      const filePath = asString(item.path || item.filePath || item.file_path, undefined as unknown as string);
      if (!filePath) return undefined;
      return {
        path: filePath,
        role: asString(item.role, 'other') as ScienceArtifactSnapshotIncludePath['role'],
        artifactId: asString(item.artifactId || item.artifact_id, undefined as unknown as string),
        artifactVersion:
          item.artifactVersion || item.artifact_version
            ? asNumber(item.artifactVersion || item.artifact_version, 1)
            : undefined,
        recursive: typeof item.recursive === 'boolean' ? item.recursive : true,
      };
    })
    .filter((item): item is ScienceArtifactSnapshotIncludePath => Boolean(item));
};

const normalizeCheckpointVerification = (value: unknown): string[] => {
  const candidates =
    isRecord(value) && Array.isArray(value.checks) ? value.checks : Array.isArray(value) ? value : [value];
  return candidates
    .map((item) => {
      if (typeof item === 'string') return item.trim();
      if (!isRecord(item)) return '';
      const command = asString(item.command || item.check || item.name);
      const rawExitCode = typeof item.exitCode === 'number' ? item.exitCode : item.exit_code;
      const exitCode = typeof rawExitCode === 'number' ? `exit ${rawExitCode}` : '';
      const result = asString(item.result || item.status || item.summary);
      return [command, exitCode, result].filter(Boolean).join(' · ');
    })
    .filter(Boolean)
    .slice(0, 20);
};

const normalizeResearchStageReceipt = (value: unknown): ProjectGitResearchStageReceipt | undefined => {
  if (value == null) return undefined;
  if (!isRecord(value)) throw new Error('payload.researchStage must be an object.');
  const list = (candidate: unknown, field: string, required = false): string[] => {
    if (!Array.isArray(candidate)) {
      if (required) throw new Error(`payload.researchStage.${field} must be a non-empty string array.`);
      return [];
    }
    const result = candidate
      .filter((item): item is string => typeof item === 'string' && Boolean(item.trim()))
      .map((item) => item.trim());
    if (result.length !== candidate.length || (required && result.length === 0)) {
      throw new Error(`payload.researchStage.${field} must be a${required ? ' non-empty' : ''} string array.`);
    }
    return result;
  };
  const stageId = asString(value.stageId || value.stage_id);
  const objective = asString(value.objective);
  const successCriteria = list(value.successCriteria || value.success_criteria, 'successCriteria', true);
  const failureCriteria = list(value.failureCriteria || value.failure_criteria, 'failureCriteria', true);
  const priorWorkRefs = list(value.priorWorkRefs || value.prior_work_refs || [], 'priorWorkRefs');
  const supportingEvidenceIds = list(
    value.supportingEvidenceIds || value.supporting_evidence_ids || [],
    'supportingEvidenceIds'
  );
  const refutingEvidenceIds = list(
    value.refutingEvidenceIds || value.refuting_evidence_ids || [],
    'refutingEvidenceIds'
  );
  const exhaustionEvidenceIds = list(
    value.exhaustionEvidenceIds || value.exhaustion_evidence_ids || [],
    'exhaustionEvidenceIds'
  );
  const disposition = asString(value.disposition) as ProjectGitResearchStageReceipt['disposition'];
  const beliefDelta = asString(value.beliefDelta || value.belief_delta);
  const reflection = asString(value.reflection);
  const nextObjective = asString(value.nextObjective || value.next_objective);
  if (!stageId || !objective || !beliefDelta || !reflection) {
    throw new Error(
      'payload.researchStage requires stageId, objective, beliefDelta, reflection, successCriteria, and failureCriteria.'
    );
  }
  if (!['supported', 'refuted', 'exhausted', 'inconclusive', 'runtime_failed'].includes(disposition)) {
    throw new Error(
      'payload.researchStage.disposition must be supported, refuted, exhausted, inconclusive, or runtime_failed.'
    );
  }
  if (disposition === 'supported' && supportingEvidenceIds.length === 0) {
    throw new Error('A supported research stage requires supportingEvidenceIds.');
  }
  if (disposition === 'refuted' && refutingEvidenceIds.length === 0) {
    throw new Error('A refuted research stage requires refutingEvidenceIds.');
  }
  if (disposition === 'exhausted' && exhaustionEvidenceIds.length === 0) {
    throw new Error('An exhausted research stage requires exhaustionEvidenceIds for the searched route or region.');
  }
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

const normalizeCheckpointMetrics = (value: unknown): ProjectGitPerformanceMetric[] => {
  const candidates: Array<{ fallbackName?: string; value: unknown }> = Array.isArray(value)
    ? value.map((item) => ({ value: item }))
    : isRecord(value) && ('name' in value || 'value' in value)
      ? [{ value }]
      : isRecord(value)
        ? Object.entries(value).map(([fallbackName, item]) => ({ fallbackName, value: item }))
        : [];
  const names = new Set<string>();
  return candidates
    .map(({ fallbackName, value: item }): ProjectGitPerformanceMetric | undefined => {
      const record = isRecord(item) ? item : undefined;
      const name = asString(record?.name || record?.label || fallbackName)
        .replace(/[\r\n]+/gu, ' ')
        .slice(0, 64);
      const rawValue = record ? (record.value ?? record.score) : item;
      const metricValue = typeof rawValue === 'number' && Number.isFinite(rawValue) ? rawValue : undefined;
      if (!name || metricValue === undefined || names.has(name)) return undefined;
      names.add(name);
      const unit = asString(record?.unit)
        .replace(/[\r\n]+/gu, ' ')
        .slice(0, 24);
      const rawDirection = asString(record?.direction || record?.goal).toLowerCase();
      const direction = ['maximize', 'max', 'higher', 'higher_is_better'].includes(rawDirection)
        ? 'maximize'
        : ['minimize', 'min', 'lower', 'lower_is_better'].includes(rawDirection)
          ? 'minimize'
          : undefined;
      return {
        name,
        value: metricValue,
        ...(unit ? { unit } : {}),
        ...(direction ? { direction } : {}),
      };
    })
    .filter((metric): metric is ProjectGitPerformanceMetric => Boolean(metric))
    .slice(0, 12);
};

const normalizeMetricContext = (value: unknown): ProjectGitMetricContext | undefined => {
  if (!isRecord(value)) return undefined;
  const contractId = asString(value.contractId || value.contract_id)
    .replace(/[\r\n]+/gu, ' ')
    .slice(0, 120);
  const evaluationId = asString(value.evaluationId || value.evaluation_id || value.protocolId || value.protocol_id)
    .replace(/[\r\n]+/gu, ' ')
    .slice(0, 160);
  const baselineCommit = asString(value.baselineCommit || value.baseline_commit)
    .replace(/[\r\n]+/gu, ' ')
    .slice(0, 80);
  const evaluationCodeRecord = isRecord(value.evaluationCode || value.evaluation_code)
    ? ((value.evaluationCode || value.evaluation_code) as JsonRecord)
    : undefined;
  const requestedCodePath = asString(evaluationCodeRecord?.path || evaluationCodeRecord?.file)
    .replace(/[\r\n]+/gu, ' ')
    .trim()
    .slice(0, 300);
  const evaluationCodePath =
    requestedCodePath && !path.isAbsolute(requestedCodePath) && !requestedCodePath.split(/[\\/]+/u).includes('..')
      ? requestedCodePath.replaceAll('\\', '/')
      : undefined;
  const rawRuntime = asString(evaluationCodeRecord?.runtime).toLowerCase();
  const evaluationRuntime = ['python', 'node', 'r', 'notebook'].includes(rawRuntime)
    ? (rawRuntime as 'python' | 'node' | 'r' | 'notebook')
    : undefined;
  const evaluationEntrypoint = asString(evaluationCodeRecord?.entrypoint)
    .replace(/[\r\n]+/gu, ' ')
    .trim()
    .slice(0, 160);
  const requestedSha256 = asString(evaluationCodeRecord?.sha256).trim().toLowerCase();
  const evaluationSha256 = /^[a-f0-9]{64}$/u.test(requestedSha256) ? requestedSha256 : undefined;
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

const listProjectResource = (
  projectRoot: string | undefined,
  kind?: ScienceArtifactResourceKind
): unknown[] | undefined => {
  if (!projectRoot) return undefined;
  const runsRoot = path.join(projectRoot, '.deepscientist', 'science-artifacts', 'runs');
  if (!fs.existsSync(runsRoot)) return [];
  const states = fs
    .readdirSync(runsRoot, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => readJson<JsonRecord>(path.join(runsRoot, entry.name, 'state.json'), {}))
    .filter(isRecord);
  const values = states.flatMap((state) => {
    if (kind === 'artifact') return Array.isArray(state.artifacts) ? state.artifacts : [];
    if (kind === 'page') return Array.isArray(state.pages) ? state.pages : [];
    if (kind === 'evidence') return Array.isArray(state.evidence) ? state.evidence : [];
    if (kind === 'claim') return Array.isArray(state.claims) ? state.claims : [];
    if (kind === 'provenance')
      return [
        ...(Array.isArray(state.provenance) ? state.provenance : []),
        ...(Array.isArray(state.edges) ? state.edges : []),
      ];
    if (kind === 'skill_use') return Array.isArray(state.usedSkills) ? state.usedSkills : [];
    if (kind === 'annotation') return Array.isArray(state.annotations) ? state.annotations : [];
    if (kind === 'memory') return Array.isArray(state.memory) ? state.memory : [];
    return [
      ...(Array.isArray(state.artifacts) ? state.artifacts : []),
      ...(Array.isArray(state.evidence) ? state.evidence : []),
      ...(Array.isArray(state.claims) ? state.claims : []),
      ...(Array.isArray(state.provenance) ? state.provenance : []),
    ];
  });
  return values;
};

const createOrReplaceResource = (
  run: ScienceRunState,
  action: 'create' | 'replace' | 'patch',
  target: TargetRef | undefined,
  payload: JsonRecord,
  baseRevision?: string,
  createIfMissing = false
): { object: unknown; target: TargetRef; resultingRevision?: string } => {
  const kind = (target?.kind || payload.kind) as ScienceArtifactResourceKind | undefined;
  if (!kind) throw new Error(`${action} requires target.kind or payload.kind.`);

  if (kind === 'run') {
    run.question = asString(payload.question, run.question);
    run.summary = asString(payload.summary, run.summary as string);
    run.status = normalizePanelStatus(payload.status, run.status, payload.status != null);
    if (isRecord(payload.stats)) run.statsPatch = payload.stats as Partial<SciencePanelData['stats']>;
    applyRunCardPayload(run, payload);
    if (payload.financeCompletion !== undefined) applyFinanceCompletion(run, payload.financeCompletion);
    return { object: getResource(run, { kind: 'run' }), target: { kind: 'run', id: run.runId } };
  }

  if (kind === 'report') {
    const mergedReportPayload = action === 'patch' && run.report ? deepMerge(run.report, payload) : payload;
    const nextReportPayload = isRecord(mergedReportPayload) ? mergedReportPayload : payload;
    if (hasVisualWaiverReason(payload) || hasVisualWaiverReason(nextReportPayload)) {
      run.visualWaiverReason = readVisualWaiverReason(payload) || readVisualWaiverReason(nextReportPayload);
    }
    run.report = normalizeReport(nextReportPayload);
    applyRunCardPayload(run, payload);
    if (payload.financeCompletion !== undefined) applyFinanceCompletion(run, payload.financeCompletion);
    syncReportResources(run, run.report);
    return { object: run.report, target: { kind: 'report', id: 'report' } };
  }

  if (kind === 'artifact') {
    const id = asString(target?.id || payload.id, makeId('artifact'));
    const version = asNumber(target?.version || payload.version, 1);
    const key = artifactKey(id, version);
    const previous = run.artifacts.get(key);
    if (action === 'create' && previous && !createIfMissing) throw new Error(`Artifact ${key} already exists.`);
    if ((action === 'patch' || action === 'replace') && previous) assertBaseRevision(previous, baseRevision);
    if ((action === 'patch' || action === 'replace') && !previous && !createIfMissing)
      throw new Error(`Artifact ${key} does not exist.`);
    const nextPayload =
      action === 'patch' && previous ? (deepMerge(previous, payload) as JsonRecord) : { ...payload, id, version };
    const artifact = normalizeArtifact(run, { ...nextPayload, id, version, revision: revision() });
    run.artifacts.set(key, artifact);
    syncArtifactEdges(run, artifact);
    return { object: artifact, target: { kind, id, version }, resultingRevision: artifact.revision };
  }

  if (kind === 'page') {
    const id = asString(target?.id || target?.pageId || payload.id, makeId('page'));
    const previous = run.pages.get(id);
    if (action === 'create' && previous && !createIfMissing) throw new Error(`Page ${id} already exists.`);
    if ((action === 'patch' || action === 'replace') && previous) assertBaseRevision(previous, baseRevision);
    if ((action === 'patch' || action === 'replace') && !previous && !createIfMissing)
      throw new Error(`Page ${id} does not exist.`);
    const nextPayload =
      action === 'patch' && previous ? (deepMerge(previous, payload) as JsonRecord) : { ...payload, id };
    const page = normalizePage(run, { ...nextPayload, id, revision: revision() });
    run.pages.set(id, page);
    return { object: page, target: { kind, id, pageId: id }, resultingRevision: page.revision };
  }

  if (kind === 'evidence') {
    const id = asString(target?.id || payload.id, makeId('evidence'));
    const previous = run.evidence.get(id);
    if (action === 'create' && previous && !createIfMissing) throw new Error(`Evidence ${id} already exists.`);
    if ((action === 'patch' || action === 'replace') && previous) assertBaseRevision(previous, baseRevision);
    if ((action === 'patch' || action === 'replace') && !previous && !createIfMissing)
      throw new Error(`Evidence ${id} does not exist.`);
    const nextPayload =
      action === 'patch' && previous ? (deepMerge(previous, payload) as JsonRecord) : { ...payload, id };
    const evidence = normalizeEvidence(run, { ...nextPayload, id, revision: revision() });
    run.evidence.set(evidence.id, evidence);
    syncEvidenceEdges(run, evidence);
    return { object: evidence, target: { kind, id: evidence.id }, resultingRevision: evidence.revision };
  }

  if (kind === 'claim') {
    const id = asString(target?.id || payload.id, makeId('claim'));
    const previous = run.claims.get(id);
    if (action === 'create' && previous && !createIfMissing) throw new Error(`Claim ${id} already exists.`);
    if ((action === 'patch' || action === 'replace') && previous) assertBaseRevision(previous, baseRevision);
    if ((action === 'patch' || action === 'replace') && !previous && !createIfMissing)
      throw new Error(`Claim ${id} does not exist.`);
    const nextPayload =
      action === 'patch' && previous ? (deepMerge(previous, payload) as JsonRecord) : { ...payload, id };
    const claim = normalizeClaim(run, { ...nextPayload, id, revision: revision() });
    run.claims.set(claim.id, claim);
    syncClaimEdges(run, claim);
    return { object: claim, target: { kind, id: claim.id }, resultingRevision: claim.revision };
  }

  if (kind === 'provenance') {
    if (Array.isArray(payload.nodes)) {
      for (const item of payload.nodes) {
        if (!isRecord(item)) continue;
        const node = normalizeNode(run, item);
        run.provenance.set(node.id, node);
      }
    }
    if (Array.isArray(payload.edges)) {
      for (const item of payload.edges) {
        if (!isRecord(item)) continue;
        upsertEdge(run, normalizeEdge(run, item));
      }
    }
    if (isRecord(payload.from) || payload.fromId || payload.from_id) {
      const edge = normalizeEdge(run, payload);
      upsertEdge(run, edge);
      return { object: edge, target: { kind, id: edge.id } };
    }
    const node = normalizeNode(run, { ...payload, id: asString(target?.id || payload.id, makeId('provenance')) });
    run.provenance.set(node.id, node);
    return { object: node, target: { kind, id: node.id } };
  }

  if (kind === 'skill_use') {
    const id = asString(target?.id || payload.id, makeId('skill_use'));
    const previous = run.usedSkills.get(id);
    if (action === 'create' && previous && !createIfMissing) throw new Error(`Skill use ${id} already exists.`);
    if ((action === 'patch' || action === 'replace') && previous) assertBaseRevision(previous, baseRevision);
    if ((action === 'patch' || action === 'replace') && !previous && !createIfMissing)
      throw new Error(`Skill use ${id} does not exist.`);
    const nextPayload =
      action === 'patch' && previous ? (deepMerge(previous, payload) as JsonRecord) : { ...payload, id };
    const skillUse = normalizeSkillUse(run, { ...nextPayload, id, revision: revision() });
    run.usedSkills.set(skillUse.id, skillUse);
    return { object: skillUse, target: { kind, id: skillUse.id }, resultingRevision: skillUse.revision };
  }

  if (kind === 'annotation') {
    const id = asString(target?.id || payload.id, makeId('annotation'));
    const previous = run.annotations.get(id);
    if (previous && action !== 'create') assertBaseRevision(previous, baseRevision);
    const annotation: AnnotationRecord = {
      id,
      runId: run.runId,
      artifactId: asString(payload.artifactId || payload.artifact_id || target?.id, undefined as unknown as string),
      pageId: asString(payload.pageId || payload.page_id || target?.pageId, undefined as unknown as string),
      text: asString(payload.text || payload.comment, 'Annotation'),
      region: isRecord(payload.region) ? payload.region : undefined,
      gitAnchor: normalizeGitAnchor(run, payload.gitAnchor || payload.git_anchor || payload.anchor),
      status: (asString(payload.status, 'open') as AnnotationRecord['status']) || 'open',
      createdAt: asNumber(payload.createdAt || payload.created_at, now()),
      revision: revision(),
    };
    run.annotations.set(id, annotation);
    return { object: annotation, target: { kind, id }, resultingRevision: annotation.revision };
  }

  if (kind === 'memory') {
    const item: ScienceArtifactMemoryEvent = {
      id: asString(target?.id || payload.id, makeId('memory')),
      runId: run.runId,
      artifactId: asString(payload.artifactId || payload.artifact_id, undefined as unknown as string),
      artifactVersion:
        payload.artifactVersion || payload.artifact_version
          ? asNumber(payload.artifactVersion || payload.artifact_version, 1)
          : undefined,
      actor: ['user', 'agent', 'system'].includes(asString(payload.actor))
        ? (asString(payload.actor) as ScienceArtifactMemoryEvent['actor'])
        : 'agent',
      action: (asString(payload.action, 'append') as ScienceArtifactMemoryEvent['action']) || 'append',
      summary: asString(payload.summary, 'Artifact memory entry'),
      changedPaths: asArray(payload.changedPaths || payload.changed_paths).filter(
        (item): item is string => typeof item === 'string'
      ),
      evidenceIds: asArray(payload.evidenceIds || payload.evidence_ids).filter(
        (item): item is string => typeof item === 'string'
      ),
      claimIds: asArray(payload.claimIds || payload.claim_ids).filter(
        (item): item is string => typeof item === 'string'
      ),
      commit: asString(payload.commit, undefined as unknown as string),
      timestamp: asNumber(payload.timestamp, now()),
      hidden: true,
    };
    run.memory.push(item);
    return { object: item, target: { kind, id: item.id } };
  }

  throw new Error(`Unsupported Science artifact kind: ${kind}`);
};

const OPTIMIZATION_SCHEMA = 'deepscientist.optimization.v1' as const;
const OPTIMIZATION_TERMINAL_LINE_STATUSES = new Set(['stopped', 'rejected', 'archived']);
const OPTIMIZATION_TERMINAL_CANDIDATE_STATUSES = new Set(['promoted', 'rejected', 'archived']);
const OPTIMIZATION_FAILED_ATTEMPT_STATUSES = new Set(['failed', 'smoke_failed', 'archived']);
const OPTIMIZATION_ACTIVE_ATTEMPT_STATUSES = new Set([
  'proposed',
  'smoke_running',
  'smoke_passed',
  'promoted',
  'full_eval_running',
]);
const OPTIMIZATION_DISPATCHABLE_ATTEMPT_STATUSES = new Set(['proposed', 'smoke_passed', 'promoted']);
const OPTIMIZATION_RUNNING_ATTEMPT_STATUSES = new Set(['smoke_running', 'full_eval_running']);
const IOAI_CANDIDATE_DISPATCH_SCHEMA = 'deepscientist.ioai.candidate-dispatch.v1' as const;
const IOAI_CANDIDATE_DISPATCH_MAX_PARALLEL = 2 as const;
const IOAI_CANDIDATE_QUALITY_SCHEMA = 'deepscientist.ioai.candidate-quality.v1' as const;
const IOAI_CHANGE_LAYERS = new Set(['Tier1', 'Tier2', 'Tier3']);
const IOAI_COMPETITION_LESSON_PREFIX = 'competition_lesson:';
const IOAI_EXTERNAL_RESEARCH_PREFIX = 'external_research:';
const IOAI_EXTERNAL_RESEARCH_REF_PATTERN = /^external_research:[a-z0-9][a-z0-9._-]{0,63}@(high|medium|low)$/u;
const IOAI_COMPETITION_RESEARCH_PACKET_PATH = 'artifacts/idea/competition_research.md';
const IOAI_CURATED_COMPETITION_LESSON_REFS = new Set([
  'competition_lesson:validation_structure_alignment@medium',
  'competition_lesson:metric_aligned_postprocessing@low',
  'competition_lesson:complementary_oof_fusion@low',
]);
const IOAI_SOURCE_LENSES = new Set([
  'baseline_refinement',
  'orthogonal_mechanism',
  'failure_repair',
  'cross_domain_transfer',
  'objective_shift',
  'search_widening',
]);
const IOAI_ALTERNATIVE_DISPOSITIONS = new Set(['evaluated', 'rejected', 'budget_excluded', 'not_applicable']);

const optimizationArtifactId = (kind: string, identity: string): string =>
  `optimization_${kind}_${crypto.createHash('sha256').update(identity).digest('hex').slice(0, 16)}`;

const readOptimizationMetadata = (
  artifact: ScienceArtifact | undefined
): ScienceOptimizationArtifactMetadata | undefined => {
  const value = artifact?.metadata?.deepScientistOptimization;
  if (!isRecord(value) || value.schema !== OPTIMIZATION_SCHEMA) return undefined;
  if (
    !['idea_candidate', 'optimization_line', 'implementation_attempt', 'main_experiment'].includes(asString(value.kind))
  )
    return undefined;
  return value as unknown as ScienceOptimizationArtifactMetadata;
};

const latestArtifactVersion = (run: ScienceRunState, id: string): ScienceArtifact | undefined =>
  [...run.artifacts.values()]
    .filter((artifact) => artifact.id === id)
    .sort((left, right) => right.version - left.version)[0];

const latestOptimizationArtifacts = (run: ScienceRunState): ScienceArtifact[] => {
  const latest = new Map<string, ScienceArtifact>();
  for (const artifact of run.artifacts.values()) {
    if (!readOptimizationMetadata(artifact)) continue;
    const previous = latest.get(artifact.id);
    if (!previous || artifact.version > previous.version) latest.set(artifact.id, artifact);
  }
  return [...latest.values()].sort(
    (left, right) => left.createdAt - right.createdAt || left.id.localeCompare(right.id)
  );
};

const findOptimizationArtifact = (
  run: ScienceRunState,
  kind: ScienceOptimizationArtifactMetadata['kind'],
  identity: string
): ScienceArtifact | undefined =>
  latestOptimizationArtifacts(run).find((artifact) => {
    const metadata = readOptimizationMetadata(artifact);
    if (!metadata || metadata.kind !== kind) return false;
    if (kind === 'idea_candidate') return metadata.ideaId === identity;
    if (kind === 'optimization_line') return metadata.lineId === identity || metadata.ideaId === identity;
    if (kind === 'implementation_attempt') return metadata.attemptId === identity;
    return metadata.runId === identity;
  });

const writeOptimizationArtifactVersion = (
  run: ScienceRunState,
  options: {
    id: string;
    type: ScienceArtifact['type'];
    title: string;
    status?: ScienceArtifact['status'];
    metadata: ScienceOptimizationArtifactMetadata;
    evidenceIds?: string[];
    changeSummary?: string;
  }
): ScienceArtifact => {
  const previous = latestArtifactVersion(run, options.id);
  const version = previous ? previous.version + 1 : 1;
  const artifact = normalizeArtifact(run, {
    ...(previous || {}),
    id: options.id,
    type: options.type,
    title: options.title,
    status: options.status || 'available',
    version,
    versionGroupId: previous?.versionGroupId || options.id,
    previousArtifactId: previous?.id,
    previousVersion: previous?.version,
    changeSummary: options.changeSummary,
    evidenceIds: options.evidenceIds || previous?.evidenceIds || [],
    metadata: {
      ...(previous?.metadata || {}),
      deepScientistOptimization: options.metadata,
    },
    createdAt: now(),
    revision: revision(),
  });
  run.artifacts.set(artifactKey(artifact.id, artifact.version), artifact);
  syncArtifactEdges(run, artifact);
  return artifact;
};

const normalizeSelectionScores = (value: unknown): Record<string, number> | undefined => {
  if (!isRecord(value)) return undefined;
  const entries = Object.entries(value).filter(
    (entry): entry is [string, number] => typeof entry[1] === 'number' && Number.isFinite(entry[1])
  );
  return entries.length ? Object.fromEntries(entries) : undefined;
};

const normalizeOptimizationMetrics = (body: JsonRecord): ScienceOptimizationMetric[] => {
  const rows = asArray(body.metricRows || body.metric_rows || (Array.isArray(body.metrics) ? body.metrics : undefined));
  const normalized = new Map<string, ScienceOptimizationMetric>();
  for (const item of rows) {
    if (!isRecord(item)) continue;
    const metricId = asString(item.metricId || item.metric_id || item.key || item.name);
    const rawValue = item.value;
    if (!metricId || typeof rawValue !== 'number' || !Number.isFinite(rawValue)) continue;
    const rawDirection = asString(item.direction, 'higher').toLowerCase();
    const baselineValue = item.baselineValue ?? item.baseline_value;
    const split = asString(item.split) || undefined;
    normalized.set(`${metricId}\u0000${split || 'aggregate'}`, {
      metricId,
      value: rawValue,
      direction: ['lower', 'lower_better', 'minimize'].includes(rawDirection) ? 'lower' : 'higher',
      baselineValue: typeof baselineValue === 'number' && Number.isFinite(baselineValue) ? baselineValue : undefined,
      split,
      primary: item.primary === true,
    });
  }
  const baselineComparison = body.baselineComparison || body.baseline_comparison;
  if (isRecord(baselineComparison)) {
    const metricId = asString(baselineComparison.metricId || baselineComparison.metric_id);
    const value = baselineComparison.candidateScore ?? baselineComparison.candidate_score;
    const baselineValue = baselineComparison.baselineScore ?? baselineComparison.baseline_score;
    const direction = asString(baselineComparison.direction, 'maximize').toLowerCase();
    const key = `${metricId}\u0000aggregate`;
    if (metricId && !normalized.has(key) && typeof value === 'number' && Number.isFinite(value)) {
      normalized.set(key, {
        metricId,
        value,
        direction: ['lower', 'lower_better', 'minimize'].includes(direction) ? 'lower' : 'higher',
        baselineValue: typeof baselineValue === 'number' && Number.isFinite(baselineValue) ? baselineValue : undefined,
        primary: true,
      });
    }
  }
  const summaries = [
    body.metricsSummary,
    body.metrics_summary,
    !Array.isArray(body.metrics) ? body.metrics : undefined,
  ];
  for (const summary of summaries) {
    if (!isRecord(summary)) continue;
    for (const [metricId, rawValue] of Object.entries(summary)) {
      const key = `${metricId}\u0000aggregate`;
      if (normalized.has(key) || typeof rawValue !== 'number' || !Number.isFinite(rawValue)) continue;
      normalized.set(key, { metricId, value: rawValue, direction: 'higher' });
    }
  }
  const result = [...normalized.values()];
  if (result.length && !result.some((metric) => metric.primary))
    (result.find((metric) => !metric.split) || result[0]).primary = true;
  return result;
};

const metricImprovement = (metric: ScienceOptimizationMetric): number | undefined => {
  if (metric.baselineValue == null) return undefined;
  const rawDelta = metric.value - metric.baselineValue;
  return metric.direction === 'lower' ? -rawDelta : rawDelta;
};

const metricUtility = (metric: ScienceOptimizationMetric): number =>
  metric.direction === 'lower' ? -metric.value : metric.value;

const primaryOptimizationMetric = (
  metadata: ScienceOptimizationArtifactMetadata
): ScienceOptimizationMetric | undefined =>
  metadata.metrics?.find((metric) => metric.primary && !metric.split) ||
  metadata.metrics?.find((metric) => !metric.split) ||
  metadata.metrics?.find((metric) => metric.primary) ||
  metadata.metrics?.[0];

const isOptimizationExecutionFailure = (failureKind: string, status: string): boolean => {
  if (
    /(worker|process|launch|timeout|wall_clock|network_isolation|execution_contract|cancel|resource|environment)/u.test(
      failureKind
    )
  )
    return true;
  return !failureKind && ['failed', 'error', 'cancelled'].includes(status);
};

const classifyOptimizationResult = (
  metadata: Pick<ScienceOptimizationArtifactMetadata, 'status' | 'valid' | 'failureKind' | 'metrics'>
): ScienceOptimizationFailureClass => {
  const status = asString(metadata.status).toLowerCase();
  const failureKind = asString(metadata.failureKind).toLowerCase();
  if (metadata.valid === false)
    return isOptimizationExecutionFailure(failureKind, status) ? 'execution_error' : 'invalid_result';
  if (isOptimizationExecutionFailure(failureKind, status)) return 'execution_error';
  const primary = primaryOptimizationMetric(metadata as ScienceOptimizationArtifactMetadata);
  const primaryImprovements = (metadata.metrics || [])
    .filter((metric) => metric.metricId === primary?.metricId && metric.direction === primary.direction)
    .map(metricImprovement)
    .filter((value): value is number => value != null);
  const improvement = primary?.split
    ? primaryImprovements.length
      ? primaryImprovements.reduce((sum, value) => sum + value, 0) / primaryImprovements.length
      : undefined
    : primary
      ? metricImprovement(primary)
      : undefined;
  return improvement != null && improvement > 0 ? 'valid_gain' : 'valid_no_gain';
};

const assessOptimizationStability = (
  metadata: Pick<ScienceOptimizationArtifactMetadata, 'valid' | 'metrics'>,
  deterministicSimpleTask: boolean
): ScienceOptimizationStabilityAssessment => {
  if (metadata.valid === false)
    return {
      aggregateImprovement: null,
      minimumImprovement: 0,
      splitCount: 0,
      worstSplitImprovement: null,
      promotionEligible: false,
      evidenceBasis: 'invalid_result',
      reason: 'Invalid or failed results cannot be promoted.',
    };
  const primary = primaryOptimizationMetric(metadata as ScienceOptimizationArtifactMetadata);
  const aggregateImprovement = primary && !primary.split ? metricImprovement(primary) : undefined;
  const splitImprovements = (metadata.metrics || [])
    .filter(
      (metric) =>
        Boolean(metric.split) &&
        metric.metricId === primary?.metricId &&
        metric.direction === primary.direction &&
        metricImprovement(metric) != null
    )
    .map((metric) => metricImprovement(metric) as number);
  const splitCount = splitImprovements.length;
  const worstSplitImprovement = splitCount ? Math.min(...splitImprovements) : null;
  if (deterministicSimpleTask) {
    const promotionEligible = aggregateImprovement != null && aggregateImprovement > 0;
    return {
      aggregateImprovement: aggregateImprovement ?? null,
      minimumImprovement: 0,
      splitCount,
      worstSplitImprovement,
      promotionEligible,
      evidenceBasis: 'deterministic_simple_task',
      reason: promotionEligible
        ? 'The established deterministic-simple-task route does not require a noise recheck.'
        : 'The deterministic result did not establish a positive improvement.',
    };
  }
  if (splitCount >= 2) {
    const mean = splitImprovements.reduce((sum, value) => sum + value, 0) / splitCount;
    const variance = splitImprovements.reduce((sum, value) => sum + (value - mean) ** 2, 0) / (splitCount - 1);
    const minimumImprovement = 1.96 * (Math.sqrt(variance) / Math.sqrt(splitCount));
    const effectiveImprovement = aggregateImprovement ?? mean;
    const promotionEligible =
      effectiveImprovement > minimumImprovement && (worstSplitImprovement as number) >= -minimumImprovement;
    return {
      aggregateImprovement: aggregateImprovement ?? mean,
      minimumImprovement,
      splitCount,
      worstSplitImprovement,
      promotionEligible,
      evidenceBasis: 'split_evidence',
      reason: promotionEligible
        ? 'Improvement clears the split-noise threshold without a collapsing split.'
        : 'Aggregate improvement is too noisy or hides a collapsing split.',
    };
  }
  const promotionEligible = aggregateImprovement != null && aggregateImprovement > 0;
  return {
    aggregateImprovement: aggregateImprovement ?? null,
    minimumImprovement: 0,
    splitCount,
    worstSplitImprovement,
    promotionEligible,
    evidenceBasis: 'aggregate_only',
    reason: promotionEligible
      ? 'Positive aggregate-only evidence is compatible but has no split-noise estimate.'
      : 'Aggregate-only evidence does not establish a positive improvement.',
  };
};

const optimizationLesson = (
  body: JsonRecord,
  metadata: ScienceOptimizationArtifactMetadata,
  line: ScienceOptimizationArtifactMetadata
): ScienceOptimizationLessonCapsule => {
  const lessonValue = body.lesson || body.lessonCapsule || body.lesson_capsule;
  const provided = isRecord(lessonValue) ? (lessonValue as JsonRecord) : {};
  const providedObservedEffect = asString(provided.observedEffect || provided.observed_effect);
  const providedFailedAssumption = asString(provided.failedAssumption || provided.failed_assumption);
  const providedUsefulComponent = asString(provided.usefulComponent || provided.useful_component);
  const providedDoNotRepeat = asString(provided.doNotRepeat || provided.do_not_repeat);
  const providedNextSearchBoundary = asString(provided.nextSearchBoundary || provided.next_search_boundary);
  const providedEvidenceRefs = asStringArray(provided.evidenceRefs || provided.evidence_refs);
  if (metadata.taskId && metadata.sealId) {
    if (!isRecord(lessonValue))
      throw new Error('Task-scoped record_main_experiment requires a complete lesson capsule.');
    const missing = [
      ['observedEffect', providedObservedEffect],
      ['failedAssumption', providedFailedAssumption],
      ['usefulComponent', providedUsefulComponent],
      ['doNotRepeat', providedDoNotRepeat],
      ['nextSearchBoundary', providedNextSearchBoundary],
      ['evidenceRefs', providedEvidenceRefs.length ? 'present' : ''],
    ]
      .filter(([, value]) => !value)
      .map(([field]) => field);
    if (missing.length) throw new Error(`Task-scoped lesson capsule is incomplete: ${missing.join(', ')}.`);
  }
  const primary = primaryOptimizationMetric(metadata);
  const improvement = primary ? metricImprovement(primary) : undefined;
  const failureKind = metadata.failureKind ? ` (${metadata.failureKind})` : '';
  const observedEffect =
    metadata.failureClass === 'execution_error'
      ? `The run produced no valid evaluation because execution failed${failureKind}.`
      : metadata.failureClass === 'invalid_result'
        ? `The evaluator rejected the candidate result${failureKind}.`
        : improvement != null
          ? `The primary metric changed by ${improvement} versus its fixed baseline.`
          : 'The valid run did not establish a baseline-relative gain.';
  const defaultAssumption =
    metadata.failureClass === 'execution_error'
      ? 'The candidate would complete under the sealed execution contract.'
      : metadata.failureClass === 'invalid_result'
        ? 'The candidate would emit a schema-valid evaluator result.'
        : metadata.failureClass === 'valid_no_gain'
          ? 'The tested mechanism would improve the fixed primary metric.'
          : 'No tested mechanism assumption was falsified by this result.';
  return {
    observedEffect: providedObservedEffect || observedEffect,
    failedAssumption: providedFailedAssumption || defaultAssumption,
    usefulComponent: asString(
      providedUsefulComponent,
      metadata.failureClass === 'valid_gain'
        ? line.mechanism || line.mechanismFamily || 'The measured mechanism remains useful.'
        : 'No reusable component was established.'
    ),
    doNotRepeat: asString(
      providedDoNotRepeat,
      `Do not repeat run ${metadata.runId} without new evidence or a bounded repair.`
    ),
    nextSearchBoundary: asString(
      providedNextSearchBoundary,
      metadata.failureClass === 'execution_error' || metadata.failureClass === 'invalid_result'
        ? 'Allow one bounded repair on this line, then archive it if repair fails.'
        : metadata.failureClass === 'valid_no_gain'
          ? 'Stay outside this exact implementation and reassess the mechanism after repeated valid non-gains.'
          : 'Promote only if the stability assessment is eligible.'
    ),
    evidenceRefs: [
      ...new Set([
        `run:${metadata.runId}`,
        ...providedEvidenceRefs,
        ...(metadata.evidenceBasis || []),
        ...(metadata.evidencePaths || []),
      ]),
    ],
  };
};

type OptimizationDispatchItem = ScienceOptimizationArtifactMetadata & {
  artifactId?: string;
  stagnant?: boolean;
};

const optimizationItemId = (item: OptimizationDispatchItem): string =>
  asString(item.attemptId || item.runId || item.lineId || item.ideaId || item.artifactId);

const optimizationEvidenceRefs = (item: OptimizationDispatchItem): string[] => [
  ...new Set(
    [...(item.evidenceBasis || []), ...(item.evidencePaths || [])].map((value) => asString(value)).filter(Boolean)
  ),
];

const verifyOptimizationEvidencePaths = (
  evidencePaths: string[] | undefined,
  projectRoot?: string
): { verified: string[]; unverified: string[] } => {
  const verified: string[] = [];
  const unverified: string[] = [];
  for (const evidencePath of asStringArray(evidencePaths)) {
    try {
      const resolved = projectRoot ? resolveProjectOwnedPath(projectRoot, evidencePath, 'evidencePath') : '';
      if (resolved && fs.existsSync(resolved) && fs.statSync(resolved).isFile()) verified.push(evidencePath);
      else unverified.push(evidencePath);
    } catch {
      unverified.push(evidencePath);
    }
  }
  return { verified, unverified };
};

const normalizeOptimizationStrongestAlternative = (
  value: unknown,
  fallback?: unknown
): ScienceOptimizationStrongestAlternative | undefined => {
  const source = isRecord(value) ? value : isRecord(fallback) ? fallback : undefined;
  if (!source) return undefined;
  const mechanismFamily = asString(source.mechanismFamily || source.mechanism_family);
  const disposition = asString(source.disposition).toLowerCase();
  const reason = asString(source.reason);
  const evidenceRefs = asStringArray(source.evidenceRefs || source.evidence_refs);
  if (!mechanismFamily && !disposition && !reason && !evidenceRefs.length) return undefined;
  return {
    mechanismFamily,
    disposition: disposition as ScienceOptimizationStrongestAlternative['disposition'],
    reason,
    evidenceRefs,
  };
};

export const assessOptimizationCandidateQuality = (
  candidate: ScienceOptimizationArtifactMetadata,
  projectRoot?: string
): ScienceOptimizationCandidateQuality => {
  const missingFields: string[] = [];
  const requiredText: Array<[string, unknown]> = [
    ['problem', candidate.problem],
    ['whyCurrentLineIsLimited', candidate.whyCurrentLineIsLimited],
    ['mechanism', candidate.mechanism],
    ['mechanismFamily', candidate.mechanismFamily],
    ['whyNow', candidate.whyNow],
    ['implementationSurface', candidate.implementationSurface],
    ['falsificationPlan', candidate.falsificationPlan],
    ['abandonmentCondition', candidate.abandonmentCondition],
    ['expectedGain', candidate.expectedGain],
  ];
  for (const [field, value] of requiredText) if (!asString(value)) missingFields.push(field);
  const alternative = candidate.strongestAlternative;
  if (!alternative) {
    missingFields.push('strongestAlternative');
  } else {
    if (!asString(alternative.mechanismFamily)) missingFields.push('strongestAlternative.mechanismFamily');
    if (!IOAI_ALTERNATIVE_DISPOSITIONS.has(asString(alternative.disposition)))
      missingFields.push('strongestAlternative.disposition');
    if (!asString(alternative.reason)) missingFields.push('strongestAlternative.reason');
    if (!asStringArray(alternative.evidenceRefs).length) missingFields.push('strongestAlternative.evidenceRefs');
    if (
      alternative.disposition !== 'not_applicable' &&
      asString(alternative.mechanismFamily).toLowerCase() === asString(candidate.mechanismFamily).toLowerCase()
    )
      missingFields.push('strongestAlternative.distinctMechanismFamily');
  }
  if (!IOAI_CHANGE_LAYERS.has(asString(candidate.changeLayer))) missingFields.push('changeLayer');
  if (!IOAI_SOURCE_LENSES.has(asString(candidate.sourceLens))) missingFields.push('sourceLens');
  if (!asStringArray(candidate.keepUnchanged).length) missingFields.push('keepUnchanged');
  if (!asStringArray(candidate.mainRisks).length) missingFields.push('mainRisks');
  const pathEvidence = verifyOptimizationEvidencePaths(candidate.evidencePaths, projectRoot);
  const evidenceBasis = asStringArray(candidate.evidenceBasis);
  const competitionLessonRefs = [
    ...new Set(evidenceBasis.filter((value) => value.startsWith(IOAI_COMPETITION_LESSON_PREFIX))),
  ];
  const externalResearchRefs = [
    ...new Set(evidenceBasis.filter((value) => value.startsWith(IOAI_EXTERNAL_RESEARCH_PREFIX))),
  ];
  const rawExternalUrls = evidenceBasis.filter((value) => /^https?:\/\//iu.test(value));
  const qualifyingNarrativeEvidence = evidenceBasis.some(
    (value) =>
      !value.startsWith(IOAI_COMPETITION_LESSON_PREFIX) &&
      !value.startsWith(IOAI_EXTERNAL_RESEARCH_PREFIX) &&
      !/^https?:\/\//iu.test(value)
  );
  const qualifyingArtifactEvidence = pathEvidence.verified.filter(
    (value) => value.replace(/\\/gu, '/').toLowerCase() !== IOAI_COMPETITION_RESEARCH_PACKET_PATH
  );
  const hasResearchPacket = pathEvidence.verified.some(
    (value) => value.replace(/\\/gu, '/').toLowerCase() === IOAI_COMPETITION_RESEARCH_PACKET_PATH
  );
  const hasIndependentTaskEvidence = qualifyingNarrativeEvidence || qualifyingArtifactEvidence.length > 0;
  if (competitionLessonRefs.some((value) => !IOAI_CURATED_COMPETITION_LESSON_REFS.has(value)))
    missingFields.push('competitionLessonRefs.known');
  if (competitionLessonRefs.length > 2) missingFields.push('competitionLessonRefs.maxTwo');
  if (competitionLessonRefs.length > 0 && !hasIndependentTaskEvidence)
    missingFields.push('competitionLessonRefs.taskEvidence');
  if (externalResearchRefs.some((value) => !IOAI_EXTERNAL_RESEARCH_REF_PATTERN.test(value)))
    missingFields.push('externalResearchRefs.valid');
  if (externalResearchRefs.length > 0 && !hasResearchPacket) missingFields.push('externalResearchRefs.researchPacket');
  if (rawExternalUrls.length > 0) missingFields.push('externalResearchRefs.packetReferenceRequired');
  if (externalResearchRefs.length > 0 && !hasIndependentTaskEvidence)
    missingFields.push('externalResearchRefs.taskEvidence');
  if (!hasIndependentTaskEvidence) missingFields.push('evidence');
  const estimatedCostMinutes =
    typeof candidate.estimatedCostMinutes === 'number' &&
    Number.isFinite(candidate.estimatedCostMinutes) &&
    candidate.estimatedCostMinutes > 0
      ? candidate.estimatedCostMinutes
      : null;
  if (estimatedCostMinutes === null) missingFields.push('estimatedCostMinutes');
  if (candidate.taskId && !candidate.metricContractId) missingFields.push('metricContractId');
  return {
    schema: IOAI_CANDIDATE_QUALITY_SCHEMA,
    eligible: missingFields.length === 0,
    missingFields,
    evidenceLevel: qualifyingArtifactEvidence.length ? 'artifact' : qualifyingNarrativeEvidence ? 'narrative' : 'none',
    verifiedEvidencePaths: pathEvidence.verified,
    unverifiedEvidencePaths: pathEvidence.unverified,
    estimatedCostMinutes,
  };
};

const evidenceLevelRank = (level: ScienceOptimizationCandidateQuality['evidenceLevel']): number =>
  level === 'artifact' ? 0 : level === 'narrative' ? 1 : 2;

const changeLayerRank = (layer: unknown): number => {
  const normalized = asString(layer);
  if (normalized === 'Tier1') return 0;
  if (normalized === 'Tier2') return 1;
  if (normalized === 'Tier3') return 2;
  return 3;
};

const optimizationTaskScope = (
  taskId: unknown,
  sealId: unknown,
  field = 'optimization task scope'
): ScienceOptimizationTaskScope | undefined => {
  const normalizedTaskId = asString(taskId);
  const normalizedSealId = asString(sealId);
  if (Boolean(normalizedTaskId) !== Boolean(normalizedSealId))
    throw new Error(`${field} requires both taskId and sealId.`);
  return normalizedTaskId ? { taskId: normalizedTaskId, sealId: normalizedSealId } : undefined;
};

const optimizationItemMatchesScope = (
  item: ScienceOptimizationArtifactMetadata | undefined,
  scope: ScienceOptimizationTaskScope | undefined
): boolean => !scope || (item?.taskId === scope.taskId && item.sealId === scope.sealId);

const selectDiverseOptimizationItems = <T extends OptimizationDispatchItem>(values: T[], limit: number): T[] => {
  const selected: T[] = [];
  const families = new Set<string>();
  const layers = new Set<string>();
  while (selected.length < limit) {
    const eligible = values.filter((value) => {
      const family = asString(value.mechanismFamily).toLowerCase();
      return family && !families.has(family) && !selected.includes(value);
    });
    if (!eligible.length) break;
    const value =
      eligible.find((candidate) => {
        const layer = asString(candidate.changeLayer);
        return layer && !layers.has(layer);
      }) || eligible[0];
    const family = asString(value.mechanismFamily).toLowerCase();
    selected.push(value);
    families.add(family);
    if (value.changeLayer) layers.add(value.changeLayer);
  }
  return selected;
};

export const decideOptimizationDispatch = (input: {
  projectRoot?: string;
  taskScope?: ScienceOptimizationTaskScope;
  route: ScienceOptimizationRoute;
  candidateBriefs: OptimizationDispatchItem[];
  lines: OptimizationDispatchItem[];
  implementationAttempts: OptimizationDispatchItem[];
  bestLineId?: string;
  fusionOpportunity?: {
    lineIds: string[];
    evidenceIds?: string[];
    evidencePaths?: string[];
  };
  repairableFailure?: OptimizationDispatchItem;
}): ScienceOptimizationDispatchDecision => {
  const occupiedSlots = Math.min(
    IOAI_CANDIDATE_DISPATCH_MAX_PARALLEL,
    input.implementationAttempts.filter((attempt) =>
      OPTIMIZATION_RUNNING_ATTEMPT_STATUSES.has(asString(attempt.status).toLowerCase())
    ).length
  );
  const availableSlots = IOAI_CANDIDATE_DISPATCH_MAX_PARALLEL - occupiedSlots;
  const activeLines = input.lines.filter(
    (line) => !OPTIMIZATION_TERMINAL_LINE_STATUSES.has(asString(line.status).toLowerCase())
  );
  const linesById = new Map(activeLines.map((line) => [asString(line.lineId), line] as const));
  const activeBriefs = input.candidateBriefs.filter(
    (brief) => !OPTIMIZATION_TERMINAL_CANDIDATE_STATUSES.has(asString(brief.status).toLowerCase())
  );
  const bestLine = activeLines.find((line) => line.lineId === input.bestLineId);
  const metricContractId = asString(
    bestLine?.metricContractId ||
      activeLines.find((line) => line.metricContractId)?.metricContractId ||
      activeBriefs.find((brief) => brief.metricContractId)?.metricContractId
  );
  const matchesMetricContract = (item: OptimizationDispatchItem): boolean =>
    !input.taskScope || (Boolean(metricContractId) && item.metricContractId === metricContractId);
  const finish = (
    action: ScienceOptimizationDispatchDecision['action'],
    selected: ScienceOptimizationDispatchTarget[],
    considered: OptimizationDispatchItem[],
    reason: string,
    route = input.route
  ): ScienceOptimizationDispatchDecision => {
    const selectedIds = new Set(selected.map((target) => target.id));
    return {
      schema: IOAI_CANDIDATE_DISPATCH_SCHEMA,
      taskScope: input.taskScope || null,
      metricContractId: metricContractId || null,
      route,
      action,
      maxParallel: IOAI_CANDIDATE_DISPATCH_MAX_PARALLEL,
      occupiedSlots,
      availableSlots,
      selected,
      heldIds: considered.map(optimizationItemId).filter((id) => id && !selectedIds.has(id)),
      reason,
    };
  };
  const target = (
    kind: ScienceOptimizationDispatchTarget['kind'],
    item: OptimizationDispatchItem,
    family = asString(item.mechanismFamily)
  ): ScienceOptimizationDispatchTarget => ({
    kind,
    id: optimizationItemId(item),
    lineId: asString(item.lineId) || null,
    mechanismFamily: family || null,
    evidenceRefs: [
      ...new Set([
        ...(item.evidenceBasis || []),
        ...verifyOptimizationEvidencePaths(item.evidencePaths, input.projectRoot).verified,
      ]),
    ],
  });

  if (input.route === 'stop') return finish('stop', [], [], 'The native optimization frontier is exhausted.');
  if (!availableSlots) return finish('wait', [], [], 'Both bounded execution slots already contain running attempts.');
  if (input.taskScope && (activeLines.length || activeBriefs.length) && !metricContractId)
    return finish(
      'wait',
      [],
      [...activeLines, ...activeBriefs],
      'CV contract gate is blocked: record one frozen metricContractId before candidate dispatch.'
    );

  if (input.route === 'debug') {
    const failure = input.repairableFailure;
    const line = failure ? linesById.get(asString(failure.lineId)) : undefined;
    if (!failure || !line)
      return finish('wait', [], [], 'The debug route has no eligible one-repair failure on an active line.');
    const repairTarget = target('main_experiment', {
      ...failure,
      mechanismFamily: line.mechanismFamily,
    });
    repairTarget.evidenceRefs = [
      ...new Set([`run:${failure.runId}`, ...repairTarget.evidenceRefs, asString(failure.failureKind)].filter(Boolean)),
    ];
    return finish(
      'prepare_repair',
      [repairTarget],
      [failure],
      `Prepare the only permitted bounded repair for run ${failure.runId}; preserve its mechanism and comparison contract.`
    );
  }

  if (input.route === 'fusion' && input.fusionOpportunity?.lineIds.length) {
    const fusionLines = [...new Set(input.fusionOpportunity.lineIds)]
      .map((lineId) => linesById.get(lineId))
      .filter((line): line is OptimizationDispatchItem => Boolean(line && matchesMetricContract(line)));
    if (new Set(fusionLines.map((line) => asString(line.mechanismFamily).toLowerCase())).size >= 2) {
      return finish(
        'fuse_lines',
        [
          {
            kind: 'fusion',
            id: fusionLines.map((line) => asString(line.lineId)).join('+'),
            lineId: null,
            mechanismFamily: null,
            evidenceRefs: [
              ...new Set([
                ...(input.fusionOpportunity.evidenceIds || []),
                ...(input.fusionOpportunity.evidencePaths || []),
              ]),
            ],
          },
        ],
        fusionLines,
        'Prepare one bounded fusion from distinct measured mechanism families.'
      );
    }
  }

  const dispatchableAttempts = input.implementationAttempts
    .filter((attempt) => {
      const line = linesById.get(asString(attempt.lineId));
      return (
        Boolean(optimizationItemId(attempt) && line && !line.stagnant) &&
        matchesMetricContract(line as OptimizationDispatchItem) &&
        OPTIMIZATION_DISPATCHABLE_ATTEMPT_STATUSES.has(asString(attempt.status).toLowerCase())
      );
    })
    .map((attempt) => ({ ...attempt, mechanismFamily: linesById.get(asString(attempt.lineId))?.mechanismFamily }))
    .sort((left, right) => {
      const leftBest = left.lineId === input.bestLineId ? 0 : 1;
      const rightBest = right.lineId === input.bestLineId ? 0 : 1;
      return leftBest - rightBest || optimizationItemId(left).localeCompare(optimizationItemId(right));
    });
  const selectedAttempts = selectDiverseOptimizationItems(dispatchableAttempts, availableSlots);
  if (selectedAttempts.length)
    return finish(
      'dispatch_attempt',
      selectedAttempts.map((attempt) => target('implementation_attempt', attempt)),
      dispatchableAttempts,
      'Dispatch prepared attempts immediately, preserving mechanism diversity when two slots are free.'
    );

  const readyLines = activeLines
    .filter((line) => line.lineId && line.mechanismFamily && !line.stagnant && matchesMetricContract(line))
    .sort((left, right) => {
      const leftBest = left.lineId === input.bestLineId ? 0 : 1;
      const rightBest = right.lineId === input.bestLineId ? 0 : 1;
      return leftBest - rightBest || optimizationItemId(left).localeCompare(optimizationItemId(right));
    });
  const selectedLines = selectDiverseOptimizationItems(readyLines, availableSlots);
  if (selectedLines.length)
    return finish(
      'prepare_attempt',
      selectedLines.map((line) => target('optimization_line', line)),
      readyLines,
      'Prepare one atomic attempt per selected line; do not fill slots with same-family parameter variants.'
    );

  const stagnantFamilies = new Set(
    activeLines
      .filter((line) => line.stagnant)
      .map((line) => asString(line.mechanismFamily).toLowerCase())
      .filter(Boolean)
  );
  const readyBriefs = activeBriefs
    .filter(
      (brief) =>
        brief.ideaId &&
        brief.mechanismFamily &&
        brief.mechanism &&
        brief.falsificationPlan &&
        optimizationEvidenceRefs(brief).length &&
        matchesMetricContract(brief) &&
        (!input.taskScope || assessOptimizationCandidateQuality(brief, input.projectRoot).eligible) &&
        !stagnantFamilies.has(asString(brief.mechanismFamily).toLowerCase())
    )
    .sort((left, right) => {
      const leftQuality = assessOptimizationCandidateQuality(left, input.projectRoot);
      const rightQuality = assessOptimizationCandidateQuality(right, input.projectRoot);
      const evidenceDelta =
        evidenceLevelRank(leftQuality.evidenceLevel) - evidenceLevelRank(rightQuality.evidenceLevel);
      if (evidenceDelta) return evidenceDelta;
      const costDelta =
        (leftQuality.estimatedCostMinutes ?? Number.POSITIVE_INFINITY) -
        (rightQuality.estimatedCostMinutes ?? Number.POSITIVE_INFINITY);
      if (costDelta) return costDelta;
      const layerDelta = changeLayerRank(left.changeLayer) - changeLayerRank(right.changeLayer);
      return layerDelta || optimizationItemId(left).localeCompare(optimizationItemId(right));
    });
  const selectedBriefs = selectDiverseOptimizationItems(readyBriefs, availableSlots);
  if (selectedBriefs.length)
    return finish(
      'promote_candidate',
      selectedBriefs.map((brief) => target('idea_candidate', brief)),
      readyBriefs,
      'Promote only evidence-ready briefs from distinct mechanism families.'
    );

  return finish(
    'generate_candidate',
    [],
    [],
    activeLines.some((line) => line.stagnant)
      ? 'All live lines are stagnant; generate one evidence-backed candidate from an orthogonal mechanism family.'
      : 'No dispatch-ready evidence-backed candidate exists; generate a small differentiated brief slate.',
    'explore'
  );
};

export const submitOptimizationIdea = (
  run: ScienceRunState,
  body: JsonRecord
): {
  artifact: ScienceArtifact;
  promotedCandidate?: ScienceArtifact;
  metadata: ScienceOptimizationArtifactMetadata;
} => {
  const mode = asString(body.mode, 'create').toLowerCase();
  if (!['create', 'revise'].includes(mode)) throw new Error('submit_idea mode must be "create" or "revise".');
  const submissionMode = asString(body.submissionMode || body.submission_mode, 'line').toLowerCase();
  if (!['candidate', 'line'].includes(submissionMode))
    throw new Error('submit_idea submissionMode must be "candidate" or "line".');

  const sourceCandidateId = asString(
    body.sourceCandidateId || body.source_candidate_id,
    undefined as unknown as string
  );
  const sourceCandidate = sourceCandidateId
    ? findOptimizationArtifact(run, 'idea_candidate', sourceCandidateId)
    : undefined;
  if (sourceCandidateId && !sourceCandidate)
    throw new Error(`Candidate brief ${sourceCandidateId} does not exist in this Science run.`);
  const source = readOptimizationMetadata(sourceCandidate);
  const ideaId = asString(
    body.ideaId || body.idea_id,
    mode === 'revise'
      ? source?.ideaId || ''
      : `idea_${Date.now().toString(36)}_${crypto.randomBytes(3).toString('hex')}`
  );
  if (!ideaId) throw new Error('submit_idea requires ideaId when mode="revise".');

  const existing =
    submissionMode === 'candidate'
      ? findOptimizationArtifact(run, 'idea_candidate', ideaId)
      : findOptimizationArtifact(run, 'optimization_line', asString(body.lineId || body.line_id, ideaId));
  if (mode === 'create' && existing)
    throw new Error(
      `${submissionMode === 'candidate' ? 'Candidate brief' : 'Optimization line'} ${ideaId} already exists.`
    );
  if (mode === 'revise' && !existing)
    throw new Error(
      `${submissionMode === 'candidate' ? 'Candidate brief' : 'Optimization line'} ${ideaId} does not exist.`
    );
  const previous = readOptimizationMetadata(existing);
  const requestedTaskScope = optimizationTaskScope(
    body.taskId || body.task_id,
    body.sealId || body.seal_id,
    'submit_idea task scope'
  );
  const inheritedTaskScope = optimizationTaskScope(
    source?.taskId || previous?.taskId,
    source?.sealId || previous?.sealId,
    'stored optimization task scope'
  );
  const taskScope = requestedTaskScope || inheritedTaskScope;
  for (const item of [source, previous]) {
    if (taskScope && item?.taskId && (item.taskId !== taskScope.taskId || item.sealId !== taskScope.sealId))
      throw new Error('submit_idea cannot move a candidate or line to another task scope.');
  }

  const field = (camel: string, snake: string): unknown => body[camel] ?? body[snake];
  const title = asString(body.title, source?.title || previous?.title || '');
  const problem = asString(body.problem, source?.problem || previous?.problem || '');
  const hypothesis = asString(body.hypothesis, source?.hypothesis || previous?.hypothesis || '');
  const mechanism = asString(body.mechanism, source?.mechanism || previous?.mechanism || '');
  const decisionReason = asString(
    field('decisionReason', 'decision_reason'),
    source?.decisionReason || previous?.decisionReason || ''
  );
  const evidenceBasis =
    asStringArray(field('evidenceBasis', 'evidence_basis')).length > 0
      ? asStringArray(field('evidenceBasis', 'evidence_basis'))
      : source?.evidenceBasis || previous?.evidenceBasis || [];
  const evidencePaths =
    asStringArray(field('evidencePaths', 'evidence_paths')).length > 0
      ? asStringArray(field('evidencePaths', 'evidence_paths'))
      : source?.evidencePaths || previous?.evidencePaths || [];
  const falsificationPlan = asString(
    field('falsificationPlan', 'falsification_plan'),
    source?.falsificationPlan || previous?.falsificationPlan || ''
  );
  const metricContractId = asString(
    field('metricContractId', 'metric_contract_id'),
    source?.metricContractId || previous?.metricContractId || ''
  );
  const whyCurrentLineIsLimited = asString(
    field('whyCurrentLineIsLimited', 'why_current_line_is_limited'),
    source?.whyCurrentLineIsLimited || previous?.whyCurrentLineIsLimited || ''
  );
  const keepUnchanged = asStringArray(field('keepUnchanged', 'keep_unchanged')).length
    ? asStringArray(field('keepUnchanged', 'keep_unchanged'))
    : source?.keepUnchanged || previous?.keepUnchanged || [];
  const implementationSurface = asString(
    field('implementationSurface', 'implementation_surface'),
    source?.implementationSurface || previous?.implementationSurface || ''
  );
  const mainRisks = asStringArray(field('mainRisks', 'main_risks')).length
    ? asStringArray(field('mainRisks', 'main_risks'))
    : source?.mainRisks || previous?.mainRisks || [];
  const rawEstimatedCost = field('estimatedCostMinutes', 'estimated_cost_minutes');
  const estimatedCostMinutes =
    typeof rawEstimatedCost === 'number' && Number.isFinite(rawEstimatedCost)
      ? rawEstimatedCost
      : source?.estimatedCostMinutes || previous?.estimatedCostMinutes;
  const strongestAlternative = normalizeOptimizationStrongestAlternative(
    field('strongestAlternative', 'strongest_alternative'),
    source?.strongestAlternative || previous?.strongestAlternative
  );
  if (taskScope && !metricContractId)
    throw new Error('IOAI-scoped submit_idea requires a frozen metricContractId before candidate search.');
  const missing = [
    ['title', title],
    ['problem', problem],
    ['hypothesis', hypothesis],
    ['mechanism', mechanism],
    ['decisionReason', decisionReason],
    ['falsificationPlan', falsificationPlan],
  ].filter(([, value]) => !value);
  if (missing.length)
    throw new Error(`submit_idea requires evidence-shaped fields: ${missing.map(([name]) => name).join(', ')}.`);
  if (!evidenceBasis.length && !evidencePaths.length)
    throw new Error('submit_idea requires evidenceBasis or evidencePaths; parameter guesses are not durable ideas.');

  const timestamp = now();
  const lineId =
    submissionMode === 'line' ? asString(body.lineId || body.line_id, previous?.lineId || ideaId) : undefined;
  const lineageIntent = asString(body.lineageIntent || body.lineage_intent, previous?.lineageIntent || '');
  if (lineageIntent && !['continue_line', 'branch_alternative'].includes(lineageIntent))
    throw new Error('lineageIntent must be "continue_line" or "branch_alternative".');
  const foundationValue = body.foundationRef ?? body.foundation_ref ?? previous?.foundationRef;
  const foundationRef = typeof foundationValue === 'string' || isRecord(foundationValue) ? foundationValue : undefined;
  const metadata: ScienceOptimizationArtifactMetadata = {
    schema: OPTIMIZATION_SCHEMA,
    kind: submissionMode === 'candidate' ? 'idea_candidate' : 'optimization_line',
    ideaId,
    lineId,
    taskId: taskScope?.taskId,
    sealId: taskScope?.sealId,
    sourceCandidateId: sourceCandidateId || previous?.sourceCandidateId,
    parentLineId: asString(
      body.parentLineId || body.parent_line_id,
      previous?.parentLineId || (undefined as unknown as string)
    ),
    branch: asString(body.branch, previous?.branch || (undefined as unknown as string)),
    foundationRef,
    lineageIntent: lineageIntent as ScienceOptimizationArtifactMetadata['lineageIntent'],
    status: asString(body.status, previous?.status || (submissionMode === 'candidate' ? 'proposed' : 'active')),
    title,
    problem,
    hypothesis,
    mechanism,
    methodBrief: asString(
      field('methodBrief', 'method_brief'),
      source?.methodBrief || previous?.methodBrief || (undefined as unknown as string)
    ),
    mechanismFamily: asString(
      field('mechanismFamily', 'mechanism_family'),
      source?.mechanismFamily || previous?.mechanismFamily || (undefined as unknown as string)
    ),
    changeLayer: asString(
      field('changeLayer', 'change_layer'),
      source?.changeLayer || previous?.changeLayer || (undefined as unknown as string)
    ),
    sourceLens: asString(
      field('sourceLens', 'source_lens'),
      source?.sourceLens || previous?.sourceLens || (undefined as unknown as string)
    ),
    whyNow: asString(
      field('whyNow', 'why_now'),
      source?.whyNow || previous?.whyNow || (undefined as unknown as string)
    ),
    whyCurrentLineIsLimited,
    keepUnchanged,
    implementationSurface,
    mainRisks,
    estimatedCostMinutes,
    strongestAlternative,
    evidenceBasis,
    evidencePaths,
    falsificationPlan,
    abandonmentCondition: asString(
      field('abandonmentCondition', 'abandonment_condition'),
      source?.abandonmentCondition || previous?.abandonmentCondition || (undefined as unknown as string)
    ),
    decisionReason,
    selectionScores:
      normalizeSelectionScores(field('selectionScores', 'selection_scores')) ||
      source?.selectionScores ||
      previous?.selectionScores,
    expectedGain: asString(
      field('expectedGain', 'expected_gain'),
      source?.expectedGain || previous?.expectedGain || (undefined as unknown as string)
    ),
    metricContractId,
    latestResultArtifactId: previous?.latestResultArtifactId,
    latestRunId: previous?.latestRunId,
    createdAt: previous?.createdAt || timestamp,
    updatedAt: timestamp,
  };
  if (taskScope) {
    const quality = assessOptimizationCandidateQuality(metadata, run.projectRoot);
    if (!quality.eligible) throw new Error(`IOAI candidate quality gate failed: ${quality.missingFields.join(', ')}.`);
  }
  const artifactId = optimizationArtifactId(metadata.kind, submissionMode === 'candidate' ? ideaId : lineId || ideaId);
  const artifact = writeOptimizationArtifactVersion(run, {
    id: artifactId,
    type: 'report',
    title,
    metadata,
    evidenceIds: asStringArray(body.evidenceIds || body.evidence_ids),
    changeSummary: mode === 'revise' ? 'Revised durable idea contract.' : 'Recorded durable idea contract.',
  });

  let promotedCandidate: ScienceArtifact | undefined;
  if (submissionMode === 'line' && source && sourceCandidate) {
    promotedCandidate = writeOptimizationArtifactVersion(run, {
      id: sourceCandidate.id,
      type: sourceCandidate.type,
      title: sourceCandidate.title,
      metadata: {
        ...source,
        status: 'promoted',
        lineId,
        updatedAt: timestamp,
      },
      evidenceIds: sourceCandidate.evidenceIds,
      changeSummary: `Promoted into durable optimization line ${lineId}.`,
    });
  }
  return { artifact, promotedCandidate, metadata };
};

const resolveOptimizationLine = (run: ScienceRunState, requestedLineId?: string): ScienceArtifact => {
  if (requestedLineId) {
    const line = findOptimizationArtifact(run, 'optimization_line', requestedLineId);
    if (!line) throw new Error(`Optimization line ${requestedLineId} does not exist in this Science run.`);
    return line;
  }
  const active = latestOptimizationArtifacts(run).filter((artifact) => {
    const metadata = readOptimizationMetadata(artifact);
    return (
      metadata?.kind === 'optimization_line' &&
      !OPTIMIZATION_TERMINAL_LINE_STATUSES.has(asString(metadata.status).toLowerCase())
    );
  });
  if (active.length !== 1)
    throw new Error('record_main_experiment requires lineId when there is not exactly one active optimization line.');
  return active[0];
};

const normalizeFusionEvidence = (
  run: ScienceRunState,
  value: unknown,
  currentLineId: string
): ScienceOptimizationFusionEvidence | undefined => {
  if (value == null) return undefined;
  if (!isRecord(value)) throw new Error('fusionEvidence must be an object.');
  const complementaryLineIds = [...new Set(asStringArray(value.complementaryLineIds || value.complementary_line_ids))];
  if (complementaryLineIds.length < 2)
    throw new Error('fusionEvidence requires at least two unique complementaryLineIds.');
  if (!complementaryLineIds.includes(currentLineId))
    throw new Error('fusionEvidence complementaryLineIds must include the current experiment lineId.');
  const missingLines = complementaryLineIds.filter(
    (lineId) => !findOptimizationArtifact(run, 'optimization_line', lineId)
  );
  if (missingLines.length)
    throw new Error(`fusionEvidence references unknown optimization line(s): ${missingLines.join(', ')}.`);
  const basis = asString(value.basis).toLowerCase();
  if (!['prediction_correlation', 'error_correlation', 'error_cluster'].includes(basis))
    throw new Error('fusionEvidence basis must be prediction_correlation, error_correlation, or error_cluster.');
  const summary = asString(value.summary);
  if (!summary) throw new Error('fusionEvidence requires a non-empty summary.');
  return {
    complementaryLineIds,
    basis: basis as ScienceOptimizationFusionEvidence['basis'],
    summary,
    evidenceIds: asStringArray(value.evidenceIds || value.evidence_ids),
    evidencePaths: asStringArray(value.evidencePaths || value.evidence_paths),
  };
};

export const recordOptimizationMainExperiment = (
  run: ScienceRunState,
  body: JsonRecord
): {
  resultArtifact: ScienceArtifact;
  lineArtifact: ScienceArtifact;
  metadata: ScienceOptimizationArtifactMetadata;
} => {
  const runIdentifier = asString(body.runId || body.run_id);
  if (!runIdentifier) throw new Error('record_main_experiment requires runId.');
  if (findOptimizationArtifact(run, 'main_experiment', runIdentifier))
    throw new Error(`Main experiment ${runIdentifier} is already recorded and immutable.`);
  const requestedLineId = asString(body.lineId || body.line_id || body.ideaId || body.idea_id);
  const line = resolveOptimizationLine(run, requestedLineId || undefined);
  const lineMetadata = readOptimizationMetadata(line);
  if (!lineMetadata?.lineId) throw new Error('The selected optimization line has no durable lineId.');
  const requestedTaskScope = optimizationTaskScope(
    body.taskId || body.task_id,
    body.sealId || body.seal_id,
    'record_main_experiment task scope'
  );
  const lineTaskScope = optimizationTaskScope(lineMetadata.taskId, lineMetadata.sealId, 'optimization line task scope');
  if (
    requestedTaskScope &&
    lineTaskScope &&
    (requestedTaskScope.taskId !== lineTaskScope.taskId || requestedTaskScope.sealId !== lineTaskScope.sealId)
  )
    throw new Error('record_main_experiment task scope does not match its optimization line.');
  const taskScope = requestedTaskScope || lineTaskScope;

  const status = asString(body.status, 'completed').toLowerCase();
  const failureKind = asString(body.failureKind || body.failure_kind) || undefined;
  const explicitValid = body.valid;
  const valid = typeof explicitValid === 'boolean' ? explicitValid : status === 'completed' && !failureKind;
  const metrics = normalizeOptimizationMetrics(body);
  if (valid && !metrics.length)
    throw new Error('A valid main experiment requires at least one finite metric row or metric summary.');
  const timestamp = now();
  const evaluationSummary = isRecord(body.evaluationSummary || body.evaluation_summary)
    ? ((body.evaluationSummary || body.evaluation_summary) as JsonRecord)
    : undefined;
  const comparable = valid && body.comparable !== false && evaluationSummary?.comparability !== 'none';
  const evidencePaths = asStringArray(body.evidencePaths || body.evidence_paths);
  const evidenceIds = asStringArray(body.evidenceIds || body.evidence_ids);
  const fusionEvidence = normalizeFusionEvidence(run, body.fusionEvidence || body.fusion_evidence, lineMetadata.lineId);
  const repairOfRunId = asString(body.repairOfRunId || body.repair_of_run_id) || undefined;
  if (repairOfRunId) {
    const original = findOptimizationArtifact(run, 'main_experiment', repairOfRunId);
    const originalMetadata = readOptimizationMetadata(original);
    if (!originalMetadata || originalMetadata.lineId !== lineMetadata.lineId)
      throw new Error('repairOfRunId must reference a main experiment on the same optimization line.');
    const originalClass = originalMetadata.failureClass || classifyOptimizationResult(originalMetadata);
    if (!['execution_error', 'invalid_result'].includes(originalClass))
      throw new Error('repairOfRunId must reference an execution_error or invalid_result.');
    const priorRepair = latestOptimizationArtifacts(run).find((artifact) => {
      const candidate = readOptimizationMetadata(artifact);
      return (
        candidate?.kind === 'main_experiment' && candidate.lineId === lineMetadata.lineId && candidate.repairOfRunId
      );
    });
    if (priorRepair) throw new Error(`Optimization line ${lineMetadata.lineId} has already used its one repair.`);
  }
  const metadata: ScienceOptimizationArtifactMetadata = {
    schema: OPTIMIZATION_SCHEMA,
    kind: 'main_experiment',
    ideaId: lineMetadata.ideaId,
    lineId: lineMetadata.lineId,
    attemptId: asString(body.attemptId || body.attempt_id, undefined as unknown as string),
    runId: runIdentifier,
    taskId: taskScope?.taskId,
    sealId: taskScope?.sealId,
    status,
    valid,
    failureKind,
    repairOfRunId,
    title: asString(body.title, runIdentifier),
    hypothesis: asString(body.hypothesis, lineMetadata.hypothesis || (undefined as unknown as string)),
    mechanism: lineMetadata.mechanism,
    mechanismFamily: lineMetadata.mechanismFamily,
    evidenceBasis: asStringArray(body.evidenceBasis || body.evidence_basis),
    evidencePaths,
    metrics,
    metricContractId: asString(
      body.metricContractId || body.metric_contract_id,
      lineMetadata.metricContractId || (undefined as unknown as string)
    ),
    comparable,
    verdict: asString(body.verdict, undefined as unknown as string),
    conclusion: asString(body.conclusion, undefined as unknown as string),
    evaluationSummary,
    fusionEvidence,
    createdAt: timestamp,
    updatedAt: timestamp,
  };
  metadata.failureClass = classifyOptimizationResult(metadata);
  const deterministicSimpleTask =
    body.deterministicSimpleTask === true ||
    body.deterministic_simple_task === true ||
    evaluationSummary?.deterministicSimpleTask === true ||
    evaluationSummary?.taskProfile === 'deterministic-simple-task.v1';
  metadata.stabilityAssessment = assessOptimizationStability(metadata, deterministicSimpleTask);
  metadata.lesson = optimizationLesson(body, metadata, lineMetadata);
  const resultArtifact = writeOptimizationArtifactVersion(run, {
    id: optimizationArtifactId('main_experiment', runIdentifier),
    type: 'run_bundle',
    title: metadata.title || runIdentifier,
    status: valid ? 'available' : 'failed',
    metadata,
    evidenceIds,
    changeSummary: `Recorded real measured result for ${lineMetadata.lineId}.`,
  });
  const repairFailed = Boolean(repairOfRunId) && ['execution_error', 'invalid_result'].includes(metadata.failureClass);
  const lineStatus = repairFailed
    ? 'archived'
    : asString(
        body.lineStatus || body.line_status,
        body.stopLine === true || body.stop_line === true ? 'stopped' : lineMetadata.status || 'active'
      );
  const lineArtifact = writeOptimizationArtifactVersion(run, {
    id: line.id,
    type: line.type,
    title: line.title,
    metadata: {
      ...lineMetadata,
      status: lineStatus,
      latestResultArtifactId: resultArtifact.id,
      latestRunId: runIdentifier,
      updatedAt: timestamp,
    },
    evidenceIds: [...new Set([...(line.evidenceIds || []), ...evidenceIds])],
    changeSummary: `Linked main experiment ${runIdentifier}.`,
  });
  return { resultArtifact, lineArtifact, metadata };
};

export const buildOptimizationFrontier = (run: ScienceRunState, taskScope?: ScienceOptimizationTaskScope) => {
  const artifacts = latestOptimizationArtifacts(run).filter((artifact) =>
    optimizationItemMatchesScope(readOptimizationMetadata(artifact), taskScope)
  );
  const candidateArtifacts = artifacts.filter(
    (artifact) => readOptimizationMetadata(artifact)?.kind === 'idea_candidate'
  );
  const lineArtifacts = artifacts.filter(
    (artifact) => readOptimizationMetadata(artifact)?.kind === 'optimization_line'
  );
  const attemptArtifacts = artifacts.filter(
    (artifact) => readOptimizationMetadata(artifact)?.kind === 'implementation_attempt'
  );
  const resultArtifacts = artifacts.filter(
    (artifact) => readOptimizationMetadata(artifact)?.kind === 'main_experiment'
  );
  const candidateBriefs = candidateArtifacts.map((artifact) => {
    const metadata = readOptimizationMetadata(artifact) as ScienceOptimizationArtifactMetadata;
    return {
      artifactId: artifact.id,
      version: artifact.version,
      ...metadata,
      quality: assessOptimizationCandidateQuality(metadata, run.projectRoot),
    };
  });
  const implementationAttempts = attemptArtifacts.map((artifact) => ({
    artifactId: artifact.id,
    version: artifact.version,
    ...readOptimizationMetadata(artifact),
  }));
  const mainExperiments = resultArtifacts.map((artifact) => ({
    artifactId: artifact.id,
    version: artifact.version,
    ...readOptimizationMetadata(artifact),
  }));
  const resultsByLine = new Map<string, ScienceOptimizationArtifactMetadata[]>();
  for (const artifact of resultArtifacts) {
    const metadata = readOptimizationMetadata(artifact);
    if (!metadata?.lineId) continue;
    const values = resultsByLine.get(metadata.lineId) || [];
    values.push(metadata);
    resultsByLine.set(metadata.lineId, values);
  }
  for (const values of resultsByLine.values())
    values.sort(
      (left, right) => left.updatedAt - right.updatedAt || asString(left.runId).localeCompare(asString(right.runId))
    );

  const failedAttemptsByLine = new Map<string, number>();
  for (const artifact of attemptArtifacts) {
    const metadata = readOptimizationMetadata(artifact);
    if (!metadata?.lineId || !OPTIMIZATION_FAILED_ATTEMPT_STATUSES.has(asString(metadata.status).toLowerCase()))
      continue;
    failedAttemptsByLine.set(metadata.lineId, (failedAttemptsByLine.get(metadata.lineId) || 0) + 1);
  }
  const lines = lineArtifacts.map((artifact) => {
    const metadata = readOptimizationMetadata(artifact) as ScienceOptimizationArtifactMetadata;
    const results = resultsByLine.get(metadata.lineId || '') || [];
    let consecutiveObjectiveFailures = 0;
    for (const result of [...results].reverse()) {
      const failureClass = result.failureClass || classifyOptimizationResult(result);
      if (failureClass === 'valid_no_gain') consecutiveObjectiveFailures += 1;
      else if (failureClass === 'execution_error' || failureClass === 'invalid_result') continue;
      else break;
    }
    const failedAttemptCount = failedAttemptsByLine.get(metadata.lineId || '') || 0;
    const repairs = results.filter((result) => result.repairOfRunId);
    const latestResult = results.at(-1);
    return {
      artifactId: artifact.id,
      version: artifact.version,
      ...metadata,
      resultCount: results.length,
      failedAttemptCount,
      consecutiveObjectiveFailures,
      repairUsed: repairs.length > 0,
      repairExhausted: repairs.some((result) =>
        ['execution_error', 'invalid_result'].includes(result.failureClass || classifyOptimizationResult(result))
      ),
      stagnant: consecutiveObjectiveFailures >= 2,
      latestResult,
    };
  });

  const comparableResults = resultArtifacts
    .map((artifact) => ({
      artifact,
      metadata: readOptimizationMetadata(artifact) as ScienceOptimizationArtifactMetadata,
    }))
    .filter(({ metadata }) => metadata.comparable && metadata.valid !== false && primaryOptimizationMetric(metadata));
  const comparisonGroups = new Map<string, typeof comparableResults>();
  for (const value of comparableResults) {
    const primary = primaryOptimizationMetric(value.metadata) as ScienceOptimizationMetric;
    const key = `${value.metadata.metricContractId || 'default'}:${primary.metricId}:${primary.direction}`;
    const group = comparisonGroups.get(key) || [];
    group.push(value);
    comparisonGroups.set(key, group);
  }
  const dominantGroup = [...comparisonGroups.entries()].sort(
    ([leftKey, left], [rightKey, right]) => right.length - left.length || leftKey.localeCompare(rightKey)
  )[0];
  const rankedDominantResults = dominantGroup
    ? [...dominantGroup[1]].sort((left, right) => {
        const leftMetric = primaryOptimizationMetric(left.metadata) as ScienceOptimizationMetric;
        const rightMetric = primaryOptimizationMetric(right.metadata) as ScienceOptimizationMetric;
        const leftImprovement = metricImprovement(leftMetric);
        const rightImprovement = metricImprovement(rightMetric);
        if (leftImprovement != null && rightImprovement != null && leftImprovement !== rightImprovement)
          return rightImprovement - leftImprovement;
        const utilityDelta = metricUtility(rightMetric) - metricUtility(leftMetric);
        if (utilityDelta) return utilityDelta;
        return asString(left.metadata.lineId).localeCompare(asString(right.metadata.lineId));
      })
    : [];
  const scoreLeader = rankedDominantResults[0];
  const bestResult = rankedDominantResults.find(({ metadata }) => {
    const assessment = metadata.stabilityAssessment || assessOptimizationStability(metadata, false);
    return assessment.promotionEligible;
  });
  const bestLine = bestResult
    ? lines.find((line) => line.lineId === bestResult.metadata.lineId)
    : lines.find((line) => !OPTIMIZATION_TERMINAL_LINE_STATUSES.has(asString(line.status).toLowerCase()));

  const positiveComparableResults = comparableResults.filter(({ metadata }) => {
    const primary = primaryOptimizationMetric(metadata);
    const improvement = primary ? metricImprovement(primary) : undefined;
    const stability = metadata.stabilityAssessment || assessOptimizationStability(metadata, false);
    return Boolean(
      metadata.metricContractId &&
      metadata.lineId &&
      improvement != null &&
      improvement > 0 &&
      stability.promotionEligible
    );
  });
  const validFusionOpportunities = resultArtifacts
    .map((artifact) => readOptimizationMetadata(artifact) as ScienceOptimizationArtifactMetadata)
    .filter((metadata) => Boolean(metadata.fusionEvidence))
    .map((metadata) => {
      const primary = primaryOptimizationMetric(metadata);
      const evidence = metadata.fusionEvidence as ScienceOptimizationFusionEvidence;
      if (!metadata.metricContractId || !primary || !metadata.comparable || metadata.status !== 'completed')
        return undefined;
      const matchedResults = evidence.complementaryLineIds.map(
        (lineId) =>
          positiveComparableResults
            .filter(({ metadata: candidate }) => {
              const candidatePrimary = primaryOptimizationMetric(candidate);
              return (
                candidate.lineId === lineId &&
                candidate.metricContractId === metadata.metricContractId &&
                candidatePrimary?.metricId === primary.metricId &&
                candidatePrimary.direction === primary.direction
              );
            })
            .sort(
              (left, right) =>
                right.metadata.updatedAt - left.metadata.updatedAt ||
                asString(left.metadata.runId).localeCompare(asString(right.metadata.runId))
            )[0]?.metadata
      );
      if (matchedResults.some((result) => !result)) return undefined;
      return {
        lineIds: evidence.complementaryLineIds,
        basis: evidence.basis,
        summary: evidence.summary,
        evidenceIds: evidence.evidenceIds,
        evidencePaths: evidence.evidencePaths,
        evidenceRunId: metadata.runId,
        metricContractId: metadata.metricContractId,
        primaryMetricId: primary.metricId,
        direction: primary.direction,
        matchedRunIds: matchedResults.map((result) => result?.runId),
        recordedAt: metadata.updatedAt,
      };
    })
    .filter((item): item is NonNullable<typeof item> => Boolean(item))
    .sort(
      (left, right) =>
        right.recordedAt - left.recordedAt || asString(left.evidenceRunId).localeCompare(asString(right.evidenceRunId))
    );
  const fusionOpportunity = validFusionOpportunities[0];
  const activeCandidateBriefs = candidateBriefs.filter(
    (candidate) => !OPTIMIZATION_TERMINAL_CANDIDATE_STATUSES.has(asString(candidate.status).toLowerCase())
  );
  const candidateQuality = {
    schema: 'deepscientist.ioai.candidate-quality-summary.v1',
    eligibleCandidateIds: activeCandidateBriefs
      .filter((candidate) => candidate.quality.eligible)
      .map((candidate) => asString(candidate.ideaId)),
    rejectedCandidates: activeCandidateBriefs
      .filter((candidate) => !candidate.quality.eligible)
      .map((candidate) => ({
        candidateId: asString(candidate.ideaId),
        missingFields: candidate.quality.missingFields,
        unverifiedEvidencePaths: candidate.quality.unverifiedEvidencePaths,
      })),
    mechanismFamilies: [
      ...new Set(activeCandidateBriefs.map((candidate) => asString(candidate.mechanismFamily)).filter(Boolean)),
    ],
    changeLayers: [
      ...new Set(activeCandidateBriefs.map((candidate) => asString(candidate.changeLayer)).filter(Boolean)),
    ],
  };
  const activeLines = lines.filter(
    (line) => !OPTIMIZATION_TERMINAL_LINE_STATUSES.has(asString(line.status).toLowerCase())
  );
  const activeAttempts = implementationAttempts.filter((attempt) =>
    OPTIMIZATION_ACTIVE_ATTEMPT_STATUSES.has(asString(attempt.status).toLowerCase())
  );
  const nonStagnantActiveLines = activeLines.filter((line) => !line.stagnant);
  const repairableFailure = activeLines
    .filter((line) => {
      const latest = line.latestResult;
      if (!latest || line.repairUsed) return false;
      const failureClass = latest.failureClass || classifyOptimizationResult(latest);
      return ['execution_error', 'invalid_result'].includes(failureClass);
    })
    .map((line) => ({
      ...(line.latestResult as ScienceOptimizationArtifactMetadata),
      mechanismFamily: line.mechanismFamily,
    }))
    .sort(
      (left, right) => right.updatedAt - left.updatedAt || asString(left.runId).localeCompare(asString(right.runId))
    )[0];

  let route: ScienceOptimizationRoute;
  let reason: string;
  if (!candidateBriefs.length && !lines.length) {
    route = 'explore';
    reason =
      'No candidate brief or durable line exists, so the next justified move is evidence-backed idea generation.';
  } else if (!activeLines.length && !activeCandidateBriefs.length) {
    route = 'stop';
    reason = 'Every recorded candidate and durable line is terminal; the current frontier is exhausted.';
  } else if (repairableFailure) {
    route = 'debug';
    reason = `Run ${repairableFailure.runId} has a concrete ${repairableFailure.failureClass} and this line has not used its one bounded repair.`;
  } else if (fusionOpportunity) {
    route = 'fusion';
    reason = `Audited ${fusionOpportunity.basis} evidence shows complementary errors or predictions between positive comparable lines.`;
  } else if (activeAttempts.length || nonStagnantActiveLines.length) {
    route = 'exploit';
    reason = bestResult
      ? 'A comparable measured incumbent exists and at least one durable line still has justified execution capacity.'
      : 'A durable line or implementation attempt is active and still needs its first decisive measured result.';
  } else if (activeCandidateBriefs.length) {
    route = 'explore';
    reason = 'Existing lines are stagnant, while unpromoted evidence-backed candidate briefs remain available.';
  } else if (activeLines.length) {
    route = 'explore';
    reason = 'Every active line is stagnant, so the next move must pivot to an orthogonal evidence-backed mechanism.';
  } else {
    route = 'stop';
    reason = 'No active optimization line or unpromoted candidate brief remains.';
  }

  const dispatchDecision = decideOptimizationDispatch({
    projectRoot: run.projectRoot,
    taskScope,
    route,
    candidateBriefs,
    lines,
    implementationAttempts,
    bestLineId: bestLine?.lineId,
    fusionOpportunity,
    repairableFailure,
  });

  const recommendedNextActions: Record<ScienceOptimizationRoute, string[]> = {
    explore: [
      'Generate or rank evidence-backed candidate briefs at the mechanism-family level.',
      'Promote only a differentiated brief with a cheap falsification path.',
    ],
    exploit: [
      'Run the cheapest decisive implementation attempt on the strongest durable line.',
      'Record the next real comparable result with record_main_experiment.',
    ],
    fusion: [
      `Test a bounded fusion of audited complementary lines: ${fusionOpportunity?.lineIds.join(', ') || ''}.`,
      'Keep the component-line metrics and the fusion result directly comparable.',
    ],
    debug: [
      `Repair run ${repairableFailure?.runId || ''} once without changing its mechanism hypothesis.`,
      'Archive the line if the bounded repair also fails or remains invalid.',
    ],
    stop: ['Record the exhausted frontier and avoid additional low-information parameter churn.'],
  };

  const recentLessons = [...mainExperiments]
    .filter((experiment) => experiment.lesson)
    .sort(
      (left, right) => right.updatedAt - left.updatedAt || asString(right.runId).localeCompare(asString(left.runId))
    )
    .slice(0, 5)
    .map((experiment) => ({
      runId: experiment.runId,
      lineId: experiment.lineId,
      failureClass: experiment.failureClass,
      updatedAt: experiment.updatedAt,
      ...experiment.lesson,
    }));

  return {
    schema: OPTIMIZATION_SCHEMA,
    taskScope: taskScope || null,
    route,
    reason,
    bestLine,
    bestRun: bestResult?.metadata,
    scoreLeader: scoreLeader?.metadata,
    comparisonGroup: dominantGroup?.[0],
    candidateBriefs,
    lines,
    implementationAttempts,
    mainExperiments,
    stagnantLines: lines.filter((line) => line.stagnant),
    fusionOpportunity,
    candidateQuality,
    dispatchDecision,
    recentLessons,
    counts: {
      candidateBriefs: candidateBriefs.length,
      activeCandidateBriefs: activeCandidateBriefs.length,
      durableLines: lines.length,
      activeLines: activeLines.length,
      implementationAttempts: implementationAttempts.length,
      activeImplementationAttempts: activeAttempts.length,
      mainExperiments: mainExperiments.length,
    },
    recommendedNextActions: recommendedNextActions[route],
  };
};

const synchronizeTargetDiscoveryPortfolio = (
  run: ScienceRunState,
  target: TargetRef,
  current: ScienceArtifact | undefined
): ScienceArtifact | undefined => {
  if (!run.projectRoot) return current;
  const snapshot = readTargetDiscoveryProjectPortfolio(run.projectRoot);
  if (snapshot.status === 'missing') return current;
  if (snapshot.status === 'invalid') {
    throw new Error(
      `${TARGET_DISCOVERY_PORTFOLIO_PATH} is invalid. Repair the canonical project portfolio before using target_portfolio.`
    );
  }

  const currentPortfolio = readTargetDiscoveryPortfolio(current?.metadata);
  if (
    currentPortfolio &&
    current?.primaryPath === snapshot.path &&
    JSON.stringify(currentPortfolio) === JSON.stringify(snapshot.portfolio)
  ) {
    return current;
  }

  const result = createOrReplaceResource(
    run,
    current ? 'patch' : 'create',
    target,
    current
      ? {
          title: snapshot.portfolio.title,
          metadata: { targetDiscovery: snapshot.portfolio },
          primaryPath: snapshot.path,
          changeSummary: 'Synchronized from the canonical target portfolio.',
        }
      : {
          type: 'table',
          title: snapshot.portfolio.title,
          status: 'available',
          viewer: { kind: 'target_discovery' },
          metadata: { targetDiscovery: snapshot.portfolio },
          primaryPath: snapshot.path,
          changeSummary: 'Loaded from the canonical target portfolio.',
        },
    current?.revision,
    false
  );
  const artifact = result.object as ScienceArtifact;
  artifact.revision = `target_file_${crypto
    .createHash('sha256')
    .update(JSON.stringify(snapshot.portfolio))
    .digest('hex')
    .slice(0, 24)}`;
  return artifact;
};

const synchronizeMathematicsPortfolio = (
  run: ScienceRunState,
  target: TargetRef,
  current: ScienceArtifact | undefined,
  currentPortfolio: MathematicsPortfolio | undefined,
  snapshot?: MathematicsProjectPortfolioSnapshot
): ScienceArtifact | undefined => {
  const runIdentity = readMathRunHistoryIdentity();
  if (runIdentity && currentPortfolio) {
    assertMathRunPortfolioOrigin(currentPortfolio, runIdentity);
    assertMathRunPortfolioPremises(currentPortfolio, run.mathematicsVerifications);
  }
  if (!run.projectRoot) return current;
  const portfolioSnapshot = snapshot || readMathematicsProjectPortfolio(run.projectRoot);
  if (portfolioSnapshot.status === 'missing') return current;
  if (portfolioSnapshot.status === 'invalid') {
    throw new Error(
      `${MATHEMATICS_PORTFOLIO_PATH} is invalid. Repair the canonical project portfolio before using math_portfolio.`
    );
  }
  if (runIdentity) {
    assertMathRunPortfolioOrigin(portfolioSnapshot.portfolio, runIdentity);
    assertMathRunPortfolioPremises(portfolioSnapshot.portfolio, run.mathematicsVerifications);
  }
  if (
    currentPortfolio &&
    current?.primaryPath === portfolioSnapshot.path &&
    isDeepStrictEqual(currentPortfolio, portfolioSnapshot.portfolio)
  ) {
    return current;
  }
  const result = createOrReplaceResource(
    run,
    current ? 'patch' : 'create',
    target,
    current
      ? {
          metadata: { mathematics: portfolioSnapshot.portfolio },
          primaryPath: portfolioSnapshot.path,
          changeSummary: 'Synchronized from the canonical mathematics portfolio.',
        }
      : {
          type: 'run_bundle',
          title: portfolioSnapshot.portfolio.title,
          status: 'available',
          viewer: { kind: 'mathematics' },
          metadata: { mathematics: portfolioSnapshot.portfolio },
          primaryPath: portfolioSnapshot.path,
          changeSummary: 'Loaded from the canonical mathematics portfolio.',
        },
    current?.revision,
    false
  );
  const artifact = result.object as ScienceArtifact;
  artifact.revision = `math_file_${portfolioSnapshot.rawHash.slice(0, 24)}`;
  return artifact;
};

const targetRankingSignature = (portfolio: TargetDiscoveryPortfolio): string =>
  JSON.stringify({
    candidates: portfolio.candidates.map((candidate) => ({
      id: candidate.id,
      symbol: candidate.symbol,
      rank: candidate.rank,
      priorityIndex: candidate.priorityIndex,
      maxPriorityIndex: candidate.maxPriorityIndex,
      coverage: candidate.coverage,
      rankStability: candidate.rankStability,
    })),
    branches: portfolio.branches.map((branch) => ({ id: branch.id, candidateIds: branch.candidateIds })),
  });

const synchronizeProjectTargetArtifact = (run: ScienceRunState): void => {
  const target = { kind: 'artifact' as const, id: TARGET_DISCOVERY_PORTFOLIO_ARTIFACT_ID, version: 1 };
  synchronizeTargetDiscoveryPortfolio(run, target, run.artifacts.get(artifactKey(target.id, target.version)));
};

const synchronizeTargetDiscoveryDelivery = async (run: ScienceRunState): Promise<void> => {
  if (!run.projectRoot) return;
  const snapshot = readTargetDiscoveryProjectPortfolio(run.projectRoot);
  const reconciled = await reconcileTargetDiscoveryProject({ projectRoot: run.projectRoot });
  if (!reconciled.valid) {
    const details = reconciled.issues
      .filter((item) => item.severity === 'error')
      .slice(0, 5)
      .map((item) => (item.row ? `Row ${item.row}: ${item.message}` : item.message))
      .join(' ');
    throw new Error(`The canonical target candidate registry is invalid.${details ? ` ${details}` : ''}`);
  }
  if (reconciled.canonicalRegistryExists) {
    synchronizeProjectTargetArtifact(run);
    return;
  }

  if (snapshot.status !== 'ready') return;
  synchronizeProjectTargetArtifact(run);

  const freezePath = path.join(run.projectRoot, 'ranking_freeze.json');
  if (!fs.existsSync(freezePath)) return;
  let freeze: JsonRecord;
  try {
    const parsed = JSON.parse(fs.readFileSync(freezePath, 'utf8'));
    if (!isRecord(parsed)) return;
    freeze = parsed;
  } catch {
    throw new Error('ranking_freeze.json is invalid; repair it before publishing the target-discovery report.');
  }
  if (freeze.frozen !== true || freeze.status !== 'frozen' || !isRecord(freeze.outputs)) return;

  const topEntry = freeze.outputs['top100_genes.csv'];
  if (!isRecord(topEntry)) {
    throw new Error(
      'The target ranking is frozen but ranking_freeze.json does not register top100_genes.csv. Repair the freeze manifest before publishing.'
    );
  }
  const relativeSourcePath = asString(topEntry.path, 'top100_genes.csv');
  const expectedHash = asString(topEntry.sha256, '').toLowerCase();
  const sourcePath = path.resolve(run.projectRoot, relativeSourcePath);
  const relative = path.relative(run.projectRoot, sourcePath);
  if (relative.startsWith(`..${path.sep}`) || relative === '..' || path.isAbsolute(relative)) {
    throw new Error('The frozen target candidate table must stay inside projectRoot.');
  }
  if (!fs.existsSync(sourcePath) || !fs.statSync(sourcePath).isFile()) {
    throw new Error(`The frozen target candidate table is missing: ${relativeSourcePath}.`);
  }
  const actualHash = crypto.createHash('sha256').update(fs.readFileSync(sourcePath)).digest('hex');
  if (!expectedHash || actualHash !== expectedHash) {
    throw new Error(
      `The frozen target candidate table hash does not match ranking_freeze.json: ${relativeSourcePath}. Re-freeze the ranking before publishing.`
    );
  }

  const loaded = await loadTargetDiscoveryImport({
    projectRoot: run.projectRoot,
    sourcePath,
    mode: 'replace',
    portfolio: snapshot.portfolio,
    knownEvidenceIds: [...run.evidence.keys()],
    requireSourceInProject: true,
  });
  if (!loaded.valid || !loaded.portfolio) {
    const details = loaded.issues
      .filter((item) => item.severity === 'error')
      .slice(0, 5)
      .map((item) => (item.row ? `Row ${item.row}: ${item.message}` : item.message))
      .join(' ');
    throw new Error(
      `The ranking is frozen but its Top 100 could not be synchronized with target_portfolio.${details ? ` ${details}` : ''}`
    );
  }
  if (targetRankingSignature(snapshot.portfolio) !== targetRankingSignature(loaded.portfolio)) {
    commitLoadedTargetDiscoveryImport(run.projectRoot, loaded);
  }
  synchronizeProjectTargetArtifact(run);
};

const assertTargetDiscoveryPublicationReady = (run: ScienceRunState): void => {
  for (const artifact of run.artifacts.values()) {
    const portfolio = readTargetDiscoveryPortfolio(artifact.metadata);
    if (!portfolio) continue;
    const integrity = inspectTargetDiscoveryPortfolio(portfolio);
    const errors = integrity.diagnostics.filter((item) => item.severity === 'error');
    if (errors.length) {
      throw new Error(`Target portfolio integrity check failed: ${errors.map((item) => item.message).join(' ')}`);
    }
    const finalDelivery =
      run.status === 'completed' || portfolio.stage === 'complete' || portfolio.status === 'complete';
    if (finalDelivery && integrity.quality.saturated) {
      throw new Error(
        'The final target ranking has insufficient score discrimination. Review clipping, caps, ties, and deterministic tie-breakers, then import the corrected complete candidate registry before publishing.'
      );
    }
    const policy = portfolio.context.researchPolicy;
    for (const candidate of portfolio.candidates.filter((item) => item.status === 'advance')) {
      if (policy?.patientDataRequired) {
        const missingEvidenceIds = (candidate.patientEvidence?.computedEvidenceIds || []).filter(
          (evidenceId) => !run.evidence.has(evidenceId)
        );
        if (missingEvidenceIds.length) {
          throw new Error(
            `Target ${candidate.id} references unregistered computed patient evidence: ${missingEvidenceIds.join(', ')}.`
          );
        }
      }
      if (
        policy?.independentAuditRequired &&
        ![...run.artifacts.values()].some((candidateArtifact) => candidateArtifact.id === candidate.auditArtifactId)
      ) {
        throw new Error(`Target ${candidate.id} references an unavailable independent audit artifact.`);
      }
    }
  }
};

const checkpointVerificationItemInput = z.union([
  z.string(),
  z
    .object({
      command: z.string().optional(),
      check: z.string().optional(),
      name: z.string().optional(),
      exitCode: z.number().optional(),
      exit_code: z.number().optional(),
      result: z.string().optional(),
      status: z.string().optional(),
      summary: z.string().optional(),
    })
    .passthrough(),
]);

const checkpointVerificationInput = z.union([
  checkpointVerificationItemInput,
  z.array(checkpointVerificationItemInput),
  z.object({ checks: z.array(checkpointVerificationItemInput) }).passthrough(),
]);

const researchStageReceiptInput = z.object({
  stageId: z.string(),
  objective: z.string(),
  successCriteria: z.array(z.string()).min(1),
  failureCriteria: z.array(z.string()).min(1),
  priorWorkRefs: z.array(z.string()).default([]),
  disposition: z.enum(['supported', 'refuted', 'exhausted', 'inconclusive', 'runtime_failed']),
  supportingEvidenceIds: z.array(z.string()).default([]),
  refutingEvidenceIds: z.array(z.string()).default([]),
  exhaustionEvidenceIds: z.array(z.string()).default([]),
  beliefDelta: z.string(),
  reflection: z.string(),
  nextObjective: z.string().optional(),
});

const directionDecisionInput = z.object({
  schema: z.literal('deepscientist.direction.v1'),
  choice: z.enum(['advance', 'hold', 'reject', 'repair', 'stop']),
  reason: z.string(),
  basisRefs: z
    .array(
      z.object({
        kind: z.enum(['evidence', 'artifact', 'commit']),
        ref: z.string(),
        label: z.string().optional(),
      })
    )
    .min(1)
    .max(4),
  nextTest: z.string().optional(),
  stopIf: z.string().optional(),
});

const projectWorkspacePayloadInput = z
  .object({
    message: z.string().optional(),
    summary: z.string().optional(),
    stage: z.string().optional(),
    routeMode: z.enum(['explore', 'deepen', 'fuse', 'repair', 'stop']).optional(),
    route_mode: z.enum(['explore', 'deepen', 'fuse', 'repair', 'stop']).optional(),
    strategy: z.enum(['explore', 'deepen', 'fuse', 'repair', 'stop']).optional(),
    domain: z.string().optional(),
    workflow: z.string().optional(),
    includePaths: z
      .array(
        z.union([
          z.string(),
          z.object({ path: z.string(), role: z.string().optional(), recursive: z.boolean().optional() }).passthrough(),
        ])
      )
      .optional(),
    verification: checkpointVerificationInput.optional(),
    validations: checkpointVerificationInput.optional(),
    goalId: z.string().optional(),
    goal_id: z.string().optional(),
    researchStage: researchStageReceiptInput.optional(),
    research_stage: researchStageReceiptInput.optional(),
    directionDecision: directionDecisionInput.optional(),
    direction_decision: directionDecisionInput.optional(),
    metrics: z
      .array(
        z.object({
          name: z.string(),
          value: z.number(),
          unit: z.string().optional(),
          direction: z.enum(['maximize', 'minimize']).optional(),
        })
      )
      .optional(),
    metricContext: z
      .object({
        contractId: z.string(),
        evaluationId: z.string(),
        baselineCommit: z.string().optional(),
        evaluationCode: z
          .object({
            path: z.string(),
            runtime: z.enum(['python', 'node', 'r', 'notebook']).optional(),
            entrypoint: z.string().optional(),
            sha256: z
              .string()
              .regex(/^[a-f0-9]{64}$/iu)
              .optional(),
          })
          .optional(),
      })
      .optional(),
    branch: z.string().optional(),
    name: z.string().optional(),
    from: z.string().optional(),
    parentRef: z.string().optional(),
    routeNodeId: z.string().optional(),
    repairsNodeId: z.string().optional(),
    objective: z.string().optional(),
    baseRef: z.string().optional(),
    headRef: z.string().optional(),
    remoteUrl: z.string().optional(),
    destination: z.string().optional(),
    baseDir: z.string().optional(),
    ref: z.string().optional(),
    depth: z.number().int().positive().max(10_000).optional(),
    id: z.string().optional(),
    category: z.enum(['methods', 'knowledge', 'lessons']).optional(),
    title: z.string().optional(),
    scope: z.array(z.string()).optional(),
    evidence: z.array(z.string()).optional(),
    content: z.string().optional(),
  })
  .passthrough();

const validateResearchRoadmapDiscipline = (roadmap: ResearchRouteMap): string[] => {
  const issues: string[] = [];
  if (!roadmap.completionContract?.criteria.length) {
    issues.push('completionContract.criteria must define the persistent objective requirements.');
  }
  const runningNodes = roadmap.nodes.filter((node) => node.lifecycle === 'running');
  if (runningNodes.length > 1) issues.push('Only one research stage may have lifecycle=running.');
  for (const node of runningNodes) {
    const execution = node.execution;
    if (
      !execution?.acceptanceCriteria.length ||
      !execution.failureCriteria?.length ||
      !execution.authoritativeChecks?.length ||
      !execution.expectedArtifacts?.length
    ) {
      issues.push(
        `Running stage ${node.id} requires objective, acceptanceCriteria, failureCriteria, authoritativeChecks, and expectedArtifacts.`
      );
    }
  }
  for (const node of roadmap.nodes) {
    if (node.outcome && ['proposed', 'selected', 'running'].includes(node.lifecycle)) {
      issues.push(
        `Stage ${node.id} has an outcome but lifecycle=${node.lifecycle}; close or block the stage atomically.`
      );
    }
    if (node.execution && ['completed', 'verified'].includes(node.lifecycle) && !node.outcome) {
      issues.push(`Closed stage ${node.id} requires an evidence-bearing outcome.`);
    }
    if (node.outcome?.nextAction === 'complete') {
      const incomplete = roadmap.completionContract?.criteria.filter((criterion) => criterion.status !== 'satisfied');
      if (!roadmap.completionContract || incomplete?.length) {
        issues.push(`Stage ${node.id} cannot request complete while completion criteria remain unsatisfied.`);
      }
    }
    if (node.outcome?.disposition === 'exhausted' && !node.outcome.exhaustionEvidenceIds?.length) {
      issues.push(`Exhausted stage ${node.id} requires exhaustionEvidenceIds, not mathematical refuting evidence.`);
    }
  }
  return issues;
};

function upsertMathematicsPortfolioItems<T extends { id: string }>(
  current: readonly T[],
  updates: readonly T[] | undefined
): T[] {
  if (!updates) return [...current];
  if (new Set(updates.map((item) => item.id)).size !== updates.length) {
    throw new Error('Mathematics portfolio patch record ids must be unique within each collection.');
  }
  const byId = new Map(updates.map((item) => [item.id, item]));
  const merged = current.map((item) => byId.get(item.id) ?? item);
  const existingIds = new Set(current.map((item) => item.id));
  for (const item of updates) {
    if (!existingIds.has(item.id)) merged.push(item);
  }
  return merged;
}

type MathematicsPortfolioPatch = Readonly<{
  title?: MathematicsPortfolio['title'];
  stage?: MathematicsPortfolio['stage'];
  status?: MathematicsPortfolio['status'];
  updatedAt?: MathematicsPortfolio['updatedAt'];
  activeProblemId?: MathematicsPortfolio['activeProblemId'] | null;
  toolchain?: MathematicsPortfolio['toolchain'];
  problems?: MathematicsPortfolio['problems'];
  attempts?: MathematicsPortfolio['attempts'];
  examples?: MathematicsPortfolio['examples'];
  evidence?: MathematicsPortfolio['evidence'];
  verifications?: MathematicsPortfolio['verifications'];
  reviews?: MathematicsPortfolio['reviews'];
  blockers?: MathematicsPortfolio['blockers'];
  nextActions?: MathematicsPortfolio['nextActions'];
}>;

function patchMathematicsPortfolio(
  current: MathematicsPortfolio,
  patch: MathematicsPortfolioPatch
): MathematicsPortfolio {
  const candidate: MathematicsPortfolio = {
    ...current,
    ...(patch.title !== undefined ? { title: patch.title } : {}),
    ...(patch.stage !== undefined ? { stage: patch.stage } : {}),
    ...(patch.status !== undefined ? { status: patch.status } : {}),
    ...(patch.toolchain !== undefined ? { toolchain: patch.toolchain } : {}),
    problems: upsertMathematicsPortfolioItems(current.problems, patch.problems),
    attempts: upsertMathematicsPortfolioItems(current.attempts, patch.attempts),
    examples: upsertMathematicsPortfolioItems(current.examples, patch.examples),
    evidence: upsertMathematicsPortfolioItems(current.evidence, patch.evidence),
    verifications: upsertMathematicsPortfolioItems(current.verifications, patch.verifications),
    reviews: upsertMathematicsPortfolioItems(current.reviews, patch.reviews),
    ...(patch.blockers !== undefined ? { blockers: patch.blockers } : {}),
    ...(patch.nextActions !== undefined ? { nextActions: patch.nextActions } : {}),
    updatedAt: patch.updatedAt ?? now(),
  };
  if (patch.activeProblemId === null) delete candidate.activeProblemId;
  else if (patch.activeProblemId !== undefined) candidate.activeProblemId = patch.activeProblemId;
  return candidate;
}

const ACCESSIBLE_LEAN_MODULE_LIMIT = 64;
const ACCESSIBLE_LEAN_DECLARATION_LIMIT = 4096;
const ACCESSIBLE_LEAN_SOURCE_BYTES = 2 * 1024 * 1024;
const MATHEMATICS_PROMPT_CACHE_TTL_MS = 5 * 60_000;
const MATHEMATICS_REMOTE_PROMPT_CACHE_TTL_MS = 30_000;
const MATHEMATICS_PROMPT_CACHE_MAX_ENTRIES = 256;
const LEAN_INPUT_FINGERPRINT_CACHE_MAX_ENTRIES = 2_048;

type AccessibleLeanPremise = Readonly<{
  declarationName: string;
  declarationType: string;
  sourceModule: string;
  sourceFile: string;
}>;

const accessibleLeanPremiseCache = new Map<
  string,
  Readonly<{ expiresAt: number; value: readonly AccessibleLeanPremise[] }>
>();
const mathematicsPromptPackCache = new Map<
  string,
  Readonly<{ expiresAt: number; value: ReturnType<typeof deriveMathematicsPromptPack> }>
>();
const leanImportClosureCache = new Map<string, Readonly<{ expiresAt: number; value: LeanImportClosure }>>();
const leanImportClosureInflight = new Map<string, Promise<LeanImportClosure>>();
type LeanInputFingerprint = Readonly<{ metadata: string; contentHash: string }>;
const leanInputFingerprintCache = new Map<string, LeanInputFingerprint>();
const leanPackageDirectoryCache = new Map<string, Readonly<{ metadata: string; names: readonly string[] }>>();

function cachePut<T>(
  cache: Map<string, Readonly<{ expiresAt: number; value: T }>>,
  key: string,
  value: T,
  nowMs = Date.now(),
  ttlMs = MATHEMATICS_PROMPT_CACHE_TTL_MS
): void {
  cache.delete(key);
  cache.set(key, Object.freeze({ expiresAt: nowMs + ttlMs, value }));
  while (cache.size > MATHEMATICS_PROMPT_CACHE_MAX_ENTRIES) {
    const oldest = cache.keys().next().value;
    if (oldest === undefined) break;
    cache.delete(oldest);
  }
}

function cacheGet<T>(
  cache: Map<string, Readonly<{ expiresAt: number; value: T }>>,
  key: string,
  nowMs = Date.now()
): T | undefined {
  const entry = cache.get(key);
  if (!entry) return undefined;
  if (entry.expiresAt <= nowMs) {
    cache.delete(key);
    return undefined;
  }
  cache.delete(key);
  cache.set(key, entry);
  return entry.value;
}

function cachedLeanInputFingerprint(file: string, maxBytes?: number): LeanInputFingerprint | undefined {
  let stats: fs.BigIntStats;
  try {
    stats = fs.statSync(file, { bigint: true });
    if (!stats.isFile()) return undefined;
  } catch {
    leanInputFingerprintCache.delete(file);
    return undefined;
  }
  const metadata = [stats.dev, stats.ino, stats.size, stats.mtimeNs, stats.ctimeNs].join(':');
  const cacheMetadata = `${metadata}:${maxBytes ?? 'all'}`;
  const cached = leanInputFingerprintCache.get(file);
  if (cached?.metadata === cacheMetadata) return cached;
  let contents: Buffer;
  try {
    contents = fs.readFileSync(file);
  } catch {
    leanInputFingerprintCache.delete(file);
    return undefined;
  }
  const bounded = maxBytes === undefined ? contents : contents.subarray(0, maxBytes);
  const value = Object.freeze({
    metadata: cacheMetadata,
    contentHash: crypto.createHash('sha256').update(bounded).digest('hex'),
  });
  leanInputFingerprintCache.delete(file);
  leanInputFingerprintCache.set(file, value);
  while (leanInputFingerprintCache.size > LEAN_INPUT_FINGERPRINT_CACHE_MAX_ENTRIES) {
    const oldest = leanInputFingerprintCache.keys().next().value;
    if (oldest === undefined) break;
    leanInputFingerprintCache.delete(oldest);
  }
  return value;
}

async function hashLeanInputFiles(
  projectRoot: string,
  input: Readonly<{ importModules?: readonly string[]; sourceFile?: string }>,
  closure?: LeanImportClosure
): Promise<string> {
  const resolvedClosure = closure ?? (await discoverLeanImportClosure(projectRoot, input));
  const digest = crypto.createHash('sha256');
  // Include the same transitive closure used for premise extraction.  A
  // change in an imported module must invalidate the prompt cache as well.
  digest.update(resolvedClosure.fingerprint);
  digest.update('\0');
  for (const name of ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean']) {
    const file = path.join(projectRoot, name);
    const fingerprint = cachedLeanInputFingerprint(file);
    digest.update(name);
    digest.update('\0');
    digest.update(fingerprint ? `${fingerprint.metadata}\0${fingerprint.contentHash}\0` : 'missing\0');
  }
  return digest.digest('hex');
}

function leanModuleNameFromPath(projectRoot: string, filePath: string): string {
  const normalized = path.resolve(filePath).replaceAll(path.sep, '/');
  const mathlibMarker = '/Mathlib/';
  const batteriesMarker = '/Batteries/';
  const marker = normalized.includes(mathlibMarker)
    ? mathlibMarker
    : normalized.includes(batteriesMarker)
      ? batteriesMarker
      : undefined;
  const relative = marker
    ? normalized.slice(normalized.indexOf(marker) + 1)
    : path.relative(projectRoot, filePath).replaceAll(path.sep, '/');
  return relative.replace(/\.lean$/u, '').replaceAll('/', '.');
}

async function resolveLeanModuleFile(projectRoot: string, moduleName: string): Promise<string | undefined> {
  const relativeModulePath = `${moduleName.replaceAll('.', path.sep)}.lean`;
  const candidates = [path.join(projectRoot, relativeModulePath)];
  const packagesRoot = path.join(projectRoot, '.lake', 'packages');
  try {
    const stats = await fs.promises.stat(packagesRoot);
    const metadata = [stats.dev, stats.ino, stats.size, stats.mtimeMs, stats.ctimeMs].join(':');
    let packageNames = leanPackageDirectoryCache.get(packagesRoot);
    if (!packageNames || packageNames.metadata !== metadata) {
      packageNames = Object.freeze({ metadata, names: Object.freeze(await fs.promises.readdir(packagesRoot)) });
      leanPackageDirectoryCache.set(packagesRoot, packageNames);
      while (leanPackageDirectoryCache.size > 128) {
        const oldest = leanPackageDirectoryCache.keys().next().value;
        if (oldest === undefined) break;
        leanPackageDirectoryCache.delete(oldest);
      }
    }
    for (const packageName of packageNames.names) {
      candidates.push(path.join(packagesRoot, packageName, relativeModulePath));
      if (candidates.length >= 48) break;
    }
  } catch {
    // Projects without Lake packages are still searchable through their own imports.
  }
  const candidateIsFile = await Promise.all(
    candidates.map(async (candidate) => {
      try {
        return (await fs.promises.stat(candidate)).isFile();
      } catch {
        return false;
      }
    })
  );
  const matchIndex = candidateIsFile.findIndex(Boolean);
  return matchIndex >= 0 ? candidates[matchIndex] : undefined;
}

function resolveLeanSourceFile(projectRoot: string, sourceFile: string): string | undefined {
  if (path.isAbsolute(sourceFile)) return undefined;
  const resolved = path.resolve(projectRoot, sourceFile);
  const relative = path.relative(projectRoot, resolved);
  if (!relative || relative.startsWith(`..${path.sep}`) || path.isAbsolute(relative)) return undefined;
  try {
    return fs.statSync(resolved).isFile() ? resolved : undefined;
  } catch {
    return undefined;
  }
}

type LeanImportClosureFile = Readonly<{
  filePath: string;
  source: string;
  metadata: string;
  contentHash: string;
}>;

type LeanImportClosure = Readonly<{
  files: readonly LeanImportClosureFile[];
  missingModules: readonly string[];
  fingerprint: string;
}>;

const leanImportClosureKey = (
  projectRoot: string,
  input: Readonly<{ importModules?: readonly string[]; sourceFile?: string }>
): string =>
  JSON.stringify([
    path.resolve(projectRoot),
    [...new Set(input.importModules ?? [])].toSorted(),
    input.sourceFile ?? '',
  ]);

const leanImportClosureIsFresh = (closure: LeanImportClosure): boolean => {
  for (const file of closure.files) {
    try {
      const stat = fs.statSync(file.filePath);
      if (!stat.isFile()) return false;
      const metadata = [stat.dev, stat.ino, stat.size, stat.mtimeMs, stat.ctimeMs].join(':');
      if (metadata !== file.metadata) return false;
    } catch {
      return false;
    }
  }
  return true;
};

/** Discover the bounded import closure once and fingerprint the bytes Lean can read. */
async function discoverLeanImportClosure(
  projectRoot: string,
  input: Readonly<{ importModules?: readonly string[]; sourceFile?: string }>
): Promise<LeanImportClosure> {
  const key = leanImportClosureKey(projectRoot, input);
  const cached = cacheGet(leanImportClosureCache, key);
  if (cached && leanImportClosureIsFresh(cached)) return cached;
  if (cached) leanImportClosureCache.delete(key);
  const active = leanImportClosureInflight.get(key);
  if (active) return active;
  const discovery = discoverLeanImportClosureUncached(projectRoot, input)
    .then((closure) => {
      cachePut(leanImportClosureCache, key, closure);
      return closure;
    })
    .finally(() => {
      leanImportClosureInflight.delete(key);
    });
  leanImportClosureInflight.set(key, discovery);
  return discovery;
}

async function discoverLeanImportClosureUncached(
  projectRoot: string,
  input: Readonly<{ importModules?: readonly string[]; sourceFile?: string }>,
  localContextOnly = false
): Promise<LeanImportClosure> {
  const sourcePath = input.sourceFile ? resolveLeanSourceFile(projectRoot, input.sourceFile) : undefined;
  const queue: string[] = [];
  const queuedModules = new Set<string>();
  const enqueue = (value: string): void => {
    const moduleName = value.trim();
    if (!moduleName || moduleName.startsWith('_') || queuedModules.has(moduleName)) return;
    queuedModules.add(moduleName);
    queue.push(moduleName);
  };
  if (sourcePath) enqueue(leanModuleNameFromPath(projectRoot, sourcePath));
  for (const moduleName of input.importModules ?? []) enqueue(moduleName);
  const missingModules = new Set<string>();
  if (input.sourceFile && !sourcePath) missingModules.add(`source-file:${input.sourceFile}`);
  const visitedFiles = new Set<string>();
  const files: LeanImportClosureFile[] = [];
  let processedModules = 0;
  while (queue.length > 0 && processedModules < ACCESSIBLE_LEAN_MODULE_LIMIT) {
    const moduleName = String(queue.shift()).trim();
    if (!moduleName || moduleName.startsWith('_')) continue;
    processedModules += 1;
    const filePath =
      sourcePath && moduleName === leanModuleNameFromPath(projectRoot, sourcePath)
        ? sourcePath
        : await resolveLeanModuleFile(projectRoot, moduleName);
    if (!filePath) {
      missingModules.add(moduleName);
      continue;
    }
    if (localContextOnly) {
      const relative = path.relative(projectRoot, filePath);
      if (relative.split(path.sep).includes('.lake')) continue;
      if (relative.startsWith(`..${path.sep}`) || path.isAbsolute(relative) || fs.realpathSync(filePath) !== filePath) {
        throw new Error('math_corpus_local_context_path_invalid');
      }
    }
    if (visitedFiles.has(filePath)) continue;
    visitedFiles.add(filePath);
    let stat: fs.Stats;
    let source: string;
    try {
      stat = await fs.promises.stat(filePath);
      if (!stat.isFile() || stat.size > ACCESSIBLE_LEAN_SOURCE_BYTES) continue;
      source = await fs.promises.readFile(filePath, 'utf8');
    } catch {
      continue;
    }
    const bounded = Buffer.from(source, 'utf8').subarray(0, ACCESSIBLE_LEAN_SOURCE_BYTES);
    files.push({
      filePath,
      source,
      metadata: [stat.dev, stat.ino, stat.size, stat.mtimeMs, stat.ctimeMs].join(':'),
      contentHash: crypto.createHash('sha256').update(bounded).digest('hex'),
    });
    for (const importMatch of source.matchAll(/^\s*import\s+([A-Za-z0-9_.]+)/gmu)) {
      if (queue.length + files.length < ACCESSIBLE_LEAN_MODULE_LIMIT) enqueue(importMatch[1]);
    }
  }
  const digest = crypto.createHash('sha256');
  for (const file of [...files].sort((left, right) => left.filePath.localeCompare(right.filePath))) {
    digest.update(path.relative(projectRoot, file.filePath));
    digest.update('\0');
    digest.update(`${file.metadata}\0${file.contentHash}\0`);
  }
  for (const moduleName of [...missingModules].sort()) digest.update(`missing-module\0${moduleName}\0`);
  return Object.freeze({
    files: Object.freeze(files),
    missingModules: Object.freeze([...missingModules].sort()),
    fingerprint: digest.digest('hex'),
  });
}

/**
 * Read a small import closure and expose only declaration headers. This keeps
 * retrieval useful on real mathlib projects without scanning or injecting the
 * entire library into a Worker context.
 */
async function collectAccessibleLeanPremises(
  projectRoot: string,
  input: Readonly<{ importModules?: readonly string[]; sourceFile?: string }>,
  closure?: LeanImportClosure
): Promise<readonly AccessibleLeanPremise[]> {
  const resolvedClosure = closure ?? (await discoverLeanImportClosure(projectRoot, input));
  const sourceFingerprint = resolvedClosure.fingerprint;
  const cacheKey = `${path.resolve(projectRoot)}\0${sourceFingerprint}\0${JSON.stringify({
    importModules: input.importModules ?? [],
    sourceFile: input.sourceFile ?? '',
  })}`;
  const cached = cacheGet(accessibleLeanPremiseCache, cacheKey);
  if (cached) return cached;
  const declarations = new Map<
    string,
    {
      declarationName: string;
      declarationType: string;
      sourceModule: string;
      sourceFile: string;
    }
  >();
  for (const file of resolvedClosure.files) {
    const sourceModule = leanModuleNameFromPath(projectRoot, file.filePath);
    const relativeSourceFile = path.relative(projectRoot, file.filePath).replaceAll(path.sep, '/');
    for (const declaration of inspectLeanDeclarations(file.source)) {
      const key = `${declaration.name}\u0000${sourceModule}`;
      if (declarations.has(key)) continue;
      declarations.set(
        key,
        Object.freeze({
          declarationName: declaration.name,
          declarationType: declaration.declarationType,
          sourceModule,
          sourceFile: relativeSourceFile,
        })
      );
      if (declarations.size >= ACCESSIBLE_LEAN_DECLARATION_LIMIT) break;
    }
    if (declarations.size >= ACCESSIBLE_LEAN_DECLARATION_LIMIT) break;
  }
  const result = Object.freeze([...declarations.values()]);
  cachePut(accessibleLeanPremiseCache, cacheKey, result);
  return result;
}

const mathematicsPortfolioContract = (projectRoot?: string, includeStarterTemplate = true) => ({
  schema: MATHEMATICS_PORTFOLIO_SCHEMA,
  version: 1,
  actions: {
    schema: 'Read this contract and starterTemplate; no project mutation.',
    validate: 'Pass portfolio; returns validation issues without creating or changing files.',
    get: 'Use once at kickoff/resume or after a revision conflict.',
    submit: 'Pass one complete portfolio. Existing portfolios require baseRevision.',
    patch: 'Update only changed fields or id-addressed records in an existing portfolio. Requires baseRevision.',
    request_review: 'Existing portfolio plus review.problemId, targetCommit, and statementHash.',
    submit_review: 'Existing portfolio plus a complete review verdict object.',
    bootstrap:
      'Materialize one pinned Lean-Eval problem into an isolated solver workspace with its MathProblemContract, route card, and bootstrap receipt.',
    official_gate:
      'Reload a durable bootstrap receipt, rerun LOCAL_GATE plus the official comparator, and atomically persist the signed receipts into the matching portfolio problem.',
  },
  revisionPolicy:
    'Reuse currentRevision from the latest successful mutation as the next baseRevision. Call get only on kickoff/resume, when object contents are needed, or after a mismatch.',
  terminalPolicy:
    'verified requires an immutable MathProblemContract, a matching statement kernel receipt that counts as formal support, passed review, and an official comparator receipt bound to the committed manifest; refuted requires a contract-bound Lean negation plus matching kernel and signed official comparator receipts.',
  derivedFields: {
    reusablePremises:
      'Bounded verified_local premises recovered from prior semi-proof checkpoints; recheck entries marked requiresRecheck before selection.',
    promptPack:
      'For get with promptQuery, returns either one bounded node-local pack or a routeCoverage pack. With sourceFile/importModules it searches a bounded Lean import closure. Explicit upstreamQueries may additionally query the public Mathlib-only LeanSearch and Loogle indexes; remote proof bodies are discarded and candidates remain unverified until checked by the target project. For non-protected projects only, explicit packageQueries discovers repository metadata through GitHub and verifies version, dependency, license, build, and current-project installation metadata against the official Reservoir registry without changing project dependencies. Registry selection prefers a registered project-pinned revision, then a built exact-compatible historical version. Explicit installedPackageScopes plus installedPackageQuery may then search query-ranked declaration headers in already-installed local Lake packages and return the fully qualified declaration and module import required for each hit. All declarations share one premise limit, with one slot reserved for an explicit installed-package or upstream hit, up to three lexically matched cross-problem mechanism capsules, and raw reusablePremises omitted.',
    feasibilityRanking:
      'For get without promptQuery, returns a derived stable ranking for problems carrying feasibility signals. The score is a bounded solve-probability estimate with zero-credit and infrastructure risks plus a first executable milestone; it does not claim official benchmark credit or proof authority.',
    leanEvalIntake:
      'When leanEvalRepositoryRoot (or DEEPSCIENTIST_LEAN_EVAL_ROOT) is supplied, get reads the pinned LeanEval catalog at 96a09300f9debeef864d8037635d6e0248c43960, verifies the checkout, analyzes active/v1/visible problems from public Challenge metadata, excludes accepted-credit tasks from eligible ranking, and returns catalogHash, evidence provenance, hole DAGs, and dynamic feasibility profiles. Set DEEPSCIENTIST_LEAN_EVAL_ELABORATION_PROBE=1 to add a bounded sandboxed #check pass for the highest-ranked public declarations. Protected Solution.lean content is never read.',
  },
  ...(includeStarterTemplate
    ? {
        starterTemplate: buildInitialMathematicsPortfolio({
          title: '<mathematics project title>',
          projectRoot,
          updatedAt: Date.now(),
          nextActionLabel: 'Understand the problem and map known results',
        }),
      }
    : {}),
});

const mathematicsValidationIssues = (errors: string[]) =>
  errors.map((message, index) => ({
    code: 'invalid_portfolio',
    path: /^([A-Za-z]+(?:\[\d+\])?(?:\.[A-Za-z]+)?)/u.exec(message)?.[1] || '$',
    message,
    issueIndex: index,
  }));

const mathematicsVerifierItemInput = z
  .object({
    id: z.string().trim().min(1).max(120).optional(),
    proofPath: z.string().trim().min(1).max(500),
    theoremName: z.string().trim().min(1).max(240),
    statementHash: z.string().trim().min(1).max(256),
    leanStatementHash: z.string().trim().min(1).max(256).optional(),
    problemId: z.string().trim().min(1).max(240).optional(),
    claim: z.enum(['statement', 'negation']).optional(),
    stateId: z.string().trim().min(1).max(160).optional(),
  })
  .strict();

const leanWorkspaceOperationInput = z.discriminatedUnion('op', [
  z
    .object({
      op: z.literal('submit_formula'),
      id: z.string().trim().min(1).max(160),
      formula: z.string().trim().min(1).max(20_000),
      label: z.string().trim().min(1).max(240).optional(),
      theoremName: z.string().trim().min(1).max(240).optional(),
      sourcePath: z.string().trim().min(1).max(500).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('open_goal'),
      stateId: z.string().trim().min(1).max(160),
      target: z.string().trim().min(1).max(20_000),
      hypotheses: z.array(z.string().max(4_000)).max(128).default([]),
      theoremName: z.string().trim().min(1).max(240).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('rewrite_goal'),
      stateId: z.string().trim().min(1).max(160),
      parentStateId: z.string().trim().min(1).max(160),
      previousTarget: z.string().trim().min(1).max(20_000),
      target: z.string().trim().min(1).max(20_000),
      hypotheses: z.array(z.string().max(4_000)).max(128).default([]),
      theoremName: z.string().trim().min(1).max(240).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('branch_goal'),
      stateId: z.string().trim().min(1).max(160),
      parentStateId: z.string().trim().min(1).max(160),
      target: z.string().trim().min(1).max(20_000),
      hypotheses: z.array(z.string().max(4_000)).max(128).default([]),
      theoremName: z.string().trim().min(1).max(240).optional(),
      branchLabel: z.string().trim().min(1).max(160).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('close_goal'),
      stateId: z.string().trim().min(1).max(160),
      parentStateId: z.string().trim().min(1).max(160).optional(),
      target: z.string().trim().min(1).max(20_000).optional(),
      theoremName: z.string().trim().min(1).max(240).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('diagnostic'),
      severity: z.enum(['info', 'warning', 'error']),
      message: z.string().trim().min(1).max(12_000),
      proofPath: z.string().trim().min(1).max(500).optional(),
      stateId: z.string().trim().min(1).max(160).optional(),
    })
    .strict(),
  z
    .object({
      op: z.literal('certify'),
      items: z.array(mathematicsVerifierItemInput).min(1).max(64),
    })
    .strict(),
]);

const createMathematicsVerificationEvent = <Kind extends MathematicsVerificationEventKind>(
  sessionId: string,
  kind: Kind,
  payload: MathematicsVerificationEventPayloadMap[Kind]
): MathematicsVerificationEvent =>
  ({
    schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
    eventId: crypto.randomUUID(),
    sessionId,
    timestamp: now(),
    kind,
    payload,
  }) as MathematicsVerificationEvent;

const mathematicsTraceMetrics = (events: MathematicsVerificationEvent[], results: MathematicsVerifierResult[]) => {
  const observedStates = new Set<string>();
  const openStates = new Set<string>();
  for (const event of events) {
    if (event.kind === 'goal.opened') {
      observedStates.add(event.payload.stateId);
      openStates.add(event.payload.stateId);
    } else if (event.kind === 'goal.rewritten' || event.kind === 'goal.branched') {
      observedStates.add(event.payload.stateId);
      openStates.delete(event.payload.parentStateId);
      openStates.add(event.payload.stateId);
    } else if (event.kind === 'goal.closed') {
      observedStates.add(event.payload.stateId);
      openStates.delete(event.payload.stateId);
    }
  }
  const checkedFiles = new Set<string>();
  let kernelVerified = 0;
  let failed = 0;
  let blocked = 0;
  let unavailable = 0;
  for (const result of results) {
    checkedFiles.add(result.proofPath);
    if (result.status === 'kernel_verified') kernelVerified += 1;
    else if (result.status === 'failed') failed += 1;
    else if (result.status === 'blocked') blocked += 1;
    else if (result.status === 'unavailable') unavailable += 1;
  }
  return {
    proofStatesChecked: observedStates.size || results.length,
    openGoals: openStates.size,
    filesChecked: checkedFiles.size,
    checks: results.length,
    kernelVerified,
    failed,
    blocked,
    unavailable,
  };
};

const storeMathematicsVerification = (
  run: ScienceRunState,
  results: MathematicsVerifierResult[],
  events: MathematicsVerificationEvent[],
  capability?: MathematicsVerificationCapability
): MathematicsVerificationTrace | undefined => {
  const receipts = new Map<string, MathematicsVerifierResult>();
  for (const result of run.mathematicsVerifications) receipts.set(result.receiptId, result);
  const compactResults: MathematicsVerifierResult[] = [];
  for (const value of results) {
    const { events: _events, ...result } = value;
    const compactResult = result as MathematicsVerifierResult;
    compactResults.push(compactResult);
    receipts.set(compactResult.receiptId, compactResult);
  }
  const retainedReceipts: MathematicsVerifierResult[] = [];
  const skippedReceiptCount = Math.max(0, receipts.size - 512);
  let receiptIndex = 0;
  for (const receipt of receipts.values()) {
    if (receiptIndex >= skippedReceiptCount) retainedReceipts.push(receipt);
    receiptIndex += 1;
  }
  run.mathematicsVerifications = retainedReceipts;
  run.mathematicsVerification = compactResults.at(-1) || run.mathematicsVerification;
  const eventById = new Map<string, MathematicsVerificationEvent>();
  for (const event of run.mathematicsVerificationEvents) eventById.set(event.eventId, event);
  for (const event of events) eventById.set(event.eventId, event);
  const mergedEvents = [...eventById.values()];
  if (!areMathematicsVerificationEventsOrdered(mergedEvents)) {
    mergedEvents.sort((left, right) => left.timestamp - right.timestamp);
  }
  if (mergedEvents.length > 2_000) mergedEvents.splice(0, mergedEvents.length - 2_000);
  run.mathematicsVerificationEvents = mergedEvents;
  if (capability) run.mathematicsVerificationCapability = capability;
  run.updatedAt = now();
  let trace: MathematicsVerificationTrace | undefined;
  if (run.projectRoot) {
    try {
      trace = writeMathematicsProjectVerificationTrace(
        run.projectRoot,
        run.mathematicsVerificationEvents,
        run.mathematicsVerificationCapability
      );
    } catch (error) {
      // The verifier receipt and in-memory run are authoritative.  A report
      // trace is a recoverable projection and must not turn a successful Lean
      // kernel result into a tool failure.
      console.warn(`[ScienceArtifactMCP] mathematics trace projection failed: ${String(error)}`);
    }
    try {
      writeMathematicsLiveVerificationTrace(
        run.projectRoot,
        run.mathematicsVerificationEvents,
        run.mathematicsVerificationCapability
      );
    } catch (error) {
      console.warn(`[ScienceArtifactMCP] mathematics live trace projection failed: ${String(error)}`);
    }
  }
  persistRunSnapshot(run);
  return trace;
};

const recoverMathematicsPortfolioVerifications = (
  run: ScienceRunState,
  portfolio: MathematicsPortfolio,
  projectRoot: string,
  verificationIndex: MathematicsVerificationIndex
): MathematicsVerificationIndex => {
  // Managed runs recover their own persisted science state, never another run's project cache.
  if (readMathRunHistoryIdentity()) return verificationIndex;
  const receiptIds = new Set<string>();
  for (const problem of portfolio.problems) {
    if (problem.verificationId) receiptIds.add(problem.verificationId);
    if (problem.localGateReceipt?.receiptId) receiptIds.add(problem.localGateReceipt.receiptId);
  }
  const referencedReviewIds = referencedMathematicsReviewIds(portfolio);
  for (const review of portfolio.reviews) {
    if (referencedReviewIds.has(review.id) && review.candidateReview?.replayReceiptId) {
      receiptIds.add(review.candidateReview.replayReceiptId);
    }
  }
  // A failed/blocked in-memory attempt must not mask a durable successful
  // receipt with the same deterministic id.  Receipt ids are derived from the
  // requested proof identity, so only a complete kernel result satisfies the
  // recovery requirement.
  const missingReceiptIds = [...receiptIds].filter(
    (receiptId) =>
      !verificationIndex.byReceiptId
        .get(receiptId)
        ?.some(
          (result) =>
            result.status === 'kernel_verified' &&
            result.verifier === 'lean-kernel' &&
            result.goalsRemaining === 0 &&
            result.sorryCount === 0 &&
            result.admitCount === 0
        )
  );
  if (!missingReceiptIds.length) return verificationIndex;
  const cachedByReceiptId = findCachedFormalVerificationReceipts(projectRoot, missingReceiptIds);
  if (!cachedByReceiptId.size) return verificationIndex;
  storeMathematicsVerification(run, [...cachedByReceiptId.values()], []);
  return indexMathematicsVerifications(run);
};

const capabilityFromVerificationBatch = (
  batch: MathematicsVerifierBatchResult,
  previous?: MathematicsVerificationCapability
): MathematicsVerificationCapability | undefined => {
  const first = batch.results[0];
  if (!first) return previous;
  if (batch.status === 'blocked') return previous;
  return {
    available: batch.status !== 'unavailable',
    command: first.toolchain.lake ? 'lake' : 'lean',
    executable: first.toolchain.lake ? 'lake' : 'lean',
    ...(batch.status === 'unavailable' ? { reason: first.error } : {}),
    batchCertification: true,
    liveGoals: false,
    persistentSession: false,
  };
};

const scienceArtifactTargetInput = z
  .object({
    kind: z.enum([
      'run',
      'report',
      'artifact',
      'page',
      'evidence',
      'claim',
      'provenance',
      'skill_use',
      'annotation',
      'memory',
    ]),
    id: z.string().trim().min(1).max(240).optional(),
    version: z.number().int().positive().optional(),
    pageId: z.string().trim().min(1).max(240).optional(),
  })
  .strict();

const scienceArtifactQueryInput = z
  .object({
    queryId: z.string().trim().min(1).max(120),
    target: scienceArtifactTargetInput,
    scope: z.enum(['run', 'project']).default('run'),
    select: z
      .array(
        z
          .string()
          .regex(/^[A-Za-z][A-Za-z0-9_]*$/u)
          .max(80)
      )
      .max(32)
      .optional(),
  })
  .strict();

const scienceArtifactTransactionOperationInput = z
  .object({
    opId: z.string().trim().min(1).max(120),
    action: z.enum(['create', 'patch', 'replace']),
    target: scienceArtifactTargetInput,
    payload: z.record(z.unknown()),
    baseRevision: z.string().trim().min(1).max(240).optional(),
    createIfMissing: z.boolean().optional(),
  })
  .strict();

const cloneScienceRunState = (run: ScienceRunState): ScienceRunState => structuredClone(run);

const projectSelectedFields = (value: unknown, fields?: string[]): unknown => {
  if (!fields?.length || !isRecord(value)) return value;
  return Object.fromEntries(
    fields.filter((field) => Object.prototype.hasOwnProperty.call(value, field)).map((field) => [field, value[field]])
  );
};

const REPORT_CHART_RECEIPT_SCHEMA = 'deepscientist.report_chart.render_receipt.v1' as const;
const REPORT_CHART_RENDERER = 'deepscientist-static-svg' as const;
const REPORT_CHART_RENDERER_VERSION_V1 = '1.2.0' as const;
const REPORT_CHART_RENDERER_VERSION_V2 = '2.0.0' as const;
const REPORT_CHART_ACCEPTED_RENDERER_VERSIONS = [
  '1.0.0',
  '1.1.0',
  REPORT_CHART_RENDERER_VERSION_V1,
  REPORT_CHART_RENDERER_VERSION_V2,
] as const;
const REPORT_CHART_RECIPE_VERSION_V1 = 2 as const;
const REPORT_CHART_RECIPE_VERSION_V2 = 1 as const;

const sha256 = (value: string): string => crypto.createHash('sha256').update(value).digest('hex');

function verifyReportChartArtifactHandoff(run: ScienceRunState, artifact: ScienceArtifact): void {
  if (artifact.viewer?.kind !== 'report_chart') return;
  if (!run.projectRoot) throw new Error('A report_chart artifact requires a bound project root.');
  if (!artifact.viewer.chartSpec) throw new Error('A report_chart artifact requires viewer.chartSpec.');

  const reportChartMetadata = isRecord(artifact.metadata?.reportChart) ? artifact.metadata.reportChart : undefined;
  const receipt =
    reportChartMetadata && isRecord(reportChartMetadata.receipt) ? reportChartMetadata.receipt : undefined;
  if (
    !receipt ||
    receipt.schema !== REPORT_CHART_RECEIPT_SCHEMA ||
    receipt.renderer !== REPORT_CHART_RENDERER ||
    !REPORT_CHART_ACCEPTED_RENDERER_VERSIONS.includes(
      receipt.rendererVersion as (typeof REPORT_CHART_ACCEPTED_RENDERER_VERSIONS)[number]
    ) ||
    receipt.deterministic !== true ||
    receipt.scriptFreeSvg !== true
  ) {
    throw new Error('A report_chart artifact requires the unmodified render receipt returned by report_chart.');
  }
  if (
    reportChartMetadata?.schema !== artifact.viewer.chartSpec.schema ||
    reportChartMetadata.kind !== artifact.viewer.chartSpec.kind ||
    reportChartMetadata.palette !== artifact.viewer.chartSpec.style.palette
  ) {
    throw new Error('Report-chart metadata must match viewer.chartSpec.');
  }
  if (
    (artifact.viewer.chartSpec.schema === REPORT_CHART_SCHEMA_V2 &&
      receipt.specSchema !== artifact.viewer.chartSpec.schema) ||
    (receipt.specSchema !== undefined && receipt.specSchema !== artifact.viewer.chartSpec.schema)
  ) {
    throw new Error('Report-chart receipt specSchema must match viewer.chartSpec.');
  }
  const recipe = artifact.viewer.chartSpec.recipe;
  const expectedRendererVersion =
    artifact.viewer.chartSpec.schema === REPORT_CHART_SCHEMA_V2
      ? REPORT_CHART_RENDERER_VERSION_V2
      : REPORT_CHART_RENDERER_VERSION_V1;
  const expectedRecipeVersion =
    artifact.viewer.chartSpec.schema === REPORT_CHART_SCHEMA_V2
      ? REPORT_CHART_RECIPE_VERSION_V2
      : REPORT_CHART_RECIPE_VERSION_V1;
  if (
    recipe
      ? receipt.rendererVersion !== expectedRendererVersion ||
        receipt.recipe !== recipe ||
        receipt.recipeVersion !== expectedRecipeVersion ||
        reportChartMetadata.recipe !== recipe ||
        reportChartMetadata.recipeVersion !== expectedRecipeVersion
      : receipt.recipe !== undefined ||
        receipt.recipeVersion !== undefined ||
        reportChartMetadata.recipe !== undefined ||
        reportChartMetadata.recipeVersion !== undefined
  ) {
    throw new Error('Report-chart recipe metadata must match viewer.chartSpec and its render receipt.');
  }

  const chartPath = asLocalPath(receipt.chartPath, 'metadata.reportChart.receipt.chartPath');
  const svgPath = asLocalPath(receipt.svgPath, 'metadata.reportChart.receipt.svgPath');
  if (!chartPath || !svgPath || path.isAbsolute(chartPath) || path.isAbsolute(svgPath)) {
    throw new Error('Report-chart receipt paths must be project-relative.');
  }
  if (
    artifact.primaryPath !== chartPath ||
    artifact.viewer.configPath !== chartPath ||
    artifact.previewPath !== svgPath
  ) {
    throw new Error('Report-chart artifact paths must match the render receipt exactly.');
  }
  if (!artifact.outputPaths?.includes(chartPath) || !artifact.outputPaths.includes(svgPath)) {
    throw new Error('Report-chart outputPaths must include both receipt files.');
  }

  const chartFile = resolveProjectOwnedPath(run.projectRoot, chartPath, 'report chart specification');
  const svgFile = resolveProjectOwnedPath(run.projectRoot, svgPath, 'report chart preview');
  assertProjectPathHasNoSymlinkEscape(run.projectRoot, chartFile, 'report chart specification');
  assertProjectPathHasNoSymlinkEscape(run.projectRoot, svgFile, 'report chart preview');
  if (
    !fs.existsSync(chartFile) ||
    !fs.statSync(chartFile).isFile() ||
    !fs.existsSync(svgFile) ||
    !fs.statSync(svgFile).isFile()
  ) {
    throw new Error('Report-chart receipt files are missing or are not regular files.');
  }

  const chartJson = fs.readFileSync(chartFile, 'utf8');
  const svg = fs.readFileSync(svgFile, 'utf8');
  const chartHash = sha256(chartJson);
  const svgHash = sha256(svg);
  if (receipt.specSha256 !== chartHash || receipt.svgSha256 !== svgHash || artifact.contentHash !== chartHash) {
    throw new Error('Report-chart files or hashes changed after render; render the chart again before registration.');
  }
  if (/<script\b|javascript:|<foreignObject\b/iu.test(svg)) {
    throw new Error('Report-chart SVG must remain script-free.');
  }

  let fileSpec: unknown;
  try {
    fileSpec = JSON.parse(chartJson);
  } catch {
    throw new Error('Report-chart specification file is not valid JSON.');
  }
  const fileValidation = validateReportChartSpec(fileSpec);
  if (!fileValidation.ok || JSON.stringify(fileValidation.spec) !== JSON.stringify(artifact.viewer.chartSpec)) {
    throw new Error('Report-chart viewer.chartSpec must match the rendered specification file exactly.');
  }

  const evidenceIds = collectReportChartEvidenceIds(fileValidation.spec);
  if (!evidenceIds.length) {
    throw new Error('A report_chart artifact requires at least one registered evidence id.');
  }
  const uncoveredMarks = collectReportChartMarkCoverage(fileValidation.spec).filter(
    (coverage) => coverage.evidenceSource === 'none'
  );
  if (uncoveredMarks.length) {
    throw new Error(
      `Every report-chart mark must inherit or declare evidence ids; uncovered marks: ${uncoveredMarks
        .slice(0, 12)
        .map((coverage) => coverage.path)
        .join(', ')}.`
    );
  }
  const sameIds = (candidate?: string[]): boolean =>
    JSON.stringify([...(candidate || [])].sort()) === JSON.stringify([...evidenceIds].sort());
  if (!sameIds(artifact.evidenceIds) || !sameIds(artifact.viewer.evidenceIds)) {
    throw new Error('Report-chart artifact and viewer evidence ids must match the rendered specification.');
  }
  const unresolved = evidenceIds.filter((id) => {
    const evidence = run.evidence.get(id);
    return !evidence || evidence.status === 'missing';
  });
  if (unresolved.length) {
    throw new Error(`Report-chart evidence ids must resolve in the same run: ${unresolved.join(', ')}.`);
  }
}

function verifyMathematicsProofTraceArtifactHandoff(run: ScienceRunState, artifact: ScienceArtifact): void {
  if (artifact.viewer?.kind !== 'proof_trace') return;
  if (!run.projectRoot) throw new Error('A proof_trace artifact requires a bound project root.');
  if (artifact.type !== 'figure') throw new Error('A proof_trace artifact must use artifact type=figure.');

  const tracePath = asLocalPath(artifact.viewer.dataPath, 'viewer.dataPath');
  if (!tracePath || path.isAbsolute(tracePath)) {
    throw new Error('A proof_trace artifact requires a project-relative viewer.dataPath.');
  }
  if (artifact.primaryPath !== tracePath) {
    throw new Error('A proof_trace artifact primaryPath must match viewer.dataPath exactly.');
  }
  const contentAddress = /^mathematics\/report-traces\/verification-([a-f0-9]{20})\.json$/u.exec(tracePath);
  if (!contentAddress) {
    throw new Error('A proof_trace artifact must use the content-addressed reportTracePath returned by Lean.');
  }

  const traceFile = resolveProjectOwnedPath(run.projectRoot, tracePath, 'mathematics proof trace');
  assertProjectPathHasNoSymlinkEscape(run.projectRoot, traceFile, 'mathematics proof trace');
  if (!fs.existsSync(traceFile) || !fs.statSync(traceFile).isFile()) {
    throw new Error('The proof_trace dataPath is missing or is not a regular file.');
  }

  const rawTrace = fs.readFileSync(traceFile, 'utf8');
  let parsedTrace: unknown;
  try {
    parsedTrace = JSON.parse(rawTrace);
  } catch {
    throw new Error('The proof_trace dataPath is not valid JSON.');
  }
  const trace = readMathematicsVerificationTrace(parsedTrace);
  if (!trace) {
    throw new Error(`The proof_trace dataPath must satisfy ${MATHEMATICS_VERIFICATION_TRACE_SCHEMA}.`);
  }
  if (!trace.events.length) {
    throw new Error('A proof_trace artifact requires at least one validated verification event.');
  }
  const kernelReceiptKeys = new Set<string>();
  const kernelCheckKeys = new Set<string>();
  const kernelTheoremsBySession = new Map<string, Set<string | undefined>>();
  for (const result of run.mathematicsVerifications) {
    if (result.status !== 'kernel_verified') continue;
    kernelReceiptKeys.add(
      JSON.stringify([result.receiptId, result.checkId, result.proofPath, result.theoremName, result.sessionId])
    );
    kernelCheckKeys.add(JSON.stringify([result.proofPath, result.sessionId]));
    const theoremSet = kernelTheoremsBySession.get(result.sessionId) ?? new Set<string | undefined>();
    theoremSet.add(result.theoremName);
    kernelTheoremsBySession.set(result.sessionId, theoremSet);
  }
  for (const event of trace.events) {
    if (event.kind === 'receipt.published' && event.payload.status === 'kernel_verified') {
      const backed = kernelReceiptKeys.has(
        JSON.stringify([
          event.payload.receiptId,
          event.payload.checkId,
          event.payload.proofPath,
          event.payload.theoremName,
          event.sessionId,
        ])
      );
      if (!backed) throw new Error('A Kernel verified proof_trace receipt must match a stored Lean verifier result.');
    }
    if (event.kind === 'check.kernel_checked' && event.payload.status === 'kernel_verified') {
      const backed = kernelCheckKeys.has(JSON.stringify([event.payload.proofPath, event.sessionId]));
      if (!backed) throw new Error('A Kernel verified proof_trace check must match a stored Lean verifier result.');
    }
    if (event.kind === 'goal.closed' && event.payload.status === 'kernel_verified') {
      const theoremSet = kernelTheoremsBySession.get(event.sessionId);
      const backed = Boolean(theoremSet && (!event.payload.theoremName || theoremSet.has(event.payload.theoremName)));
      if (!backed)
        throw new Error('A Kernel verified proof_trace Goal closure must match a stored Lean verifier result.');
    }
  }
  const traceHash = sha256(rawTrace);
  if (contentAddress[1] !== traceHash.slice(0, 20)) {
    throw new Error('The proof_trace reportTracePath digest does not match the frozen trace content.');
  }
  if (artifact.contentHash !== traceHash) {
    throw new Error(
      'The proof_trace file changed while the artifact was registered. Register the current trace again.'
    );
  }
}

async function main() {
  readMathRunRetrievalCorpus(process.env, path.resolve(process.argv[1]));
  readMathResearchPolicy();
  const server = new McpServer({
    name: BUILTIN_SCIENCE_ARTIFACT_NAME,
    version: '1.0.0',
  });

  const workspaceActions = researchTeamAuthorizedToolActions(PROJECT_WORKSPACE_TOOL_NAME, [
    'status',
    'checkpoint',
    'frontier',
    'prepare_branch',
    'activate_branch',
    'compare_branches',
    'clone',
  ] as const);
  const workspaceTool = server.tool(
    PROJECT_WORKSPACE_TOOL_NAME,
    PROJECT_WORKSPACE_TOOL_DESCRIPTION,
    {
      action: z.enum(workspaceActions.length ? [workspaceActions[0]!, ...workspaceActions.slice(1)] : ['status']),
      runId: z.string().optional(),
      conversationId: z.string().optional(),
      projectRoot: z.string().optional(),
      target: z
        .object({
          kind: z.enum(['artifact']).optional(),
          id: z.string().optional(),
          version: z.number().optional(),
        })
        .optional(),
      payload: projectWorkspacePayloadInput.optional(),
      displayIntent: z.enum(['background', 'open', 'focus']).optional(),
    },
    async ({ action, runId: requestedRunId, conversationId, projectRoot, target, payload, displayIntent }) => {
      assertResearchTeamToolActionAuthorized(PROJECT_WORKSPACE_TOOL_NAME, action);
      const resolvedConversationId = resolveSessionIdentifier(
        conversationId,
        PROJECT_WORKSPACE_ENV_KEYS.conversationId,
        'conversationId'
      );
      const discoveryIdentity = await resolveRuntimeDiscoveryIdentity(resolvedConversationId);
      const effectiveRunId = resolveRuntimeDiscoveryRunId(requestedRunId, discoveryIdentity);
      const body = bindRuntimeDiscoveryGoalId(payload || {}, discoveryIdentity);
      if (action === 'clone') {
        const remoteUrl = asString(body.remoteUrl || body.remote_url, '');
        const destination = asString(body.destination, '');
        const baseDir = asString(body.baseDir || body.base_dir, '');
        const cloned = cloneProjectGit({
          remoteUrl,
          ...(destination ? { destination } : {}),
          ...(baseDir ? { baseDir } : {}),
          ...(body.ref ? { ref: asString(body.ref, '') } : {}),
          ...(body.depth != null ? { depth: Number(body.depth) } : {}),
          conversationId: resolvedConversationId,
        });
        if (!cloned.ok || !cloned.binding || !cloned.workspace) {
          throw new Error(cloned.error || 'The Git repository could not be cloned.');
        }
        setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectRoot, cloned.workspace);
        setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.conversationId, resolvedConversationId);
        setSessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectId, cloned.projectId);
        const bindingPersisted = resolvedConversationId
          ? await persistProjectBindingToCore(resolvedConversationId, cloned.binding)
          : false;
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          conversationId: resolvedConversationId,
          projectId: cloned.projectId,
          workspace: cloned.workspace,
          repository: cloned.repository,
          binding: cloned.binding,
          bindingPersisted,
          next: 'Use project_workspace(action="status") before writing files or creating a checkpoint.',
          displayIntent: displayIntent || 'open',
        });
      }

      const resolvedProjectRoot = await resolveModeProjectRoot(projectRoot, resolvedConversationId);
      if (!resolvedProjectRoot) {
        throw new Error(
          'project_workspace requires the current project root. Reopen the task if the runtime did not bind one.'
        );
      }
      const projectId = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.projectId);

      if ((action === 'prepare_branch' || action === 'activate_branch') && !effectiveRunId) {
        throw new Error('project_workspace branch operations require a runtime-bound or explicit runId.');
      }

      if (action === 'status') {
        const discovered = discoverProjectGit({ workspace: resolvedProjectRoot });
        if (!discovered.ok || !discovered.repository) {
          throw new Error(discovered.error || 'The bound project is not a readable Git repository.');
        }
        const graph = listProjectGitGraph({ workspace: resolvedProjectRoot, limit: 200 });
        if (!graph.ok) throw new Error(graph.error || 'The project checkpoint history could not be read.');
        const workingTree = getProjectGitWorkingTree({ workspace: resolvedProjectRoot });
        if (!workingTree.ok) throw new Error(workingTree.error || 'The project working tree could not be read.');
        const financeReceipt = projectWorkspaceStatusFinanceReceipt({
          runId: effectiveRunId,
          conversationId: resolvedConversationId,
          projectId,
          projectRoot: resolvedProjectRoot,
          head: discovered.repository.head,
          branch: discovered.repository.branch,
          dirtyPaths: workingTree.files.map((file) => file.path),
        });
        const allowedStages = boundCheckpointStages();
        const checkpointDomain = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain);
        const normalizedCheckpointDomain = normalizeProjectDomain(checkpointDomain, 'general');
        const routeModeRequiredForStages = allowedStages.filter((stage) =>
          requiresResearchStrategyForCheckpoint(normalizedCheckpointDomain, stage)
        );
        const requestedGoalId = asString(body.goalId || body.goal_id, '');
        const completedResearchStages = graph.commits
          .filter(
            (commit) =>
              (commit.checkpoint?.researchStage || commit.checkpoint?.directionDecision) &&
              (!requestedGoalId || commit.checkpoint.goalId === requestedGoalId)
          )
          .slice(0, 20)
          .map((commit) => ({
            commit: commit.sha,
            shortCommit: commit.shortSha,
            checkpointStage: commit.checkpoint!.stage,
            researchStrategy: commit.checkpoint!.researchStrategy,
            routeNodeId: commit.checkpoint!.routeNodeId,
            repairsNodeId: commit.checkpoint!.repairsNodeId,
            goalId: commit.checkpoint!.goalId,
            runId: commit.checkpoint!.runId,
            researchStage: commit.checkpoint!.researchStage,
            directionDecision: commit.checkpoint!.directionDecision,
          }));
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          projectId,
          conversationId: resolvedConversationId,
          repository: discovered.repository,
          latestCheckpoint: graph.commits.find((commit) => Boolean(commit.checkpoint)) || null,
          completedResearchStages,
          workingTree: workingTree.files,
          financeReceipt,
          checkpointContract: {
            domain: checkpointDomain || null,
            allowedStages,
            required: ['message', 'stage', 'includePaths', 'verification'],
            routeModes: ['explore', 'deepen', 'fuse', 'repair', 'stop'],
            routeModeRequiredForStages,
            routeModeRule:
              routeModeRequiredForStages.length > 0
                ? `routeMode is required for these research stages: ${routeModeRequiredForStages.join(', ')}. Project initialization and presentation-only stages are exempt.`
                : 'routeMode is optional for the stages in this project.',
            verificationShapes: [
              'string',
              '{command, exitCode, summary}',
              '[{command, exitCode, summary}]',
              '{checks:[{command, exitCode, summary}]}',
            ],
            researchStage:
              'When Discovery Mode is active, include stageId, objective, successCriteria, failureCriteria, priorWorkRefs, disposition, supportingEvidenceIds, refutingEvidenceIds, exhaustionEvidenceIds, beliefDelta, reflection, and optional nextObjective.',
            directionDecision:
              'Optional only when this checkpoint records a material route choice. Include schema=deepscientist.direction.v1, choice, one concise reason, 1-4 evidence/artifact/commit basisRefs, and nextTest/stopIf when the route continues. Omit it for routine progress.',
            directionDecisionExample: {
              schema: 'deepscientist.direction.v1',
              choice: 'advance',
              reason: 'The current result removes the main uncertainty and makes the bounded validation decisive.',
              basisRefs: [{ kind: 'commit', ref: 'HEAD', label: 'verified baseline' }],
              nextTest: 'Run the smallest validation that separates the remaining explanations.',
              stopIf: 'Stop this route if the declared primary endpoint misses its threshold.',
            },
            researchStageExample: {
              stageId: 'stage-verify-assumption',
              objective: 'Test the highest-value unresolved assumption.',
              successCriteria: ['A reproducible result supports the assumption within the declared scope.'],
              failureCriteria: ['A reproducible witness refutes it, or the declared search region is exhausted.'],
              priorWorkRefs: ['checkpoint:<prior-commit-or-stage-id>'],
              disposition: 'inconclusive',
              supportingEvidenceIds: [],
              refutingEvidenceIds: [],
              exhaustionEvidenceIds: [],
              beliefDelta: 'The available evidence did not resolve the assumption.',
              reflection: 'Change the method or search region before retrying.',
              nextObjective: 'Run the next highest-information verification.',
            },
            example: {
              message: 'Record a verified stage result',
              stage: routeModeRequiredForStages[0] || allowedStages[0] || '<allowed-stage>',
              ...(routeModeRequiredForStages.length > 0 ? { routeMode: 'deepen' } : {}),
              includePaths: ['README.md', 'results/stage-result.json'],
              verification: [{ command: 'test command', exitCode: 0, summary: 'completed' }],
            },
          },
          displayIntent: displayIntent || 'background',
        });
      }

      const requestedRun = effectiveRunId ? ensureRun(effectiveRunId, resolvedProjectRoot, body) : undefined;
      if (requestedRun) {
        applyRunContext(requestedRun, body, { conversationId: resolvedConversationId });
      }

      if (action === 'frontier') {
        const routeState = requestedRun ? researchRouteForRun(requestedRun) : undefined;
        const frontier = listProjectGitResearchFrontier({
          workspace: resolvedProjectRoot,
          goalId: asString(body.goalId || body.goal_id, routeState?.map?.goalId || (undefined as unknown as string)),
        });
        if (!frontier.ok) throw new Error(frontier.error || 'The project frontier could not be read.');
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          projectId,
          conversationId: resolvedConversationId,
          frontier,
          researchRoute: routeState?.presentation || null,
          displayIntent: displayIntent || 'background',
        });
      }

      if (action === 'prepare_branch') {
        const branch = asString(body.branch || body.name, undefined as unknown as string);
        const routeNodeId = asString(body.routeNodeId || body.route_node_id, undefined as unknown as string);
        const routeSelection = requireAnsweredResearchRouteBranchSelection(requestedRun, routeNodeId);
        if (routeSelection.node?.git?.branchRef) {
          throw new Error('The selected project route already owns a Git branch; activate that branch instead.');
        }
        const prepared = prepareProjectGitResearchBranch({
          workspace: resolvedProjectRoot,
          branch,
          from: asString(body.from || body.fromSha || body.from_sha || body.startPoint || body.start_point, 'HEAD'),
          parentRef: asString(body.parentRef || body.parent_ref, undefined as unknown as string),
          goalId: asString(body.goalId || body.goal_id, undefined as unknown as string),
          routeNodeId,
          objective: asString(body.objective || body.reason, undefined as unknown as string),
        });
        if (!prepared.ok || !prepared.branch)
          throw new Error(prepared.error || 'The project branch could not be prepared.');
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          projectId,
          conversationId: resolvedConversationId,
          branch: prepared.branch,
          displayIntent: displayIntent || 'background',
        });
      }

      if (action === 'activate_branch') {
        const branch = asString(body.branch || body.name, undefined as unknown as string);
        const routeNodeId = asString(body.routeNodeId || body.route_node_id, undefined as unknown as string);
        const routeSelection = requireAnsweredResearchRouteBranchSelection(requestedRun, routeNodeId);
        if (routeSelection.node && routeSelection.node.git?.branchRef !== branch) {
          throw new Error('The requested branch does not match the selected project route.');
        }
        const activated = activateProjectGitResearchBranch({
          workspace: resolvedProjectRoot,
          branch,
          routeNodeId,
        });
        if (!activated.ok || !activated.branch) {
          throw new Error(activated.error || 'The project branch could not be activated.');
        }
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          projectId,
          conversationId: resolvedConversationId,
          branch: activated.branch,
          displayIntent: displayIntent || 'background',
        });
      }

      if (action === 'compare_branches') {
        const compared = compareProjectGitResearchBranches({
          workspace: resolvedProjectRoot,
          baseRef: asString(body.baseRef || body.base_ref || body.base, undefined as unknown as string),
          headRef: asString(body.headRef || body.head_ref || body.head, undefined as unknown as string),
        });
        if (!compared.ok) throw new Error(compared.error || 'The project branches could not be compared.');
        return jsonText({
          tool: PROJECT_WORKSPACE_TOOL_NAME,
          action,
          projectId,
          conversationId: resolvedConversationId,
          comparison: compared,
          displayIntent: displayIntent || 'background',
        });
      }

      const includePaths = normalizeIncludePaths(body.includePaths || body.include_paths || body.paths);
      const linkedArtifact =
        requestedRun && target?.kind === 'artifact' && target.id
          ? requestedRun.artifacts.get(artifactKey(target.id, target.version || 1))
          : undefined;
      const targetPortfolio = readTargetDiscoveryPortfolio(linkedArtifact?.metadata);
      const factorPortfolio = readFinancialFactorPortfolio(linkedArtifact?.metadata);
      const mathematicsPortfolio = readMathematicsPortfolio(linkedArtifact?.metadata);
      const requestedStage = asString(
        body.stage || (targetPortfolio ? `target-${targetPortfolio.stage.replaceAll('_', '-')}` : undefined),
        ''
      );
      if (!requestedStage) {
        throw new Error('project_workspace checkpoint requires an explicit stage allowed by the active mode.');
      }
      const verification = normalizeCheckpointVerification(body.verification || body.validations);
      if (verification.length === 0) {
        throw new Error('project_workspace checkpoint requires at least one completed verification entry.');
      }
      const domain = resolveBoundProjectDomain(
        body.domain || body.workflow,
        targetPortfolio
          ? 'target_discovery'
          : factorPortfolio
            ? 'financial_factor'
            : mathematicsPortfolio
              ? 'mathematics'
              : 'general'
      );
      const requestedResearchStrategy = body.routeMode || body.route_mode || body.strategy;
      const explicitResearchStrategy = normalizeResearchStrategy(requestedResearchStrategy);
      if (requestedResearchStrategy && !explicitResearchStrategy) {
        throw new Error('project_workspace checkpoint received an invalid research strategy.');
      }
      const researchStage = normalizeResearchStageReceipt(body.researchStage || body.research_stage);
      const requestedDirectionDecision = body.directionDecision || body.direction_decision;
      const directionDecision = normalizeProjectGitDirectionDecision(requestedDirectionDecision);
      if (requestedDirectionDecision && !directionDecision) {
        throw new Error(
          'project_workspace checkpoint received an invalid directionDecision. Use schema=deepscientist.direction.v1, a valid choice, a concise reason, and 1-4 evidence, artifact, or commit basisRefs.'
        );
      }
      const roadmap = requestedRun ? researchRouteForRun(requestedRun).map : undefined;
      const explicitRouteNodeId = asString(body.routeNodeId || body.route_node_id, '');
      const inferredRouteNode = roadmap
        ? roadmap.nodes.find(
            (node) =>
              node.id === explicitRouteNodeId ||
              node.id === researchStage?.stageId ||
              (!explicitRouteNodeId && !researchStage?.stageId && node.id === roadmap.focusNodeId)
          )
        : undefined;
      if (roadmap && explicitRouteNodeId && !inferredRouteNode) {
        throw new Error('project_workspace checkpoint routeNodeId does not exist in the active research roadmap.');
      }
      const expectedResearchStrategy = inferredRouteNode?.strategy || roadmap?.routeMode;
      if (
        explicitResearchStrategy &&
        expectedResearchStrategy &&
        explicitResearchStrategy !== expectedResearchStrategy
      ) {
        throw new Error('project_workspace checkpoint strategy conflicts with the active research route.');
      }
      const researchStrategy = explicitResearchStrategy || expectedResearchStrategy;
      const routeNodeId = explicitRouteNodeId || inferredRouteNode?.id;
      const repairsNodeId =
        asString(body.repairsNodeId || body.repairs_node_id, '') || inferredRouteNode?.repairsNodeId;
      if (requiresResearchStrategyForCheckpoint(domain, requestedStage) && !researchStrategy) {
        throw new Error(
          `project_workspace checkpoint stage ${requestedStage} requires payload.routeMode: explore, deepen, fuse, repair, or stop.`
        );
      }
      const checkpoint = createProjectGitCheckpoint({
        workspace: resolvedProjectRoot,
        message: asString(body.message || body.summary, undefined as unknown as string),
        stage: resolveBoundCheckpointStage(requestedStage),
        researchStrategy,
        routeNodeId,
        repairsNodeId,
        includePaths: includePaths.map((item) => item.path),
        verification,
        metrics: normalizeCheckpointMetrics(
          body.metrics || body.performanceMetrics || body.performance_metrics || body.metric
        ),
        metricContext: normalizeMetricContext(
          body.metricContext || body.metric_context || body.evaluationContext || body.evaluation_context
        ),
        goalId: asString(body.goalId || body.goal_id, undefined as unknown as string),
        researchStage,
        directionDecision,
        runId: requestedRun?.runId || effectiveRunId,
        conversationId: resolvedConversationId,
        domain,
        artifactRef: linkedArtifact
          ? {
              runId: requestedRun?.runId || effectiveRunId || '',
              artifactId: linkedArtifact.id,
              version: linkedArtifact.version,
              revision: linkedArtifact.revision,
            }
          : undefined,
        targetSummary: targetPortfolio ? summarizeTargetDiscoveryPortfolio(targetPortfolio) : undefined,
      });
      if (!checkpoint.ok || !checkpoint.commit || !checkpoint.shortCommit || !checkpoint.subject) {
        throw new Error(checkpoint.error || 'The project Git checkpoint could not be created.');
      }
      const sourceGit: ScienceSourceGitRef = {
        repoRoot: checkpoint.repository?.repoRoot,
        branch: checkpoint.repository?.branch,
        commit: checkpoint.commit,
        shortCommit: checkpoint.shortCommit,
        subject: checkpoint.subject,
        stage: checkpoint.stage,
        researchStrategy: checkpoint.researchStrategy,
        routeNodeId: checkpoint.routeNodeId,
        repairsNodeId: checkpoint.repairsNodeId,
        domain: checkpoint.domain,
        artifactRef: checkpoint.artifactRef,
        targetSummary: checkpoint.targetSummary,
        changedFiles: checkpoint.changedFiles,
        verification: checkpoint.verification,
        metrics: checkpoint.metrics,
        metricContext: checkpoint.metricContext,
        goalId: checkpoint.goalId,
        researchStage: checkpoint.researchStage,
        directionDecision: checkpoint.directionDecision,
      };
      if (requestedRun) requestedRun.sourceGit = sourceGit;
      return jsonText({
        tool: PROJECT_WORKSPACE_TOOL_NAME,
        action,
        projectId,
        conversationId: resolvedConversationId,
        checkpoint: sourceGit,
        displayIntent: displayIntent || 'background',
      });
    }
  );

  if (!workspaceActions.length) workspaceTool.disable();

  

  

  

  

  

  

  if (!isMathLiteRunEnvironment(process.env)) {
    const { registerMathResearchCompatibilityTool } = await import("./mathResearchCompatibility");
    registerMathResearchCompatibilityTool(server, resolveModeProjectRoot);
  }

  const leanDependencyCandidateInput = z
    .object({
      source: z.literal('reservoir'),
      packageName: z.string().trim().min(1).max(128),
      repositoryFullName: z.string().trim().min(1).max(256),
      repositoryUrl: z.string().url().max(512),
      revision: z.string().regex(/^[a-f0-9]{40}$/u),
      version: z.string().max(128).optional(),
      license: z.string().trim().min(1).max(256),
      buildStatus: z.literal('built'),
      compatibility: z.literal('exact'),
      adoptionStatus: z.literal('eligible'),
      leanToolchain: z.string().max(256).optional(),
      mathlibRevision: z.string().max(256).optional(),
    })
    .strict();

  // Fail closed for malformed policy; advertise only actions the runtime permits.
  readResearchTeamToolPolicy();
  const allowedLeanActions = mathWorkspaceActions.filter((action) => {
    try {
      assertResearchTeamToolActionAuthorized('lean_workspace', action);
      return true;
    } catch {
      return false;
    }
  });
  const leanWorkspaceInput = {
    action: allowedLeanActions.length
      ? z.enum([allowedLeanActions[0]!, ...allowedLeanActions.slice(1)], {
          errorMap: () => ({ message: 'This action is not authorized for lean_workspace in the current role.' }),
        })
      : z.never(),
    proofSession: z
      .object({
        sourceFile: z.string().min(1).max(1024).optional(),
        expectedSourceHash: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        projectRelative: z.string().max(1024).optional(),
        searchMode: z.enum(['auto', 'provided', 'premises', 'generic']).optional(),
        lookahead: z.boolean().optional(),
        premiseQuery: z.string().max(4000).optional(),
        premiseLimit: z.number().int().min(1).max(32).optional(),
        applyBest: z.boolean().optional(),
        branchId: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        branchOffset: z.number().int().nonnegative().optional(),
        branchPageSize: z.number().int().positive().max(128).optional(),
        branchGeneration: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        goalIndex: z.number().int().nonnegative().optional(),
        candidateOffset: z.number().int().nonnegative().optional(),
        candidateBatchSize: z.number().int().positive().max(128).optional(),
        candidateSetHash: z
          .string()
          .regex(/^[a-f0-9]{64}$/u)
          .optional(),
        candidates: z
          .array(
            z
              .object({
                kind: z.enum(['tactic', 'premise', 'rewrite', 'constructor', 'cases', 'induction', 'helper', 'import']),
                payload: z.string().min(1).max(12000),
                source: z.string().min(1).max(2_000_000),
              })
              .strict()
          )
          .max(128)
          .optional(),
      })
      .strict()
      .optional(),
    synthesis: mathSynthesisInputSchema.optional(),
    packageCandidate: leanDependencyCandidateInput.optional(),
    packageCandidates: z.array(leanDependencyCandidateInput).min(1).max(8).optional(),
    counterexample: z
      .object({
        expression: z.string().min(1).max(12000),
        precondition: z.string().max(12000).optional(),
        cases: z.array(z.string().min(1).max(12000)).min(1).max(16).optional(),
        sampleDesign: z
          .union([
            z
              .object({
                kind: z.literal('integer_range'),
                min: z.number().int(),
                max: z.number().int(),
                count: z.number().int().min(1).max(16),
                seed: z.string().min(1).max(256),
                includeBoundaries: z.boolean().optional(),
              })
              .strict(),
            z
              .object({
                kind: z.enum(['integer_list', 'rational_grid', 'finite_graph', 'finite_operation']),
                count: z.number().int().min(1).max(16),
                seed: z.string().min(1).max(256),
                min: z.number().int().optional(),
                max: z.number().int().optional(),
                maxLength: z.number().int().nonnegative().optional(),
                denominatorMax: z.number().int().positive().optional(),
                vertices: z.number().int().nonnegative().optional(),
                carrierSize: z.number().int().positive().optional(),
              })
              .strict(),
          ])
          .optional(),
        minimizeWitness: z.boolean().optional(),
        question: z.string().min(1).max(4000).optional(),
        expectedObservation: z.string().min(1).max(4000).optional(),
        mode: z.enum(['proposition', 'boolean']).optional(),
        imports: z
          .array(z.string().regex(/^[A-Za-z][A-Za-z0-9_.]*$/u))
          .max(16)
          .optional(),
      })
      .strict()
      .refine(
        (value) => Boolean(value.cases) !== Boolean(value.sampleDesign),
        'Supply exactly one of cases or sampleDesign'
      )
      .optional(),
    exploration: mathExplorationInput.optional(),
    routeRefutation: z
      .object({
        planNodeId: z.string().min(1),
        proofPath: z.string().min(1).optional(),
        theoremName: z.string().min(1).optional(),
      })
      .strict()
      .optional(),
    assignmentId: z
      .string()
      .min(1)
      .max(160)
      .optional()
      .describe(
        'In lite Mathematics runs, omit this field to bind the current accepted Worker assignment automatically. An explicit value must be copied exactly from the runtime-issued assignment identity.'
      ),
    runId: z.string().optional(),
    conversationId: z.string().optional(),
    messageId: z.string().optional(),
    toolCallId: z.string().optional(),
    projectRoot: z.string().optional(),
    targetCommit: z.string().optional(),
    timeoutMs: z
      .number()
      .int()
      .positive()
      .max(24 * 60 * 60 * 1000)
      .optional(),
    items: z.array(mathematicsVerifierItemInput).min(1).max(64).optional(),
    operations: z.array(leanWorkspaceOperationInput).min(1).max(64).optional(),
    probeMode: z
      .enum(['compile', 'check', 'exact', 'apply', 'simp'])
      .optional()
      .describe(
        'For an ordinary lite formalization checkpoint, send only action="probe". The runtime selects the assigned candidate. Set a mode for an explicit auxiliary file or expression experiment.'
      ),
    sourceProbe: leanSourceProbeInput
      .optional()
      .describe(
        'A tactic experiment at an exact committed source span. Requires current commit, source and span hashes. For an ordinary lite formalization checkpoint, send only action="probe"; source positions are derived by the runtime.'
      ),
    probeExpression: z.string().max(12000).optional(),
    probeSourceFile: z.string().max(1024).optional(),
    probeImportModules: z.array(z.string()).max(16).optional(),
    displayIntent: z.enum(['background', 'open', 'focus']).optional(),
  };

  server.tool(
    'lean_workspace',
    LEAN_WORKSPACE_TOOL_DESCRIPTION,
    leanWorkspaceInput,
    withMathToolRecovery<typeof leanWorkspaceInput>(
      async (
        {
          action,
          runId: requestedRunId,
          conversationId,
          messageId,
          toolCallId,
          projectRoot,
          targetCommit,
          timeoutMs,
          items,
          operations,
          probeMode,
          sourceProbe,
          synthesis,
          proofSession,
          packageCandidate,
          packageCandidates,
          exploration,
          counterexample,
          routeRefutation,
          assignmentId: requestedAssignmentId,
          probeExpression,
          probeSourceFile,
          probeImportModules,
          displayIntent,
        },
        extra
      ) => {
        const checkpointTiming = createMathToolTiming();
        let assignmentId = requestedAssignmentId;
        assertResearchTeamToolActionAuthorized('lean_workspace', action);
        if (action !== 'describe' && action !== 'events') assertMathMcpRunning();
        if (action === 'describe') {
          return jsonStructured({
            tool: 'lean_workspace',
            action,
            schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
            contract: {
              actions: Object.fromEntries(
                allowedLeanActions.map((name) => [name, mathWorkspaceActionContract[name].description])
              ),
              authorities: {
                agent: 'Public formula and Goal observations; never proof authority.',
                'lean-process': 'Diagnostics and draft state produced by a Lean adapter.',
                'lean-kernel': 'Successful committed-source certification; the only Kernel verified authority.',
              },
              batching: {
                maxItems: 64,
                maxOperations: 64,
                sameFilePolicy: 'one Lean process per unique proofPath, then separate per-theorem receipts',
                failurePolicy: 'per-item results are preserved; failed siblings do not erase successful receipts',
              },
              tracePath: MATHEMATICS_VERIFICATION_TRACE_PATH,
              reportHandoff: {
                artifactType: 'figure',
                viewerKind: 'proof_trace',
                embedRenderer: 'proof_trace',
                pathPolicy:
                  'artifactDraft primaryPath and viewer.dataPath are the same content-addressed project-relative reportTracePath',
                authorityPolicy: 'Only lean-kernel events may render as Kernel verified',
              },
              progressPolicy: 'Exact event/count/time values only. No inferred percentage or synthetic activity.',
            },
            displayIntent: displayIntent || 'background',
          });
        }

        const resolvedConversationId = resolveSessionIdentifier(
          conversationId,
          PROJECT_WORKSPACE_ENV_KEYS.conversationId,
          'conversationId'
        );
        const resolvedProjectRoot = await resolveLeanWorkspaceProjectRoot(projectRoot, resolvedConversationId);
        if (!resolvedProjectRoot) {
          throw new Error(
            'lean_workspace requires the current project root. Reopen the task if the runtime did not bind one.'
          );
        }
        const run = ensureRun(
          stableMathematicsRunId(requestedRunId, resolvedProjectRoot, resolvedConversationId),
          resolvedProjectRoot,
          { question: 'Lean workspace' }
        );
        applyRunContext(run, undefined, { conversationId: resolvedConversationId, messageId, toolCallId });
        let liteResearchAssignment = false;
        let probeAssignmentContext: MathAssignmentContext | undefined;
        if (
          isMathLiteRunEnvironment(process.env) &&
          [
            'synthesize',
            'search',
            'probe',
            'branches',
            'checkout',
            'check_connection',
            'counterexample',
            'execute',
            'certify',
            'preflight',
            'events',
            'refute_route',
            'adopt_package',
            'adopt_packages',
          ].includes(action)
        ) {
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (capability?.roleKind === 'worker') {
            if (fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot))
              throw new Error('math_tool_project_identity');
            const receipts = listProjectGitResearchTeamAssignments({
              workspace: resolvedProjectRoot,
              teamId: capability.teamId,
              strict: true,
            });
            // Preserve standalone checks before a Lean slot has an accepted task.
            // An accepted research task always follows its own private probe scope.
            const standaloneProbe =
              action === 'probe' &&
              !assignmentId &&
              !proofSession &&
              Boolean(probeMode || sourceProbe || probeExpression || probeSourceFile) &&
              capability.roster.find((member) => member.slotId === capability.slotId)?.laneId === 'lean-engineering' &&
              !receipts.some((item) => item.slotId === capability.slotId && item.state === 'accepted');
            if (!standaloneProbe) {
              assignmentId = bindMathToolAssignment(capability, assignmentId, extra.signal);
              const receipt = receipts.find((item) => item.assignmentId === assignmentId);
              if (
                !receipt ||
                receipt.state !== 'accepted' ||
                receipt.delivery ||
                receipt.integration ||
                receipt.supersessionPending ||
                receipt.budgetCancellation ||
                receipt.slotId !== capability.slotId
              )
                throw new Error(
                  receipt?.budgetCancellation
                    ? 'Lean operations require the current uncancelled Worker assignment.'
                    : action === 'synthesize'
                      ? 'math_synthesis_assignment_unavailable'
                      : 'math_tool_assignment_unavailable: Omit assignmentId to bind the current assignment automatically, or copy its exact runtime-supplied ID. Keep the existing worktree; do not create another task.'
                );
              if (receipt.schema === 'deepscientist.research_team_assignment.v2') {
                const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!)));
                const view = projectRuntimeMathAssignmentToExecutionView(receipt.assignment, {
                  expectedRunId: binding.runId,
                  expectedBindingDigest: mathDigest(canonicalMathJson(binding)),
                  expectedTargetSlotId: capability.slotId,
                  ...(receipt.preparedGit?.baseCommit ? { expectedBaseCommit: receipt.preparedGit.baseCommit } : {}),
                });
                liteResearchAssignment = view.kind === 'research';
                if (action === 'probe' && view.kind === 'formalize' && (sourceProbe || probeSourceFile))
                  probeAssignmentContext = resolveMathAssignmentContext({
                    receipt,
                    projectRoot: resolvedProjectRoot,
                    expectedTeamId: capability.teamId,
                    expectedSlotId: capability.slotId,
                    expectedAssignmentId: assignmentId,
                  });
              } else {
                // Legacy v1 records have no assignment kind. Preserve their
                // lane-bound scope and fail closed for strategy Workers rather
                // than treating an unknown legacy task as formalization.
                liteResearchAssignment =
                  capability.roster.find((member) => member.slotId === capability.slotId)?.laneId !==
                  'lean-engineering';
              }
            }
            // A slot advertises its maximum capability. The current assignment
            // may narrow it to research, even on a Lean engineering slot.
            if (
              liteResearchAssignment &&
              action !== 'probe' &&
              !mathWorkspaceActionContract[action].roles.includes('researcher')
            )
              throw new Error(`lean_workspace ${action} is not authorized for a research assignment.`);
          }
        }
        if (action === 'synthesize') {
          if (!assignmentId || !synthesis) throw new Error('synthesize requires assignmentId and synthesis.');
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (!capability) throw new Error('synthesize requires an authenticated mathematics Team assignment.');
          const response = await executeMathSynthesis({
            capability,
            projectRoot: resolvedProjectRoot,
            assignmentId,
            synthesis,
            signal: extra.signal,
            deadlineAt: Date.now() + Math.min(timeoutMs ?? 30_000, 120_000),
          });
          return jsonStructured({ tool: 'lean_workspace', action, assignmentId, ...response });
        }
        const checkpointResponse = async (payload: Record<string, unknown>) => {
          extra.signal.throwIfAborted();
          let enrichment: Record<string, unknown> = {};
          try {
            if (isMathLiteRunEnvironment(process.env)) {
              const capability = await resolveResearchTeamRuntimeCapability(undefined);
              if (
                capability?.roleKind === 'worker' &&
                fs.realpathSync(capability.projectRoot) === fs.realpathSync(resolvedProjectRoot)
              )
                enrichment = await enrichMathLeanCheckpoint({ capability, payload, signal: extra.signal });
            }
          } catch (error) {
            extra.signal.throwIfAborted();
            if (isMathPlanningSafetyError(error)) throw error;
            enrichment = {
              planningContext: {
                status: 'unavailable',
                instruction: 'Lean result is unchanged. Retry research_team read_feedback for current findings.',
              },
            };
          }
          extra.signal.throwIfAborted();
          return jsonStructured({
            ...(isMathLiteRunEnvironment(process.env) ? compactMathLeanProbeResponse(payload) : payload),
            timing: checkpointTiming(),
            ...enrichment,
          });
        };

        if (action === 'adopt_package' || action === 'adopt_packages') {
          const candidates =
            action === 'adopt_package' ? (packageCandidate ? [packageCandidate] : undefined) : packageCandidates;
          if (!assignmentId || !candidates?.length)
            throw new Error(
              action === 'adopt_package'
                ? 'adopt_package requires assignmentId and packageCandidate.'
                : 'adopt_packages requires assignmentId and packageCandidates.'
            );
          if (extra.signal.aborted) throw new Error('Dependency adoption request was aborted before execution.');
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (!capability || capability.roleKind !== 'worker')
            throw new Error('adopt_package requires an authenticated Lean Worker.');
          if (fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot))
            throw new Error('Dependency adoption project does not match the Worker capability.');
          const receipt = listProjectGitResearchTeamAssignments({
            workspace: resolvedProjectRoot,
            teamId: capability.teamId,
            strict: true,
          }).find((item) => item.assignmentId === assignmentId);
          if (!receipt || receipt.state !== 'accepted' || receipt.slotId !== capability.slotId)
            throw new Error('adopt_package requires the active assigned Worker.');
          const assignmentContext = resolveMathAssignmentContext({
            receipt,
            projectRoot: resolvedProjectRoot,
            expectedTeamId: capability.teamId,
            expectedSlotId: capability.slotId,
            expectedAssignmentId: assignmentId,
          });
          if (!assignmentContext.routeRevisionsSupported)
            throw new Error('Dependency adoption requires a formalization assignment.');
          if (
            assignmentContext.protocol === 'v2' ||
            readMathRunRetrievalCorpus(process.env, path.resolve(process.argv[1]))
          )
            throw new Error('Dependency adoption is forbidden for a frozen mathematics run.');
          const workspaceRoot = receipt.preparedGit?.worktreePath || resolvedProjectRoot;
          const adoption =
            action === 'adopt_package'
              ? await adoptUpstreamLeanPackage({
                  projectRoot: workspaceRoot,
                  package: candidates[0] as Parameters<typeof adoptUpstreamLeanPackage>[0]['package'],
                  timeoutMs,
                })
              : await adoptUpstreamLeanPackages({
                  projectRoot: workspaceRoot,
                  packages: candidates as Parameters<typeof adoptUpstreamLeanPackages>[0]['packages'],
                  timeoutMs,
                });
          const adoptionSucceeded = adoption.status === 'adopted' || adoption.status === 'already_present';
          return jsonStructured({
            tool: 'lean_workspace',
            action,
            assignmentId,
            result: adoption,
            authority: adoptionSucceeded ? 'lake-manifest' : 'lean-process',
            solverReady: false,
            ...(adoption.status === 'adopted' ? { restartSessionRequired: true } : {}),
          });
        }

        if (
          action === 'search' ||
          action === 'branches' ||
          action === 'checkout' ||
          (action === 'probe' &&
            (proofSession ||
              (isMathLiteRunEnvironment(process.env) &&
                !probeMode &&
                !sourceProbe &&
                !probeExpression &&
                !probeSourceFile)))
        ) {
          const liteRun = isMathLiteRunEnvironment(process.env);
          if (!assignmentId || (!proofSession && action !== 'probe'))
            throw new Error('Worker proof construction requires assignmentId and proofSession.');
          if ((action === 'search' || action === 'checkout') && !proofSession?.expectedSourceHash)
            throw new Error('Proof search and checkout require expectedSourceHash for the active source.');
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (!capability || capability.roleKind !== 'worker')
            throw new Error('Worker proof construction requires an authenticated Worker.');
          if (fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot))
            throw new Error('Worker proof project does not match its capability.');
          const receipt = listProjectGitResearchTeamAssignments({
            workspace: resolvedProjectRoot,
            teamId: capability.teamId,
            strict: true,
          }).find((item) => item.assignmentId === assignmentId);
          if (!receipt || receipt.state !== 'accepted' || receipt.slotId !== capability.slotId)
            throw new Error('Worker proof construction requires the active assigned Worker.');
          const assignmentContext = resolveMathAssignmentContext({
            receipt,
            projectRoot: resolvedProjectRoot,
            expectedTeamId: capability.teamId,
            expectedSlotId: capability.slotId,
            expectedAssignmentId: assignmentId,
          });
          if (!assignmentContext.routeRevisionsSupported)
            throw new Error('Worker proof construction requires a direct formalization assignment.');
          const inferredSourceFile =
            action === 'probe' && liteRun && !proofSession?.sourceFile
              ? (() => {
                  const sourcePaths = [
                    ...new Set(assignmentContext.verificationTargets.map((target) => target.pathRelative)),
                  ];
                  return sourcePaths.length === 1 && assignmentContext.sourceRootRelative
                    ? path.posix.join(assignmentContext.sourceRootRelative, sourcePaths[0]!)
                    : undefined;
                })()
              : proofSession?.sourceFile;
          if (!inferredSourceFile) {
            throw new Error(
              action === 'probe' && liteRun
                ? 'A lite proof probe with verification targets in multiple source files requires proofSession.sourceFile.'
                : 'Worker proof construction requires proofSession.sourceFile.'
            );
          }
          const activeProofSession = { ...proofSession, sourceFile: inferredSourceFile };
          if (action === 'search')
            resolveMathSearchPlan({
              searchMode: activeProofSession.searchMode,
              candidateCount: activeProofSession.candidates?.length ?? 0,
              premiseQuery: activeProofSession.premiseQuery,
              lookahead: activeProofSession.lookahead,
            });

          const workspaceRoot = receipt.preparedGit?.worktreePath || resolvedProjectRoot;
          const frozenCorpus = readMathRunRetrievalCorpus(process.env, path.resolve(process.argv[1]));
          let boundProjectRelative: string | undefined;
          let originalContractSource: string | undefined;
          if (assignmentContext.protocol === 'v2') {
            const encoded = process.env[MATH_RUN_INPUTS_ENV];
            if (!encoded) throw new Error('Mathematics run binding is unavailable.');
            const binding = readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded)));
            if (new Set(assignmentContext.verificationTargets.map((target) => target.pathRelative)).size === 1)
              originalContractSource = binding.problem?.formalStatement;
            const paths = resolveMathRunProjectPaths(binding, capability.projectRoot, workspaceRoot);
            if (
              receipt.preparedGit?.solverProjectRoot &&
              receipt.preparedGit.solverProjectRoot !== paths.solverProjectRoot
            )
              throw new Error('Worker proof project does not match its worktree binding.');
            boundProjectRelative = path.relative(workspaceRoot, paths.solverProjectRoot).split(path.sep).join('/');
            if (frozenCorpus && (frozenCorpus.projectSubdirectory ?? '') !== boundProjectRelative)
              throw new Error('Proof session project binding does not match the frozen corpus.');
          }
          const frozenProjectRelative = boundProjectRelative ?? frozenCorpus?.projectSubdirectory;
          if (
            (assignmentContext.protocol === 'v2' || frozenCorpus) &&
            activeProofSession.projectRelative !== undefined &&
            activeProofSession.projectRelative !== (frozenProjectRelative ?? '')
          )
            throw new Error('Proof session projectRelative must match the frozen project mapping.');
          const projectRelative = frozenProjectRelative ?? activeProofSession.projectRelative;
          activeProofSession.sourceFile = resolveMathAssignmentProofSource(
            assignmentContext,
            activeProofSession.sourceFile,
            projectRelative
          );
          const boundSourcePath = [projectRelative, activeProofSession.sourceFile].filter(Boolean).join('/');
          const assignmentSourcePath =
            assignmentContext.protocol === 'v2' ? activeProofSession.sourceFile : boundSourcePath;
          if (!isAllowedMathProofSource(boundSourcePath))
            throw new Error('Proof session source path is not an allowed candidate.');
          if (
            assignmentContext.artifactPaths.length > 0 &&
            !assignmentContext.artifactPaths.includes(assignmentSourcePath)
          )
            throw new Error('Proof session source is not owned by the active assignment.');
          const sourceParts = boundSourcePath.replaceAll('\\', '/').split('/');
          if (
            sourceParts.some((part) => !part || part === '.' || part === '..') ||
            path.isAbsolute(boundSourcePath) ||
            /^[A-Za-z]:/u.test(boundSourcePath)
          )
            throw new Error('Proof session source path is invalid.');
          let sourcePath = fs.realpathSync(workspaceRoot);
          for (const part of sourceParts) {
            sourcePath = path.join(sourcePath, part);
            const stat = fs.lstatSync(sourcePath);
            if (stat.isSymbolicLink()) throw new Error('Proof session source path contains a symlink.');
          }
          const expectedSourceHash = activeProofSession.expectedSourceHash ?? mathDigest(fs.readFileSync(sourcePath));
          const workflow = liteRun
            ? undefined
            : readMathResearchWorkflowState(resolvedProjectRoot, assignmentContext.problemId, assignmentId);
          if (
            workflow &&
            (workflow.binding.teamId !== capability.teamId ||
              workflow.binding.slotId !== receipt.slotId ||
              workflow.binding.assignmentDigest !== assignmentContext.assignmentDigest)
          )
            throw new Error('Worker proof research state does not match its durable assignment.');
          const routeFingerprint = workflow?.route.fingerprint ?? assignmentContext.initialRouteFingerprint;
          const routeRevision = workflow?.route.revision ?? 0;
          const acceptedRouteFingerprints = [
            assignmentContext.initialRouteFingerprint,
            ...(workflow?.decisions
              .filter((decision) => decision.decision === 'accept')
              .map((decision) => decision.fingerprint) ?? []),
          ];
          const premiseProvider =
            action === 'search' &&
            (activeProofSession.searchMode === 'premises' ||
              (activeProofSession.searchMode === undefined && Boolean(activeProofSession.premiseQuery?.trim())) ||
              (activeProofSession.searchMode === 'auto' && Boolean(activeProofSession.premiseQuery?.trim())))
              ? async (
                  view: MathValidatedGoalView,
                  context?: Readonly<{ signal?: AbortSignal; remainingTimeoutMs?: number }>
                ) => {
                  if (context?.signal?.aborted ?? extra.signal.aborted) throw new Error('math_search_aborted');
                  if (!frozenCorpus) throw new Error('math_search_frozen_corpus_unavailable');
                  const retrieved = searchMathRetrievalCorpus(
                    workspaceRoot,
                    frozenCorpus,
                    [activeProofSession.premiseQuery ?? '', view.goal],
                    activeProofSession.premiseLimit ?? 4,
                    0
                  );
                  if (context?.signal?.aborted ?? extra.signal.aborted) throw new Error('math_search_aborted');
                  return retrieved.premises.map((premise) => ({
                    name: premise.declarationName,
                    type: premise.declarationType,
                    packageName: premise.packageName,
                    packageRevision: premise.packageRevision,
                    sourceModule: premise.sourceModule,
                    sourceFile: premise.sourceFile,
                    providerRank: premise.providerRank,
                    corpusDigest: retrieved.corpusDigest,
                  }));
                }
              : undefined;
          assertMathMcpRunning();
          let discoveryObstructions: readonly import("../math/mathDiscoveryFrontier").MathDiscoveryObstruction[] =
            [];
          const result = await runMathWorkerProofAction({
            workspaceRoot,
            sourceFile: activeProofSession.sourceFile,
            ...(projectRelative ? { projectRelative } : {}),
            statementHash: assignmentContext.statementHash,
            ...(originalContractSource ? { contractSource: originalContractSource } : {}),
            initialRouteFingerprint: assignmentContext.initialRouteFingerprint,
            routeFingerprint,
            routeRevision,
            acceptedRouteFingerprints,
            validateActiveRoute: () => {
              const activeReceipt = listProjectGitResearchTeamAssignments({
                workspace: resolvedProjectRoot,
                teamId: capability.teamId,
                strict: true,
              }).find((item) => item.assignmentId === assignmentId);
              if (
                !activeReceipt ||
                activeReceipt.state !== 'accepted' ||
                activeReceipt.slotId !== receipt.slotId ||
                activeReceipt.slotId !== capability.slotId
              )
                return false;
              let activeAssignmentContext: typeof assignmentContext;
              try {
                activeAssignmentContext = resolveMathAssignmentContext({
                  receipt: activeReceipt,
                  projectRoot: resolvedProjectRoot,
                  expectedTeamId: capability.teamId,
                  expectedSlotId: capability.slotId,
                  expectedAssignmentId: assignmentId,
                });
              } catch {
                return false;
              }
              if (
                activeAssignmentContext.assignmentDigest !== assignmentContext.assignmentDigest ||
                activeAssignmentContext.statementHash !== assignmentContext.statementHash ||
                (activeAssignmentContext.artifactPaths.length > 0 &&
                  !activeAssignmentContext.artifactPaths.includes(assignmentSourcePath))
              )
                return false;
              if (liteRun) {
                return routeRevision === 0 && routeFingerprint === assignmentContext.initialRouteFingerprint;
              }
              const current = readMathResearchWorkflowState(
                resolvedProjectRoot,
                assignmentContext.problemId,
                assignmentId
              );
              return current
                ? current.binding.teamId === capability.teamId &&
                    current.binding.slotId === receipt.slotId &&
                    current.binding.assignmentDigest === assignmentContext.assignmentDigest &&
                    current.route.fingerprint === routeFingerprint &&
                    current.route.revision === routeRevision
                : routeRevision === 0 && routeFingerprint === assignmentContext.initialRouteFingerprint;
            },
            episodeId: assignmentId,
            expectedSourceHash,
            signal: extra.signal,
            ...(timeoutMs !== undefined ? { timeoutMs } : {}),
            problemId: assignmentContext.problemId,
            historyProjectRoot: resolvedProjectRoot,
            action,
            searchMode: activeProofSession.searchMode,
            ...(liteRun && action === 'search'
              ? {
                  checkedProofBlocks: (view, context) =>
                    collectMathCheckedProofSupport({
                      capability,
                      environmentId: view.environmentFingerprint ?? '',
                      proofSource: { file: activeProofSession.sourceFile, sha256: view.sourceHash },
                      onDiscoveryObstructions: (observations) => {
                        discoveryObstructions = observations;
                      },
                      signal: context?.signal ?? extra.signal,
                      deadlineAt: Date.now() + (context?.remainingTimeoutMs ?? timeoutMs ?? 30_000),
                    }),
                }
              : {}),
            lookahead: activeProofSession.lookahead,
            premiseQuery: activeProofSession.premiseQuery,
            ...(premiseProvider ? { premiseProvider } : {}),
            applyBest: activeProofSession.applyBest,
            branchId: activeProofSession.branchId,
            branchOffset: activeProofSession.branchOffset,
            branchPageSize: activeProofSession.branchPageSize,
            branchGeneration: activeProofSession.branchGeneration,
            includeBranchMetadata: !liteRun || action !== 'probe',
            goalIndex: activeProofSession.goalIndex,
            candidateOffset: activeProofSession.candidateOffset,
            candidateBatchSize: activeProofSession.candidateBatchSize,
            candidateSetHash: activeProofSession.candidateSetHash,
            candidates: activeProofSession.candidates?.map((candidate) => ({
              kind: candidate.kind!,
              payload: candidate.payload!,
              source: candidate.source!,
            })),
          });
          return checkpointResponse({
            tool: 'lean_workspace',
            action,
            assignmentId,
            routeFingerprint,
            result,
            ...(discoveryObstructions.length ? { discoveryObstructions } : {}),
            authority: 'lean-process',
            solverReady: false,
          });
        }

        if (action === 'counterexample') {
          if (!assignmentId || !counterexample?.expression)
            throw new Error('counterexample requires a bound assignmentId and explicit sample predicate.');
          readMathRunHistoryIdentity();
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (!capability) throw new Error('counterexample requires an authenticated Team assignment.');
          const receipt = listProjectGitResearchTeamAssignments({
            workspace: resolvedProjectRoot,
            teamId: capability.teamId,
            strict: true,
          }).find((item) => item.assignmentId === assignmentId);
          if (
            !receipt ||
            receipt.state !== 'accepted' ||
            (capability.roleKind === 'worker' && receipt.slotId !== capability.slotId)
          )
            throw new Error('counterexample requires the active assigned Worker.');
          const assignmentContext = resolveMathAssignmentContext({
            receipt,
            projectRoot: resolvedProjectRoot,
            expectedTeamId: capability.teamId,
            expectedSlotId: receipt.slotId,
            expectedAssignmentId: assignmentId,
          });
          const frozenCorpus = readMathRunRetrievalCorpus(process.env, path.resolve(process.argv[1]));
          const result = await runLeanEvalCounterexampleProbe({
            projectRoot: receipt.preparedGit?.worktreePath || resolvedProjectRoot,
            ...(frozenCorpus?.projectSubdirectory ? { projectRelative: frozenCorpus.projectSubdirectory } : {}),
            ...counterexample,
            expression: counterexample.expression,
            sampleDesign: counterexample.sampleDesign
              ? counterexample.sampleDesign.kind === 'integer_range'
                ? {
                    kind: 'integer_range',
                    min: counterexample.sampleDesign.min!,
                    max: counterexample.sampleDesign.max!,
                    count: counterexample.sampleDesign.count!,
                    seed: counterexample.sampleDesign.seed!,
                    includeBoundaries: counterexample.sampleDesign.includeBoundaries,
                  }
                : {
                    ...counterexample.sampleDesign,
                    kind: counterexample.sampleDesign.kind!,
                    count: counterexample.sampleDesign.count!,
                    seed: counterexample.sampleDesign.seed!,
                  }
              : undefined,
            minimizeWitness: counterexample.minimizeWitness,
            timeoutMs,
            signal: extra.signal,
          });
          const observationEvidence =
            result.outcome !== 'inconclusive' && result.proofStateFingerprint
              ? signMathResearchObservation({
                  teamId: capability.teamId,
                  assignmentId,
                  fingerprint: result.proofStateFingerprint,
                  provenance: {
                    inputDigest: mathDigest(canonicalMathJson(counterexample)),
                    casesDigest: mathDigest(
                      canonicalMathJson({
                        cases: result.casesUsed ?? [],
                        originalCases: result.originalCasesUsed ?? [],
                      })
                    ),
                    expression: counterexample.expression.slice(0, 1000),
                    ...(counterexample.precondition ? { precondition: counterexample.precondition.slice(0, 500) } : {}),
                    mode: counterexample.mode ?? 'proposition',
                    outcome: result.outcome,
                    casesChecked: result.casesChecked,
                    casesRequested: result.casesRequested ?? result.casesChecked,
                    ...(counterexample.sampleDesign
                      ? { designDigest: mathDigest(canonicalMathJson(counterexample.sampleDesign)) }
                      : {}),
                    ...(result.witness ? { witnessDigest: mathDigest(result.witness) } : {}),
                  },
                  statement:
                    `Sampled predicate ${counterexample.expression.slice(0, 1000)}: ${result.outcome}; checked=${result.casesChecked}; witness=${result.witness ?? 'none'}`.slice(
                      0,
                      1500
                    ),
                })
              : undefined;
          const notebook = isMathLiteRunEnvironment(process.env)
            ? undefined
            : readMathResearchWorkflowState(resolvedProjectRoot, assignmentContext.problemId, assignmentId);
          let notebookKey: string | undefined;
          if (notebook) {
            const worker = capability.roster.find(
              (member) => member.slotId === receipt.slotId && member.roleKind === 'worker'
            );
            if (
              notebook.binding.teamId !== capability.teamId ||
              notebook.binding.slotId !== receipt.slotId ||
              notebook.binding.workerId !== worker?.roleId ||
              notebook.binding.assignmentDigest !== assignmentContext.assignmentDigest
            )
              throw new Error('Counterexample notebook assignment binding changed.');
            notebookKey = `sample-${mathDigest(canonicalMathJson({ counterexample, result }))}`;
            await updateMathResearchWorkflow({
              projectRoot: resolvedProjectRoot,
              problemId: assignmentContext.problemId,
              assignmentId,
              actor: { roleId: capability.roleId, roleKind: capability.roleKind },
              binding: notebook.binding,
              command: {
                action: 'record',
                key: notebookKey,
                kind: 'experiment',
                summary: `Sample probe: ${result.outcome}; checked=${result.casesChecked}; skipped=${result.casesSkipped ?? 0}`,
                evidenceRefs: observationEvidence ? [observationEvidence.reference] : [],
                assessment: 'inconclusive',
                experiment: {
                  question: counterexample.question ?? counterexample.expression.slice(0, 4000),
                  expectedObservation:
                    counterexample.expectedObservation ??
                    'A true supplied negation predicate witnesses a sampled counterexample.',
                  procedure: canonicalMathJson(counterexample).slice(0, 4000),
                  observation: canonicalMathJson(result).slice(0, 4000),
                  outcome: result.outcome === 'counterexample_found' ? 'supports' : 'inconclusive',
                },
              },
            });
          }
          return jsonStructured({
            tool: 'lean_workspace',
            action,
            runId: run.runId,
            assignmentId,
            problemId: assignmentContext.problemId,
            result,
            notebookKey,
            observationEvidence,
            authority: 'lean-process',
            solverReady: false,
          });
        }

        if (action === 'check_connection') {
          if (!exploration) throw new Error('check_connection requires the exact candidate version and parent type.');
          readMathRunHistoryIdentity();
          if (!assignmentId) throw new Error('check_connection requires the bound assignmentId.');
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (!capability) throw new Error('check_connection requires an authenticated Team assignment.');
          const receipt = listProjectGitResearchTeamAssignments({
            workspace: resolvedProjectRoot,
            teamId: capability.teamId,
            strict: true,
          }).find((item) => item.assignmentId === assignmentId);
          if (
            !receipt ||
            receipt.state !== 'accepted' ||
            (capability.roleKind === 'worker' && receipt.slotId !== capability.slotId)
          )
            throw new Error('check_connection requires the active assigned Worker.');
          const assignmentContext = resolveMathAssignmentContext({
            receipt,
            projectRoot: resolvedProjectRoot,
            expectedTeamId: capability.teamId,
            expectedSlotId: receipt.slotId,
            expectedAssignmentId: assignmentId,
          });
          if (!assignmentContext.routeRevisionsSupported)
            throw new Error('check_connection requires a direct formalization assignment.');
          if (!assignmentContext.leanStatementHash || !assignmentContext.formalStatement)
            throw new Error('check_connection requires a frozen formal statement binding.');
          if (exploration.integration && !assignmentContext.artifactPaths.includes(exploration.integration.sourceFile))
            throw new Error('Exploration integration must target an artifact owned by the original assignment.');
          const result = await verifyMathExploration(resolvedProjectRoot, exploration, {
            parentBinding: {
              statementHash: assignmentContext.statementHash,
              leanStatementHash: assignmentContext.leanStatementHash,
              formalStatement: assignmentContext.formalStatement,
            },
          });
          const results = [
            result.candidate.verifierResult,
            result.connection.verifierResult,
            ...(result.integration ? [result.integration] : []),
          ];
          storeMathematicsVerification(
            run,
            results,
            results.flatMap((item) => item.events ?? [])
          );
          return jsonStructured({ tool: 'lean_workspace', action, runId: run.runId, ...result });
        }

        if (action === 'refute_route') {
          if (!assignmentId || !routeRefutation)
            throw new Error('Route refutation requires an assignment and planNodeId');
          const capability = await resolveResearchTeamRuntimeCapability(undefined);
          if (
            !capability ||
            capability.roleKind !== 'worker' ||
            fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot)
          )
            throw new Error('Route refutation requires the authenticated assigned Worker');
          const receipt = listProjectGitResearchTeamAssignments({
            workspace: resolvedProjectRoot,
            teamId: capability.teamId,
            strict: true,
          }).find((item) => item.assignmentId === assignmentId);
          if (!receipt || receipt.state !== 'accepted' || receipt.slotId !== capability.slotId)
            throw new Error('Route refutation requires the active assignment');
          const assigned = z
            .object({
              git: z.object({ baseCommit: z.string().min(1) }),
              math: z.object({
                statementHash: z.string(),
                routeFingerprint: z.string(),
                routeCards: z.array(z.unknown()),
              }),
            })
            .parse(receipt.assignment);
          const math = assigned.math;
          const routeCard = math.routeCards
            .map((card) => normalizeMathRouteCard(card as never))
            .find(
              (card) => card.routeFingerprint === math.routeFingerprint && card.statementHash === math.statementHash
            );
          if (!routeCard) throw new Error('Original assigned route card is missing');
          const binding = {
            teamId: capability.teamId,
            assignmentId,
            routeCard,
            planNodeId: routeRefutation.planNodeId,
            baseCommit: assigned.git.baseCommit,
          };
          const target = prepareMathRouteRefutationTarget(binding);
          const eliminatedApproach = `Route ${target.routeFingerprint} requires refuted obligation ${target.planNodeId}`;
          if (!routeRefutation.proofPath)
            return jsonStructured({ action, target, eliminatedApproach, authority: 'agent', solverReady: false });
          if (!targetCommit || !routeRefutation.theoremName)
            throw new Error('Refutation verification requires targetCommit and theoremName');
          if (!isAllowedMathProofSource(routeRefutation.proofPath))
            throw new Error('Refutation proof must use an authorized solver source');
          const result = await verifyMathRouteRefutation({
            ...binding,
            projectRoot: receipt.preparedGit?.worktreePath || resolvedProjectRoot,
            proofPath: routeRefutation.proofPath,
            theoremName: routeRefutation.theoremName,
            targetCommit,
          });
          return jsonStructured({
            action,
            result,
            eliminatedApproach,
            authority: result.status === 'kernel_verified' ? 'lean-kernel' : 'lean-process',
            solverReady: false,
          });
        }

        if (action === 'preflight') {
          // An assigned Worker checks its own proof project; see workerSolverProjectRoot.
          let preflightRoot = resolvedProjectRoot;
          const runtimeCapability = process.env[MATH_RUN_INPUTS_ENV]
            ? await resolveResearchTeamRuntimeCapability(undefined)
            : undefined;
          if (
            runtimeCapability?.roleKind === 'worker' &&
            fs.realpathSync(runtimeCapability.projectRoot) === fs.realpathSync(resolvedProjectRoot)
          ) {
            let boundAssignmentId: string | undefined;
            try {
              boundAssignmentId = bindMathToolAssignment(runtimeCapability, assignmentId, extra.signal);
            } catch {
              // No current assignment: keep the Team project root as before.
            }
            const preparedGit = boundAssignmentId
              ? listProjectGitResearchTeamAssignments({
                  workspace: resolvedProjectRoot,
                  teamId: runtimeCapability.teamId,
                  strict: true,
                }).find(
                  (candidate) =>
                    candidate.assignmentId === boundAssignmentId && candidate.slotId === runtimeCapability.slotId
                )?.preparedGit
              : undefined;
            if (preparedGit?.worktreePath)
              preflightRoot = workerSolverProjectRoot(resolvedProjectRoot, preparedGit) ?? preflightRoot;
          }
          const capability = await inspectFormalVerifierCapability(preflightRoot);
          run.mathematicsVerificationCapability = capability;
          run.updatedAt = now();
          writeMathematicsLiveVerificationTrace(resolvedProjectRoot, run.mathematicsVerificationEvents, capability);
          persistRunSnapshot(run);
          return jsonStructured({
            tool: 'lean_workspace',
            action,
            schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
            runId: run.runId,
            conversationId: resolvedConversationId,
            capability,
            nextAction: capability.available
              ? 'Use execute for a public proof-state pipeline or certify with all currently independent theorem items.'
              : 'Keep formal claims unverified and report the missing toolchain. Do not retry until the environment changes.',
            displayIntent: displayIntent || 'background',
          });
        }

        if (action === 'events') {
          const savedTrace = [
            readMathematicsProjectVerificationTrace(resolvedProjectRoot),
            readMathematicsVerificationTraceAtPath(resolvedProjectRoot, MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH),
          ]
            .filter((candidate): candidate is MathematicsVerificationTrace => Boolean(candidate))
            .toSorted((left, right) => right.updatedAt - left.updatedAt)[0];
          const trace: MathematicsVerificationTrace =
            savedTrace ||
            ({
              schema: MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
              version: 1,
              runIdentity: readMathRunHistoryIdentity(),
              updatedAt: run.updatedAt,
              ...(run.mathematicsVerificationCapability ? { capability: run.mathematicsVerificationCapability } : {}),
              events: run.mathematicsVerificationEvents,
            } satisfies MathematicsVerificationTrace);
          return jsonStructured({
            tool: 'lean_workspace',
            action,
            schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
            runId: run.runId,
            trace,
            tracePath: MATHEMATICS_VERIFICATION_TRACE_PATH,
            metrics: mathematicsTraceMetrics(trace.events, run.mathematicsVerifications),
            displayIntent: displayIntent || 'background',
          });
        }

        if (action === 'probe') {
          if (sourceProbe) {
            let sourceProbeRoot = resolvedProjectRoot;
            let sourceProbeProjectRelative = '';
            let validateResearchAssignment: (() => void) | undefined;
            if (assignmentId && isMathLiteRunEnvironment(process.env)) {
              const capability = await resolveResearchTeamRuntimeCapability(undefined);
              if (
                !capability ||
                capability.roleKind !== 'worker' ||
                fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot)
              )
                throw new Error('Private auxiliary probes require an authenticated assigned Worker.');
              // Scope follows the authenticated assignment, not the slot's
              // specialization. Research never gains shared-source authority.
              if (liteResearchAssignment) {
                const readReceipt = () =>
                  listProjectGitResearchTeamAssignments({
                    workspace: resolvedProjectRoot,
                    teamId: capability.teamId,
                    strict: true,
                  }).find((item) => item.assignmentId === assignmentId);
                const receipt = readReceipt();
                if (
                  !receipt ||
                  receipt.state !== 'accepted' ||
                  receipt.delivery ||
                  receipt.integration ||
                  receipt.supersessionPending ||
                  receipt.budgetCancellation ||
                  receipt.slotId !== capability.slotId
                )
                  throw new Error('Private auxiliary probes require the current uncancelled research assignment.');
                const context = resolveMathAssignmentContext({
                  receipt,
                  projectRoot: resolvedProjectRoot,
                  expectedTeamId: capability.teamId,
                  expectedSlotId: capability.slotId,
                  expectedAssignmentId: assignmentId,
                });
                if (context.protocol !== 'v2' || context.routeRevisionsSupported || context.verificationTargets.length)
                  throw new Error(
                    'Private auxiliary source probes require a research assignment, without final proof authority.'
                  );
                const encoded = process.env[MATH_RUN_INPUTS_ENV];
                if (!encoded || !receipt.preparedGit?.worktreePath)
                  throw new Error('Private auxiliary probes require a frozen run and prepared private worktree.');
                const paths = resolveMathRunProjectPaths(
                  readMathRunBinding(verifyMathRunInputs(JSON.parse(encoded))),
                  resolvedProjectRoot,
                  receipt.preparedGit.worktreePath
                );
                if (
                  receipt.preparedGit.solverProjectRoot !== paths.solverProjectRoot ||
                  fs.realpathSync(paths.solverProjectRoot) === fs.realpathSync(resolvedProjectRoot)
                )
                  throw new Error('Auxiliary proof project does not match its private worktree binding.');
                sourceProbeRoot = paths.solverProjectRoot;
                validateResearchAssignment = () => {
                  extra.signal.throwIfAborted();
                  const active = readReceipt();
                  if (
                    !active ||
                    active.state !== 'accepted' ||
                    active.delivery ||
                    active.integration ||
                    active.supersessionPending ||
                    active.budgetCancellation ||
                    active.slotId !== capability.slotId ||
                    active.preparedGit?.solverProjectRoot !== sourceProbeRoot ||
                    resolveMathAssignmentContext({
                      receipt: active,
                      projectRoot: resolvedProjectRoot,
                      expectedTeamId: capability.teamId,
                      expectedSlotId: capability.slotId,
                      expectedAssignmentId: assignmentId,
                    }).assignmentDigest !== context.assignmentDigest
                  )
                    throw new Error('math_assignment_changed_during_auxiliary_probe');
                };
                validateResearchAssignment();
              } else if (process.env[MATH_RUN_INPUTS_ENV]) {
                const scope = selectMathWorkerProbeScope({
                  receipts: listProjectGitResearchTeamAssignments({
                    workspace: resolvedProjectRoot,
                    teamId: capability.teamId,
                    strict: true,
                  }),
                  slotId: capability.slotId,
                  assignmentId,
                  binding: readMathRunBinding(verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]))),
                  teamWorkspace: capability.projectRoot,
                });
                if (scope) {
                  sourceProbeRoot = path.join(scope.workspaceRoot, scope.projectRelative);
                  sourceProbeProjectRelative = scope.projectRelative;
                }
              }
            }
            const boundSourceProbe = probeAssignmentContext
              ? {
                  ...sourceProbe,
                  sourceFile: resolveMathAssignmentProbeSource(
                    probeAssignmentContext,
                    sourceProbe.sourceFile,
                    sourceProbeProjectRelative
                  ),
                }
              : sourceProbe;
            const probe = await runLeanSourceProbe(sourceProbeRoot, boundSourceProbe, {
              timeoutMs,
              signal: extra.signal,
            });
            validateResearchAssignment?.();
            return checkpointResponse({
              tool: 'lean_workspace',
              action,
              runId: run.runId,
              probe,
              solverReady: false,
              displayIntent: displayIntent || 'background',
            });
          }
          if (!probeMode) throw new Error('lean_workspace(action="probe") requires probeMode.');
          let probeScope: { workspaceRoot: string; projectRelative?: string } = { workspaceRoot: resolvedProjectRoot };
          if (isMathLiteRunEnvironment(process.env) && process.env[MATH_RUN_INPUTS_ENV]) {
            const capability = await resolveResearchTeamRuntimeCapability(undefined);
            if (capability?.roleKind === 'worker') {
              const scope = selectMathWorkerProbeScope({
                receipts: listProjectGitResearchTeamAssignments({
                  workspace: resolvedProjectRoot,
                  teamId: capability.teamId,
                  strict: true,
                }),
                slotId: capability.slotId,
                ...(assignmentId ? { assignmentId } : {}),
                binding: readMathRunBinding(verifyMathRunInputs(JSON.parse(process.env[MATH_RUN_INPUTS_ENV]!))),
                teamWorkspace: capability.projectRoot,
              });
              // Every assigned Worker checks its own candidate, even when the
              // Team project contains a seed with the same relative filename.
              if (liteResearchAssignment && !scope)
                throw new Error('Research probes require an unambiguous private worktree scope.');
              if (scope) probeScope = scope;
            }
          }
          const probe = await runLeanEvalLeanProbe({
            ...probeScope,
            reuseFailedChecks: true,
            mode: probeMode,
            ...(probeExpression !== undefined ? { expression: probeExpression } : {}),
            ...(probeSourceFile
              ? {
                  sourceFile: probeAssignmentContext
                    ? resolveMathAssignmentProbeSource(
                        probeAssignmentContext,
                        probeSourceFile,
                        probeScope.projectRelative
                      )
                    : probeSourceFile,
                }
              : {}),
            ...(probeImportModules ? { importModules: probeImportModules } : {}),
            timeoutMs,
            signal: extra.signal,
          });
          return checkpointResponse({
            tool: 'lean_workspace',
            action,
            schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
            runId: run.runId,
            conversationId: resolvedConversationId,
            probe,
            nextContext: {
              proofStateFingerprint: probe.proofStateFingerprint,
              firstGoal: probe.firstGoal,
              sourceOffset: probe.sourceOffset,
            },
            displayIntent: displayIntent || 'focus',
          });
        }

        let publicEvents: MathematicsVerificationEvent[] = [];
        let certificationItems: Array<MathematicsVerifierBatchItem & { stateId?: string; problemId?: string }> = [];
        if (action === 'execute') {
          if (!operations?.length) throw new Error('lean_workspace(action="execute") requires operations[].');
          const firstCertifyIndex = operations.findIndex((operation) => operation.op === 'certify');
          if (
            firstCertifyIndex >= 0 &&
            operations.slice(firstCertifyIndex).some((operation) => operation.op !== 'certify')
          ) {
            throw new Error('All certify operations must be contiguous at the end of an execute pipeline.');
          }
          const sessionId = crypto.randomUUID();
          operations.forEach((operation, operationIndex) => {
            if (operation.op === 'submit_formula') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'formula.submitted', {
                  formulaId: operation.id,
                  formula: operation.formula,
                  label: operation.label,
                  theoremName: operation.theoremName,
                  sourcePath: operation.sourcePath,
                  authority: 'agent',
                })
              );
            } else if (operation.op === 'open_goal') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'goal.opened', {
                  stateId: operation.stateId,
                  target: operation.target,
                  hypotheses: operation.hypotheses,
                  theoremName: operation.theoremName,
                  authority: 'agent',
                })
              );
            } else if (operation.op === 'rewrite_goal') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'goal.rewritten', {
                  stateId: operation.stateId,
                  parentStateId: operation.parentStateId,
                  previousTarget: operation.previousTarget,
                  target: operation.target,
                  hypotheses: operation.hypotheses,
                  theoremName: operation.theoremName,
                  authority: 'agent',
                })
              );
            } else if (operation.op === 'branch_goal') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'goal.branched', {
                  stateId: operation.stateId,
                  parentStateId: operation.parentStateId,
                  target: operation.target,
                  hypotheses: operation.hypotheses,
                  theoremName: operation.theoremName,
                  branchLabel: operation.branchLabel,
                  authority: 'agent',
                })
              );
            } else if (operation.op === 'close_goal') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'goal.closed', {
                  stateId: operation.stateId,
                  parentStateId: operation.parentStateId,
                  target: operation.target,
                  theoremName: operation.theoremName,
                  status: 'draft_closed',
                  authority: 'agent',
                })
              );
            } else if (operation.op === 'diagnostic') {
              publicEvents.push(
                createMathematicsVerificationEvent(sessionId, 'diagnostic.emitted', {
                  source: 'agent',
                  severity: operation.severity,
                  message: operation.message,
                  proofPath: operation.proofPath,
                  stateId: operation.stateId,
                })
              );
            } else {
              certificationItems.push(
                ...operation.items.map((item, itemIndex) => ({
                  id: item.id || `pipeline-${operationIndex + 1}-${itemIndex + 1}`,
                  proofPath: item.proofPath,
                  theoremName: item.theoremName,
                  statementHash: item.statementHash,
                  leanStatementHash: item.leanStatementHash,
                  problemId: item.problemId,
                  claim: item.claim,
                  stateId: item.stateId,
                }))
              );
            }
          });
        } else {
          if (!items?.length) throw new Error('lean_workspace(action="certify") requires items[].');
          certificationItems = items.map((item) => ({
            id: item.id,
            proofPath: item.proofPath as string,
            theoremName: item.theoremName,
            statementHash: item.statementHash as string,
            leanStatementHash: item.leanStatementHash,
            problemId: item.problemId,
            claim: item.claim,
            stateId: item.stateId,
          }));
        }

        let batch: MathematicsVerifierBatchResult | undefined;
        if (certificationItems.length > 0) {
          // A Team Worker constructs proofs in its prepared assignment worktree.
          // The MCP session itself remains bound to the canonical project root
          // for portfolio/artifact state, but certification must read the same
          // Git repository that produced targetCommit. Using the canonical root
          // here makes every fresh Worker commit look unresolved and causes the
          // model to retry the same certification forever.
          let verificationProjectRoot = resolvedProjectRoot;
          if (assignmentId) {
            const capability = await resolveResearchTeamRuntimeCapability(undefined);
            if (!capability || capability.roleKind !== 'worker') {
              throw new Error('Lean certification with assignmentId requires an authenticated Worker.');
            }
            if (fs.realpathSync(capability.projectRoot) !== fs.realpathSync(resolvedProjectRoot)) {
              throw new Error('Lean certification project does not match the Worker capability.');
            }
            const receipt = listProjectGitResearchTeamAssignments({
              workspace: resolvedProjectRoot,
              teamId: capability.teamId,
              strict: true,
            }).find((candidate) => candidate.assignmentId === assignmentId);
            if (!receipt || receipt.state !== 'accepted' || receipt.slotId !== capability.slotId) {
              throw new Error('Lean certification requires the active assigned Worker.');
            }
            if (receipt.preparedGit?.worktreePath) {
              verificationProjectRoot = fs.realpathSync(receipt.preparedGit.worktreePath);
              const solverProjectRoot = workerSolverProjectRoot(resolvedProjectRoot, receipt.preparedGit);
              if (solverProjectRoot) {
                // Run 23 attempt 9: the sealed proof environment was taken on the Lean
                // project, so certifying at the worktree top always reported a config
                // mismatch. Verify at the project and keep paths relative to it, as
                // Lead promotion does (mathIntegrationPromotion.ts).
                const worktreeRoot = verificationProjectRoot;
                certificationItems = certificationItems.map((item) => {
                  const fromWorktree = path.resolve(worktreeRoot, item.proofPath);
                  const source = isMathPathWithin(solverProjectRoot, fromWorktree)
                    ? fromWorktree
                    : path.resolve(solverProjectRoot, item.proofPath);
                  if (!isMathPathWithin(solverProjectRoot, source))
                    throw new Error('Lean certification proofPath is outside the Worker proof project.');
                  return { ...item, proofPath: path.relative(solverProjectRoot, source).split(path.sep).join('/') };
                });
                verificationProjectRoot = solverProjectRoot;
              }
            }
          }
          const storedPortfolio = latestMathematicsPortfolio(run.artifacts.values());
          const contractsByStatementHash = new Map<string | undefined, MathProblemContract[]>();
          const contractByIdentity = new Map<string, MathProblemContract>();
          for (const problem of storedPortfolio?.problems ?? []) {
            if (!problem.problemContract) continue;
            const contracts = contractsByStatementHash.get(problem.statementHash) ?? [];
            contracts.push(problem.problemContract);
            contractsByStatementHash.set(problem.statementHash, contracts);
            contractByIdentity.set(`${problem.statementHash}\0${problem.id}`, problem.problemContract);
          }
          certificationItems = certificationItems.map((item) => {
            const contracts = contractsByStatementHash.get(item.statementHash) ?? [];
            if (item.claim === 'negation' && !item.problemId) {
              throw new Error('Lean negation certification requires problemId.');
            }
            if (!item.problemId && contracts.length > 1) {
              throw new Error(
                `Lean certification statementHash is ambiguous; supply problemId for ${item.statementHash}.`
              );
            }
            const contract = item.problemId
              ? contractByIdentity.get(`${item.statementHash}\0${item.problemId}`)
              : contracts[0];
            if (item.problemId && !contract) {
              throw new Error(
                `Lean certification problemId has no matching immutable MathProblemContract: ${item.problemId}.`
              );
            }
            const claimLeanHash = item.claim === 'negation' ? contract?.leanNegationHash : contract?.leanStatementHash;
            const claimStatement =
              item.claim === 'negation' ? contract?.formalNegationStatement : contract?.formalStatement;
            if (item.claim === 'negation' && (!claimLeanHash || !claimStatement)) {
              throw new Error('Lean negation certification requires a canonical negation in MathProblemContract.');
            }
            if (contract && item.leanStatementHash && item.leanStatementHash !== claimLeanHash) {
              throw new Error('Lean certification leanStatementHash must match the immutable MathProblemContract.');
            }
            return {
              ...item,
              ...(contract ? { leanStatementHash: claimLeanHash } : {}),
              ...(contract && item.theoremName
                ? {
                    expectedSourceDeclarationHash: hashMathFormalSourceDeclaration(claimStatement!, item.theoremName),
                  }
                : {}),
            };
          });
          const liveWriter = createMathematicsLiveTraceWriter(
            resolvedProjectRoot,
            [run.mathematicsVerificationEvents, publicEvents],
            run.mathematicsVerificationCapability
          );
          liveWriter.flush();
          try {
            batch = await checkManyFormalVerifications(
              {
                projectRoot: verificationProjectRoot,
                targetCommit,
                timeoutMs,
                items: certificationItems.map(({ stateId: _stateId, problemId: _problemId, ...item }) => item),
              },
              {
                onEvent: (event) => {
                  liveWriter.append(event);
                },
              }
            );
          } finally {
            liveWriter.close();
          }
          const stateByCheckId = new Map<string, string | undefined>();
          for (let index = 0; index < certificationItems.length; index += 1) {
            const item = certificationItems[index];
            stateByCheckId.set(item.id || `check-${index + 1}`, item.stateId);
          }
          for (const event of batch.events) publicEvents.push(event);
          for (const result of batch.results) {
            const stateId = stateByCheckId.get(result.checkId);
            if (!stateId || result.status !== 'kernel_verified') continue;
            publicEvents.push(
              createMathematicsVerificationEvent(batch.sessionId, 'goal.closed', {
                stateId,
                theoremName: result.theoremName,
                status: 'kernel_verified',
                authority: 'lean-kernel',
              })
            );
          }
        }

        const results = batch?.results || [];
        const capability = batch
          ? capabilityFromVerificationBatch(batch, run.mathematicsVerificationCapability)
          : run.mathematicsVerificationCapability;
        const trace = storeMathematicsVerification(run, results, publicEvents, capability);
        let reportTracePath: string | undefined;
        if (trace) {
          try {
            reportTracePath = writeMathematicsProofTraceSnapshot(resolvedProjectRoot, trace);
          } catch (error) {
            console.warn(`[ScienceArtifactMCP] mathematics report trace snapshot failed: ${String(error)}`);
          }
        }
        const metrics = mathematicsTraceMetrics(publicEvents, results);
        return checkpointResponse({
          tool: 'lean_workspace',
          action,
          schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
          runId: run.runId,
          conversationId: resolvedConversationId,
          status: batch?.status || 'recorded',
          capability,
          metrics,
          results,
          events: publicEvents,
          tracePath: trace ? MATHEMATICS_VERIFICATION_TRACE_PATH : undefined,
          ...(reportTracePath
            ? { reportTracePath, artifactDraft: mathematicsProofTraceArtifactDraft(reportTracePath) }
            : {}),
          nextContext: {
            targetCommit: batch?.targetCommit,
            receiptIds: results.map((result) => result.receiptId),
            openGoals: metrics.openGoals,
            failedCheckIds: results
              .filter((result) => result.status !== 'kernel_verified')
              .map((result) => result.checkId),
          },
          displayIntent:
            displayIntent || (results.some((result) => result.status === 'kernel_verified') ? 'focus' : 'background'),
        });
      }
    )
  );

  server.tool(
    'formal_verifier',
    FORMAL_VERIFIER_TOOL_DESCRIPTION,
    {
      action: z.enum(['check', 'official_compare']),
      runId: z.string().optional(),
      conversationId: z.string().optional(),
      messageId: z.string().optional(),
      toolCallId: z.string().optional(),
      projectRoot: z.string().optional(),
      proofPath: z.string().optional(),
      theoremName: z.string().optional(),
      statementHash: z.string().optional(),
      leanStatementHash: z.string().optional(),
      /** Problem identity lets the runtime bind the Lean proposition hash to the immutable contract. */
      problemId: z.string().optional(),
      leanEvalRepositoryRoot: z.string().optional(),
      claim: z.enum(['statement', 'negation']).optional(),
      targetCommit: z.string().optional(),
      localGateReceiptId: z.string().optional(),
      routeFingerprint: z.string().optional(),
      officialVerificationCommand: z.string().optional(),
      officialManifestPath: z.string().optional(),
      timeoutMs: z
        .number()
        .int()
        .positive()
        .max(24 * 60 * 60 * 1000)
        .optional(),
    },
    async ({
      action,
      runId: requestedRunId,
      conversationId,
      messageId,
      toolCallId,
      projectRoot,
      proofPath,
      theoremName,
      statementHash,
      leanStatementHash,
      problemId,
      leanEvalRepositoryRoot,
      claim,
      targetCommit,
      localGateReceiptId,
      routeFingerprint,
      officialVerificationCommand,
      officialManifestPath,
      timeoutMs,
    }) => {
      assertResearchTeamToolActionAuthorized('formal_verifier', action);
      const resolvedConversationId = resolveSessionIdentifier(
        conversationId,
        PROJECT_WORKSPACE_ENV_KEYS.conversationId,
        'conversationId'
      );
      const resolvedProjectRoot = await resolveModeProjectRoot(projectRoot, resolvedConversationId);
      if (!resolvedProjectRoot) {
        throw new Error(
          'formal_verifier requires the current project root. Reopen the task if the runtime did not bind one.'
        );
      }
      const run = ensureRun(
        stableMathematicsRunId(requestedRunId, resolvedProjectRoot, resolvedConversationId),
        resolvedProjectRoot,
        { question: 'Mathematical verification' }
      );
      applyRunContext(run, undefined, { conversationId: resolvedConversationId, messageId, toolCallId });
      if (action === 'official_compare') {
        const stableLocalReceiptId = localGateReceiptId?.trim();
        const command = officialVerificationCommand?.trim();
        let manifestPath = officialManifestPath?.trim() || '.deepscientist/math/official-manifest.json';
        let generatedOfficialManifest: MathOfficialProblemManifest | undefined;
        if (!stableLocalReceiptId || !command || !routeFingerprint?.trim() || !problemId?.trim()) {
          throw new Error(
            'formal_verifier(action="official_compare") requires problemId, localGateReceiptId, routeFingerprint, and officialVerificationCommand.'
          );
        }
        const verificationIndex = indexMathematicsVerifications(run);
        let localVerification = verificationIndex.byReceiptId
          .get(stableLocalReceiptId)
          ?.find(
            (result) =>
              result.status === 'kernel_verified' &&
              result.verifier === 'lean-kernel' &&
              result.goalsRemaining === 0 &&
              result.sorryCount === 0 &&
              result.admitCount === 0 &&
              result.axioms.every(isMathFoundationalLeanAxiom) &&
              Boolean(result.theoremName && result.theoremDeclarationHash)
          );
        if (!localVerification) {
          const cached = findCachedFormalVerificationReceipt(resolvedProjectRoot, stableLocalReceiptId);
          if (cached) {
            storeMathematicsVerification(run, [cached], []);
            localVerification = cached;
          }
        }
        if (!localVerification) {
          throw new Error(
            'official_compare requires a stored successful Lean receipt with a named committed theorem and no sorry, admit, or non-foundational axioms.'
          );
        }
        const storedPortfolio = latestMathematicsPortfolio(run.artifacts.values());
        const storedProblem = storedPortfolio?.problems.find((problem) => problem.id === problemId.trim());
        const contract = storedProblem?.problemContract;
        if (!storedProblem || !contract) {
          throw new Error(
            'official_compare requires an immutable MathProblemContract for the stored Team mathematics problem.'
          );
        }
        if (!storedProblem.localGateReceipt) {
          throw new Error("official_compare requires the problem's frozen LOCAL_GATE receipt.");
        }
        const storedLocalReceipt = normalizeMathLocalGateReceipt(storedProblem.localGateReceipt);
        const normalizedRoute = normalizeMathRouteFingerprint(routeFingerprint);
        assertMathematicsOfficialCompareReceiptBinding(
          storedLocalReceipt,
          localVerification,
          stableLocalReceiptId,
          routeFingerprint
        );
        const normalizedContract = contract ? normalizeMathProblemContract(contract) : undefined;
        if (!normalizedContract?.officialManifestId || !normalizedContract.officialManifestHash) {
          throw new Error(
            'official_compare requires officialManifestId and officialManifestHash in the immutable MathProblemContract.'
          );
        }
        if (leanEvalRepositoryRoot) {
          const catalog = readLeanEvalCatalog({
            repositoryRoot: leanEvalRepositoryRoot,
            benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
            verifyGitCommit: true,
          });
          const catalogProblem = findLeanEvalCatalogProblem(catalog, normalizedContract.problemId);
          if (!catalogProblem || catalogProblem.statementRevision !== 1) {
            throw new Error(
              `LeanEval problem ${normalizedContract.problemId} is not present at the pinned statement revision.`
            );
          }
          let freshLeaderboard: Awaited<ReturnType<typeof fetchLeanEvalLeaderboardCredits>>;
          try {
            freshLeaderboard = await fetchLeanEvalLeaderboardCredits({ forceRefresh: true });
          } catch (error) {
            throw new Error(
              `official_compare is blocked because Lean-Eval leaderboard freshness could not be verified: ${
                error instanceof Error ? error.message : String(error)
              }`,
              { cause: error }
            );
          }
          if (
            freshLeaderboard.credits.some(
              (credit) =>
                credit.problemId === normalizedContract.problemId &&
                credit.statementRevision === catalogProblem.statementRevision
            )
          ) {
            throw new Error('official_compare refuses a Lean-Eval problem with a newly accepted leaderboard credit.');
          }
          const binding = prepareLeanEvalProblemBinding({
            projectRoot: resolvedProjectRoot,
            problemId: normalizedContract.problemId,
            title: catalogProblem.title,
            informalStatement: normalizedContract.informalStatement,
            assumptions: normalizedContract.assumptions,
            statementRevision: catalogProblem.statementRevision,
            baselineCommit: catalog.benchmarkCommit,
            repositoryUrl: LEAN_EVAL_REPOSITORY_URL,
          });
          if (
            binding.officialManifest.manifestId !== normalizedContract.officialManifestId ||
            binding.officialManifest.manifestHash !== normalizedContract.officialManifestHash
          ) {
            throw new Error('LeanEval generated official manifest does not match the immutable problem contract.');
          }
          generatedOfficialManifest = binding.officialManifest;
          materializeLeanEvalProblemBinding(binding);
          // The comparator resolves this path from the repository root, not
          // from the problem subdirectory.
          manifestPath = binding.officialManifestPath;
        }
        if (normalizedContract && normalizedContract.statementHash !== localVerification.statementHash) {
          throw new Error('official_compare contract statementHash must match the stored Lean receipt.');
        }
        const expectedClaimLeanHash =
          localVerification.claim === 'negation'
            ? normalizedContract.leanNegationHash
            : normalizedContract.leanStatementHash;
        if (!expectedClaimLeanHash || localVerification.leanStatementHash !== expectedClaimLeanHash) {
          throw new Error('official_compare contract claim hash must match the stored Lean receipt.');
        }
        if (normalizedContract && normalizedContract.officialVerificationCommand !== command) {
          throw new Error('official_compare command must match the immutable MathProblemContract.');
        }
        if (targetCommit && targetCommit.trim().toLowerCase() !== localVerification.targetCommit) {
          throw new Error('official_compare targetCommit must match the stored local Lean receipt.');
        }
        // Authority and pinned-hash anchors live outside the committed target
        // checkout. Re-run the comparator on every request so an authority
        // removal or edit cannot turn an old receipt into a fresh approval.
        const comparison = await runOfficialComparator({
          projectRoot: resolvedProjectRoot,
          targetCommit: localVerification.targetCommit,
          command,
          ...(generatedOfficialManifest
            ? { officialManifest: generatedOfficialManifest }
            : { officialManifestPath: manifestPath }),
          problemId: problemId.trim(),
          statementHash: localVerification.statementHash,
          ...(normalizedContract ? { expectedContract: normalizedContract } : {}),
          timeoutMs,
        });
        let officialGateReceipt: MathOfficialGateReceipt | undefined;
        if (comparison.status === 'official_verified') {
          const secret = readMathematicsReceiptSecret();
          if (!secret) throw new Error('The local mathematics receipt signing key is unavailable.');
          const receiptIdentity = sha256(
            JSON.stringify({
              targetCommit: comparison.targetCommit,
              statementHash: localVerification.statementHash,
              claim: localVerification.claim,
              routeFingerprint: normalizedRoute,
              localGateReceiptId: stableLocalReceiptId,
              theoremName: localVerification.theoremName,
              proofHash: localVerification.proofHash,
              theoremDeclarationHash: localVerification.theoremDeclarationHash,
              sourceDeclarationHash: localVerification.sourceDeclarationHash,
              command: comparison.command,
              stdoutSha256: comparison.stdoutSha256,
              stderrSha256: comparison.stderrSha256,
              problemId: normalizedContract.problemId,
              officialManifestPath: manifestPath,
              officialManifestId: comparison.officialManifestId,
              officialManifestHash: comparison.officialManifestHash,
              leanStatementHash: expectedClaimLeanHash,
              officialRepositoryUrl: comparison.officialRepositoryUrl,
              officialBaselineCommit: comparison.officialBaselineCommit,
              benchmarkAdapterId: comparison.benchmarkAdapterId,
              benchmarkAdapterVersion: comparison.benchmarkAdapterVersion,
            })
          );
          officialGateReceipt = signMathOfficialGateReceipt(
            {
              receiptId: `official-${receiptIdentity.slice(0, 24)}`,
              targetCommit: comparison.targetCommit,
              statementHash: localVerification.statementHash,
              claim: localVerification.claim,
              routeFingerprint: normalizedRoute,
              localGateReceiptId: stableLocalReceiptId,
              theoremName: localVerification.theoremName!,
              proofHash: localVerification.proofHash,
              theoremDeclarationHash: localVerification.theoremDeclarationHash!,
              ...(localVerification.sourceDeclarationHash
                ? { sourceDeclarationHash: localVerification.sourceDeclarationHash }
                : {}),
              status: 'official_verified',
              verifier: 'official-comparator',
              command: comparison.command,
              exitCode: 0,
              timedOut: false,
              stdoutSha256: comparison.stdoutSha256,
              stderrSha256: comparison.stderrSha256,
              durationMs: comparison.durationMs,
              checkedAt: comparison.checkedAt,
              problemId: normalizedContract.problemId,
              officialManifestPath: manifestPath,
              officialManifestId: comparison.officialManifestId!,
              officialManifestHash: comparison.officialManifestHash!,
              leanStatementHash: expectedClaimLeanHash,
              officialRepositoryUrl: comparison.officialRepositoryUrl!,
              officialBaselineCommit: comparison.officialBaselineCommit!,
              benchmarkAdapterId: comparison.benchmarkAdapterId!,
              benchmarkAdapterVersion: comparison.benchmarkAdapterVersion!,
            },
            secret
          );
          const retainedOfficialReceipts: MathOfficialGateReceipt[] = [];
          for (const receipt of run.mathematicsOfficialGateReceipts) {
            if (
              receipt.targetCommit === officialGateReceipt.targetCommit &&
              receipt.statementHash === officialGateReceipt.statementHash &&
              receipt.localGateReceiptId === officialGateReceipt.localGateReceiptId &&
              receipt.routeFingerprint === officialGateReceipt.routeFingerprint
            ) {
              continue;
            }
            retainedOfficialReceipts.push(receipt);
          }
          retainedOfficialReceipts.push(officialGateReceipt);
          if (retainedOfficialReceipts.length > 512) {
            retainedOfficialReceipts.splice(0, retainedOfficialReceipts.length - 512);
          }
          run.mathematicsOfficialGateReceipts = retainedOfficialReceipts;
          run.updatedAt = now();
          persistRunSnapshot(run);
        }
        return jsonStructured({
          schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
          eventId: eventId(),
          tool: 'formal_verifier',
          action,
          runId: run.runId,
          conversationId: resolvedConversationId,
          timestamp: now(),
          comparison,
          ...(officialGateReceipt ? { officialGateReceipt } : {}),
          nextContext: officialGateReceipt
            ? {
                targetCommit: officialGateReceipt.targetCommit,
                localGateReceiptId: officialGateReceipt.localGateReceiptId,
                officialGateReceiptId: officialGateReceipt.receiptId,
              }
            : undefined,
          displayIntent: comparison.status === 'official_verified' ? 'focus' : 'background',
        });
      }
      if (!proofPath?.trim() || !statementHash?.trim()) {
        throw new Error('formal_verifier(action="check") requires proofPath and statementHash.');
      }
      let boundLeanStatementHash = leanStatementHash?.trim() || undefined;
      const storedPortfolio = latestMathematicsPortfolio(run.artifacts.values());
      const normalizedStatementHash = statementHash.trim();
      const normalizedProblemId = problemId?.trim();
      const normalizedClaim = claim || 'statement';
      if (normalizedClaim === 'negation' && !normalizedProblemId) {
        throw new Error('formal_verifier(action="check") negation requires problemId.');
      }
      let boundContract: MathProblemContract | undefined;
      for (const problem of storedPortfolio?.problems ?? []) {
        if (
          !problem.problemContract ||
          problem.statementHash !== normalizedStatementHash ||
          (normalizedProblemId && problem.id !== normalizedProblemId)
        ) {
          continue;
        }
        if (boundContract) {
          throw new Error('formal_verifier statementHash is ambiguous; supply problemId.');
        }
        boundContract = problem.problemContract;
      }
      if (normalizedProblemId && !boundContract) {
        throw new Error('formal_verifier(action="check") problemId requires a stored immutable MathProblemContract.');
      }
      const contractClaimLeanHash =
        normalizedClaim === 'negation' ? boundContract?.leanNegationHash : boundContract?.leanStatementHash;
      const contractClaimStatement =
        normalizedClaim === 'negation' ? boundContract?.formalNegationStatement : boundContract?.formalStatement;
      if (normalizedClaim === 'negation' && (!contractClaimLeanHash || !contractClaimStatement)) {
        throw new Error('formal_verifier negation requires a canonical Lean negation in MathProblemContract.');
      }
      if (boundContract && boundLeanStatementHash && boundLeanStatementHash !== contractClaimLeanHash) {
        throw new Error('formal_verifier leanStatementHash must match the immutable MathProblemContract.');
      }
      if (boundContract) boundLeanStatementHash = contractClaimLeanHash;
      const liveWriter = createMathematicsLiveTraceWriter(
        resolvedProjectRoot,
        [run.mathematicsVerificationEvents],
        run.mathematicsVerificationCapability
      );
      liveWriter.flush();
      let verification: MathematicsVerifierResult;
      try {
        verification = await runFormalVerification(
          {
            projectRoot: resolvedProjectRoot,
            proofPath,
            theoremName,
            statementHash,
            ...(boundLeanStatementHash ? { leanStatementHash: boundLeanStatementHash } : {}),
            ...(boundContract && theoremName
              ? {
                  expectedSourceDeclarationHash: hashMathFormalSourceDeclaration(contractClaimStatement!, theoremName),
                }
              : {}),
            claim: normalizedClaim,
            targetCommit,
            timeoutMs,
          },
          {
            onEvent: (event) => {
              liveWriter.append(event);
            },
          }
        );
      } finally {
        liveWriter.close();
      }
      const verificationEvents = verification.events || [];
      const capability: MathematicsVerificationCapability | undefined =
        verification.status === 'blocked'
          ? run.mathematicsVerificationCapability
          : {
              available: verification.status !== 'unavailable',
              command: verification.toolchain.lake ? 'lake' : 'lean',
              executable: verification.toolchain.lake ? 'lake' : 'lean',
              ...(verification.status === 'unavailable' ? { reason: verification.error } : {}),
              batchCertification: true,
              liveGoals: false,
              persistentSession: false,
            };
      const trace = storeMathematicsVerification(run, [verification], verificationEvents, capability);
      let reportTracePath: string | undefined;
      if (trace) {
        try {
          reportTracePath = writeMathematicsProofTraceSnapshot(resolvedProjectRoot, trace);
        } catch (error) {
          console.warn(`[ScienceArtifactMCP] mathematics report trace snapshot failed: ${String(error)}`);
        }
      }
      return jsonStructured({
        schema: MATHEMATICS_VERIFICATION_EVENT_SCHEMA,
        eventId: eventId(),
        tool: 'formal_verifier',
        action,
        runId: run.runId,
        conversationId: resolvedConversationId,
        timestamp: now(),
        verification,
        events: verificationEvents,
        tracePath: MATHEMATICS_VERIFICATION_TRACE_PATH,
        ...(reportTracePath
          ? { reportTracePath, artifactDraft: mathematicsProofTraceArtifactDraft(reportTracePath) }
          : {}),
        nextContext: {
          targetCommit: verification.targetCommit,
          receiptId: verification.receiptId,
          checkId: verification.checkId,
        },
        displayIntent: verification.status === 'kernel_verified' ? 'focus' : 'background',
      });
    }
  );

  const portfolioActions = mathPortfolioToolActions(isMathLiteRunEnvironment(process.env));
  if (portfolioActions.length) {
    server.tool(
      'math_portfolio',
      MATHEMATICS_PORTFOLIO_TOOL_DESCRIPTION,
      await createMathPortfolioToolInput(portfolioActions),
      async ({
        action,
        runId: requestedRunId,
        conversationId,
        messageId,
        toolCallId,
        projectRoot,
        leanEvalRepositoryRoot,
        leanEvalCredits,
        leanEvalProblemId,
        leanEvalBootstrapReceiptPath,
        leanEvalPage,
        leanEvalPageSize,
        artifactId,
        artifactVersion,
        baseRevision,
        title,
        changeSummary,
        portfolio,
        portfolioPatch,
        review,
        targetCommit,
        statementHash,
        promptQuery,
        displayIntent,
      }) => {
        assertResearchTeamToolActionAuthorized('math_portfolio', action);
        let leanEvalOfficialGate:
          | Readonly<{
              gate: Awaited<ReturnType<typeof runPersistedLeanEvalOfficialGate>>;
              receiptPath: string;
              projectRoot: string;
            }>
          | undefined;
        let leanEvalOfficialGateUpdate:
          | Readonly<{
              problemId: string;
              localGateReceipt: MathLocalGateReceipt;
              officialGateReceipt: MathOfficialGateReceipt;
              localResult: MathematicsVerifierResult;
            }>
          | undefined;
        if (promptQuery && action !== 'get') {
          throw new Error('math_portfolio promptQuery is available only for action="get".');
        }
        if (portfolioPatch && action !== 'patch') {
          throw new Error('math_portfolio portfolioPatch is available only for action="patch".');
        }
        if (action === 'patch' && (!portfolioPatch || portfolio)) {
          throw new Error('math_portfolio(action="patch") requires portfolioPatch and does not accept portfolio.');
        }
        if (action === 'bootstrap') {
          const catalogRoot = leanEvalRepositoryRoot || process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT;
          if (!catalogRoot) throw new Error('math_portfolio(action="bootstrap") requires leanEvalRepositoryRoot.');
          if (!leanEvalProblemId) throw new Error('math_portfolio(action="bootstrap") requires leanEvalProblemId.');
          const bootstrapped = await bootstrapLeanEvalProblem({
            repositoryRoot: catalogRoot,
            problemId: leanEvalProblemId,
            workspaceParent: projectRoot,
            // Formal MCP intake always uses the published leaderboard. Caller
            // credits remain test-only input for direct service-level fixtures.
            useOfficialCredits: true,
          });
          return jsonStructured({
            schema: MATHEMATICS_EVENT_SCHEMA,
            eventId: eventId(),
            tool: 'math_portfolio',
            action,
            timestamp: now(),
            problem: bootstrapped.problem,
            analysis: bootstrapped.analysis,
            routeCard: bootstrapped.routeCard,
            route: bootstrapped.route,
            problemContract: bootstrapped.binding.problemContract,
            receipt: bootstrapped.receipt,
            workspaceRoot: bootstrapped.receipt.workspaceRoot,
            projectRoot: bootstrapped.receipt.projectRoot,
            displayIntent: displayIntent || 'focus',
          });
        }
        if (action === 'official_gate') {
          const receiptPath =
            leanEvalBootstrapReceiptPath?.trim() ||
            (projectRoot && leanEvalProblemId ? findLeanEvalTeamReceipt(projectRoot, leanEvalProblemId) : undefined);
          const catalogRoot = leanEvalRepositoryRoot || process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT;
          const portfolioRoot = projectRoot || (portfolio?.projectRoot as string | undefined);
          if (!receiptPath || !catalogRoot || !portfolioRoot) {
            throw new Error(
              'math_portfolio(action="official_gate") requires leanEvalBootstrapReceiptPath, leanEvalRepositoryRoot, and projectRoot.'
            );
          }
          const gate = await runPersistedLeanEvalOfficialGate({
            activeProblemPath: receiptPath,
            repositoryRoot: catalogRoot,
          });
          if (!gate.officialGateReceipt) {
            return jsonStructured({
              schema: MATHEMATICS_EVENT_SCHEMA,
              eventId: eventId(),
              tool: 'math_portfolio',
              action,
              timestamp: now(),
              localGate: gate.localGate,
              comparison: gate.comparison,
              receiptPath,
              persisted: false,
              displayIntent: displayIntent || 'focus',
            });
          }
          // Continue through the ordinary portfolio mutation path below. This
          // makes the signed gate receipt visible to Team binding, `get`, and
          // the terminal decision gate instead of leaving it as an ephemeral
          // MCP response.
          leanEvalOfficialGate = Object.freeze({ gate, receiptPath, projectRoot: portfolioRoot });
        }
        if (action === 'schema') {
          return jsonText({
            schema: MATHEMATICS_EVENT_SCHEMA,
            eventId: eventId(),
            tool: 'math_portfolio',
            action,
            timestamp: now(),
            contract: mathematicsPortfolioContract(projectRoot),
            displayIntent: displayIntent || 'background',
          });
        }
        if (action === 'validate') {
          const validation = validateMathematicsPortfolio(portfolio);
          return {
            ...jsonText({
              schema: MATHEMATICS_EVENT_SCHEMA,
              eventId: eventId(),
              tool: 'math_portfolio',
              action,
              timestamp: now(),
              ok: validation.ok,
              errors: validation.errors,
              issues: mathematicsValidationIssues(validation.errors),
              recoveryAction: validation.ok ? 'submit' : 'repair the listed paths and validate once more',
              displayIntent: displayIntent || 'background',
            }),
            ...(validation.ok ? {} : { isError: true as const }),
          };
        }
        const portfolioProjectRoot = asString(portfolio?.projectRoot, undefined as unknown as string);
        const resolvedConversationId = resolveSessionIdentifier(
          conversationId,
          PROJECT_WORKSPACE_ENV_KEYS.conversationId,
          'conversationId'
        );
        const resolvedProjectRoot = await resolveModeProjectRoot(
          projectRoot || portfolioProjectRoot,
          resolvedConversationId
        );
        if (
          leanEvalOfficialGate &&
          path.resolve(resolvedProjectRoot) !== path.resolve(leanEvalOfficialGate.projectRoot)
        ) {
          throw new Error('Lean-Eval official gate projectRoot does not match the bound mathematics project.');
        }
        const run = ensureRun(
          stableMathematicsRunId(requestedRunId, resolvedProjectRoot, resolvedConversationId),
          resolvedProjectRoot,
          portfolio
        );
        applyRunContext(run, portfolio, { conversationId: resolvedConversationId, messageId, toolCallId });
        let existingMathArtifact: ScienceArtifact | undefined;
        let existingMathPortfolio: MathematicsPortfolio | undefined;
        if (!artifactId) {
          for (const artifact of run.artifacts.values()) {
            const candidate = readMathematicsPortfolio(artifact.metadata);
            if (!candidate) continue;
            if (
              !existingMathArtifact ||
              artifact.createdAt > existingMathArtifact.createdAt ||
              (artifact.createdAt === existingMathArtifact.createdAt && artifact.version > existingMathArtifact.version)
            ) {
              existingMathArtifact = artifact;
              existingMathPortfolio = candidate;
            }
          }
        }
        const id = artifactId || existingMathArtifact?.id || MATHEMATICS_PORTFOLIO_ARTIFACT_ID;
        const version = artifactVersion || existingMathArtifact?.version || 1;
        const target = { kind: 'artifact' as const, id, version };
        let current = run.artifacts.get(artifactKey(id, version));
        let currentPortfolio =
          current === existingMathArtifact && existingMathPortfolio
            ? existingMathPortfolio
            : readMathematicsPortfolio(current?.metadata);
        if (leanEvalOfficialGate) {
          const gateReceipt = leanEvalOfficialGate.gate.officialGateReceipt;
          const localResult = selectMathematicsOfficialGateLocalResult(
            leanEvalOfficialGate.gate.localGate,
            gateReceipt?.localGateReceiptId || ''
          );
          if (!localResult || !gateReceipt) {
            throw new Error('Lean-Eval official gate did not produce a matching LOCAL_GATE receipt.');
          }
          const problemId = gateReceipt.problemId;
          if (!problemId) throw new Error('Lean-Eval official gate receipt is missing problemId.');
          const localGateReceipt = normalizeMathLocalGateReceipt({
            receiptId: localResult.receiptId,
            targetCommit: localResult.targetCommit,
            statementHash: localResult.statementHash,
            claim: localResult.claim,
            ...(localResult.leanStatementHash ? { leanStatementHash: localResult.leanStatementHash } : {}),
            routeFingerprint: gateReceipt.routeFingerprint,
            status: 'kernel_verified',
            verifier: 'lean-kernel',
            theoremName: localResult.theoremName!,
            proofHash: localResult.proofHash,
            theoremDeclarationHash: localResult.theoremDeclarationHash!,
            ...(localResult.sourceDeclarationHash ? { sourceDeclarationHash: localResult.sourceDeclarationHash } : {}),
            goalsRemaining: 0,
            sorryCount: 0,
            admitCount: 0,
            axioms: localResult.axioms,
            checkedAt: localResult.checkedAt,
          });
          if (
            gateReceipt.localGateReceiptId !== localGateReceipt.receiptId ||
            gateReceipt.targetCommit !== localGateReceipt.targetCommit ||
            gateReceipt.statementHash !== localGateReceipt.statementHash
          ) {
            throw new Error('Lean-Eval official gate receipt does not match its LOCAL_GATE result.');
          }
          assertMathematicsOfficialCompareReceiptBinding(
            localGateReceipt,
            localResult,
            gateReceipt.localGateReceiptId,
            gateReceipt.routeFingerprint
          );
          if (
            (gateReceipt.claim || 'statement') !== (localGateReceipt.claim || 'statement') ||
            gateReceipt.theoremName !== localGateReceipt.theoremName ||
            gateReceipt.proofHash !== localGateReceipt.proofHash ||
            gateReceipt.theoremDeclarationHash !== localGateReceipt.theoremDeclarationHash ||
            (gateReceipt.sourceDeclarationHash !== undefined &&
              gateReceipt.sourceDeclarationHash !== localGateReceipt.sourceDeclarationHash)
          ) {
            throw new Error('Lean-Eval official gate receipt theorem identity does not match its LOCAL_GATE result.');
          }
          leanEvalOfficialGateUpdate = Object.freeze({
            problemId,
            localGateReceipt,
            officialGateReceipt: gateReceipt,
            localResult,
          });
        }
        const projectPortfolioSnapshot = resolvedProjectRoot
          ? readMathematicsProjectPortfolio(resolvedProjectRoot)
          : undefined;
        const mathRunIdentity = readMathRunHistoryIdentity();
        if (mathRunIdentity && projectPortfolioSnapshot?.status === 'ready') {
          assertMathRunPortfolioOrigin(projectPortfolioSnapshot.portfolio, mathRunIdentity);
        }
        let canonicalPortfolioSnapshot = projectPortfolioSnapshot;
        let portfolioIntegrity: 'trusted' | 'untrusted_terminal' | undefined;
        if (
          projectPortfolioSnapshot?.status === 'ready' &&
          isTerminalMathematicsPortfolio(projectPortfolioSnapshot.portfolio)
        ) {
          try {
            let verificationIndex = indexMathematicsVerifications(run);
            verificationIndex = recoverMathematicsPortfolioVerifications(
              run,
              projectPortfolioSnapshot.portfolio,
              resolvedProjectRoot!,
              verificationIndex
            );
            assertMathematicsRuntimeReceipts(run, projectPortfolioSnapshot.portfolio, verificationIndex);
            assertMathematicsDecisionGate(run, projectPortfolioSnapshot.portfolio);
            assertCurrentMathematicsPortfolioCommitted(resolvedProjectRoot!, projectPortfolioSnapshot.portfolio);
            portfolioIntegrity = 'trusted';
          } catch {
            portfolioIntegrity = 'untrusted_terminal';
            canonicalPortfolioSnapshot = {
              status: 'missing',
              path: projectPortfolioSnapshot.path,
              rawHash: projectPortfolioSnapshot.rawHash,
            };
          }
        }
        if (action !== 'get' && portfolioIntegrity === 'untrusted_terminal') {
          throw new Error(
            `${MATHEMATICS_PORTFOLIO_PATH} contains an untrusted terminal state. Restore the last accepted portfolio before mutating mathematics state.`
          );
        }
        if (action !== 'get' && canonicalPortfolioSnapshot?.status === 'invalid') {
          throw new Error(
            `${MATHEMATICS_PORTFOLIO_PATH} is invalid. Repair the canonical project portfolio before mutating mathematics state.`
          );
        }

        if (action === 'get') {
          const revisionBeforeSynchronization = current?.revision;
          current = synchronizeMathematicsPortfolio(run, target, current, currentPortfolio, canonicalPortfolioSnapshot);
          if (canonicalPortfolioSnapshot?.status === 'ready') {
            currentPortfolio = canonicalPortfolioSnapshot.portfolio;
          }
          const synchronizedFromProject = current?.revision !== revisionBeforeSynchronization;
          if (synchronizedFromProject) persistRunSnapshot(run);
          const normalizedPromptQuery = promptQuery
            ? {
                problemId: asString(promptQuery.problemId, ''),
                routeFingerprint: asString(promptQuery.routeFingerprint, ''),
                ...(promptQuery.planNodeId ? { planNodeId: asString(promptQuery.planNodeId) } : {}),
                ...(promptQuery.goal ? { goal: asString(promptQuery.goal) } : {}),
                ...(promptQuery.targetGoal ? { targetGoal: asString(promptQuery.targetGoal) } : {}),
                ...(promptQuery.targetProbeMode ? { targetProbeMode: promptQuery.targetProbeMode } : {}),
                ...(promptQuery.proofStateFingerprint
                  ? { proofStateFingerprint: asString(promptQuery.proofStateFingerprint) }
                  : {}),
                ...(promptQuery.failureKind ? { failureKind: promptQuery.failureKind } : {}),
                ...(promptQuery.failureDiagnostic
                  ? { failureDiagnostic: asString(promptQuery.failureDiagnostic) }
                  : {}),
                ...(promptQuery.routeCoverage !== undefined ? { routeCoverage: promptQuery.routeCoverage } : {}),
                ...(promptQuery.routeNodeLimit !== undefined ? { routeNodeLimit: promptQuery.routeNodeLimit } : {}),
                importModules: Array.isArray(promptQuery.importModules)
                  ? promptQuery.importModules.filter((value): value is string => typeof value === 'string')
                  : undefined,
                ...(promptQuery.sourceFile ? { sourceFile: asString(promptQuery.sourceFile) } : {}),
                ...(promptQuery.upstreamQueries ? { upstreamQueries: promptQuery.upstreamQueries } : {}),
                ...(promptQuery.packageQueries ? { packageQueries: promptQuery.packageQueries } : {}),
                ...(promptQuery.installedPackageScopes
                  ? { installedPackageScopes: promptQuery.installedPackageScopes }
                  : {}),
                ...(promptQuery.installedPackageQuery
                  ? { installedPackageQuery: promptQuery.installedPackageQuery }
                  : {}),
                installedPackageOffset: promptQuery.installedPackageOffset ?? 0,
                installedPackageCheckTypes: promptQuery.installedPackageCheckTypes ?? false,
                premiseLimit: promptQuery.premiseLimit,
                lessonLimit: promptQuery.lessonLimit,
              }
            : undefined;
          const promptProblem = normalizedPromptQuery
            ? currentPortfolio?.problems.find((problem) => problem.id === normalizedPromptQuery.problemId)
            : undefined;
          const frozenCorpus = readMathRunRetrievalCorpus(process.env, path.resolve(process.argv[1]));
          // The get response includes the full portfolio, including unscoped notes.
          // A mixed portfolio cannot be safely reduced to a prompt-only projection.
          if (frozenCorpus && currentPortfolio) {
            const problemId = currentPortfolio.activeProblemId;
            if (
              !problemId ||
              currentPortfolio.problems.length !== 1 ||
              currentPortfolio.problems[0].id !== problemId ||
              (normalizedPromptQuery && normalizedPromptQuery.problemId !== problemId) ||
              [
                ...currentPortfolio.attempts,
                ...currentPortfolio.examples,
                ...currentPortfolio.evidence,
                ...currentPortfolio.verifications,
                ...currentPortfolio.reviews,
              ].some((entry) => entry.problemId !== problemId)
            ) {
              throw new Error('Frozen mathematics retrieval requires a portfolio confined to the active problem.');
            }
          }
          if (frozenCorpus && normalizedPromptQuery?.packageQueries?.length) {
            throw new Error('Frozen mathematics retrieval forbids online package discovery.');
          }
          if (
            frozenCorpus &&
            promptProblem?.problemContract?.officialManifestId?.startsWith('lean-eval:') &&
            frozenCorpus.sources.some((source) => source.packageName.toLowerCase() !== 'mathlib')
          ) {
            throw new Error('LeanEval frozen retrieval is limited to Mathlib.');
          }
          if (
            frozenCorpus &&
            normalizedPromptQuery?.installedPackageScopes?.some((scope) => !frozenCorpus.scopes.includes(scope))
          ) {
            throw new Error('Frozen mathematics retrieval scope is outside the corpus.');
          }
          if (
            !frozenCorpus &&
            normalizedPromptQuery?.installedPackageQuery &&
            !normalizedPromptQuery.installedPackageScopes?.length
          ) {
            throw new Error('installedPackageQuery requires one or more installedPackageScopes.');
          }
          if (
            !frozenCorpus &&
            (normalizedPromptQuery?.packageQueries?.length || normalizedPromptQuery?.installedPackageScopes?.length) &&
            promptProblem?.problemContract?.officialManifestId?.startsWith('lean-eval:')
          ) {
            throw new Error(
              'Extended package discovery is forbidden for LeanEval. Protected tasks are limited to the approved Mathlib-only indexes.'
            );
          }
          const accessibleLeanClosure =
            currentPortfolio && normalizedPromptQuery && resolvedProjectRoot
              ? frozenCorpus
                ? await discoverLeanImportClosureUncached(resolvedProjectRoot, normalizedPromptQuery, true)
                : await discoverLeanImportClosure(resolvedProjectRoot, normalizedPromptQuery)
              : undefined;
          const promptCacheKey =
            currentPortfolio &&
            normalizedPromptQuery &&
            resolvedProjectRoot &&
            !frozenCorpus &&
            !normalizedPromptQuery.installedPackageScopes?.length
              ? `${path.resolve(resolvedProjectRoot)}\0${current?.revision ?? currentPortfolio.updatedAt}\0${await hashLeanInputFiles(
                  resolvedProjectRoot,
                  normalizedPromptQuery,
                  accessibleLeanClosure
                )}\0${JSON.stringify(normalizedPromptQuery)}`
              : undefined;
          const cachedPromptPack = promptCacheKey ? cacheGet(mathematicsPromptPackCache, promptCacheKey) : undefined;
          const [accessiblePremises, upstreamSearch, upstreamPackageSearch, installedPackageSearch] =
            normalizedPromptQuery && resolvedProjectRoot && !cachedPromptPack
              ? await Promise.all([
                  collectAccessibleLeanPremises(resolvedProjectRoot, normalizedPromptQuery, accessibleLeanClosure),
                  frozenCorpus
                    ? Promise.resolve({ premises: [], attempts: [], provenance: [] })
                    : normalizedPromptQuery.failureKind && normalizedPromptQuery.goal
                      ? retrieveLeanPremisesForFailure(
                          {
                            goal: normalizedPromptQuery.goal,
                            failureKind: normalizedPromptQuery.failureKind,
                            failureDiagnostic: normalizedPromptQuery.failureDiagnostic,
                            importModules: normalizedPromptQuery.importModules,
                            sourceFile: normalizedPromptQuery.sourceFile,
                            proofStateFingerprint: normalizedPromptQuery.proofStateFingerprint,
                            ...(normalizedPromptQuery.targetGoal
                              ? { targetGoal: normalizedPromptQuery.targetGoal }
                              : {}),
                          },
                          {
                            resultLimit: normalizedPromptQuery.premiseLimit,
                          }
                        )
                      : searchUpstreamLeanPremises(normalizedPromptQuery.upstreamQueries ?? {}, {
                          resultLimit: normalizedPromptQuery.premiseLimit,
                        }),
                  normalizedPromptQuery.packageQueries?.length
                    ? readLeanProjectCompatibility(resolvedProjectRoot).then((compatibility) =>
                        searchUpstreamLeanPackages(normalizedPromptQuery.packageQueries ?? [], compatibility)
                      )
                    : Promise.resolve({ packages: [], attempts: [] }),
                  frozenCorpus
                    ? Promise.resolve(
                        searchMathRetrievalCorpus(
                          resolvedProjectRoot,
                          frozenCorpus,
                          [
                            normalizedPromptQuery.installedPackageQuery ?? '',
                            normalizedPromptQuery.targetGoal ?? normalizedPromptQuery.goal ?? '',
                            ...Object.values(normalizedPromptQuery.upstreamQueries ?? {}).filter(
                              (value): value is string => typeof value === 'string'
                            ),
                          ],
                          normalizedPromptQuery.premiseLimit ?? 4,
                          normalizedPromptQuery.installedPackageOffset
                        )
                      )
                    : normalizedPromptQuery.installedPackageScopes?.length
                      ? searchInstalledLeanPackagePremises(
                          resolvedProjectRoot,
                          normalizedPromptQuery.installedPackageScopes,
                          [
                            normalizedPromptQuery.installedPackageQuery ?? '',
                            normalizedPromptQuery.goal ?? '',
                            normalizedPromptQuery.planNodeId ?? '',
                            normalizedPromptQuery.routeFingerprint,
                          ],
                          {
                            resultLimit: normalizedPromptQuery.premiseLimit ?? 4,
                            offset: normalizedPromptQuery.installedPackageOffset,
                            currentGoal: normalizedPromptQuery.targetGoal ?? normalizedPromptQuery.goal,
                          }
                        )
                      : Promise.resolve({ premises: [], attempts: [] }),
                ])
              : [[], { premises: [], attempts: [] }, { packages: [], attempts: [] }, { premises: [], attempts: [] }];
          const installedHeaderValidation =
            normalizedPromptQuery?.installedPackageCheckTypes && resolvedProjectRoot
              ? await validateInstalledLeanPremiseHeaders(resolvedProjectRoot, installedPackageSearch.premises, {
                  projectRelative: frozenCorpus?.projectSubdirectory,
                  currentGoal: normalizedPromptQuery.targetGoal ?? normalizedPromptQuery.goal,
                  dependencyFingerprint:
                    'corpusDigest' in installedPackageSearch && typeof installedPackageSearch.corpusDigest === 'string'
                      ? installedPackageSearch.corpusDigest
                      : undefined,
                })
              : undefined;
          const automaticPremiseValidation =
            normalizedPromptQuery?.failureKind &&
            normalizedPromptQuery.goal &&
            upstreamSearch.premises.length &&
            resolvedProjectRoot
              ? await validateLeanPremiseCandidates(
                  rankUpstreamLeanPremises(
                    upstreamSearch.premises,
                    normalizedPromptQuery.targetGoal || normalizedPromptQuery.goal,
                    8
                  ),
                  {
                    projectRoot: resolvedProjectRoot,
                    importModules: normalizedPromptQuery.importModules,
                    ...(normalizedPromptQuery.proofStateFingerprint
                      ? { proofStateFingerprint: normalizedPromptQuery.proofStateFingerprint }
                      : {}),
                    ...(normalizedPromptQuery.targetGoal ? { targetGoal: normalizedPromptQuery.targetGoal } : {}),
                    ...(normalizedPromptQuery.targetProbeMode
                      ? { targetProbeMode: normalizedPromptQuery.targetProbeMode }
                      : {}),
                    maxCandidates: 8,
                    ...(normalizedPromptQuery.targetGoal ? { stopAfterFirstTyped: true } : {}),
                  }
                )
              : undefined;
          // Public indexes are advisory and may return a broad lexical tail.
          // Rank every path against the exact live target before validation and
          // prompt construction; failure retrieval already supplies a precise
          // targetGoal, while ordinary queries fall back to the full query
          // context.  The Lean target probe remains the authority for adoption.
          const upstreamPremisesForPrompt = rankUpstreamLeanPremises(
            automaticPremiseValidation?.premises ?? upstreamSearch.premises,
            normalizedPromptQuery
              ? normalizedPromptQuery.targetGoal || normalizedPromptQuery.goal || normalizedPromptQuery.planNodeId || ''
              : '',
            32
          );
          const promptPack =
            cachedPromptPack ??
            (currentPortfolio && normalizedPromptQuery
              ? deriveMathematicsPromptPack(
                  currentPortfolio,
                  frozenCorpus
                    ? {
                        ...normalizedPromptQuery,
                        installedPackageScopes: normalizedPromptQuery.installedPackageScopes?.length
                          ? normalizedPromptQuery.installedPackageScopes
                          : [...frozenCorpus.scopes],
                      }
                    : normalizedPromptQuery,
                  accessiblePremises,
                  upstreamPremisesForPrompt,
                  upstreamSearch.attempts,
                  upstreamPackageSearch.packages,
                  upstreamPackageSearch.attempts,
                  installedHeaderValidation?.premises ?? installedPackageSearch.premises,
                  installedPackageSearch.attempts,
                  upstreamSearch.provenance ?? [],
                  mathRunIdentity || frozenCorpus ? 'same_problem' : 'portfolio'
                )
              : undefined);
          if (
            promptCacheKey &&
            promptPack &&
            !cachedPromptPack &&
            upstreamSearch.attempts.every((attempt) => attempt.status === 'ok') &&
            upstreamPackageSearch.attempts.every((attempt) => attempt.status === 'ok')
          ) {
            const hasRemoteLookup = upstreamSearch.attempts.length > 0 || upstreamPackageSearch.attempts.length > 0;
            cachePut(
              mathematicsPromptPackCache,
              promptCacheKey,
              promptPack,
              Date.now(),
              hasRemoteLookup ? MATHEMATICS_REMOTE_PROMPT_CACHE_TTL_MS : MATHEMATICS_PROMPT_CACHE_TTL_MS
            );
          }
          const contract = mathematicsPortfolioContract(resolvedProjectRoot, !currentPortfolio);
          const feasibilityRanking = currentPortfolio
            ? deriveMathematicsFeasibilityRanking(currentPortfolio, currentPortfolio.updatedAt)
            : undefined;
          let leanEvalIntake: Readonly<Record<string, unknown>> | undefined;
          const catalogRoot = leanEvalRepositoryRoot || process.env.DEEPSCIENTIST_LEAN_EVAL_ROOT;
          if (catalogRoot && !frozenCorpus) {
            try {
              // Caller-supplied credits are test/display data only. They never
              // participate in official eligibility; production intake uses the
              // fetched leaderboard snapshot.
              const leaderboard = leanEvalCredits
                ? {
                    credits: [] as readonly Record<string, unknown>[],
                    generatedAt: Date.now(),
                    sourceUrl: 'caller-supplied:test-only',
                  }
                : await fetchLeanEvalLeaderboardCredits();
              const catalog = readLeanEvalCatalog({
                repositoryRoot: catalogRoot,
                benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
                credits: leaderboard.credits,
                generatedAt: leaderboard.generatedAt,
                verifyGitCommit: true,
              });
              const activeProblems = catalog.problems.filter(
                (problem) => problem.activeV1 && problem.status === 'active' && problem.visible
              );
              const cacheRoot = resolvedProjectRoot || catalogRoot;
              const compileProbeEnabled = process.env.DEEPSCIENTIST_LEAN_EVAL_COMPILE_PROBE === '1';
              const compileProbeLimit = compileProbeEnabled ? leanEvalCompileProbeLimit() : 0;
              const elaborationProbeEnabled = process.env.DEEPSCIENTIST_LEAN_EVAL_ELABORATION_PROBE === '1';
              const elaborationProbeLimit = elaborationProbeEnabled ? leanEvalCompileProbeLimit() : 0;
              const outcomeLedgerRevision = resolvedProjectRoot
                ? readLeanEvalOutcomeLedgerRevision(resolvedProjectRoot)
                : '';
              const baseAnalyses = await mapWithConcurrency(activeProblems, 4, async (problem) => {
                const cached = readCachedLeanEvalAnalysis({
                  cacheRoot,
                  benchmarkCommit: catalog.benchmarkCommit,
                  catalogHash: catalog.catalogHash,
                  problemId: problem.id,
                  toolchain: 'leanprover/lean4:v4.33.0',
                  outcomeLedgerRevision,
                });
                if (
                  cached &&
                  (!compileProbeEnabled || cached.firstCompileProbe.attempted) &&
                  (!elaborationProbeEnabled || cached.elaborationProbe?.attempted)
                )
                  return cached;
                const analysis = await analyzeLeanEvalProblem(problem, {
                  repositoryRoot: catalogRoot,
                  benchmarkCommit: catalog.benchmarkCommit,
                  ...(resolvedProjectRoot
                    ? {
                        historicalOutcomes: (() => {
                          const summary = readLeanEvalOutcomeSummary(resolvedProjectRoot, problem.id);
                          return { attempts: summary.attempts, successes: summary.successes };
                        })(),
                      }
                    : {}),
                });
                writeCachedLeanEvalAnalysis(
                  {
                    cacheRoot,
                    benchmarkCommit: catalog.benchmarkCommit,
                    catalogHash: catalog.catalogHash,
                    problemId: problem.id,
                    toolchain: 'leanprover/lean4:v4.33.0',
                    outcomeLedgerRevision,
                  },
                  analysis
                );
                return analysis;
              });
              const eligibleIds = new Set(
                catalog.problems.filter((problem) => problem.eligible).map((problem) => problem.id)
              );
              const initialRanking = rankMathFeasibilityCandidates(
                baseAnalyses.filter((entry) => eligibleIds.has(entry.problemId)).map((entry) => entry.feasibility)
              );
              const compileProbeIds = new Set(
                initialRanking
                  .slice(0, Math.max(compileProbeLimit, elaborationProbeLimit))
                  .flatMap((candidate) => (candidate.candidateId ? [candidate.candidateId] : []))
              );
              const analyzed =
                (compileProbeEnabled || elaborationProbeEnabled) && compileProbeIds.size
                  ? await mapWithConcurrency(baseAnalyses, 2, async (analysis) => {
                      if (!compileProbeIds.has(analysis.problemId)) return analysis;
                      const problem = catalog.problems.find((candidate) => candidate.id === analysis.problemId);
                      if (!problem) return analysis;
                      const probed = await analyzeLeanEvalProblem(problem, {
                        repositoryRoot: catalogRoot,
                        benchmarkCommit: catalog.benchmarkCommit,
                        ...(resolvedProjectRoot
                          ? {
                              historicalOutcomes: (() => {
                                const summary = readLeanEvalOutcomeSummary(resolvedProjectRoot, problem.id);
                                return { attempts: summary.attempts, successes: summary.successes };
                              })(),
                            }
                          : {}),
                        ...(compileProbeEnabled
                          ? { compileProbe: (problemRoot: string) => runLeanEvalSandboxedCompileProbe(problemRoot) }
                          : {}),
                        ...(elaborationProbeEnabled
                          ? {
                              elaborationProbe: (
                                problemRoot: string,
                                declarations: readonly string[],
                                dependencyTargets: readonly string[]
                              ) =>
                                runLeanEvalSandboxedElaborationProbe(
                                  problemRoot,
                                  declarations,
                                  30_000,
                                  dependencyTargets
                                ),
                            }
                          : {}),
                      });
                      writeCachedLeanEvalAnalysis(
                        {
                          cacheRoot,
                          benchmarkCommit: catalog.benchmarkCommit,
                          catalogHash: catalog.catalogHash,
                          problemId: problem.id,
                          toolchain: 'leanprover/lean4:v4.33.0',
                          outcomeLedgerRevision,
                        },
                        probed
                      );
                      return probed;
                    })
                  : baseAnalyses;
              const ranked = rankMathFeasibilityCandidates(
                analyzed.filter((entry) => eligibleIds.has(entry.problemId)).map((entry) => entry.feasibility)
              );
              const intakeReceipt = createLeanEvalIntakeReceipt(
                catalog,
                analyzed,
                leaderboard.sourceUrl,
                'leanprover/lean4:v4.33.0'
              );
              const intakePage = paginateLeanEvalAnalyses(catalog, analyzed, ranked, intakeReceipt, {
                page: leanEvalPage,
                pageSize: leanEvalPageSize,
                problemId: leanEvalProblemId,
              });
              const receiptPath = resolvedProjectRoot
                ? persistLeanEvalIntakeReceipt(resolvedProjectRoot, intakeReceipt)
                : undefined;
              leanEvalIntake = Object.freeze({
                schema: 'deepscientist.mathematics.lean-eval-intake.v1',
                repositoryUrl: catalog.repositoryUrl,
                benchmarkCommit: catalog.benchmarkCommit,
                setId: catalog.setId,
                catalogHash: catalog.catalogHash,
                eligibleProblemCount: catalog.problems.filter((problem) => problem.eligible).length,
                zeroCreditProblemCount: catalog.problems.filter((problem) => problem.eligible && problem.zeroCredit)
                  .length,
                compileProbe: Object.freeze({
                  enabled: compileProbeEnabled,
                  limit: compileProbeLimit,
                  problemIds: Object.freeze([...compileProbeIds].toSorted()),
                }),
                elaborationProbe: Object.freeze({
                  enabled: elaborationProbeEnabled,
                  limit: elaborationProbeLimit,
                  problemIds: Object.freeze(
                    elaborationProbeEnabled
                      ? initialRanking
                          .slice(0, elaborationProbeLimit)
                          .flatMap((candidate) => (candidate.candidateId ? [candidate.candidateId] : []))
                      : []
                  ),
                }),
                receipt: intakeReceipt,
                ...(receiptPath ? { receiptPath } : {}),
                page: intakePage.page,
                pageSize: intakePage.pageSize,
                totalPages: intakePage.totalPages,
                detailProblemId: leanEvalProblemId,
                analyses: intakePage.analyses,
                ranking: intakePage.ranking,
              });
            } catch (error) {
              leanEvalIntake = Object.freeze({
                schema: 'deepscientist.mathematics.lean-eval-intake.v1',
                benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT,
                error: error instanceof Error ? error.message : String(error),
              });
            }
          }
          return jsonText({
            schema: MATHEMATICS_EVENT_SCHEMA,
            eventId: eventId(),
            tool: 'math_portfolio',
            action,
            runId: run.runId,
            timestamp: now(),
            target,
            exists: Boolean(current),
            currentRevision: current?.revision,
            object: current,
            portfolio: currentPortfolio,
            portfolioIntegrity,
            synchronizedFromProject,
            ...(promptPack
              ? { promptPack }
              : { reusablePremises: currentPortfolio ? deriveMathematicsReusablePremises(currentPortfolio) : [] }),
            ...('corpusDigest' in installedPackageSearch
              ? { retrievalCorpusDigest: installedPackageSearch.corpusDigest }
              : {}),
            ...('coverage' in installedPackageSearch
              ? {
                  installedPackageCoverage: installedPackageSearch.coverage,
                  retrievalInterpretation:
                    'Complete refers to permitted source files in the selected package or frozen corpus. Declaration headers are parsed lexically; generated declarations and applicability still require Lean checks. An empty lexical search does not establish that no applicable theorem exists.',
                }
              : {}),
            ...(feasibilityRanking && feasibilityRanking.candidates.length ? { feasibilityRanking } : {}),
            ...(leanEvalIntake ? { leanEvalIntake } : {}),
            ...(!currentPortfolio
              ? {
                  contract,
                  starterTemplate: contract.starterTemplate,
                }
              : {
                  revisionPolicy: contract.revisionPolicy,
                }),
            decision: currentPortfolio
              ? getMathematicsTerminalGateReadiness(currentPortfolio, currentPortfolio.activeProblemId, {
                  verifiedOfficialReceiptIds: verifiedMathematicsOfficialReceiptIds(currentPortfolio),
                }).decision
              : undefined,
            displayIntent: displayIntent || 'focus',
          });
        }

        // Every mutating operation must first project the latest canonical file
        // into the run.  Otherwise a stale in-memory run can overwrite a newer
        // portfolio while still passing its caller-supplied revision check.
        if (canonicalPortfolioSnapshot?.status === 'ready') {
          const revisionBeforeSynchronization = current?.revision;
          current = synchronizeMathematicsPortfolio(run, target, current, currentPortfolio, canonicalPortfolioSnapshot);
          currentPortfolio = canonicalPortfolioSnapshot.portfolio;
          if (current?.revision !== revisionBeforeSynchronization) persistRunSnapshot(run);
        }

        if (leanEvalOfficialGateUpdate) {
          if (!currentPortfolio) {
            throw new Error('math_portfolio(action="official_gate") requires an existing canonical portfolio.');
          }
          const update = leanEvalOfficialGateUpdate;
          if (!currentPortfolio.problems.some((entry) => entry.id === update.problemId)) {
            throw new Error(
              `Lean-Eval official gate problem ${update.problemId} is absent from the canonical portfolio.`
            );
          }
          currentPortfolio = Object.freeze({
            ...currentPortfolio,
            problems: currentPortfolio.problems.map((entry) =>
              entry.id === update.problemId
                ? Object.freeze({
                    ...entry,
                    localGateReceipt: update.localGateReceipt,
                    officialGateReceipt: update.officialGateReceipt,
                    updatedAt: now(),
                  })
                : entry
            ),
            updatedAt: now(),
          });
        }

        let candidate: MathematicsPortfolio | undefined;
        let reviewStateUpdate: JsonRecord | undefined;
        if (portfolio) {
          candidate = portfolio as unknown as MathematicsPortfolio;
          if (action !== 'submit') {
            const submittedValidation = validateMathematicsPortfolio(portfolio);
            if (!submittedValidation.ok) {
              throw new Error(`Mathematics portfolio validation failed: ${submittedValidation.errors.join(' ')}`);
            }
            candidate = normalizeValidatedMathematicsPortfolio(portfolio as Record<string, unknown>);
          }
        } else if (current) {
          candidate = currentPortfolio;
        }

        if (action === 'official_gate') {
          if (!leanEvalOfficialGate || !candidate) {
            throw new Error('math_portfolio(action="official_gate") requires an existing canonical portfolio.');
          }
          // The gate branch already prepared an immutable problem update above;
          // keep all other portfolio records unchanged and let the normal
          // revision/lock/write path publish it atomically.
          candidate = currentPortfolio;
        }

        if (action === 'patch') {
          if (!candidate || !portfolioPatch) {
            throw new Error('math_portfolio(action="patch") requires an existing portfolio.');
          }
          candidate = patchMathematicsPortfolio(candidate, portfolioPatch as unknown as MathematicsPortfolioPatch);
        }

        if (action === 'request_review') {
          if (!candidate) throw new Error('math_portfolio(action="request_review") requires an existing portfolio.');
          const reviewId = asString(review?.id, `review_${Date.now().toString(36)}`);
          const reviewProblemId = asString(review?.problemId, candidate.activeProblemId || '');
          const reviewProblem = candidate.problems.find((item) => item.id === reviewProblemId);
          if (!reviewProblem) throw new Error(`Review ${reviewId} must reference an existing mathematics problem.`);
          const reviewTargetCommit = asString(targetCommit || review?.targetCommit, '');
          const reviewStatementHash = asString(statementHash || review?.statementHash, '');
          if (!reviewTargetCommit || reviewTargetCommit === 'WORKTREE') {
            throw new Error('A mathematics review must target a committed Git revision.');
          }
          if (reviewProblem.statementHash && reviewStatementHash !== reviewProblem.statementHash) {
            throw new Error(`Review ${reviewId} must match problem ${reviewProblem.id}'s statementHash.`);
          }
          const reviewRecord = {
            id: reviewId,
            problemId: reviewProblemId,
            status: 'queued' as const,
            targetCommit: reviewTargetCommit,
            statementHash: reviewStatementHash,
            reviewerSessionId: asString(review?.reviewerSessionId, undefined as unknown as string),
            issueIds: Array.isArray(review?.issueIds)
              ? review.issueIds.filter((item): item is string => typeof item === 'string')
              : [],
            updatedAt: now(),
          };
          reviewStateUpdate = reviewRecord;
          candidate = {
            ...candidate,
            stage: 'review',
            status: 'needs_review',
            reviews: [...candidate.reviews.filter((item) => item.id !== reviewId), reviewRecord],
            updatedAt: now(),
          };
        } else if (action === 'submit_review') {
          if (!candidate || !review)
            throw new Error('math_portfolio(action="submit_review") requires an existing portfolio and review.');
          const reviewId = asString(review.id, '');
          if (!reviewId) throw new Error('review.id is required.');
          const nextReview: JsonRecord & { id: string; updatedAt: number } = {
            ...(review as JsonRecord),
            id: reviewId,
            updatedAt: asNumber(review.updatedAt, now()),
          };
          reviewStateUpdate = nextReview;
          const reviewProblemId = asString(nextReview.problemId, '');
          const reviewProblem = candidate.problems.find((item) => item.id === reviewProblemId);
          if (!reviewProblem) throw new Error(`Review ${reviewId} must reference an existing mathematics problem.`);
          if (!asString(nextReview.targetCommit, '') || asString(nextReview.targetCommit, '') === 'WORKTREE') {
            throw new Error('A mathematics review must target a committed Git revision.');
          }
          if (reviewProblem.statementHash && asString(nextReview.statementHash, '') !== reviewProblem.statementHash) {
            throw new Error(`Review ${reviewId} must match problem ${reviewProblem.id}'s statementHash.`);
          }
          candidate = {
            ...candidate,
            reviews: [
              ...candidate.reviews.filter((item) => item.id !== reviewId),
              nextReview as unknown as MathematicsPortfolio['reviews'][number],
            ],
            updatedAt: now(),
          };
        }

        if (!candidate) throw new Error('math_portfolio mutation requires an existing or submitted portfolio.');
        // Stage history is runtime-authored. Never accept a caller-supplied
        // history as authority, and never allow a terminal stage to roll back.
        const storedPortfolio = currentPortfolio;
        if (storedPortfolio) {
          if (['verified', 'refuted'].includes(storedPortfolio.stage) && candidate.stage !== storedPortfolio.stage) {
            throw new Error(`Mathematics portfolio cannot roll back from terminal stage ${storedPortfolio.stage}.`);
          }
          const history = [...(storedPortfolio.stageHistory ?? [])];
          if (candidate.stage !== storedPortfolio.stage) {
            history.push({
              from: storedPortfolio.stage,
              to: candidate.stage,
              commit: targetCommit?.trim() || 'WORKTREE',
              timestamp: candidate.updatedAt,
              reason: changeSummary?.trim() || `stage transition ${storedPortfolio.stage} -> ${candidate.stage}`,
            });
          }
          candidate = { ...candidate, stageHistory: history };
        } else {
          candidate = { ...candidate, stageHistory: [] };
        }
        const validation = validateMathematicsPortfolio(candidate);
        if (!validation.ok) throw new Error(`Mathematics portfolio validation failed: ${validation.errors.join(' ')}`);
        candidate = normalizeValidatedMathematicsPortfolio(candidate as unknown as Record<string, unknown>);
        if (mathRunIdentity) {
          candidate = bindMathRunPortfolio(candidate, mathRunIdentity);
          assertMathRunPortfolioPremises(candidate, run.mathematicsVerifications);
        }
        let verificationIndex = indexMathematicsVerifications(run);
        const referencedVerificationIds = new Set(
          candidate.problems
            .map((problem) => problem.verificationId)
            .filter((verificationId): verificationId is string => Boolean(verificationId))
        );
        const kernelVerifications: MathematicsPortfolio['verifications'][number][] = [];
        for (const verification of candidate.verifications) {
          if (referencedVerificationIds.has(verification.id) && verification.status === 'kernel_verified') {
            kernelVerifications.push(verification);
          }
        }
        if (resolvedProjectRoot) {
          verificationIndex = recoverMathematicsPortfolioVerifications(
            run,
            candidate,
            resolvedProjectRoot,
            verificationIndex
          );
        }
        // Validate against the gate result before publishing it into the run.
        // This keeps all pre-commit validation failures side-effect free.
        if (leanEvalOfficialGateUpdate) {
          const gateResult = leanEvalOfficialGateUpdate.localResult;
          const existing = verificationIndex.byReceiptId.get(gateResult.receiptId) || [];
          if (
            !existing.some(
              (item) =>
                item.status === 'kernel_verified' &&
                item.verifier === 'lean-kernel' &&
                item.targetCommit === gateResult.targetCommit &&
                item.statementHash === gateResult.statementHash &&
                item.claim === gateResult.claim &&
                item.proofHash === gateResult.proofHash &&
                item.theoremName === gateResult.theoremName &&
                item.theoremDeclarationHash === gateResult.theoremDeclarationHash &&
                item.sourceDeclarationHash === gateResult.sourceDeclarationHash
            )
          ) {
            verificationIndex = indexMathematicsVerifications({
              ...run,
              mathematicsVerifications: [...run.mathematicsVerifications, gateResult],
            });
          }
        }
        assertMathematicsRuntimeReceipts(run, candidate, verificationIndex);
        const terminalReadiness = assertMathematicsDecisionGate(run, candidate);
        if (resolvedProjectRoot) {
          assertTerminalMathematicsPortfolioCommitted(resolvedProjectRoot, targetCommit, candidate);
        }
        if (kernelVerifications.length) {
          for (const entry of kernelVerifications) {
            if (!entry.theoremName) {
              throw new Error(
                `Verification ${entry.id} must name the Lean theorem certified for this terminal statement.`
              );
            }
            const verificationKey = JSON.stringify([
              entry.proofHash,
              entry.targetCommit,
              entry.statementHash,
              entry.claim || 'statement',
              entry.theoremName,
            ]);
            if (!verificationIndex.kernelIdentityKeys.has(verificationKey)) {
              throw new Error(
                `Verification ${entry.id} is not backed by a stored successful Lean receipt for the same proof hash, statement hash, claim, theorem, and target commit.`
              );
            }
          }
        }
        if (current) assertBaseRevision(current, baseRevision);
        const portfolioPath = resolvedProjectRoot ? MATHEMATICS_PORTFOLIO_PATH : undefined;
        const mutationAction = current ? 'patch' : 'create';
        const mutationPayload: JsonRecord = current
          ? {
              metadata: { mathematics: candidate },
              evidenceIds: mathematicsEvidenceIds(candidate),
              ...(portfolioPath ? { primaryPath: portfolioPath } : {}),
              ...(title ? { title } : {}),
              ...(changeSummary ? { changeSummary } : {}),
            }
          : {
              type: 'run_bundle',
              title: title || candidate.title,
              status: 'available',
              viewer: { kind: 'mathematics' },
              metadata: { mathematics: candidate },
              evidenceIds: mathematicsEvidenceIds(candidate),
              ...(portfolioPath ? { primaryPath: portfolioPath } : {}),
              ...(changeSummary ? { changeSummary } : {}),
            };
        const previousReview = run.mathematicsReview;
        const previousEdges = new Map(run.edges);
        const previousMathematicsVerification = run.mathematicsVerification;
        const previousMathematicsVerifications = [...run.mathematicsVerifications];
        const previousMathematicsVerificationEvents = [...run.mathematicsVerificationEvents];
        const previousMathematicsVerificationCapability = run.mathematicsVerificationCapability;
        const previousMathematicsOfficialGateReceipts = [...run.mathematicsOfficialGateReceipts];
        const previousUpdatedAt = run.updatedAt;
        const restoreMutationState = (): void => {
          run.mathematicsVerification = previousMathematicsVerification;
          run.mathematicsVerifications = previousMathematicsVerifications;
          run.mathematicsVerificationEvents = previousMathematicsVerificationEvents;
          run.mathematicsVerificationCapability = previousMathematicsVerificationCapability;
          run.mathematicsOfficialGateReceipts = previousMathematicsOfficialGateReceipts;
          run.updatedAt = previousUpdatedAt;
        };
        if (leanEvalOfficialGateUpdate) {
          const update = leanEvalOfficialGateUpdate;
          if (
            !run.mathematicsVerifications.some(
              (result) =>
                result.status === 'kernel_verified' &&
                result.verifier === 'lean-kernel' &&
                result.receiptId === update.localResult.receiptId &&
                result.targetCommit === update.localResult.targetCommit &&
                result.statementHash === update.localResult.statementHash &&
                result.claim === update.localResult.claim &&
                result.proofHash === update.localResult.proofHash &&
                result.theoremName === update.localResult.theoremName &&
                result.theoremDeclarationHash === update.localResult.theoremDeclarationHash &&
                result.sourceDeclarationHash === update.localResult.sourceDeclarationHash
            )
          ) {
            run.mathematicsVerifications.push(update.localResult);
          }
          const retainedOfficialReceipts = run.mathematicsOfficialGateReceipts.filter(
            (receipt) =>
              !(
                receipt.targetCommit === update.officialGateReceipt.targetCommit &&
                receipt.statementHash === update.officialGateReceipt.statementHash &&
                receipt.localGateReceiptId === update.officialGateReceipt.localGateReceiptId &&
                receipt.routeFingerprint === update.officialGateReceipt.routeFingerprint
              )
          );
          retainedOfficialReceipts.push(update.officialGateReceipt);
          if (retainedOfficialReceipts.length > 512) {
            retainedOfficialReceipts.splice(0, retainedOfficialReceipts.length - 512);
          }
          run.mathematicsOfficialGateReceipts = retainedOfficialReceipts;
        }
        let result: { object: unknown; target: TargetRef; resultingRevision?: string };
        const commitMutation = (): void => {
          result = createOrReplaceResource(run, mutationAction, target, mutationPayload, baseRevision, false);
          try {
            // The resource projection is the commit boundary.  Write the
            // project-owned portfolio only after the in-memory mutation succeeds,
            // and use an atomic rename so a failed write cannot leave a truncated
            // portfolio that disagrees with the artifact projection.
            if (resolvedProjectRoot) {
              writeMathematicsProjectPortfolio(resolvedProjectRoot, candidate, canonicalPortfolioSnapshot?.rawHash);
            }
          } catch (error) {
            const key = artifactKey(target.id || MATHEMATICS_PORTFOLIO_ARTIFACT_ID, target.version || 1);
            if (current) run.artifacts.set(key, current);
            else run.artifacts.delete(key);
            run.edges = previousEdges;
            run.mathematicsReview = previousReview;
            restoreMutationState();
            throw error;
          }
        };
        try {
          if (resolvedProjectRoot) withMathematicsPortfolioLock(resolvedProjectRoot, commitMutation);
          else commitMutation();
        } catch (error) {
          // Lock acquisition can fail before commitMutation runs.  Restore the
          // same runtime fields in that case so an uncommitted gate cannot be
          // observed by a later request in this process.
          restoreMutationState();
          throw error;
        }
        if (reviewStateUpdate) run.mathematicsReview = reviewStateUpdate;
        const panel = buildPanel(run);
        const evt = eventFor(run, mutationAction, result.target, {
          baseRevision,
          resultingRevision: result.resultingRevision,
          artifactIds: [id],
          panel,
          displayIntent: displayIntent || 'focus',
          warnings: validateGraph(run),
        });
        return jsonText({
          ...evt,
          schema: MATHEMATICS_EVENT_SCHEMA,
          tool: 'math_portfolio',
          operation:
            action === 'official_gate'
              ? 'official_gate_persisted'
              : action === 'request_review'
                ? 'review_requested'
                : action === 'submit_review'
                  ? 'review_submitted'
                  : current
                    ? 'updated'
                    : 'registered',
          currentRevision: result.resultingRevision,
          mutationReceipt: {
            target,
            previousRevision: current?.revision,
            currentRevision: result.resultingRevision,
            reuseAsBaseRevision: true,
          },
          portfolio: candidate,
          reusablePremises: deriveMathematicsReusablePremises(candidate),
          decision: terminalReadiness.decision,
          ...(leanEvalOfficialGate
            ? {
                officialGateReceipt: leanEvalOfficialGate.gate.officialGateReceipt,
                receiptPath: leanEvalOfficialGate.receiptPath,
                persisted: true,
              }
            : {}),
          object: result.object,
        });
      }
    );
  }

  

  server.tool(
    'science_artifact',
    SCIENCE_ARTIFACT_TOOL_DESCRIPTION,
    {
      action: z.enum([
        'describe',
        'status',
        'reserve_id',
        'get',
        'list',
        'query_many',
        'transact',
        'create',
        'patch',
        'replace',
        'append',
        'version',
        'submit_idea',
        'get_optimization_frontier',
        'record_main_experiment',
        'checkpoint',
        'research_frontier',
        'prepare_branch',
        'activate_branch',
        'compare_branches',
        'snapshot',
        'publish',
        'annotate',
        'focus_page',
      ]),
      runId: z.string().optional(),
      conversationId: z.string().optional(),
      messageId: z.string().optional(),
      toolCallId: z.string().optional(),
      projectRoot: z.string().optional(),
      target: z
        .object({
          kind: z
            .enum([
              'run',
              'report',
              'artifact',
              'page',
              'evidence',
              'claim',
              'provenance',
              'skill_use',
              'annotation',
              'memory',
            ])
            .optional(),
          id: z.string().optional(),
          version: z.number().optional(),
          pageId: z.string().optional(),
        })
        .optional(),
      baseRevision: z.string().optional(),
      createIfMissing: z.boolean().optional(),
      payload: z.record(z.unknown()).optional(),
      queries: z.array(scienceArtifactQueryInput).min(1).max(64).optional(),
      operations: z.array(scienceArtifactTransactionOperationInput).min(1).max(64).optional(),
      commandId: z.string().trim().min(1).max(240).optional(),
      atomicity: z.literal('all_or_nothing').optional(),
      dryRun: z.boolean().optional(),
      displayIntent: z.enum(['background', 'open', 'focus']).optional(),
      userAuthorizedClose: z.boolean().optional(),
    },
    async ({
      action,
      runId: requestedRunId,
      conversationId,
      messageId,
      toolCallId,
      projectRoot,
      target,
      baseRevision,
      createIfMissing,
      payload,
      queries,
      operations,
      commandId,
      atomicity,
      dryRun,
      displayIntent,
      userAuthorizedClose,
    }) => {
      assertResearchTeamToolActionAuthorized('science_artifact', action);
      if (action === 'describe') {
        return jsonText({
          schema: SCIENCE_EVENT_SCHEMA,
          tool: 'science_artifact',
          action,
          timestamp: now(),
          contract: SCIENCE_ARTIFACT_FULL_CONTRACT,
          reportVisualRoles: SCIENCE_REPORT_VISUAL_ROLES,
          guidance:
            'Read the loaded science-artifact skill first. Use this full contract only for report, Viewer, evidence-boundary, or publication details not covered by the compact tool description.',
          displayIntent: 'background',
        });
      }
      const body = payload || {};
      const specializedMutationPayloads = operations?.map((operation) => operation.payload) || [];
      if (isFactorPortfolioArtifactMutation(action, body)) {
        throw new Error(
          `Financial factor portfolios must be registered with factor_registry(action="register"). Do not create or version ${FINANCIAL_FACTOR_PORTFOLIO_PATH} with science_artifact; factor_registry validates the complete portfolio, updates the dedicated Viewer, and writes that project mirror atomically.`
        );
      }
      if (isMathematicsPortfolioArtifactMutation(action, body)) {
        throw new Error(
          `Mathematics portfolios must be registered with math_portfolio(action="submit"). Do not create or version ${MATHEMATICS_PORTFOLIO_PATH} with science_artifact; math_portfolio validates the typed state, prevents fabricated verification, updates the dedicated Viewer, and writes the project mirror.`
        );
      }
      if (specializedMutationPayloads.some((item) => isFactorPortfolioArtifactMutation('create', item))) {
        throw new Error(
          'science_artifact transactions cannot mutate a Financial factor portfolio; use factor_registry.'
        );
      }
      if (specializedMutationPayloads.some((item) => isMathematicsPortfolioArtifactMutation('create', item))) {
        throw new Error('science_artifact transactions cannot mutate a Mathematics portfolio; use math_portfolio.');
      }
      const projectGitWriteAction =
        action === 'checkpoint' || action === 'prepare_branch' || action === 'activate_branch';
      if ((action === 'prepare_branch' || action === 'activate_branch') && !requestedRunId) {
        throw new Error('science_artifact branch aliases require an explicit runId.');
      }
      const resolvedConversationId = resolveSessionIdentifier(
        conversationId,
        PROJECT_WORKSPACE_ENV_KEYS.conversationId,
        'conversationId'
      );
      const resolvedProjectRoot = projectGitWriteAction
        ? await requireBoundProjectRoot(projectRoot, resolvedConversationId)
        : resolveSessionProjectRoot(projectRoot);
      const run = ensureRun(requestedRunId, resolvedProjectRoot, body);
      applyRunContext(run, body, { conversationId: resolvedConversationId, messageId, toolCallId });

      if (action === 'status') {
        const financeCompletionGuide = buildFinanceCompletionGuide(
          body.financeTaskContractId || body.finance_task_contract_id,
          run
        );
        return jsonText({
          schema: SCIENCE_EVENT_SCHEMA,
          action,
          runId: run.runId,
          panel: buildPanel(run),
          openRuns: [...runs.keys()],
          reportAuthoringGuide: buildReportAuthoringGuide(run),
          ...(financeCompletionGuide ? { financeCompletionGuide } : {}),
        });
      }

      if (action === 'query_many') {
        if (!queries?.length) throw new Error('science_artifact(action="query_many") requires queries[].');
        const duplicateQueryIds = queries
          .map((query) => query.queryId)
          .filter((queryId, index, values) => values.indexOf(queryId) !== index);
        if (duplicateQueryIds.length) {
          throw new Error(`query_many queryIds must be unique: ${duplicateQueryIds.join(', ')}`);
        }
        const results = queries.map((query) => {
          const queryTarget = query.target as TargetRef;
          if (query.scope === 'project' && ['run', 'report'].includes(queryTarget.kind || '')) {
            return {
              queryId: query.queryId,
              status: 'unsupported_scope',
              items: [] as unknown[],
              error: `Project-scoped ${queryTarget.kind} queries are ambiguous; query a specific run instead.`,
            };
          }
          let values: unknown[];
          if (query.scope === 'project') {
            values = listProjectResource(run.projectRoot, queryTarget.kind) || [];
            if (queryTarget.id) {
              values = values.filter((value) => isRecord(value) && value.id === queryTarget.id);
            }
          } else if (queryTarget.id || queryTarget.pageId || ['run', 'report'].includes(queryTarget.kind || '')) {
            const value = getResource(run, queryTarget);
            values = value == null ? [] : [value];
          } else {
            values = listResource(run, queryTarget.kind);
          }
          return {
            queryId: query.queryId,
            status: values.length ? 'ok' : 'not_found',
            items: values.map((value) => projectSelectedFields(value, query.select)),
          };
        });
        return jsonStructured({
          schema: SCIENCE_EVENT_SCHEMA,
          tool: 'science_artifact',
          action,
          runId: run.runId,
          snapshotVersion: scienceRunSnapshotVersion(run),
          results,
          displayIntent: displayIntent || 'background',
        });
      }

      if (action === 'transact') {
        if (!operations?.length) throw new Error('science_artifact(action="transact") requires operations[].');
        if (atomicity && atomicity !== 'all_or_nothing') {
          throw new Error('science_artifact transactions support only atomicity="all_or_nothing".');
        }
        const duplicateOperationIds = operations
          .map((operation) => operation.opId)
          .filter((opId, index, values) => values.indexOf(opId) !== index);
        if (duplicateOperationIds.length) {
          throw new Error(`Transaction opIds must be unique: ${duplicateOperationIds.join(', ')}`);
        }
        const requestHash = sha256(JSON.stringify({ operations, atomicity: 'all_or_nothing' }));
        const effectiveCommandId = commandId || toolCallId || `auto-${requestHash.slice(0, 24)}`;
        const previousCommand = effectiveCommandId ? run.commandReceipts.get(effectiveCommandId) : undefined;
        if (previousCommand) {
          if (previousCommand.requestHash !== requestHash) {
            throw new Error('IDEMPOTENCY_KEY_REUSED: commandId was already used with a different transaction.');
          }
          return jsonStructured({ ...previousCommand.response, replayed: true });
        }

        const candidate = cloneScienceRunState(run);
        const operationReceipts = operations.map((operation) => {
          if (
            operation.action === 'create' &&
            !operation.target.id &&
            !operation.target.pageId &&
            !['run', 'report'].includes(operation.target.kind)
          ) {
            throw new Error(
              `Operation ${operation.opId} must give create a stable target id so retries and later operations refer to the same record.`
            );
          }
          if (
            operation.target.id === MATHEMATICS_PORTFOLIO_ARTIFACT_ID ||
            isMathematicsPortfolioArtifactMutation(operation.action, operation.payload)
          ) {
            throw new Error(`Operation ${operation.opId} must use math_portfolio for Mathematics state.`);
          }
          if (
            operation.target.id === FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID ||
            isFactorPortfolioArtifactMutation(operation.action, operation.payload)
          ) {
            throw new Error(`Operation ${operation.opId} must use factor_registry for Financial factor state.`);
          }
          if (operation.target.id === TARGET_DISCOVERY_PORTFOLIO_ARTIFACT_ID) {
            throw new Error(`Operation ${operation.opId} must use target_portfolio for Target Discovery state.`);
          }
          const result = createOrReplaceResource(
            candidate,
            operation.action,
            operation.target as TargetRef,
            operation.payload,
            operation.baseRevision,
            operation.createIfMissing
          );
          return {
            opId: operation.opId,
            status: 'applied',
            target: result.target,
            previousRevision: operation.baseRevision,
            currentRevision: result.resultingRevision,
            object: result.object,
          };
        });

        if (dryRun) {
          return jsonStructured({
            schema: SCIENCE_EVENT_SCHEMA,
            tool: 'science_artifact',
            action,
            runId: run.runId,
            committed: false,
            dryRun: true,
            atomicity: 'all_or_nothing',
            operationReceipts,
            warnings: validateGraph(candidate),
            displayIntent: displayIntent || 'background',
          });
        }

        Object.assign(run, candidate);
        const changedTargets = operationReceipts.map((receipt) => receipt.target);
        const evt = eventFor(run, action, undefined, {
          artifactIds: changedTargets
            .filter((changed) => changed.kind === 'artifact' && changed.id)
            .map((changed) => changed.id as string),
          evidenceIds: changedTargets
            .filter((changed) => changed.kind === 'evidence' && changed.id)
            .map((changed) => changed.id as string),
          claimIds: changedTargets
            .filter((changed) => changed.kind === 'claim' && changed.id)
            .map((changed) => changed.id as string),
          panel: displayIntent && displayIntent !== 'background' ? buildPanel(run) : undefined,
          displayIntent: displayIntent || 'background',
          warnings: validateGraph(run),
        });
        const response: JsonRecord = {
          ...evt,
          tool: 'science_artifact',
          committed: true,
          atomicity: 'all_or_nothing',
          commandId: effectiveCommandId,
          requestHash,
          operationReceipts,
          nextContext: {
            revisions: Object.fromEntries(
              operationReceipts
                .filter((receipt) => receipt.currentRevision)
                .map((receipt) => [receipt.opId, receipt.currentRevision])
            ),
            snapshotVersion: scienceRunSnapshotVersion(run),
          },
          financeReceipt: scienceArtifactFinanceReceipt(run, action),
        };
        if (effectiveCommandId) {
          run.commandReceipts.set(effectiveCommandId, {
            id: effectiveCommandId,
            requestHash,
            response,
            createdAt: now(),
          });
          if (run.commandReceipts.size > 256) {
            const oldest = [...run.commandReceipts.values()].toSorted(
              (left, right) => left.createdAt - right.createdAt
            )[0];
            if (oldest) run.commandReceipts.delete(oldest.id);
          }
          persistRunSnapshot(run);
        }
        return jsonStructured(response);
      }

      if (action === 'reserve_id') {
        const kind = (target?.kind || body.kind || 'artifact') as ScienceArtifactResourceKind;
        const id = asString(target?.id || body.id, makeId(kind));
        const evt = eventFor(
          run,
          action,
          { kind, id, version: target?.version || (kind === 'artifact' ? 1 : undefined) },
          {
            artifactIds: kind === 'artifact' ? [id] : undefined,
            pageIds: kind === 'page' ? [id] : undefined,
            evidenceIds: kind === 'evidence' ? [id] : undefined,
            claimIds: kind === 'claim' ? [id] : undefined,
          }
        );
        return jsonText({ ...evt, reserved: { kind, id, version: evt.target?.version } });
      }

      if (action === 'get') {
        const anchorInput = body.gitAnchor || body.git_anchor || body.anchor;
        if (isRecord(anchorInput) && anchorInput.kind === 'git_lines') {
          if (!run.projectRoot) throw new Error('projectRoot is required to read Git lines.');
          const filePath = asString(
            anchorInput.filePath || anchorInput.file_path || anchorInput.path,
            undefined as unknown as string
          );
          if (!filePath) throw new Error('A git_lines anchor requires filePath.');
          return jsonText(
            readScienceArtifactGitLines({
              projectRoot: run.projectRoot,
              anchor: {
                kind: 'git_lines',
                commit: asString(anchorInput.commit, undefined as unknown as string),
                filePath,
                lineStart: asNumber(anchorInput.lineStart || anchorInput.line_start, 1),
                lineEnd:
                  anchorInput.lineEnd || anchorInput.line_end
                    ? asNumber(anchorInput.lineEnd || anchorInput.line_end, 1)
                    : undefined,
                side: anchorInput.side === 'parent' ? 'parent' : 'current',
              },
            })
          );
        }
        const object = getResource(run, target);
        return jsonText({
          schema: SCIENCE_EVENT_SCHEMA,
          eventId: eventId(),
          runId: run.runId,
          action,
          timestamp: now(),
          target,
          object,
        });
      }

      if (action === 'list') {
        const scope = asString(body.scope, 'run');
        const evidenceIndex =
          scope === 'project' && target?.kind === 'evidence' && run.projectRoot
            ? searchScienceArtifactEvidenceIndex({
                projectRoot: run.projectRoot,
                query: asString(body.query, undefined as unknown as string),
                runId: asString(body.runId || body.run_id, undefined as unknown as string),
                artifactId: asString(body.artifactId || body.artifact_id, undefined as unknown as string),
                limit: asNumber(body.limit, 80),
              })
            : undefined;
        const projectItems =
          evidenceIndex?.ok === true
            ? evidenceIndex.items.map((item) => item.evidence)
            : scope === 'project'
              ? listProjectResource(run.projectRoot, target?.kind)
              : undefined;
        return jsonText({
          schema: SCIENCE_EVENT_SCHEMA,
          eventId: eventId(),
          runId: run.runId,
          action,
          timestamp: now(),
          target,
          scope,
          items: projectItems || listResource(run, target?.kind),
          evidenceIndex: evidenceIndex?.ok ? evidenceIndex.items : undefined,
        });
      }

      if (action === 'get_optimization_frontier') {
        const taskScope = optimizationTaskScope(
          body.taskId || body.task_id,
          body.sealId || body.seal_id,
          'get_optimization_frontier task scope'
        );
        return jsonText({
          schema: SCIENCE_EVENT_SCHEMA,
          eventId: eventId(),
          runId: run.runId,
          action,
          timestamp: now(),
          optimizationFrontier: buildOptimizationFrontier(run, taskScope),
        });
      }

      if (action === 'submit_idea') {
        const result = submitOptimizationIdea(run, body);
        const evt = eventFor(
          run,
          action,
          { kind: 'artifact', id: result.artifact.id, version: result.artifact.version },
          {
            resultingRevision: result.artifact.revision,
            artifactIds: [result.artifact.id, ...(result.promotedCandidate ? [result.promotedCandidate.id] : [])],
            evidenceIds: result.artifact.evidenceIds,
            displayIntent: displayIntent || 'background',
          }
        );
        return jsonText({
          ...evt,
          operation: result.metadata.kind === 'idea_candidate' ? 'candidate_recorded' : 'line_recorded',
          submissionMode: result.metadata.kind === 'idea_candidate' ? 'candidate' : 'line',
          ideaId: result.metadata.ideaId,
          lineId: result.metadata.lineId,
          sourceCandidateId: result.metadata.sourceCandidateId,
          object: result.artifact,
          promotedCandidate: result.promotedCandidate,
        });
      }

      if (action === 'record_main_experiment') {
        const result = recordOptimizationMainExperiment(run, body);
        const evt = eventFor(
          run,
          action,
          { kind: 'artifact', id: result.resultArtifact.id, version: result.resultArtifact.version },
          {
            resultingRevision: result.resultArtifact.revision,
            artifactIds: [result.resultArtifact.id, result.lineArtifact.id],
            evidenceIds: result.resultArtifact.evidenceIds,
            displayIntent: displayIntent || 'background',
          }
        );
        return jsonText({
          ...evt,
          operation: 'main_experiment_recorded',
          runIdentifier: result.metadata.runId,
          lineId: result.metadata.lineId,
          resultArtifact: result.resultArtifact,
          lineArtifact: result.lineArtifact,
          optimizationFrontier: buildOptimizationFrontier(
            run,
            optimizationTaskScope(result.metadata.taskId, result.metadata.sealId)
          ),
        });
      }

      if (action === 'create' || action === 'patch' || action === 'replace') {
        const result = createOrReplaceResource(run, action, target, body, baseRevision, createIfMissing);
        const targetPortfolio =
          result.target.kind === 'artifact'
            ? readTargetDiscoveryPortfolio((result.object as ScienceArtifact).metadata)
            : undefined;
        const factorPortfolio =
          result.target.kind === 'artifact'
            ? readFinancialFactorPortfolio((result.object as ScienceArtifact).metadata)
            : undefined;
        const resolvedDisplayIntent = displayIntent || (targetPortfolio || factorPortfolio ? 'focus' : undefined);
        const evt = eventFor(run, action, result.target, {
          baseRevision,
          resultingRevision: result.resultingRevision,
          artifactIds: result.target.kind === 'artifact' && result.target.id ? [result.target.id] : undefined,
          pageIds: result.target.kind === 'page' && result.target.id ? [result.target.id] : undefined,
          evidenceIds: result.target.kind === 'evidence' && result.target.id ? [result.target.id] : undefined,
          claimIds: result.target.kind === 'claim' && result.target.id ? [result.target.id] : undefined,
          panel: resolvedDisplayIntent ? buildPanel(run) : undefined,
          displayIntent: resolvedDisplayIntent,
          warnings: validateGraph(run),
        });
        return jsonText({
          ...evt,
          object: result.object,
          mutationReceipt: {
            target: result.target,
            previousRevision: baseRevision,
            currentRevision: result.resultingRevision,
            reuseAsBaseRevision: true,
          },
          financeReceipt: scienceArtifactFinanceReceipt(run, action),
        });
      }

      if (action === 'append') {
        const appendTarget = target?.kind || (body.kind as ScienceArtifactResourceKind | undefined);
        if (!appendTarget) throw new Error('append requires target.kind.');
        const items = Array.isArray(body.items) ? body.items : [body];
        if (items.length === 0) throw new Error('append requires at least one item.');
        if (items.length > 64) throw new Error('append accepts at most 64 items per atomic batch.');
        const candidate = cloneScienceRunState(run);
        const created = [];
        for (const [index, item] of items.entries()) {
          if (!isRecord(item)) throw new Error(`append items[${index}] must be an object.`);
          const result = createOrReplaceResource(candidate, 'create', { kind: appendTarget }, item, undefined, true);
          created.push(result.object);
        }
        Object.assign(run, candidate);
        const evt = eventFor(run, action, target, { warnings: validateGraph(run) });
        return jsonText({ ...evt, items: created, financeReceipt: scienceArtifactFinanceReceipt(run, action) });
      }

      if (action === 'version') {
        if (target?.kind !== 'artifact' || !target.id)
          throw new Error('version requires target.kind="artifact" and target.id.');
        const currentVersion = target.version || 1;
        const current = run.artifacts.get(artifactKey(target.id, currentVersion));
        if (!current) throw new Error(`Artifact ${target.id}@${currentVersion} does not exist.`);
        assertBaseRevision(current, baseRevision);
        const nextVersion = asNumber(body.version, currentVersion + 1);
        const nextPayload = deepMerge(current, {
          ...body,
          id: target.id,
          version: nextVersion,
          previousArtifactId: current.id,
          previousVersion: current.version,
          versionGroupId: current.versionGroupId || current.id,
        }) as JsonRecord;
        const artifact = normalizeArtifact(run, { ...nextPayload, revision: revision() });
        run.artifacts.set(artifactKey(artifact.id, artifact.version), artifact);
        syncArtifactEdges(run, artifact);
        const targetPortfolio = readTargetDiscoveryPortfolio(artifact.metadata);
        const factorPortfolio = readFinancialFactorPortfolio(artifact.metadata);
        const resolvedDisplayIntent = displayIntent || (targetPortfolio || factorPortfolio ? 'focus' : undefined);
        const evt = eventFor(
          run,
          action,
          { kind: 'artifact', id: artifact.id, version: artifact.version },
          {
            baseRevision,
            resultingRevision: artifact.revision,
            artifactIds: [artifact.id],
            panel: resolvedDisplayIntent ? buildPanel(run) : undefined,
            displayIntent: resolvedDisplayIntent,
            warnings: validateGraph(run),
          }
        );
        return jsonText({
          ...evt,
          object: artifact,
          mutationReceipt: {
            target: { kind: 'artifact', id: artifact.id, version: artifact.version },
            previousRevision: current.revision,
            currentRevision: artifact.revision,
            reuseAsBaseRevision: true,
          },
          financeReceipt: scienceArtifactFinanceReceipt(run, action),
        });
      }

      if (action === 'research_frontier') {
        if (!run.projectRoot) throw new Error('projectRoot is required to inspect the research frontier.');
        const routeState = researchRouteForRun(run);
        const frontier = listProjectGitResearchFrontier({
          workspace: run.projectRoot,
          goalId: asString(body.goalId || body.goal_id, routeState.map?.goalId || (undefined as unknown as string)),
        });
        if (!frontier.ok) throw new Error(frontier.error || 'The research frontier could not be read.');
        return jsonText({
          action,
          runId: run.runId,
          displayIntent: displayIntent || 'background',
          frontier,
          researchRoute: routeState.presentation || null,
          message: `Found ${frontier.branches.length} research branch(es); active branch is ${frontier.activeBranch || 'detached HEAD'}.`,
        });
      }

      if (action === 'prepare_branch') {
        if (!run.projectRoot) throw new Error('projectRoot is required to prepare a research branch.');
        const branch = asString(body.branch || body.name, undefined as unknown as string);
        const routeNodeId = asString(body.routeNodeId || body.route_node_id, undefined as unknown as string);
        const routeSelection = requireAnsweredResearchRouteBranchSelection(run, routeNodeId);
        if (routeSelection.node?.git?.branchRef) {
          throw new Error('The selected research route node already owns a Git branch; activate that branch instead.');
        }
        const prepared = prepareProjectGitResearchBranch({
          workspace: resolvedProjectRoot,
          branch,
          from: asString(body.from || body.fromSha || body.from_sha || body.startPoint || body.start_point, 'HEAD'),
          parentRef: asString(body.parentRef || body.parent_ref, undefined as unknown as string),
          goalId: asString(body.goalId || body.goal_id, undefined as unknown as string),
          routeNodeId,
          objective: asString(body.objective || body.reason, undefined as unknown as string),
        });
        if (!prepared.ok || !prepared.branch)
          throw new Error(prepared.error || 'The research branch could not be prepared.');
        return jsonText({
          action,
          runId: run.runId,
          displayIntent: displayIntent || 'background',
          branch: prepared.branch,
          message: `Created and activated research branch ${prepared.branch.name} at ${prepared.branch.shortHead}.`,
        });
      }

      if (action === 'activate_branch') {
        if (!run.projectRoot) throw new Error('projectRoot is required to activate a research branch.');
        const branch = asString(body.branch || body.name, undefined as unknown as string);
        const routeNodeId = asString(body.routeNodeId || body.route_node_id, undefined as unknown as string);
        const routeSelection = requireAnsweredResearchRouteBranchSelection(run, routeNodeId);
        if (routeSelection.node && routeSelection.node.git?.branchRef !== branch) {
          throw new Error('The requested branch does not match the selected research route node.');
        }
        const activated = activateProjectGitResearchBranch({
          workspace: resolvedProjectRoot,
          branch,
          routeNodeId,
        });
        if (!activated.ok || !activated.branch)
          throw new Error(activated.error || 'The research branch could not be activated.');
        return jsonText({
          action,
          runId: run.runId,
          displayIntent: displayIntent || 'background',
          branch: activated.branch,
          message: `Activated research branch ${activated.branch.name} at ${activated.branch.shortHead}. Re-read README.md and the latest checkpoint before editing.`,
        });
      }

      if (action === 'compare_branches') {
        if (!run.projectRoot) throw new Error('projectRoot is required to compare research branches.');
        const compared = compareProjectGitResearchBranches({
          workspace: run.projectRoot,
          baseRef: asString(body.baseRef || body.base_ref || body.base, undefined as unknown as string),
          headRef: asString(body.headRef || body.head_ref || body.head, undefined as unknown as string),
        });
        if (!compared.ok) throw new Error(compared.error || 'The research branches could not be compared.');
        return jsonText({
          action,
          runId: run.runId,
          displayIntent: displayIntent || 'background',
          comparison: compared,
          message: `Compared ${compared.base?.name || 'base'} with ${compared.head?.name || 'head'}; ${compared.metrics.filter((metric) => metric.comparable).length} metric(s) are directly comparable.`,
        });
      }

      if (action === 'checkpoint') {
        if (!run.projectRoot) throw new Error('projectRoot is required to create a Git checkpoint.');
        const includePaths = normalizeIncludePaths(body.includePaths || body.include_paths || body.paths);
        const metrics = normalizeCheckpointMetrics(
          body.metrics || body.performanceMetrics || body.performance_metrics || body.metric
        );
        const metricContext = normalizeMetricContext(
          body.metricContext || body.metric_context || body.evaluationContext || body.evaluation_context
        );
        const linkedArtifact =
          target?.kind === 'artifact' && target.id
            ? run.artifacts.get(artifactKey(target.id, target.version || 1))
            : undefined;
        const targetPortfolio = readTargetDiscoveryPortfolio(linkedArtifact?.metadata);
        const factorPortfolio = readFinancialFactorPortfolio(linkedArtifact?.metadata);
        const mathematicsPortfolio = readMathematicsPortfolio(linkedArtifact?.metadata);
        const checkpointDomainFallback = targetPortfolio
          ? 'target_discovery'
          : factorPortfolio
            ? 'financial_factor'
            : mathematicsPortfolio
              ? 'mathematics'
              : 'research';
        const checkpointDomain = sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.domain)
          ? resolveBoundProjectDomain(body.domain || body.workflow, checkpointDomainFallback)
          : normalizeProjectDomain(body.domain || body.workflow, checkpointDomainFallback);
        const sessionStagesBound = Boolean(sessionEnvValue(PROJECT_WORKSPACE_ENV_KEYS.checkpointStages));
        const requestedCheckpointStage = asString(body.stage, '');
        if (!requestedCheckpointStage) {
          throw new Error('science_artifact checkpoint alias requires an explicit stage.');
        }
        const checkpointStage = sessionStagesBound
          ? resolveBoundCheckpointStage(requestedCheckpointStage || undefined)
          : requestedCheckpointStage;
        const verification = normalizeCheckpointVerification(body.verification || body.validations);
        if (verification.length === 0) {
          throw new Error('science_artifact checkpoint alias requires at least one completed verification entry.');
        }
        const artifactRef = linkedArtifact
          ? {
              runId: run.runId,
              artifactId: linkedArtifact.id,
              version: linkedArtifact.version,
              revision: linkedArtifact.revision,
            }
          : undefined;
        const targetSummary = targetPortfolio ? summarizeTargetDiscoveryPortfolio(targetPortfolio) : undefined;
        const requestedResearchStrategy = body.routeMode || body.route_mode || body.strategy;
        const explicitResearchStrategy = normalizeResearchStrategy(requestedResearchStrategy);
        if (requestedResearchStrategy && !explicitResearchStrategy) {
          throw new Error('science_artifact checkpoint alias received an invalid research strategy.');
        }
        const researchStage = normalizeResearchStageReceipt(body.researchStage || body.research_stage);
        const roadmap = researchRouteForRun(run).map;
        const explicitRouteNodeId = asString(body.routeNodeId || body.route_node_id, '');
        const inferredRouteNode = roadmap
          ? roadmap.nodes.find(
              (node) =>
                node.id === explicitRouteNodeId ||
                node.id === researchStage?.stageId ||
                (!explicitRouteNodeId && !researchStage?.stageId && node.id === roadmap.focusNodeId)
            )
          : undefined;
        if (roadmap && explicitRouteNodeId && !inferredRouteNode) {
          throw new Error(
            'science_artifact checkpoint alias routeNodeId does not exist in the active research roadmap.'
          );
        }
        const expectedResearchStrategy = inferredRouteNode?.strategy || roadmap?.routeMode;
        if (
          explicitResearchStrategy &&
          expectedResearchStrategy &&
          explicitResearchStrategy !== expectedResearchStrategy
        ) {
          throw new Error('science_artifact checkpoint alias strategy conflicts with the active research route.');
        }
        const researchStrategy = explicitResearchStrategy || expectedResearchStrategy;
        const routeNodeId = explicitRouteNodeId || inferredRouteNode?.id;
        const repairsNodeId =
          asString(body.repairsNodeId || body.repairs_node_id, '') || inferredRouteNode?.repairsNodeId;
        if (requiresResearchStrategyForCheckpoint(checkpointDomain, checkpointStage) && !researchStrategy) {
          throw new Error(
            `science_artifact checkpoint stage ${checkpointStage} requires payload.routeMode: explore, deepen, fuse, repair, or stop.`
          );
        }
        const checkpoint = createProjectGitCheckpoint({
          workspace: resolvedProjectRoot,
          message: asString(body.message || body.summary, undefined as unknown as string),
          stage: checkpointStage,
          researchStrategy,
          routeNodeId,
          repairsNodeId,
          includePaths: includePaths.map((item) => item.path),
          verification,
          metrics,
          metricContext,
          goalId: asString(body.goalId || body.goal_id, undefined as unknown as string),
          researchStage,
          runId: run.runId,
          conversationId: run.conversationId,
          domain: checkpointDomain,
          artifactRef,
          targetSummary,
        });
        if (!checkpoint.ok || !checkpoint.commit || !checkpoint.shortCommit || !checkpoint.subject) {
          throw new Error(checkpoint.error || 'The project Git checkpoint could not be created.');
        }
        const sourceGit: ScienceSourceGitRef = {
          repoRoot: checkpoint.repository?.repoRoot,
          branch: checkpoint.repository?.branch,
          commit: checkpoint.commit,
          shortCommit: checkpoint.shortCommit,
          subject: checkpoint.subject,
          stage: checkpoint.stage,
          researchStrategy: checkpoint.researchStrategy,
          routeNodeId: checkpoint.routeNodeId,
          repairsNodeId: checkpoint.repairsNodeId,
          domain: checkpoint.domain,
          artifactRef: checkpoint.artifactRef,
          targetSummary: checkpoint.targetSummary,
          changedFiles: checkpoint.changedFiles,
          verification: checkpoint.verification,
          metrics: checkpoint.metrics,
          metricContext: checkpoint.metricContext,
          goalId: checkpoint.goalId,
          researchStage: checkpoint.researchStage,
        };
        run.sourceGit = sourceGit;
        const evt = eventFor(
          run,
          action,
          { kind: 'run', id: run.runId },
          {
            sourceGit,
            warnings: validateGraph(run),
            snapshot: { includePaths },
          },
          includePaths
        );
        return jsonText({
          ...evt,
          displayIntent: displayIntent || 'background',
          checkpoint: sourceGit,
          message: `Created project checkpoint ${sourceGit.shortCommit} and linked its artifact snapshot.`,
        });
      }

      if (action === 'snapshot') {
        const includePaths = normalizeIncludePaths(body.includePaths || body.include_paths || body.paths);
        const evt = eventFor(
          run,
          action,
          target,
          {
            warnings: validateGraph(run),
            snapshot: {
              includePaths,
            },
          },
          includePaths
        );
        return jsonText({
          ...evt,
          displayIntent: displayIntent || 'background',
          message:
            includePaths.length > 0
              ? `Recorded ${includePaths.length} explicit include path(s) in the project artifact git snapshot.`
              : 'Recorded a project artifact git snapshot.',
        });
      }

      if (action === 'annotate') {
        const annotationPayload = {
          ...body,
          artifactId:
            asString(body.artifactId || body.artifact_id, undefined as unknown as string) ||
            (target?.kind === 'artifact' ? target.id : undefined),
          pageId:
            asString(body.pageId || body.page_id, undefined as unknown as string) ||
            (target?.kind === 'page' ? target.pageId || target.id : target?.pageId),
        };
        const result = createOrReplaceResource(
          run,
          'create',
          {
            kind: 'annotation',
            id: target?.kind === 'annotation' ? target.id : asString(body.id, undefined as unknown as string),
            pageId: annotationPayload.pageId,
          },
          annotationPayload,
          undefined,
          true
        );
        const annotation = result.object as AnnotationRecord;
        if (annotation.artifactId) {
          upsertEdge(run, {
            id: `edge_${annotation.id}_${annotation.artifactId}`,
            runId: run.runId,
            from: { kind: 'message', id: annotation.id },
            to: { kind: 'artifact', id: annotation.artifactId },
            type: 'annotates',
            confidence: 'declared',
            createdAt: now(),
          });
        }
        const evt = eventFor(run, action, result.target, {
          resultingRevision: result.resultingRevision,
          artifactIds: annotation.artifactId ? [annotation.artifactId] : undefined,
          pageIds: annotation.pageId ? [annotation.pageId] : undefined,
        });
        return jsonText({ ...evt, object: annotation, financeReceipt: scienceArtifactFinanceReceipt(run, action) });
      }

      if (action === 'focus_page') {
        const pageIds =
          target?.pageId || target?.id
            ? [target.pageId || target.id || '']
            : asArray(body.pageIds || body.page_ids).filter((item): item is string => typeof item === 'string');
        const panel = buildPanel(run);
        const evt = eventFor(
          run,
          action,
          { kind: 'page', id: pageIds[0], pageId: pageIds[0] },
          {
            pageIds,
            warnings:
              userAuthorizedClose !== true && asString(body.closePageId || body.close_page_id)
                ? [
                    {
                      id: `warn_close_not_authorized_${Date.now()}`,
                      runId: run.runId,
                      severity: 'warning',
                      code: 'broken_reference',
                      message:
                        'The agent requested a page close without userAuthorizedClose=true; UI should ignore close-like behavior.',
                      createdAt: now(),
                    },
                  ]
                : undefined,
          }
        );
        return jsonText({ ...evt, panel, displayIntent: displayIntent || 'focus' });
      }

      if (action === 'publish') {
        await synchronizeTargetDiscoveryDelivery(run);
        const candidate: ScienceRunState = {
          ...run,
          report: run.report ? clone(run.report) : undefined,
          cards: clone(run.cards),
          cardDiagnostics: [...run.cardDiagnostics],
          financeCompletion: run.financeCompletion ? clone(run.financeCompletion) : undefined,
          financePreflight: run.financePreflight ? clone(run.financePreflight) : undefined,
          statsPatch: run.statsPatch ? clone(run.statsPatch) : undefined,
          evidence: new Map(run.evidence),
          artifacts: new Map(run.artifacts),
          pages: new Map(run.pages),
          claims: new Map(run.claims),
          provenance: new Map(run.provenance),
          edges: new Map(run.edges),
          graphWarnings: new Map(run.graphWarnings),
          usedSkills: new Map(run.usedSkills),
          annotations: new Map(run.annotations),
          commandReceipts: new Map(run.commandReceipts),
          memory: [...run.memory],
          events: [...run.events],
        };
        if (body.question) candidate.question = asString(body.question, candidate.question);
        if (body.summary) candidate.summary = asString(body.summary, candidate.summary as string);
        if (body.status) candidate.status = normalizePanelStatus(body.status, candidate.status, true);
        if (hasVisualWaiverReason(body)) {
          candidate.visualWaiverReason = readVisualWaiverReason(body);
        }
        if (isRecord(body.report)) {
          if (hasVisualWaiverReason(body.report)) {
            candidate.visualWaiverReason = readVisualWaiverReason(body.report);
          }
          candidate.report = normalizeReport(body.report);
          syncReportResources(candidate, candidate.report);
        } else {
          syncReportResources(candidate, candidate.report);
        }
        applyRunCardPayload(candidate, body);
        if (body.financeCompletion !== undefined) applyFinanceCompletion(candidate, body.financeCompletion);
        assertTargetDiscoveryPublicationReady(candidate);
        assertResultSummaryEvidence(candidate);
        if (isRecord(body.stats)) candidate.statsPatch = body.stats as Partial<SciencePanelData['stats']>;
        const candidateWarnings = validateGraph(candidate);
        const candidateVerification = buildClaimVerification([...candidate.claims.values()], candidateWarnings);
        if (
          candidate.status === 'completed' &&
          candidateVerification.totalClaims > 0 &&
          candidateVerification.state !== 'verified'
        ) {
          candidate.status = 'partial';
        }
        candidate.financePreflight = preflightRunFinanceCompletion(
          candidate,
          candidate.report || {
            title: candidate.question || 'Science Artifact Report',
            sections: [{ id: 'summary', heading: 'Research Output', blocks: fallbackBlocks(candidate) }],
          },
          candidate.cards
        );
        // Presentation helpers are advisory for Finance Mode.  A reader-first
        // report with verified evidence must remain publishable even when a
        // provider, card suggestion, or optional section is unavailable.  The
        // preflight result keeps those gaps visible and marks the panel partial.
        if (candidate.financePreflight?.status === 'blocked') {
          candidate.status = 'blocked';
        } else if (
          candidate.financePreflight &&
          candidate.financePreflight.status !== 'completed' &&
          candidate.status !== 'failed'
        ) {
          candidate.status = 'partial';
        }
        Object.assign(run, candidate);
        let panel = buildPanel(run);
        let visualReview =
          panel.visualReview ||
          reviewScienceReportVisuals(panel.report, panel.artifacts, panel.status, panel.cards, run.visualWaiverReason);
        if (run.status === 'completed' && visualReview.demand === 'required' && visualReview.visualCount === 0) {
          run.status = 'partial';
          panel = buildPanel(run);
          visualReview =
            panel.visualReview ||
            reviewScienceReportVisuals(
              panel.report,
              panel.artifacts,
              panel.status,
              panel.cards,
              run.visualWaiverReason
            );
        }
        const evt = eventFor(run, action, target, {
          panel,
          artifactIds: panel.artifacts.map((item) => item.id),
          pageIds: panel.pages?.map((item) => item.id),
          evidenceIds: panel.evidence.map((item) => item.id),
          claimIds: panel.claims?.map((item) => item.id),
          provenanceNodeIds: panel.provenance.map((item) => item.id),
          warnings: panel.graphWarnings,
        });
        return jsonText({
          ...evt,
          verification: panel.verification,
          visualReview,
          publicationGap: buildFinancePublicationGap(panel.financePreflight),
          displayIntent: displayIntent || 'open',
          financeReceipt: scienceArtifactFinanceReceipt(run, action),
        });
      }

      throw new Error(`Unsupported science_artifact action: ${action}`);
    }
  );

  const transport = new StdioServerTransport();
  installMathMcpShutdown(() => server.close());
  await server.connect(transport);
}

main().catch((error) => {
  console.error('[ScienceArtifactMCP] Fatal error:', error);
  process.exit(1);
});
