/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

/** Runtime-neutral contracts shared by research Team profiles and orchestrators. */

import {
  MATH_PROOF_STAGES,
  MATH_WORKFLOW_STAGES,
  assertNormalizedMathRouteCardsStructurallyDistinct,
  normalizeMathAlignmentCheck,
  normalizeMathCandidateReview,
  normalizeMathFailureLedger,
  normalizeMathFastCheck,
  normalizeMathLesson,
  normalizeMathLocalGateReceipt,
  normalizeMathHelperReceipt,
  normalizeMathNodeProofReceipt,
  normalizeMathOfficialGateReceipt,
  normalizeMathPlanNodeId,
  normalizeMathProofPlan,
  normalizeMathProofState,
  normalizeMathProgressDelta,
  normalizeMathProblemContract,
  normalizeMathResearchFinding,
  normalizeMathResearchProblemContract,
  normalizeMathWorkflowStage,
  normalizeMathRecoveryCheckpoint,
  normalizeMathRouteCard,
  normalizeMathRouteFingerprint,
  normalizeMathRouteProbeReceipt,
  normalizeMathRouteSelectionFromNormalized,
  normalizeMathExecutionPolicy,
  type MathAlignmentCheck,
  type MathCandidateReview,
  type MathFailureLedger,
  type MathFastCheck,
  type MathLesson,
  type MathLocalGateReceipt,
  type MathHelperReceipt,
  type MathNodeProofReceipt,
  type MathOfficialGateReceipt,
  type MathProgressDelta,
  type MathProofPlan,
  type MathProofState,
  type MathProblemContract,
  type MathResearchFinding,
  type MathResearchProblemContract,
  type MathProofStage,
  type MathWorkflowStage,
  type MathRecoveryCheckpoint,
  type MathRouteCard,
  type MathRouteProbeReceipt,
  type MathRouteSelection,
  type MathExecutionPolicy,
} from "./mathematicsTeam";

export const RESEARCH_TEAM_PROFILE_SCHEMA = 'deepscientist.research-team.profile.v1' as const;
export const RESEARCH_TEAM_POOL_SCHEMA = 'deepscientist.research-team.pool.v1' as const;
export const RESEARCH_TEAM_ASSIGNMENT_SCHEMA = 'deepscientist.research-team.assignment.v1' as const;
export const RESEARCH_TEAM_RESULT_SCHEMA = 'deepscientist.research-team.result.v1' as const;

export const RESEARCH_TEAM_EXECUTION_PROFILES = ['assist', 'parallel', 'extreme'] as const;
export type ResearchTeamExecutionProfile = (typeof RESEARCH_TEAM_EXECUTION_PROFILES)[number];

export type ResearchTeamPoolConfig = Readonly<{
  executionProfile: ResearchTeamExecutionProfile;
  /** Reusable Worker slots. The Lead is not included. */
  agentLimit: number;
  /** Maximum simultaneously active Worker reasoning turns. */
  reasoningConcurrency: number;
}>;

export type ResearchTeamPoolContract = Readonly<{
  schema: typeof RESEARCH_TEAM_POOL_SCHEMA;
  executionProfile: ResearchTeamExecutionProfile;
  agentLimit: number;
  reasoningConcurrency: number;
}>;

export const RESEARCH_TEAM_POOL_PRESETS: Readonly<Record<ResearchTeamExecutionProfile, ResearchTeamPoolConfig>> =
  Object.freeze({
    assist: Object.freeze({ executionProfile: 'assist', agentLimit: 4, reasoningConcurrency: 2 }),
    parallel: Object.freeze({ executionProfile: 'parallel', agentLimit: 8, reasoningConcurrency: 4 }),
    extreme: Object.freeze({ executionProfile: 'extreme', agentLimit: 16, reasoningConcurrency: 8 }),
  });

export const DEFAULT_RESEARCH_TEAM_EXECUTION_PROFILE: ResearchTeamExecutionProfile = 'parallel';
export const RESEARCH_TEAM_MIN_AGENT_LIMIT = 1;
export const RESEARCH_TEAM_MAX_AGENT_LIMIT = 50;
export const RESEARCH_TEAM_MIN_REASONING_CONCURRENCY = 1;
export const RESEARCH_TEAM_MAX_REASONING_CONCURRENCY = 16;

export type NormalizeResearchTeamPoolOptions = Readonly<{
  minimumAgentLimit?: number;
  maximumAgentLimit?: number;
  maximumReasoningConcurrency?: number;
}>;

export function normalizeResearchTeamPoolConfig(
  value?: Partial<ResearchTeamPoolConfig>,
  options: NormalizeResearchTeamPoolOptions = {}
): ResearchTeamPoolConfig {
  const executionProfile = isResearchTeamExecutionProfile(value?.executionProfile)
    ? value.executionProfile
    : DEFAULT_RESEARCH_TEAM_EXECUTION_PROFILE;
  const preset = RESEARCH_TEAM_POOL_PRESETS[executionProfile];
  const minimumAgentLimit = normalizeBound(
    options.minimumAgentLimit,
    RESEARCH_TEAM_MIN_AGENT_LIMIT,
    RESEARCH_TEAM_MIN_AGENT_LIMIT,
    RESEARCH_TEAM_MAX_AGENT_LIMIT
  );
  const maximumAgentLimit = normalizeBound(
    options.maximumAgentLimit,
    RESEARCH_TEAM_MAX_AGENT_LIMIT,
    minimumAgentLimit,
    RESEARCH_TEAM_MAX_AGENT_LIMIT
  );
  const maximumReasoningConcurrency = normalizeBound(
    options.maximumReasoningConcurrency,
    RESEARCH_TEAM_MAX_REASONING_CONCURRENCY,
    RESEARCH_TEAM_MIN_REASONING_CONCURRENCY,
    RESEARCH_TEAM_MAX_REASONING_CONCURRENCY
  );
  const agentLimit = normalizeInteger(value?.agentLimit, preset.agentLimit, minimumAgentLimit, maximumAgentLimit);
  const reasoningConcurrency = normalizeInteger(
    value?.reasoningConcurrency,
    Math.min(preset.reasoningConcurrency, agentLimit),
    RESEARCH_TEAM_MIN_REASONING_CONCURRENCY,
    Math.min(maximumReasoningConcurrency, agentLimit)
  );

  return Object.freeze({ executionProfile, agentLimit, reasoningConcurrency });
}

export function createResearchTeamPoolContract(
  value?: Partial<ResearchTeamPoolConfig>,
  options?: NormalizeResearchTeamPoolOptions
): ResearchTeamPoolContract {
  return Object.freeze({
    schema: RESEARCH_TEAM_POOL_SCHEMA,
    ...normalizeResearchTeamPoolConfig(value, options),
  });
}

export type ResearchTeamRoleKind = 'lead' | 'worker';

export type ResearchTeamAuthority = Readonly<{
  dispatchAssignments: boolean;
  writeAssignedWorktree: boolean;
  integrateWorkerCommits: boolean;
  runCanonicalEvaluation: boolean;
  mutateCanonicalRegistry: boolean;
  checkpointProject: boolean;
  publishReport: boolean;
}>;

export type ResearchTeamToolActionPolicy = Readonly<{
  toolName: string;
  actions: readonly string[] | '*';
}>;

export type ResearchTeamRoleContract = Readonly<{
  id: string;
  kind: ResearchTeamRoleKind;
  displayName: string;
  laneId?: string;
  /** Optional role provenance used by domain Team profiles. */
  source?: 'xalpha' | 'generic';
  roleTemplateId?: string;
  authority: ResearchTeamAuthority;
  allowedTools: readonly ResearchTeamToolActionPolicy[];
  deniedTools: readonly ResearchTeamToolActionPolicy[];
  prompt: string;
}>;

export type ResearchTeamLaneContract = Readonly<{
  id: string;
  displayName: string;
  purpose: string;
  deliverables: readonly string[];
}>;

export type ResearchTeamExclusiveCapability = Readonly<{
  id: string;
  ownerRoleId: string;
  toolName: string;
  actions: readonly string[] | '*';
}>;

export type ResearchTeamProfile = Readonly<{
  schema: typeof RESEARCH_TEAM_PROFILE_SCHEMA;
  version: 1;
  id: string;
  workflowId: string;
  displayName: string;
  leadRoleId: string;
  pool: ResearchTeamPoolContract;
  lanes: readonly ResearchTeamLaneContract[];
  roles: readonly ResearchTeamRoleContract[];
  exclusiveCapabilities: readonly ResearchTeamExclusiveCapability[];
  coordinationRules: readonly string[];
}>;

export type ResearchTeamGitLineage = Readonly<{
  projectRoot: string;
  /** Optional references to an existing committed research roadmap. Never invent them for a fresh Git task. */
  goalId?: string;
  routeNodeId?: string;
  roadmapRevision?: string;
  baseCommit: string;
  branch?: string;
  worktreePath?: string;
  headCommit?: string;
}>;

export type ResearchTeamFalsificationPlan = Readonly<{
  hypothesis: string;
  test: string;
  failureSignal: string;
}>;

export const RESEARCH_TEAM_EXECUTION_MODES = ['advisory', 'artifact'] as const;
export type ResearchTeamExecutionMode = (typeof RESEARCH_TEAM_EXECUTION_MODES)[number];

export const MATHEMATICS_SESSION_CONTINUATION_MODES = ['reuse_source_slot', 'fresh_slot'] as const;
export type MathematicsSessionContinuationMode = (typeof MATHEMATICS_SESSION_CONTINUATION_MODES)[number];
export const MATHEMATICS_SESSION_CONTINUATION_PURPOSES = [
  'candidate_repair',
  'critic',
  'alternate_route',
  'bottleneck_helper',
] as const;
export type MathematicsSessionContinuationPurpose = (typeof MATHEMATICS_SESSION_CONTINUATION_PURPOSES)[number];
export type MathematicsSessionContinuation = Readonly<{
  sourceAssignmentId: string;
  mode: MathematicsSessionContinuationMode;
  purpose: MathematicsSessionContinuationPurpose;
}>;

export type ResearchTeamMathAssignment = Readonly<{
  /** Internal execution action; workflowStage is the canonical research lifecycle projection. */
  stage: MathProofStage;
  workflowStage?: MathWorkflowStage;
  statementHash: string;
  routeFingerprint: string;
  /** Direct proof episode; `direct-goal` owns the whole-problem claim, while a custom node id owns one disjoint declaration cluster. */
  directAttempt?: boolean;
  /** Runtime-validated bounded falsification decision that gates substantive proof work. */
  fastCheck?: MathFastCheck;
  /** Project-relative proof/artifact paths reserved by this Worker. */
  artifactPaths?: readonly string[];
  /** Exact dependency-ready DAG node; omitted direct attempts normalize to `direct-goal`. */
  activePlanNodeId?: string;
  /** A route-candidate episode proposes, probes, and retains one surviving route in one assignment. */
  routeProposalMode?: 'candidate';
  /** Normalized proof-pattern identity used to enforce avoid_pattern lessons. */
  routePattern?: string;
  previousConsecutiveStalls?: number;
  /** Binds a follow-up to the same Worker context or to an independent one. */
  sessionContinuation?: MathematicsSessionContinuation;
  /** Immutable statement/acceptance identity copied into every substantive wave. */
  problemContract?: MathProblemContract;
  /** Natural-language research identity used while the Lean statement is unsettled. */
  researchContract?: MathResearchProblemContract;
  /** Write-ahead state used to resume a failed route without repeating it. */
  failureLedger?: MathFailureLedger;
  /** Required evidence for entering OFFICIAL_GATE. */
  candidateReviews?: readonly MathCandidateReview[];
  /** Frozen LOCAL_GATE kernel receipt required by REVIEW and OFFICIAL_GATE. */
  localGateReceipt?: MathLocalGateReceipt;
  alignmentCheck?: MathAlignmentCheck;
  routeCards?: readonly MathRouteCard[];
  routeSelection?: MathRouteSelection;
  /** Runtime-generated proof that the selected route composes in the bound Lean environment. */
  routeProbeReceipt?: MathRouteProbeReceipt;
  /** Runtime-owned Lean-Eval model/tactic/premise cursor. */
  executionPolicy?: MathExecutionPolicy;
  /** Versioned executable plan and resumable Lean state for P0 proof search. */
  proofPlan?: MathProofPlan;
  proofState?: MathProofState;
  applicableLessons?: readonly MathLesson[];
}>;

export type ResearchTeamAssignment = Readonly<{
  schema: typeof RESEARCH_TEAM_ASSIGNMENT_SCHEMA;
  assignmentId: string;
  workflowId: string;
  laneId: string;
  /** Lead-selected XAlpha template or a bounded generic role. */
  roleTemplateId?: string;
  roleKind?: 'xalpha' | 'generic';
  /** Optional human-readable label and bounded instructions for a generic role. */
  roleLabel?: string;
  roleInstructions?: string;
  /** Advisory work returns structured reasoning without a Git branch. Artifact work is the strict default. */
  executionMode?: ResearchTeamExecutionMode;
  /** Optional Mathematics Team stage and route identity. */
  math?: ResearchTeamMathAssignment;
  title: string;
  objective: string;
  acceptanceCriteria: readonly string[];
  failureCriteria: readonly string[];
  evidenceRefs: readonly string[];
  doNotRepeat: readonly string[];
  expectedArtifacts: readonly string[];
  falsificationPlan: ResearchTeamFalsificationPlan;
  git: ResearchTeamGitLineage;
  budget?: Readonly<{
    maxMinutes?: number;
    maxAttempts?: number;
  }>;
}>;

export type ResearchTeamEvidenceKind = 'measurement' | 'source' | 'code' | 'review' | 'artifact';

export type ResearchTeamEvidence = Readonly<{
  id: string;
  kind: ResearchTeamEvidenceKind;
  ref: string;
  claim: string;
  supports: boolean;
  contentSha256?: string;
}>;

export type ResearchTeamFalsificationOutcome = 'survived' | 'refuted' | 'inconclusive' | 'not_run';

export type ResearchTeamFalsificationResult = Readonly<{
  hypothesis: string;
  test: string;
  outcome: ResearchTeamFalsificationOutcome;
  evidenceIds: readonly string[];
  reason?: string;
}>;

export type ResearchTeamVerification = Readonly<{
  command: string;
  status: 'passed' | 'failed' | 'not_run';
  summary: string;
  evidenceIds: readonly string[];
}>;

export type ResearchTeamResultDisposition = 'accepted' | 'refuted' | 'inconclusive' | 'blocked';

/**
 * Echoed by a Worker so a Lead can prove that a result belongs to the exact
 * assignment that was dispatched.  This is intentionally small and immutable;
 * the full assignment remains a dispatch concern.
 */
export type ResearchTeamAssignmentBinding = Readonly<{
  assignmentId: string;
  workflowId: string;
  laneId: string;
  baseCommit: string;
  stage?: MathProofStage;
  workflowStage?: MathWorkflowStage;
  statementHash?: string;
  routeFingerprint?: string;
  activePlanNodeId?: string;
  localGateReceiptId?: string;
  officialVerificationCommand?: string;
}>;

export type ResearchTeamResult = Readonly<{
  schema: typeof RESEARCH_TEAM_RESULT_SCHEMA;
  assignmentId: string;
  workflowId: string;
  laneId: string;
  /** Lead-selected XAlpha template or bounded generic role metadata. */
  roleTemplateId?: string;
  roleKind?: 'xalpha' | 'generic';
  roleLabel?: string;
  /** Must match the assignment. Omission preserves the legacy artifact default. */
  executionMode?: ResearchTeamExecutionMode;
  /** Lean-grounded progress delta for a Mathematics Team assignment. */
  math?: MathProgressDelta;
  /** Structured review returned by an independent Mathematics Reviewer. */
  mathReview?: MathCandidateReview;
  /** Frozen LOCAL_GATE kernel receipt echoed by a Reviewer. */
  localGateReceipt?: MathLocalGateReceipt;
  /** Kernel receipt for one independently completed route-DAG node. */
  mathNodeReceipt?: MathNodeProofReceipt;
  /** Kernel receipt for a helper introduced beneath an expanded route milestone. */
  mathHelperReceipt?: MathHelperReceipt;
  /** Exact official comparator receipt returned by OFFICIAL_GATE. */
  officialGateReceipt?: MathOfficialGateReceipt;
  /** Exact dispatch identity echoed by the Worker. Required for Mathematics results. */
  assignmentBinding?: ResearchTeamAssignmentBinding;
  /** Write-ahead checkpoint returned when a Mathematics route must be resumed. */
  mathCheckpoint?: MathRecoveryCheckpoint;
  /** Structured route proposal returned by exploration lanes. */
  mathRouteCard?: MathRouteCard;
  /** Lightweight discovery result returned before formal proof planning. */
  mathResearchFinding?: MathResearchFinding;
  /** Evidence-bound reusable lessons extracted from a failure. */
  mathLessons?: readonly MathLesson[];
  inputsUsed: readonly string[];
  outputs: readonly string[];
  limitations: readonly string[];
  nextRecommendation?: string;
  disposition: ResearchTeamResultDisposition;
  summary: string;
  git: ResearchTeamGitLineage;
  evidence: readonly ResearchTeamEvidence[];
  /** Optional for implementation, data-preparation, visualization, or blocked assignments. */
  falsification?: ResearchTeamFalsificationResult;
  verification: readonly ResearchTeamVerification[];
  artifactPaths: readonly string[];
  producedAt: string;
}>;

export type CreateResearchTeamAssignmentInput = Omit<ResearchTeamAssignment, 'schema'>;
export type CreateResearchTeamResultInput = Omit<
  ResearchTeamResult,
  'schema' | 'evidence' | 'falsification' | 'verification' | 'artifactPaths'
> & {
  evidence?: readonly ResearchTeamEvidence[];
  falsification?: ResearchTeamFalsificationResult;
  verification?: readonly ResearchTeamVerification[];
  artifactPaths?: readonly string[];
  inputsUsed?: readonly string[];
  outputs?: readonly string[];
  limitations?: readonly string[];
};

export function createResearchTeamAssignment(input: CreateResearchTeamAssignmentInput): ResearchTeamAssignment {
  const executionMode = normalizeExecutionMode(input.executionMode);
  const assignment = {
    schema: RESEARCH_TEAM_ASSIGNMENT_SCHEMA,
    assignmentId: requiredText(input.assignmentId, 'assignmentId'),
    workflowId: requiredText(input.workflowId, 'workflowId'),
    laneId: requiredText(input.laneId, 'laneId'),
    ...(input.roleTemplateId ? { roleTemplateId: requiredText(input.roleTemplateId, 'roleTemplateId') } : {}),
    ...(input.roleKind ? { roleKind: input.roleKind } : {}),
    ...(input.roleLabel ? { roleLabel: requiredText(input.roleLabel, 'roleLabel') } : {}),
    ...(input.roleInstructions ? { roleInstructions: requiredText(input.roleInstructions, 'roleInstructions') } : {}),
    ...(input.executionMode ? { executionMode } : {}),
    ...(input.math ? { math: freezeMathAssignment(input.math) } : {}),
    title: requiredText(input.title, 'title'),
    objective: requiredText(input.objective, 'objective'),
    acceptanceCriteria: requiredTextList(input.acceptanceCriteria, 'acceptanceCriteria'),
    failureCriteria: requiredTextList(input.failureCriteria, 'failureCriteria'),
    evidenceRefs: textList(input.evidenceRefs, 'evidenceRefs'),
    doNotRepeat: textList(input.doNotRepeat, 'doNotRepeat'),
    expectedArtifacts: requiredTextList(input.expectedArtifacts, 'expectedArtifacts'),
    falsificationPlan: freezeFalsificationPlan(input.falsificationPlan),
    git: freezeGitLineage(input.git, false),
    ...(input.budget ? { budget: freezeBudget(input.budget) } : {}),
  } satisfies ResearchTeamAssignment;
  return Object.freeze(assignment);
}

export function createResearchTeamResult(input: CreateResearchTeamResultInput): ResearchTeamResult {
  const evidence = Object.freeze((input.evidence || []).map((item, index) => freezeEvidence(item, index)));
  const evidenceIds = new Set(evidence.map((item) => item.id));
  if (evidenceIds.size !== evidence.length) throw new TypeError('Research Team result evidence ids must be unique');
  const falsification = input.falsification ? freezeFalsificationResult(input.falsification, evidenceIds) : undefined;
  const verification = Object.freeze(
    (input.verification || []).map((item, index) => freezeVerification(item, index, evidenceIds))
  );
  const producedAt = requiredText(input.producedAt, 'producedAt');
  if (!Number.isFinite(Date.parse(producedAt)))
    throw new TypeError('Research Team producedAt must be an ISO timestamp');

  const executionMode = normalizeExecutionMode(input.executionMode);
  if (
    executionMode === 'advisory' &&
    (input.git.branch !== undefined || input.git.worktreePath !== undefined || input.git.headCommit !== undefined)
  ) {
    throw new TypeError('Research Team advisory result must not contain Git delivery fields');
  }
  return Object.freeze({
    schema: RESEARCH_TEAM_RESULT_SCHEMA,
    assignmentId: requiredText(input.assignmentId, 'assignmentId'),
    workflowId: requiredText(input.workflowId, 'workflowId'),
    laneId: requiredText(input.laneId, 'laneId'),
    ...(input.roleTemplateId ? { roleTemplateId: requiredText(input.roleTemplateId, 'roleTemplateId') } : {}),
    ...(input.roleKind ? { roleKind: normalizeRoleKind(input.roleKind) } : {}),
    ...(input.roleLabel ? { roleLabel: requiredText(input.roleLabel, 'roleLabel') } : {}),
    ...(input.executionMode ? { executionMode } : {}),
    ...(input.math ? { math: normalizeMathProgressDelta(input.math) } : {}),
    ...(input.mathReview ? { mathReview: normalizeMathCandidateReview(input.mathReview) } : {}),
    ...(input.localGateReceipt ? { localGateReceipt: normalizeMathLocalGateReceipt(input.localGateReceipt) } : {}),
    ...(input.mathNodeReceipt ? { mathNodeReceipt: normalizeMathNodeProofReceipt(input.mathNodeReceipt) } : {}),
    ...(input.mathHelperReceipt ? { mathHelperReceipt: normalizeMathHelperReceipt(input.mathHelperReceipt) } : {}),
    ...(input.officialGateReceipt
      ? { officialGateReceipt: normalizeMathOfficialGateReceipt(input.officialGateReceipt) }
      : {}),
    ...(input.assignmentBinding ? { assignmentBinding: normalizeAssignmentBinding(input.assignmentBinding) } : {}),
    ...(input.mathCheckpoint ? { mathCheckpoint: normalizeMathRecoveryCheckpoint(input.mathCheckpoint) } : {}),
    ...(input.mathRouteCard ? { mathRouteCard: normalizeMathRouteCard(input.mathRouteCard) } : {}),
    ...(input.mathResearchFinding
      ? { mathResearchFinding: normalizeMathResearchFinding(input.mathResearchFinding) }
      : {}),
    ...(input.mathLessons ? { mathLessons: Object.freeze(input.mathLessons.map(normalizeMathLesson)) } : {}),
    inputsUsed: textList(input.inputsUsed || [], 'inputsUsed'),
    outputs: textList(input.outputs || [], 'outputs'),
    limitations: textList(input.limitations || [], 'limitations'),
    ...(input.nextRecommendation
      ? { nextRecommendation: requiredText(input.nextRecommendation, 'nextRecommendation') }
      : {}),
    disposition: input.disposition,
    summary: requiredText(input.summary, 'summary'),
    git: freezeGitLineage(input.git, executionMode === 'artifact'),
    evidence,
    falsification,
    verification,
    artifactPaths: textList(input.artifactPaths || [], 'artifactPaths'),
    producedAt,
  });
}

function normalizeAssignmentBinding(input: ResearchTeamAssignmentBinding): ResearchTeamAssignmentBinding {
  const stage = input.stage;
  if (stage !== undefined && !MATH_PROOF_STAGES.includes(stage)) {
    throw new TypeError('Research Team assignmentBinding.stage is invalid');
  }
  const workflowStage =
    input.workflowStage === undefined
      ? stage === undefined
        ? undefined
        : normalizeMathWorkflowStage(stage)
      : normalizeMathWorkflowStage(input.workflowStage);
  const candidateRouteExpansion = workflowStage === 'candidate' && (stage === 'diversify' || stage === 'replan');
  if (stage !== undefined && workflowStage !== normalizeMathWorkflowStage(stage) && !candidateRouteExpansion) {
    throw new TypeError('Research Team assignmentBinding.workflowStage does not match its execution stage');
  }
  const statementHash =
    input.statementHash === undefined
      ? undefined
      : requiredHash(input.statementHash, 'assignmentBinding.statementHash');
  const routeFingerprint =
    input.routeFingerprint === undefined ? undefined : normalizeMathRouteFingerprint(input.routeFingerprint);
  const activePlanNodeId =
    input.activePlanNodeId === undefined
      ? undefined
      : normalizeMathPlanNodeId(input.activePlanNodeId, 'assignmentBinding.activePlanNodeId');
  const localGateReceiptId =
    input.localGateReceiptId === undefined
      ? undefined
      : requiredText(input.localGateReceiptId, 'assignmentBinding.localGateReceiptId');
  const officialVerificationCommand =
    input.officialVerificationCommand === undefined
      ? undefined
      : requiredText(input.officialVerificationCommand, 'assignmentBinding.officialVerificationCommand');
  return Object.freeze({
    assignmentId: requiredText(input.assignmentId, 'assignmentBinding.assignmentId'),
    workflowId: requiredText(input.workflowId, 'assignmentBinding.workflowId'),
    laneId: requiredText(input.laneId, 'assignmentBinding.laneId'),
    baseCommit: requiredGitOid(input.baseCommit, 'assignmentBinding.baseCommit'),
    ...(stage ? { stage } : {}),
    ...(workflowStage ? { workflowStage } : {}),
    ...(statementHash ? { statementHash } : {}),
    ...(routeFingerprint ? { routeFingerprint } : {}),
    ...(activePlanNodeId ? { activePlanNodeId } : {}),
    ...(localGateReceiptId ? { localGateReceiptId } : {}),
    ...(officialVerificationCommand ? { officialVerificationCommand } : {}),
  });
}

function isResearchTeamExecutionProfile(value: unknown): value is ResearchTeamExecutionProfile {
  return typeof value === 'string' && RESEARCH_TEAM_EXECUTION_PROFILES.includes(value as ResearchTeamExecutionProfile);
}

function normalizeBound(value: number | undefined, fallback: number, minimum: number, maximum: number): number {
  return Number.isSafeInteger(value) ? Math.min(maximum, Math.max(minimum, Number(value))) : fallback;
}

function normalizeInteger(value: number | undefined, fallback: number, minimum: number, maximum: number): number {
  return Number.isSafeInteger(value) ? Math.min(maximum, Math.max(minimum, Number(value))) : fallback;
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) throw new TypeError(`Research Team ${field} is required`);
  return value.trim();
}

function requiredHash(value: unknown, field: string): string {
  const normalized = requiredText(value, field).toLowerCase();
  if (!/^[0-9a-f]{64}$/u.test(normalized)) throw new TypeError(`Research Team ${field} must be SHA-256`);
  return normalized;
}

function normalizeRoleKind(value: unknown): 'xalpha' | 'generic' {
  if (value === 'xalpha' || value === 'generic') return value;
  throw new TypeError('Research Team roleKind must be xalpha or generic');
}

function normalizeExecutionMode(value: unknown): ResearchTeamExecutionMode {
  if (value === undefined || value === 'artifact') return 'artifact';
  if (value === 'advisory') return 'advisory';
  throw new TypeError('Research Team executionMode must be advisory or artifact');
}

function freezeMathAssignment(value: ResearchTeamMathAssignment): ResearchTeamMathAssignment {
  if (!MATH_PROOF_STAGES.includes(value.stage)) {
    throw new TypeError(`Research Team math.stage is invalid; expected one of ${MATH_PROOF_STAGES.join('|')}`);
  }
  const routeProposalMode = value.routeProposalMode;
  const workflowStage =
    routeProposalMode === 'candidate' ? ('candidate' as const) : normalizeMathWorkflowStage(value.stage);
  const suppliedWorkflowStage =
    value.workflowStage === undefined ? undefined : normalizeMathWorkflowStage(value.workflowStage);
  if (suppliedWorkflowStage !== undefined && suppliedWorkflowStage !== workflowStage) {
    throw new TypeError(
      `Research Team math.workflowStage does not match math.stage; expected ${workflowStage} ` +
        `(canonical values: ${MATH_WORKFLOW_STAGES.join('|')})`
    );
  }
  const statementHash = requiredText(value.statementHash, 'math.statementHash').toLowerCase();
  if (!/^[0-9a-f]{64}$/u.test(statementHash)) {
    throw new TypeError('Research Team math.statementHash must be SHA-256');
  }
  const routeFingerprint = normalizeMathRouteFingerprint(value.routeFingerprint);
  const directAttempt = value.directAttempt === true;
  if (value.directAttempt !== undefined && typeof value.directAttempt !== 'boolean') {
    throw new TypeError('Research Team math.directAttempt must be boolean');
  }
  if (directAttempt && !['formalize', 'review'].includes(value.stage)) {
    throw new TypeError('Research Team math.directAttempt is valid only during FORMALIZE or REVIEW');
  }
  const fastCheck = value.fastCheck ? normalizeMathFastCheck(value.fastCheck) : undefined;
  if (fastCheck && fastCheck.statementHash !== statementHash) {
    throw new TypeError('Research Team math.fastCheck must match math.statementHash');
  }
  const artifactPaths = value.artifactPaths ? normalizeMathArtifactPaths(value.artifactPaths) : undefined;
  const activePlanNodeId = value.activePlanNodeId
    ? normalizeMathPlanNodeId(value.activePlanNodeId, 'math.activePlanNodeId')
    : directAttempt && value.stage === 'formalize'
      ? 'direct-goal'
      : undefined;
  if (value.stage !== 'formalize' && activePlanNodeId) {
    throw new TypeError('Research Team node-local math fields are only valid during FORMALIZE');
  }
  if (routeProposalMode && routeProposalMode !== 'candidate') {
    throw new TypeError('Research Team math.routeProposalMode must be candidate');
  }
  if (routeProposalMode && !['diversify', 'replan'].includes(value.stage)) {
    throw new TypeError('Research Team math.routeProposalMode is only valid during route exploration');
  }
  const previousConsecutiveStalls = optionalNonnegativeInteger(
    value.previousConsecutiveStalls,
    'math.previousConsecutiveStalls'
  );
  const sessionContinuation = value.sessionContinuation
    ? normalizeMathematicsSessionContinuation(value.sessionContinuation)
    : undefined;
  if (sessionContinuation?.purpose === 'candidate_repair' && sessionContinuation.mode !== 'reuse_source_slot') {
    throw new TypeError('Research Team Mathematics candidate repair must reuse the source Worker slot');
  }
  if (sessionContinuation?.purpose === 'critic' && sessionContinuation.mode !== 'fresh_slot') {
    throw new TypeError('Research Team Mathematics Critic must use a fresh Worker slot');
  }
  const problemContract = value.problemContract ? normalizeMathProblemContract(value.problemContract) : undefined;
  if (problemContract && problemContract.statementHash !== statementHash) {
    throw new TypeError('Research Team math.problemContract.statementHash must match math.statementHash');
  }
  const researchContract = value.researchContract
    ? normalizeMathResearchProblemContract(value.researchContract)
    : undefined;
  if (researchContract && researchContract.problemId !== problemContract?.problemId && problemContract) {
    throw new TypeError('Research Team math.researchContract.problemId must match math.problemContract.problemId');
  }
  const alignmentCheck = value.alignmentCheck
    ? normalizeMathAlignmentCheck(value.alignmentCheck, problemContract)
    : undefined;
  if (directAttempt && (!problemContract || !alignmentCheck || alignmentCheck.verdict !== 'exact')) {
    throw new TypeError('Research Team math.directAttempt requires problemContract and exact alignmentCheck');
  }
  if (
    fastCheck?.candidateClaim === 'negation' &&
    (!problemContract?.formalNegationStatement || !problemContract.leanNegationHash)
  ) {
    throw new TypeError('Research Team negation work requires a canonical formal negation and hash');
  }
  if (alignmentCheck && !problemContract) {
    throw new TypeError('Research Team math.alignmentCheck requires problemContract');
  }
  if (
    alignmentCheck &&
    (alignmentCheck.statementHash !== statementHash || alignmentCheck.problemId !== problemContract.problemId)
  ) {
    throw new TypeError('Research Team math.alignmentCheck must match math.statementHash and problemContract');
  }
  const routeCards = value.routeCards ? Object.freeze(value.routeCards.map(normalizeMathRouteCard)) : undefined;
  let assignedRouteCard: MathRouteCard | undefined;
  if (routeCards) {
    for (const card of routeCards) {
      if (card.statementHash !== statementHash) {
        throw new TypeError('Research Team math.routeCards must match math.statementHash');
      }
      if (card.routeFingerprint === routeFingerprint) assignedRouteCard = card;
    }
  }
  if (routeCards && !value.routeSelection) assertNormalizedMathRouteCardsStructurallyDistinct(routeCards);
  if (routeProposalMode === 'candidate' && !problemContract) {
    throw new TypeError('Research Team route candidate requires a frozen formal problemContract');
  }
  const routeSelection = value.routeSelection
    ? normalizeMathRouteSelectionFromNormalized(value.routeSelection, routeCards ?? [])
    : undefined;
  if (routeSelection && routeSelection.statementHash !== statementHash) {
    throw new TypeError('Research Team math.routeSelection must match math.statementHash');
  }
  if (directAttempt && (routeCards || routeSelection)) {
    throw new TypeError('Research Team math.directAttempt must not carry routeCards or routeSelection');
  }
  const routeProbeReceipt = value.routeProbeReceipt
    ? normalizeMathRouteProbeReceipt(value.routeProbeReceipt)
    : undefined;
  if (
    routeProbeReceipt &&
    (routeProbeReceipt.statementHash !== statementHash || routeProbeReceipt.routeFingerprint !== routeFingerprint)
  ) {
    throw new TypeError('Research Team math.routeProbeReceipt must match the statement and route identity');
  }
  if (routeProbeReceipt && directAttempt) {
    throw new TypeError('Research Team math.directAttempt cannot carry a routed preflight receipt');
  }
  const executionPolicy = value.executionPolicy ? normalizeMathExecutionPolicy(value.executionPolicy) : undefined;
  const proofPlan = value.proofPlan ? normalizeMathProofPlan(value.proofPlan) : undefined;
  const proofState = value.proofState ? normalizeMathProofState(value.proofState) : undefined;
  if (proofPlan && (proofPlan.statementHash !== statementHash || proofPlan.routeFingerprint !== routeFingerprint)) {
    throw new TypeError('Research Team math.proofPlan must match the statement and route identity');
  }
  if (proofState && (proofState.statementHash !== statementHash || proofState.routeFingerprint !== routeFingerprint)) {
    throw new TypeError('Research Team math.proofState must match the statement and route identity');
  }
  if (proofPlan && proofState?.planId && proofState.planId !== proofPlan.planId) {
    throw new TypeError('Research Team math.proofState.planId must match math.proofPlan.planId');
  }
  if (activePlanNodeId && routeCards) {
    if (!assignedRouteCard || !assignedRouteCard.openFrontierNodeIds.includes(activePlanNodeId)) {
      throw new TypeError('Research Team math.activePlanNodeId must be actionable on the assigned route');
    }
  }
  let candidateReviewMismatch = false;
  const candidateReviews = value.candidateReviews
    ? Object.freeze(
        value.candidateReviews.map((review) => {
          const normalized = normalizeMathCandidateReview(review);
          if (
            normalized.statementHash !== statementHash ||
            (problemContract && normalized.problemId !== problemContract.problemId)
          ) {
            candidateReviewMismatch = true;
          }
          return normalized;
        })
      )
    : undefined;
  if (candidateReviewMismatch) {
    throw new TypeError('Research Team math.candidateReviews must match the problem contract identity');
  }
  const localGateReceipt = value.localGateReceipt ? normalizeMathLocalGateReceipt(value.localGateReceipt) : undefined;
  if (localGateReceipt && localGateReceipt.statementHash !== statementHash) {
    throw new TypeError('Research Team math.localGateReceipt must match math.statementHash');
  }
  let applicableLessonMismatch = false;
  const applicableLessons = value.applicableLessons
    ? Object.freeze(
        value.applicableLessons.map((lesson) => {
          const normalized = normalizeMathLesson(lesson);
          if (normalized.statementHash !== statementHash) applicableLessonMismatch = true;
          return normalized;
        })
      )
    : undefined;
  if (applicableLessonMismatch) {
    throw new TypeError('Research Team math.applicableLessons must match math.statementHash');
  }
  return Object.freeze({
    stage: value.stage,
    workflowStage,
    statementHash,
    routeFingerprint,
    ...(directAttempt ? { directAttempt: true } : {}),
    ...(fastCheck ? { fastCheck } : {}),
    ...(artifactPaths ? { artifactPaths } : {}),
    ...(activePlanNodeId ? { activePlanNodeId } : {}),
    ...(routeProposalMode ? { routeProposalMode } : {}),
    ...(value.routePattern ? { routePattern: normalizeRoutePattern(value.routePattern) } : {}),
    ...(previousConsecutiveStalls !== undefined ? { previousConsecutiveStalls } : {}),
    ...(sessionContinuation ? { sessionContinuation } : {}),
    ...(problemContract ? { problemContract } : {}),
    ...(researchContract ? { researchContract } : {}),
    ...(value.failureLedger ? { failureLedger: normalizeMathFailureLedger(value.failureLedger) } : {}),
    ...(candidateReviews ? { candidateReviews } : {}),
    ...(localGateReceipt ? { localGateReceipt } : {}),
    ...(alignmentCheck ? { alignmentCheck } : {}),
    ...(routeCards ? { routeCards } : {}),
    ...(routeSelection ? { routeSelection } : {}),
    ...(routeProbeReceipt ? { routeProbeReceipt } : {}),
    ...(executionPolicy ? { executionPolicy } : {}),
    ...(proofPlan ? { proofPlan } : {}),
    ...(proofState ? { proofState } : {}),
    ...(applicableLessons ? { applicableLessons } : {}),
  });
}

function normalizeMathematicsSessionContinuation(
  value: MathematicsSessionContinuation
): MathematicsSessionContinuation {
  if (!value || typeof value !== 'object') {
    throw new TypeError('Research Team math.sessionContinuation must be an object');
  }
  if (!MATHEMATICS_SESSION_CONTINUATION_MODES.includes(value.mode)) {
    throw new TypeError('Research Team math.sessionContinuation.mode is invalid');
  }
  if (!MATHEMATICS_SESSION_CONTINUATION_PURPOSES.includes(value.purpose)) {
    throw new TypeError('Research Team math.sessionContinuation.purpose is invalid');
  }
  return Object.freeze({
    sourceAssignmentId: requiredText(value.sourceAssignmentId, 'math.sessionContinuation.sourceAssignmentId'),
    mode: value.mode,
    purpose: value.purpose,
  });
}

function normalizeMathArtifactPaths(values: readonly string[]): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError('Research Team math.artifactPaths must be an array');
  const normalized = values.map((value, index) => {
    if (typeof value !== 'string' || !value.trim()) {
      throw new TypeError(`Research Team math.artifactPaths[${index}] is required`);
    }
    const candidate = value.trim().replaceAll('\\', '/');
    if (candidate.startsWith('/') || candidate.split('/').includes('..') || candidate.includes('\0')) {
      throw new TypeError(`Research Team math.artifactPaths[${index}] must remain project-relative`);
    }
    return candidate.replace(/^\.\//u, '');
  });
  if (new Set(normalized).size !== normalized.length) {
    throw new TypeError('Research Team math.artifactPaths must be unique');
  }
  return Object.freeze(normalized);
}

function textList(values: readonly string[], field: string): readonly string[] {
  if (!Array.isArray(values)) throw new TypeError(`Research Team ${field} must be an array`);
  const normalized = values.map((value, index) => requiredText(value, `${field}[${index}]`));
  if (new Set(normalized).size !== normalized.length) throw new TypeError(`Research Team ${field} must be unique`);
  return Object.freeze(normalized);
}

function normalizeRoutePattern(value: string): string {
  const normalized = requiredText(value, 'math.routePattern').toLowerCase().replace(/\s+/gu, ' ');
  if (normalized.length > 512) throw new TypeError('Research Team math.routePattern is too long');
  return normalized;
}

function requiredTextList(values: readonly string[], field: string): readonly string[] {
  const normalized = textList(values, field);
  if (!normalized.length) throw new TypeError(`Research Team ${field} must not be empty`);
  return normalized;
}

function freezeGitLineage(value: ResearchTeamGitLineage, requireDelivery: boolean): ResearchTeamGitLineage {
  const baseCommit = requiredGitOid(value.baseCommit, 'baseCommit');
  const headCommit = value.headCommit ? requiredGitOid(value.headCommit, 'headCommit') : undefined;
  if (requireDelivery && (!value.branch || !headCommit)) {
    throw new TypeError('Research Team result requires an exact branch and headCommit');
  }
  return Object.freeze({
    projectRoot: requiredText(value.projectRoot, 'git.projectRoot'),
    ...(value.goalId ? { goalId: requiredText(value.goalId, 'git.goalId') } : {}),
    ...(value.routeNodeId ? { routeNodeId: requiredText(value.routeNodeId, 'git.routeNodeId') } : {}),
    ...(value.roadmapRevision ? { roadmapRevision: requiredText(value.roadmapRevision, 'git.roadmapRevision') } : {}),
    baseCommit,
    ...(value.branch ? { branch: requiredText(value.branch, 'git.branch') } : {}),
    ...(value.worktreePath ? { worktreePath: requiredText(value.worktreePath, 'git.worktreePath') } : {}),
    ...(headCommit ? { headCommit } : {}),
  });
}

export function requiredGitOid(value: unknown, field: string): string {
  const normalized = requiredText(value, `git.${field}`).toLowerCase();
  if (!/^(?:[0-9a-f]{40}|[0-9a-f]{64})$/.test(normalized)) {
    throw new TypeError(`Research Team git.${field} must be a full Git object id`);
  }
  return normalized;
}

function freezeFalsificationPlan(value: ResearchTeamFalsificationPlan): ResearchTeamFalsificationPlan {
  return Object.freeze({
    hypothesis: requiredText(value.hypothesis, 'falsificationPlan.hypothesis'),
    test: requiredText(value.test, 'falsificationPlan.test'),
    failureSignal: requiredText(value.failureSignal, 'falsificationPlan.failureSignal'),
  });
}

function freezeBudget(
  value: NonNullable<ResearchTeamAssignment['budget']>
): NonNullable<ResearchTeamAssignment['budget']> {
  const maxMinutes = optionalPositiveInteger(value.maxMinutes, 'budget.maxMinutes');
  const maxAttempts = optionalPositiveInteger(value.maxAttempts, 'budget.maxAttempts');
  if (maxMinutes === undefined && maxAttempts === undefined) {
    throw new TypeError('Research Team budget requires maxMinutes or maxAttempts');
  }
  return Object.freeze({ ...(maxMinutes ? { maxMinutes } : {}), ...(maxAttempts ? { maxAttempts } : {}) });
}

function optionalPositiveInteger(value: number | undefined, field: string): number | undefined {
  if (value === undefined) return undefined;
  if (!Number.isSafeInteger(value) || value <= 0)
    throw new TypeError(`Research Team ${field} must be a positive integer`);
  return value;
}

function optionalNonnegativeInteger(value: number | undefined, field: string): number | undefined {
  if (value === undefined) return undefined;
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new TypeError(`Research Team ${field} must be a nonnegative integer`);
  }
  return value;
}

function freezeEvidence(value: ResearchTeamEvidence, index: number): ResearchTeamEvidence {
  const contentSha256 = value.contentSha256?.trim().toLowerCase();
  if (contentSha256 && !/^[0-9a-f]{64}$/.test(contentSha256)) {
    throw new TypeError(`Research Team evidence[${index}].contentSha256 must be SHA-256`);
  }
  return Object.freeze({
    id: requiredText(value.id, `evidence[${index}].id`),
    kind: value.kind,
    ref: requiredText(value.ref, `evidence[${index}].ref`),
    claim: requiredText(value.claim, `evidence[${index}].claim`),
    supports: value.supports,
    ...(contentSha256 ? { contentSha256 } : {}),
  });
}

function freezeFalsificationResult(
  value: ResearchTeamFalsificationResult,
  evidenceIds: ReadonlySet<string>
): ResearchTeamFalsificationResult {
  const referencedEvidence = textList(value.evidenceIds, 'falsification.evidenceIds');
  assertEvidenceRefs(referencedEvidence, evidenceIds, 'falsification.evidenceIds');
  if (value.outcome !== 'not_run' && referencedEvidence.length === 0) {
    throw new TypeError('Research Team completed falsification requires evidenceIds');
  }
  if (value.outcome === 'not_run' && !value.reason?.trim()) {
    throw new TypeError('Research Team unrun falsification requires a reason');
  }
  return Object.freeze({
    hypothesis: requiredText(value.hypothesis, 'falsification.hypothesis'),
    test: requiredText(value.test, 'falsification.test'),
    outcome: value.outcome,
    evidenceIds: referencedEvidence,
    ...(value.reason ? { reason: requiredText(value.reason, 'falsification.reason') } : {}),
  });
}

function freezeVerification(
  value: ResearchTeamVerification,
  index: number,
  evidenceIds: ReadonlySet<string>
): ResearchTeamVerification {
  const referencedEvidence = textList(value.evidenceIds, `verification[${index}].evidenceIds`);
  assertEvidenceRefs(referencedEvidence, evidenceIds, `verification[${index}].evidenceIds`);
  return Object.freeze({
    command: requiredText(value.command, `verification[${index}].command`),
    status: value.status,
    summary: requiredText(value.summary, `verification[${index}].summary`),
    evidenceIds: referencedEvidence,
  });
}

function assertEvidenceRefs(values: readonly string[], evidenceIds: ReadonlySet<string>, field: string): void {
  const unknown = values.find((value) => !evidenceIds.has(value));
  if (unknown) throw new TypeError(`Research Team ${field} references unknown evidence ${unknown}`);
}
