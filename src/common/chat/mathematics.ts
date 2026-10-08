/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  MATH_WORKFLOW_STAGES,
  aggregateMathCandidateReviews,
  assertNormalizedMathRouteCardsStructurallyDistinct,
  normalizeMathAlignmentCheck,
  normalizeMathCandidateReview,
  normalizeMathFastCheck,
  normalizeMathLesson,
  normalizeMathLocalGateReceipt,
  normalizeMathOfficialGateReceipt,
  normalizeMathProblemContract,
  normalizeMathRecoveryCheckpoint,
  normalizeMathRouteFingerprint,
  normalizeMathRouteCard,
  normalizeMathRouteSelectionFromNormalized,
  normalizeMathResearchProblemContract,
  buildMathFeasibilityProfile,
  rankMathFeasibilityCandidates,
  mathVerifiedLemmaToPremiseCandidate,
  mathPremiseRouteSchedule,
  type MathAlignmentCheck,
  type MathCandidateReview,
  type MathFastCheck,
  type MathLesson,
  type MathLocalGateReceipt,
  type MathOfficialGateReceipt,
  type MathPremiseCandidate,
  type MathPremiseCoverageRow,
  type MathProblemContract,
  type MathResearchProblemContract,
  type MathRecoveryCheckpoint,
  type MathRouteCard,
  type MathRouteSelection,
  type MathWorkflowStage,
  type MathFeasibilityProfile,
  type MathFeasibilitySignals,
} from "../types/team/mathematicsTeam";

export { rankMathFeasibilityCandidates } from "../types/team/mathematicsTeam";

export const MATHEMATICS_MODE_ID = 'mathematical-research' as const;
export const MATHEMATICS_SKILL_NAME = 'deepscientist-mathematics' as const;
export const MATHEMATICS_PORTFOLIO_SCHEMA = 'deepscientist.mathematics.portfolio.v1' as const;
export const MATHEMATICS_PORTFOLIO_ARTIFACT_ID = 'mathematics_portfolio' as const;
export const MATHEMATICS_PORTFOLIO_PATH = 'mathematics/portfolio.json' as const;
export const MATHEMATICS_EVENT_SCHEMA = 'deepscientist.mathematics.event.v1' as const;
export const MATHEMATICS_VERIFICATION_EVENT_SCHEMA = 'deepscientist.mathematics.verification_event.v1' as const;
export const MATHEMATICS_VERIFICATION_TRACE_SCHEMA = 'deepscientist.mathematics.verification_trace.v1' as const;
export const MATHEMATICS_VERIFICATION_TRACE_PATH = 'mathematics/verification-trace.json' as const;
export const MATHEMATICS_VERIFICATION_LIVE_TRACE_PATH =
  '.deepscientist/science-artifacts/mathematics/verification-live.json' as const;
export const MATHEMATICS_UPSTREAM_PREMISE_SOURCES = ['leansearch', 'loogle'] as const;
export type MathematicsUpstreamPremiseSource = (typeof MATHEMATICS_UPSTREAM_PREMISE_SOURCES)[number];

type LegacyMathematicsStage = 'examples' | 'proving' | 'verified' | 'refuted';
export type MathematicsStage = MathWorkflowStage | LegacyMathematicsStage;

export type MathematicsPortfolioStatus =
  | 'planning'
  | 'running'
  | 'needs_review'
  | 'verified'
  | 'refuted'
  | 'inconclusive'
  | 'blocked';
export type MathematicsProblemStatus =
  | 'draft'
  | 'formalized'
  | 'candidate'
  | 'verified'
  | 'refuted'
  | 'inconclusive'
  | 'blocked';
export type MathematicsAttemptStatus = 'draft' | 'running' | 'candidate' | 'verified' | 'refuted' | 'failed' | 'stale';
export type MathematicsExampleKind = 'positive' | 'negative' | 'boundary' | 'counterexample';
export type MathematicsEvidencePolarity = 'supporting' | 'refuting' | 'context';
export type MathematicsEvidenceStrength = 'observed' | 'reproduced' | 'supporting' | 'refuting' | 'formal';
export type MathematicsReproducibility = 'single_run' | 'reproduced' | 'independent' | 'formal';
export type MathematicsReviewStatus =
  | 'not_requested'
  | 'queued'
  | 'running'
  | 'passed'
  | 'changes_requested'
  | 'refuted'
  | 'inconclusive'
  | 'stale';
export type MathematicsVerificationStatus = 'pending' | 'kernel_verified' | 'failed' | 'blocked' | 'unavailable';
export type MathematicsVerificationClaim = 'statement' | 'negation';

export type MathematicsGoalState = {
  stateId: string;
  target: string;
  hypotheses: string[];
  theoremName?: string;
};

export type MathematicsVerificationEventPayloadMap = {
  'session.opened': {
    projectRoot: string;
    itemCount: number;
    uniqueFileCount: number;
  };
  'toolchain.resolved': {
    command: 'lake' | 'lean';
    executable: string;
    lakeFile?: string;
    available?: boolean;
  };
  'formula.submitted': {
    formulaId: string;
    formula: string;
    label?: string;
    theoremName?: string;
    sourcePath?: string;
    authority: 'agent';
  };
  'goal.opened': MathematicsGoalState & {
    authority: 'agent' | 'lean-process';
  };
  'goal.rewritten': MathematicsGoalState & {
    parentStateId: string;
    previousTarget: string;
    authority: 'agent' | 'lean-process';
  };
  'goal.branched': MathematicsGoalState & {
    parentStateId: string;
    branchLabel?: string;
    authority: 'agent' | 'lean-process';
  };
  'goal.closed': {
    stateId: string;
    parentStateId?: string;
    target?: string;
    theoremName?: string;
  } & ({ status: 'draft_closed'; authority: 'agent' } | { status: 'kernel_verified'; authority: 'lean-kernel' });
  'file.opened': {
    proofPath: string;
    proofHash: string;
    bytes: number;
    checkCount: number;
  };
  'check.draft_checked': {
    proofPath: string;
    status: 'accepted' | 'rejected';
    sorryCount: number;
    admitCount: number;
    axioms: string[];
  };
  'diagnostic.emitted': {
    source: 'git' | 'safety' | 'process' | 'stdout' | 'stderr' | 'agent';
    severity: 'info' | 'warning' | 'error';
    message: string;
    proofPath?: string;
    stateId?: string;
  };
  'check.kernel_checked': {
    proofPath: string;
    status: MathematicsVerificationStatus;
    exitCode: number | null;
    signal: string | null;
    timedOut: boolean;
    aborted: boolean;
    durationMs: number;
  };
  'receipt.published': {
    receiptId: string;
    checkId: string;
    proofPath: string;
    theoremName?: string;
    status: MathematicsVerificationStatus;
  };
  'session.closed': {
    status: MathematicsVerificationStatus;
    resultCount: number;
    durationMs: number;
  };
};

export type MathematicsVerificationEventKind = keyof MathematicsVerificationEventPayloadMap;

export type MathematicsVerificationEvent = {
  [Kind in MathematicsVerificationEventKind]: {
    schema: typeof MATHEMATICS_VERIFICATION_EVENT_SCHEMA;
    eventId: string;
    sessionId: string;
    timestamp: number;
    kind: Kind;
    payload: MathematicsVerificationEventPayloadMap[Kind];
  };
}[MathematicsVerificationEventKind];

export type MathematicsVerificationCapability = {
  available: boolean;
  command?: 'lake' | 'lean';
  executable?: string;
  version?: string;
  reason?: string;
  sandboxBackends?: readonly ('unshare' | 'bwrap' | 'docker' | 'podman')[];
  batchCertification: true;
  liveGoals: boolean;
  persistentSession: boolean;
};

export type MathematicsVerificationTrace = {
  schema: typeof MATHEMATICS_VERIFICATION_TRACE_SCHEMA;
  runIdentity?: string;
  version: 1;
  updatedAt: number;
  capability?: MathematicsVerificationCapability;
  events: MathematicsVerificationEvent[];
};

export type MathematicsDecisionBasis =
  | 'supporting_evidence'
  | 'refuting_evidence'
  | 'conflicting_evidence'
  | 'insufficient_evidence';

export type MathematicsDecisionReason =
  | 'verified_by_supporting_evidence'
  | 'refuted_by_counterexample'
  | 'refuted_by_formal_negation'
  | 'conflicting_evidence'
  | 'supporting_evidence_not_verified'
  | 'refuting_evidence_not_decisive'
  | 'insufficient_evidence';

export interface MathematicsEvidenceDecision {
  disposition: 'verified' | 'refuted' | 'inconclusive';
  basis: MathematicsDecisionBasis;
  reason: MathematicsDecisionReason;
}

export interface MathematicsProblem {
  id: string;
  title: string;
  informalStatement: string;
  formalStatement?: string;
  assumptions: string[];
  statementHash?: string;
  problemContract?: MathProblemContract;
  /** Research identity that remains usable before a formal statement exists. */
  researchContract?: MathResearchProblemContract;
  /** Intake-only signals used to rank formal candidates before solver work. */
  feasibility?: MathFeasibilitySignals;
  alignmentCheck?: MathAlignmentCheck;
  fastCheck?: MathFastCheck;
  routeCards?: MathRouteCard[];
  routeSelection?: MathRouteSelection;
  /** Frozen Team receipts retained so terminal verification cannot lose gate provenance. */
  localGateReceipt?: MathLocalGateReceipt;
  officialGateReceipt?: MathOfficialGateReceipt;
  status: MathematicsProblemStatus;
  attemptIds: string[];
  exampleIds: string[];
  verificationId?: string;
  reviewId?: string;
  /** Two-review Team gate. reviewId remains the legacy single-review pointer. */
  reviewIds?: string[];
  updatedAt: number;
}

export interface MathematicsAttempt {
  id: string;
  /** Runtime-authored provenance for managed research memory. */
  runIdentity?: string;
  problemId: string;
  strategy: string;
  status: MathematicsAttemptStatus;
  artifactId?: string;
  artifactVersion?: number;
  branch?: string;
  commit?: string;
  proofPath?: string;
  theoremName?: string;
  parentAttemptId?: string;
  recoveryCheckpoint?: MathRecoveryCheckpoint;
  lessons?: MathLesson[];
  createdAt: number;
  updatedAt: number;
}

export type MathematicsReusablePremise = Readonly<{
  problemId: string;
  attemptId: string;
  routeFingerprint: string;
  planNodeId: string;
  sourceCommit: string;
  premise: MathPremiseCandidate;
  requiresRecheck: boolean;
}>;

export type MathematicsPromptQuery = Readonly<{
  problemId: string;
  routeFingerprint: string;
  planNodeId?: string;
  goal?: string;
  /** Stable live-goal identity used to reuse retrieval while the proof state is unchanged. */
  proofStateFingerprint?: string;
  /** Set by the Lean runtime after a premise-shaped failure to trigger automatic retrieval. */
  failureKind?:
    | 'unknown_identifier'
    | 'type_mismatch'
    | 'instance_synthesis_failed'
    | 'unsolved_goals'
    | 'tactic_failed';
  /** Bounded first Lean diagnostic used to recover the missing name, instance, or tactic context. */
  failureDiagnostic?: string;
  routeCoverage?: boolean;
  routeNodeLimit?: number;
  importModules?: readonly string[];
  sourceFile?: string;
  /** Explicit opt-in queries sent only to the named public Mathlib indexes. */
  upstreamQueries?: Readonly<Partial<Record<MathematicsUpstreamPremiseSource, string>>>;
  /** Explicit opt-in package discovery through GitHub metadata, verified against Reservoir. */
  packageQueries?: readonly string[];
  /** Explicit installed Lake dependencies whose local declaration headers may be searched. */
  installedPackageScopes?: readonly string[];
  /** Optional type/name/concept query for the selected installed package scopes. */
  installedPackageQuery?: string;
  premiseLimit?: number;
  lessonLimit?: number;
}>;

/** A declaration discovered in the current Lean import/source closure. */
export type MathematicsAccessiblePremise = Readonly<{
  declarationName: string;
  declarationType: string;
  sourceModule: string;
  sourceFile: string;
}>;

export type MathematicsRankedAccessiblePremise = MathematicsAccessiblePremise &
  Readonly<{
    relevanceScore: number;
    matchReasons: readonly string[];
    targetPlanNodeIds: readonly string[];
  }>;

/** A declaration candidate returned by a public Mathlib-only index. */
export type MathematicsUpstreamPremise = Readonly<{
  source: MathematicsUpstreamPremiseSource;
  declarationName: string;
  declarationType: string;
  sourceModule?: string;
  documentationUrl: string;
  providerRank: number;
  /** Remote indexes may target another Mathlib revision; the current project remains authoritative. */
  compatibility: 'unverified';
  targetValidationRequired: true;
}>;

export type MathematicsRankedUpstreamPremise = MathematicsUpstreamPremise &
  Readonly<{
    relevanceScore: number;
    matchReasons: readonly string[];
    targetPlanNodeIds: readonly string[];
  }>;

export type MathematicsUpstreamSearchAttempt = Readonly<{
  source: MathematicsUpstreamPremiseSource;
  status: 'ok' | 'unavailable';
  resultCount: number;
  errorCode?: string;
}>;

/** Content-addressed replay metadata for an advisory public-index response. */
export type MathematicsUpstreamSearchProvenance = Readonly<{
  source: MathematicsUpstreamPremiseSource;
  queryHash: string;
  responseHash?: string;
  fetchedAt: number;
  cacheHit: boolean;
}>;

export type MathematicsUpstreamPackageCompatibility = 'exact' | 'mismatch' | 'unknown';
export type MathematicsUpstreamPackageLocalAvailability =
  | 'installed_exact'
  | 'installed_different_revision'
  | 'not_installed';
export type MathematicsUpstreamPackageAdoptionStatus =
  | 'eligible'
  | 'incompatible'
  | 'license_review_required'
  | 'build_unverified'
  | 'compatibility_review_required';
export type MathematicsUpstreamPackageUsageAction =
  | 'search_installed_package'
  | 'keep_pinned_local_revision'
  | 'request_dependency_approval'
  | 'resolve_compatibility'
  | 'review_license'
  | 'verify_registry_build';

/** Read-only package metadata from the official Lean Reservoir registry. */
export type MathematicsUpstreamPackage = Readonly<{
  source: 'reservoir';
  fullName: string;
  packageName: string;
  description?: string;
  repositoryFullName: string;
  repositoryUrl: string;
  registryUrl: string;
  homepageUrl?: string;
  keywords: readonly string[];
  license?: string;
  stars: number;
  updatedAt: string;
  version: string;
  revision: string;
  leanToolchain?: string;
  mathlibRevision?: string;
  mathlibInputRevision?: string;
  buildStatus: 'built' | 'failed' | 'unknown';
  compatibility: MathematicsUpstreamPackageCompatibility;
  compatibilityReasons: readonly string[];
  adoptionStatus: MathematicsUpstreamPackageAdoptionStatus;
  localAvailability: MathematicsUpstreamPackageLocalAvailability;
  installedRevision?: string;
  usageAction: MathematicsUpstreamPackageUsageAction;
  providerRank: number;
  /** Discovery never grants authority to edit lakefile.toml or lakefile.lean. */
  dependencyMutationAllowed: false;
  targetValidationRequired: true;
}>;

/** Declaration header found in one explicitly scoped, already-installed Lake dependency. */
export type MathematicsInstalledPackagePremise = Readonly<{
  packageName: string;
  packageRevision: string;
  declarationName: string;
  declarationType: string;
  sourceModule: string;
  sourceFile: string;
  providerRank: number;
  localDependency: true;
  importRequired: true;
  targetValidationRequired: true;
}>;

export type MathematicsRankedInstalledPackagePremise = MathematicsInstalledPackagePremise &
  Readonly<{
    relevanceScore: number;
    matchReasons: readonly string[];
    targetPlanNodeIds: readonly string[];
  }>;

export type MathematicsInstalledPackageSearchAttempt = Readonly<{
  scope: string;
  status: 'ok' | 'not_installed' | 'unavailable';
  resultCount: number;
  errorCode?: string;
}>;

export type MathematicsUpstreamPackageSearchAttempt = Readonly<{
  source: 'reservoir';
  status: 'ok' | 'unavailable';
  resultCount: number;
  excludedCount: number;
  errorCode?: string;
}>;

/** A compact mechanism from another problem that may transfer to this one. */
export type MathematicsMechanismCapsule = Readonly<{
  sourceProblemId: string;
  sourceProblemTitle: string;
  routeFingerprint: string;
  structuralCommitment: string;
  decisiveLemma: string;
  falsificationSignal: string;
  relevanceScore: number;
  matchReasons: readonly string[];
}>;

export type MathematicsRankedPremise = MathematicsReusablePremise &
  Readonly<{
    relevanceScore: number;
    matchReasons: readonly string[];
    targetPlanNodeIds: readonly string[];
  }>;

export type MathematicsRankedLesson = Readonly<{
  lesson: MathLesson;
  relevanceScore: number;
  matchReasons: readonly string[];
}>;

export type MathematicsPromptPack = Readonly<{
  problemId: string;
  routeFingerprint: string;
  queryMode: 'node' | 'route_coverage';
  planNodeId?: string;
  planNodeIds: readonly string[];
  coverage?: readonly MathPremiseCoverageRow[];
  premises: readonly MathematicsRankedPremise[];
  accessiblePremises: readonly MathematicsRankedAccessiblePremise[];
  upstreamPremises: readonly MathematicsRankedUpstreamPremise[];
  upstreamSearchAttempts: readonly MathematicsUpstreamSearchAttempt[];
  upstreamSearchProvenance: readonly MathematicsUpstreamSearchProvenance[];
  upstreamPackages: readonly MathematicsUpstreamPackage[];
  upstreamPackageSearchAttempts: readonly MathematicsUpstreamPackageSearchAttempt[];
  installedPackagePremises: readonly MathematicsRankedInstalledPackagePremise[];
  installedPackageSearchAttempts: readonly MathematicsInstalledPackageSearchAttempt[];
  mechanismCapsules: readonly MathematicsMechanismCapsule[];
  lessons: readonly MathematicsRankedLesson[];
  omittedPremiseCount: number;
  omittedAccessiblePremiseCount: number;
  omittedUpstreamPremiseCount: number;
  omittedInstalledPackagePremiseCount: number;
  omittedMechanismCapsuleCount: number;
  omittedLessonCount: number;
}>;

export interface MathematicsExample {
  id: string;
  problemId: string;
  kind: MathematicsExampleKind;
  input: string;
  expected?: string;
  observed?: string;
  scope?: string;
  seed?: string;
  /** Exact command used to replay this witness from the committed project. */
  replayCommand?: string;
  artifactId?: string;
  evidenceIds: string[];
  createdAt: number;
}

/**
 * A typed pointer into the shared Science Evidence graph.
 *
 * The math portfolio records why an observation supports or refutes a
 * specific statement; the full source/provenance remains owned by
 * `science_artifact` and is referenced through `evidenceIds`.
 */
export interface MathematicsEvidence {
  id: string;
  problemId: string;
  statementHash?: string;
  polarity: MathematicsEvidencePolarity;
  strength: MathematicsEvidenceStrength;
  scope: string;
  method: string;
  inputRefs: string[];
  outputRefs: string[];
  evidenceIds: string[];
  observed: string;
  reproducibility: MathematicsReproducibility;
  commit: string;
  command?: string;
  source?: string;
  seed?: string;
  createdAt: number;
}

export interface MathematicsToolchain {
  lean: string;
  mathlib?: string;
  lake?: string;
  lockfilePath?: string;
  lockfileHash?: string;
}

export interface MathematicsVerification {
  id: string;
  problemId: string;
  status: MathematicsVerificationStatus;
  targetCommit: string;
  statementHash: string;
  /** Omitted only by legacy proof receipts, where `statement` is implied. */
  claim?: MathematicsVerificationClaim;
  toolchain: MathematicsToolchain;
  theoremName?: string;
  proofHash?: string;
  logPath?: string;
  goalsRemaining: number;
  sorryCount: number;
  admitCount: number;
  axioms: string[];
  verifier: 'lean-kernel' | 'bounded-check' | 'unavailable';
  checkedAt?: number;
  error?: string;
}

export interface MathematicsReview {
  id: string;
  problemId: string;
  status: MathematicsReviewStatus;
  targetCommit: string;
  statementHash: string;
  reviewerSessionId?: string;
  verdict?: 'passed' | 'changes_requested' | 'refuted' | 'inconclusive';
  summary?: string;
  issueIds: string[];
  reportArtifactId?: string;
  candidateReview?: MathCandidateReview;
  updatedAt: number;
}

export interface MathematicsAction {
  id: string;
  label: string;
  kind: 'formalize' | 'search' | 'verify' | 'review' | 'decision';
  priority: 'now' | 'next' | 'later';
  owner?: 'agent' | 'user' | 'reviewer';
}

export interface MathematicsStageTransition {
  from: MathematicsStage;
  to: MathematicsStage;
  commit: string;
  timestamp: number;
  reason: string;
}

export interface MathematicsPortfolio {
  schema: typeof MATHEMATICS_PORTFOLIO_SCHEMA;
  /** Runtime-authored provenance; absent only on legacy portfolios. */
  runIdentity?: string;
  version: 1;
  title: string;
  stage: MathematicsStage;
  status: MathematicsPortfolioStatus;
  updatedAt: number;
  /** Durable, runtime-authored stage transitions; terminal stages cannot roll back. */
  stageHistory?: MathematicsStageTransition[];
  projectRoot?: string;
  activeProblemId?: string;
  toolchain?: MathematicsToolchain;
  problems: MathematicsProblem[];
  attempts: MathematicsAttempt[];
  examples: MathematicsExample[];
  /** Evidence ledger; omitted only by legacy portfolios before this field was introduced. */
  evidence: MathematicsEvidence[];
  verifications: MathematicsVerification[];
  reviews: MathematicsReview[];
  blockers: string[];
  nextActions: MathematicsAction[];
}

/** Read-only candidate ranking derived from the portfolio at intake/resume. */
export type MathematicsFeasibilityRanking = Readonly<{
  generatedAt: number;
  candidates: readonly MathFeasibilityProfile[];
}>;

export interface MathematicsConversationExtra {
  enabled: true;
  mode: typeof MATHEMATICS_MODE_ID;
  schema: typeof MATHEMATICS_PORTFOLIO_SCHEMA;
  projectRoot?: string;
  defaultSkill: typeof MATHEMATICS_SKILL_NAME;
}

export interface MathematicsValidationResult {
  ok: boolean;
  errors: string[];
}

export interface MathematicsEvidenceSummary {
  problemId?: string;
  statementHash?: string;
  supporting: MathematicsEvidence[];
  refuting: MathematicsEvidence[];
  context: MathematicsEvidence[];
  exactStatementSupporting: MathematicsEvidence[];
  exactStatementRefuting: MathematicsEvidence[];
  counts: MathematicsEvidenceCounts;
  evidenceIds: ReadonlySet<string>;
}

export interface MathematicsEvidenceCounts {
  total: number;
  supporting: number;
  refuting: number;
  context: number;
  exactStatementSupporting: number;
  exactStatementRefuting: number;
  qualifiedSupporting: number;
  reproducibleRefuting: number;
}

export interface MathematicsTerminalGateReadiness {
  problemId?: string;
  statementHash?: string;
  evidence: MathematicsEvidenceCounts;
  decision: MathematicsEvidenceDecision;
  hasKernelVerification: boolean;
  hasPassedReview: boolean;
  /** True for legacy non-Team problems, or when the exact Team official comparator receipt is present. */
  hasOfficialVerification: boolean;
  hasReproducibleCounterexample: boolean;
  hasFormalRefutation: boolean;
  /** True when both decisive evidence lanes are present for the exact statement. */
  hasConflictingEvidence: boolean;
  canVerify: boolean;
  canRefute: boolean;
  verifyMissing: string[];
  refuteMissing: string[];
}

export interface MathematicsValidationOptions {
  /**
   * Read-only migration path for v1 portfolios written before the evidence
   * ledger existed. Mutating callers should keep the strict default.
   */
  allowLegacyEvidenceOmission?: boolean;
}

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Boolean(value) && typeof value === 'object' && !Array.isArray(value);

const recordItems = (value: unknown): readonly Record<string, unknown>[] => {
  if (!Array.isArray(value)) return [];
  for (const item of value) {
    if (!isRecord(item)) return value.filter(isRecord);
  }
  return value;
};

const isNonEmptyString = (value: unknown): value is string => typeof value === 'string' && value.trim().length > 0;

const isNumber = (value: unknown): value is number => typeof value === 'number' && Number.isFinite(value);

const isStringArray = (value: unknown): value is string[] =>
  Array.isArray(value) && value.every((item) => typeof item === 'string');

const includesValue = <T extends string>(values: readonly T[], value: unknown): value is T =>
  typeof value === 'string' && values.includes(value as T);

const MATHEMATICS_STAGES: readonly MathematicsStage[] = [
  ...MATH_WORKFLOW_STAGES,
  'examples',
  'proving',
  'verified',
  'refuted',
];
const PORTFOLIO_STATUSES: readonly MathematicsPortfolioStatus[] = [
  'planning',
  'running',
  'needs_review',
  'verified',
  'refuted',
  'inconclusive',
  'blocked',
];
const PROBLEM_STATUSES: readonly MathematicsProblemStatus[] = [
  'draft',
  'formalized',
  'candidate',
  'verified',
  'refuted',
  'inconclusive',
  'blocked',
];
const ATTEMPT_STATUSES: readonly MathematicsAttemptStatus[] = [
  'draft',
  'running',
  'candidate',
  'verified',
  'refuted',
  'failed',
  'stale',
];
const EXAMPLE_KINDS: readonly MathematicsExampleKind[] = ['positive', 'negative', 'boundary', 'counterexample'];
const EVIDENCE_POLARITIES: readonly MathematicsEvidencePolarity[] = ['supporting', 'refuting', 'context'];
const EVIDENCE_STRENGTHS: readonly MathematicsEvidenceStrength[] = [
  'observed',
  'reproduced',
  'supporting',
  'refuting',
  'formal',
];
const REPRODUCIBILITY_LEVELS: readonly MathematicsReproducibility[] = [
  'single_run',
  'reproduced',
  'independent',
  'formal',
];
const VERIFICATION_STATUSES: readonly MathematicsVerificationStatus[] = [
  'pending',
  'kernel_verified',
  'failed',
  'blocked',
  'unavailable',
];
const VERIFICATION_CLAIMS: readonly MathematicsVerificationClaim[] = ['statement', 'negation'];
const VERIFIERS: readonly MathematicsVerification['verifier'][] = ['lean-kernel', 'bounded-check', 'unavailable'];
const REVIEW_STATUSES: readonly MathematicsReviewStatus[] = [
  'not_requested',
  'queued',
  'running',
  'passed',
  'changes_requested',
  'refuted',
  'inconclusive',
  'stale',
];

const PORTFOLIO_STATUS_BY_STAGE: Readonly<Record<MathematicsStage, readonly MathematicsPortfolioStatus[]>> = {
  intake: ['planning', 'running', 'inconclusive', 'blocked'],
  exploration: ['planning', 'running', 'inconclusive', 'blocked'],
  candidate: ['planning', 'running', 'needs_review', 'inconclusive', 'blocked'],
  formalization: ['planning', 'running', 'inconclusive', 'blocked'],
  review: ['running', 'needs_review', 'inconclusive', 'blocked'],
  final_verification: ['running', 'needs_review', 'inconclusive', 'blocked'],
  done: ['verified', 'refuted', 'inconclusive', 'blocked'],
  // Read-only compatibility for v1 portfolios created before workflow unification.
  examples: ['planning', 'running', 'inconclusive', 'blocked'],
  proving: ['planning', 'running', 'needs_review', 'inconclusive', 'blocked'],
  verified: ['verified'],
  refuted: ['refuted'],
};

const indexByStringId = <T extends { id?: unknown }>(
  items: readonly T[],
  label?: string,
  errors?: string[]
): Map<string, T> => {
  const index = new Map<string, T>();
  const ids = label && errors ? new Set<string>() : undefined;
  let validCount = 0;
  for (const item of items) {
    const id = item.id;
    if (ids && typeof id === 'string') {
      validCount += 1;
      ids.add(id);
    }
    if (isNonEmptyString(id)) index.set(id, item);
  }
  if (ids && errors) {
    if (validCount !== items.length) errors.push(`${label} must contain a string id for every item.`);
    if (ids.size !== validCount) errors.push(`${label} ids must be unique.`);
  }
  return index;
};

export function validateMathematicsPortfolio(
  value: unknown,
  options: MathematicsValidationOptions = {}
): MathematicsValidationResult {
  const errors: string[] = [];
  if (!isRecord(value)) return { ok: false, errors: ['Mathematics portfolio must be an object.'] };
  if (value.schema !== MATHEMATICS_PORTFOLIO_SCHEMA) errors.push(`schema must be ${MATHEMATICS_PORTFOLIO_SCHEMA}.`);
  if (value.version !== 1) errors.push('version must be 1.');
  if (
    value.runIdentity !== undefined &&
    (typeof value.runIdentity !== 'string' || !/^[a-f0-9]{64}$/u.test(value.runIdentity))
  ) {
    errors.push('runIdentity must be a SHA-256 identity.');
  }
  if (!isNonEmptyString(value.title)) errors.push('title is required.');
  if (!includesValue(MATHEMATICS_STAGES, value.stage))
    errors.push(`stage must be one of ${MATHEMATICS_STAGES.join(', ')}.`);
  if (!includesValue(PORTFOLIO_STATUSES, value.status)) {
    errors.push(`status must be one of ${PORTFOLIO_STATUSES.join(', ')}.`);
  }
  if (
    includesValue(MATHEMATICS_STAGES, value.stage) &&
    includesValue(PORTFOLIO_STATUSES, value.status) &&
    !PORTFOLIO_STATUS_BY_STAGE[value.stage].includes(value.status)
  ) {
    errors.push(`stage=${String(value.stage)} cannot use status=${String(value.status)}.`);
  }
  if (!isNumber(value.updatedAt)) errors.push('updatedAt must be a finite number.');
  const stageHistory = value.stageHistory;
  if (stageHistory !== undefined) {
    if (!Array.isArray(stageHistory)) {
      errors.push('stageHistory must be an array.');
    } else {
      let previous: MathematicsStage | undefined;
      stageHistory.forEach((entry, index) => {
        if (!isRecord(entry)) {
          errors.push(`stageHistory[${index}] must be an object.`);
          return;
        }
        if (!includesValue(MATHEMATICS_STAGES, entry.from) || !includesValue(MATHEMATICS_STAGES, entry.to)) {
          errors.push(`stageHistory[${index}] must use valid from/to stages.`);
        }
        if (previous !== undefined && entry.from !== previous) {
          errors.push(`stageHistory[${index}].from must match the preceding stage.`);
        }
        if (['verified', 'refuted', 'done'].includes(String(entry.from)) && entry.to !== entry.from) {
          errors.push(`stageHistory[${index}] cannot roll back from a terminal stage.`);
        }
        if (!isNonEmptyString(entry.commit)) errors.push(`stageHistory[${index}].commit is required.`);
        if (!isNumber(entry.timestamp) || entry.timestamp <= 0)
          errors.push(`stageHistory[${index}].timestamp is invalid.`);
        if (!isNonEmptyString(entry.reason)) errors.push(`stageHistory[${index}].reason is required.`);
        if (includesValue(MATHEMATICS_STAGES, entry.to)) previous = entry.to;
      });
      if (stageHistory.length > 0 && stageHistory[stageHistory.length - 1]?.to !== value.stage) {
        errors.push('stageHistory must terminate at the portfolio stage.');
      }
    }
  }

  const problems = recordItems(value.problems);
  const attempts = recordItems(value.attempts);
  const examples = recordItems(value.examples);
  const hasEvidenceLedger = Object.prototype.hasOwnProperty.call(value, 'evidence');
  const evidence = recordItems(value.evidence);
  const verifications = recordItems(value.verifications);
  const reviews = recordItems(value.reviews);
  const evidenceIdSet = new Set<string>();

  if (!Array.isArray(value.problems)) errors.push('problems must be an array.');
  if (!Array.isArray(value.attempts)) errors.push('attempts must be an array.');
  if (!Array.isArray(value.examples)) errors.push('examples must be an array.');
  // Legacy v1 portfolios did not have an evidence ledger. Treat an omitted
  // field as empty for parsing, but terminal decisions below still require it.
  if (value.evidence != null && !Array.isArray(value.evidence)) errors.push('evidence must be an array.');
  if (!Array.isArray(value.verifications)) errors.push('verifications must be an array.');
  if (!Array.isArray(value.reviews)) errors.push('reviews must be an array.');
  const problemById = indexByStringId(problems, 'problems', errors);
  const attemptById = indexByStringId(attempts, 'attempts', errors);
  const exampleById = indexByStringId(examples, 'examples', errors);
  indexByStringId(evidence, 'evidence', errors);
  const verificationById = indexByStringId(verifications, 'verifications', errors);
  const reviewById = indexByStringId(reviews, 'reviews', errors);
  const gateReceiptsByProblem = new WeakMap<
    object,
    Readonly<{ localGateReceipt?: MathLocalGateReceipt; officialGateReceipt?: MathOfficialGateReceipt }>
  >();
  const normalizedGateReceiptsFor = (problem: {
    localGateReceipt?: unknown;
    officialGateReceipt?: unknown;
  }): Readonly<{ localGateReceipt?: MathLocalGateReceipt; officialGateReceipt?: MathOfficialGateReceipt }> => {
    const cached = gateReceiptsByProblem.get(problem);
    if (cached) return cached;
    const receipts = {
      ...(problem.localGateReceipt
        ? { localGateReceipt: normalizeMathLocalGateReceipt(problem.localGateReceipt as MathLocalGateReceipt) }
        : {}),
      ...(problem.officialGateReceipt
        ? {
            officialGateReceipt: normalizeMathOfficialGateReceipt(
              problem.officialGateReceipt as MathOfficialGateReceipt
            ),
          }
        : {}),
    };
    gateReceiptsByProblem.set(problem, receipts);
    return receipts;
  };

  const terminalProblems: MathematicsProblem[] = [];
  const terminalProblemStatuses = new Set<MathematicsProblemStatus>();
  problems.forEach((problem, index) => {
    if (!isNonEmptyString(problem.id)) errors.push(`problems[${index}].id is required.`);
    if (!isNonEmptyString(problem.title)) errors.push(`problems[${index}].title is required.`);
    if (!isNonEmptyString(problem.informalStatement)) errors.push(`problems[${index}].informalStatement is required.`);
    if (!isStringArray(problem.assumptions)) errors.push(`problems[${index}].assumptions must be a string array.`);
    if (!isStringArray(problem.attemptIds)) errors.push(`problems[${index}].attemptIds must be a string array.`);
    if (!isStringArray(problem.exampleIds)) errors.push(`problems[${index}].exampleIds must be a string array.`);
    if (problem.reviewIds != null && !isStringArray(problem.reviewIds)) {
      errors.push(`problems[${index}].reviewIds must be a string array.`);
    }
    if (problem.fastCheck != null) {
      try {
        const fastCheck = normalizeMathFastCheck(problem.fastCheck as unknown as MathFastCheck);
        if (isNonEmptyString(problem.statementHash) && fastCheck.statementHash !== problem.statementHash) {
          errors.push(`problems[${index}].fastCheck.statementHash must match problem statementHash.`);
        }
      } catch (error) {
        errors.push(
          `problems[${index}].fastCheck is invalid: ${error instanceof Error ? error.message : String(error)}`
        );
      }
    }
    if (problem.problemContract != null) {
      try {
        const contract = normalizeMathProblemContract(problem.problemContract as unknown as MathProblemContract);
        if (contract.problemId !== problem.id) {
          errors.push(`problems[${index}].problemContract.problemId must match problem id.`);
        }
        if (isNonEmptyString(problem.statementHash) && contract.statementHash !== problem.statementHash) {
          errors.push(`problems[${index}].problemContract.statementHash must match problem statementHash.`);
        }
        if (contract.informalStatement !== problem.informalStatement) {
          errors.push(`problems[${index}].problemContract.informalStatement must match problem informalStatement.`);
        }
        if (isNonEmptyString(problem.formalStatement) && contract.formalStatement !== problem.formalStatement) {
          errors.push(`problems[${index}].problemContract.formalStatement must match problem formalStatement.`);
        }
        if (
          isStringArray(problem.assumptions) &&
          (contract.assumptions.length !== problem.assumptions.length ||
            contract.assumptions.some(
              (assumption, assumptionIndex) => assumption !== (problem.assumptions as string[])[assumptionIndex]
            ))
        ) {
          errors.push(`problems[${index}].problemContract.assumptions must match problem assumptions.`);
        }
        if (problem.alignmentCheck != null) {
          const alignment = normalizeMathAlignmentCheck(
            problem.alignmentCheck as unknown as MathAlignmentCheck,
            contract
          );
          if (alignment.contractCommit === 'WORKTREE') {
            errors.push(`problems[${index}].alignmentCheck must target a committed contract.`);
          }
        }
        if (problem.routeCards != null) {
          const hasRouteSelection = problem.routeSelection != null;
          const routeFingerprints = hasRouteSelection ? undefined : new Set<string>();
          let routeStatementMismatch = false;
          const routeCards = (problem.routeCards as unknown as MathRouteCard[]).map((card) => {
            const normalized = normalizeMathRouteCard(card);
            routeFingerprints?.add(normalized.routeFingerprint);
            if (!hasRouteSelection) routeStatementMismatch ||= normalized.statementHash !== problem.statementHash;
            return normalized;
          });
          if (routeCards.length < 1) errors.push(`problems[${index}].routeCards must contain at least one card.`);
          if (!hasRouteSelection) {
            if (routeFingerprints!.size !== routeCards.length) {
              errors.push(`problems[${index}].routeCards must use distinct route fingerprints.`);
            }
            assertNormalizedMathRouteCardsStructurallyDistinct(routeCards);
            if (isNonEmptyString(problem.statementHash) && routeStatementMismatch) {
              errors.push(`problems[${index}].routeCards statementHash must match problem statementHash.`);
            }
          } else {
            const routeSelection = normalizeMathRouteSelectionFromNormalized(
              problem.routeSelection as unknown as MathRouteSelection,
              routeCards
            );
            if (isNonEmptyString(problem.statementHash) && routeSelection.statementHash !== problem.statementHash) {
              errors.push(`problems[${index}].routeSelection statementHash must match problem statementHash.`);
            }
          }
        } else if (problem.routeSelection != null) {
          errors.push(`problems[${index}].routeSelection requires routeCards.`);
        }
        const { localGateReceipt, officialGateReceipt } = normalizedGateReceiptsFor(problem);
        if (officialGateReceipt && !localGateReceipt) {
          errors.push(`problems[${index}].officialGateReceipt requires localGateReceipt.`);
        }
        const expectedReceiptClaim = problem.status === 'refuted' ? 'negation' : 'statement';
        const expectedLeanHash =
          expectedReceiptClaim === 'negation' ? contract.leanNegationHash : contract.leanStatementHash;
        if (localGateReceipt) {
          if (localGateReceipt.statementHash !== contract.statementHash) {
            errors.push(`problems[${index}].localGateReceipt statementHash must match problemContract.`);
          }
          if (
            (problem.status === 'verified' || problem.status === 'refuted') &&
            ((localGateReceipt.claim || 'statement') !== expectedReceiptClaim ||
              localGateReceipt.leanStatementHash !== expectedLeanHash)
          ) {
            errors.push(`problems[${index}].localGateReceipt must match the terminal claim and canonical Lean hash.`);
          }
          if (
            problem.routeSelection &&
            ![
              (problem.routeSelection as unknown as MathRouteSelection).primaryFingerprint,
              (problem.routeSelection as unknown as MathRouteSelection).reserveFingerprint,
            ]
              .filter(Boolean)
              .includes(localGateReceipt.routeFingerprint)
          ) {
            errors.push(`problems[${index}].localGateReceipt route must match the frozen routeSelection.`);
          }
        }
        if (
          officialGateReceipt &&
          localGateReceipt &&
          (officialGateReceipt.statementHash !== contract.statementHash ||
            (officialGateReceipt.claim || 'statement') !== expectedReceiptClaim ||
            (officialGateReceipt.claim || 'statement') !== (localGateReceipt.claim || 'statement') ||
            officialGateReceipt.targetCommit !== localGateReceipt.targetCommit ||
            officialGateReceipt.routeFingerprint !== localGateReceipt.routeFingerprint ||
            officialGateReceipt.localGateReceiptId !== localGateReceipt.receiptId ||
            officialGateReceipt.theoremName !== localGateReceipt.theoremName ||
            officialGateReceipt.proofHash !== localGateReceipt.proofHash ||
            officialGateReceipt.theoremDeclarationHash !== localGateReceipt.theoremDeclarationHash ||
            officialGateReceipt.command !== contract.officialVerificationCommand ||
            (officialGateReceipt.sourceDeclarationHash !== undefined &&
              officialGateReceipt.sourceDeclarationHash !== localGateReceipt.sourceDeclarationHash) ||
            officialGateReceipt.problemId !== contract.problemId ||
            officialGateReceipt.officialManifestId !== contract.officialManifestId ||
            officialGateReceipt.officialManifestHash !== contract.officialManifestHash ||
            officialGateReceipt.leanStatementHash !== expectedLeanHash)
        ) {
          errors.push(
            `problems[${index}].officialGateReceipt must match the contract, local receipt, route, commit, and official command.`
          );
        }
      } catch (error) {
        errors.push(`problems[${index}].problemContract is invalid: ${String((error as Error).message || error)}.`);
      }
    } else if (problem.alignmentCheck != null) {
      errors.push(`problems[${index}].alignmentCheck requires problemContract.`);
    }
    if (problem.researchContract != null) {
      try {
        const researchContract = normalizeMathResearchProblemContract(
          problem.researchContract as unknown as MathResearchProblemContract
        );
        if (researchContract.problemId !== problem.id) {
          errors.push(`problems[${index}].researchContract.problemId must match problem id.`);
        }
      } catch (error) {
        errors.push(`problems[${index}].researchContract is invalid: ${String((error as Error).message || error)}.`);
      }
    }
    if (problem.feasibility != null) {
      try {
        const feasibility = buildMathFeasibilityProfile(problem.feasibility as unknown as MathFeasibilitySignals);
        if (feasibility.candidateId && feasibility.candidateId !== problem.id) {
          errors.push(`problems[${index}].feasibility.candidateId must match problem id.`);
        }
      } catch (error) {
        errors.push(`problems[${index}].feasibility is invalid: ${String((error as Error).message || error)}.`);
      }
    }
    if (!includesValue(PROBLEM_STATUSES, problem.status)) {
      errors.push(`problems[${index}].status must be one of ${PROBLEM_STATUSES.join(', ')}.`);
    }
    if (!isNumber(problem.updatedAt)) errors.push(`problems[${index}].updatedAt must be a finite number.`);
    if (problem.status === 'verified' || problem.status === 'refuted') {
      terminalProblems.push(problem as unknown as MathematicsProblem);
      terminalProblemStatuses.add(problem.status);
    }
  });
  // A missing ledger is accepted only for read-only migration of old v1
  // projections. A caller that explicitly supplies `evidence: []` remains
  // subject to the terminal evidence gate.
  const enforceTerminalEvidence = hasEvidenceLedger || !options.allowLegacyEvidenceOmission;
  const collectTerminalEvidence = enforceTerminalEvidence && terminalProblems.length > 0;

  if (
    value.activeProblemId != null &&
    (!isNonEmptyString(value.activeProblemId) || !problemById.has(value.activeProblemId))
  ) {
    errors.push('activeProblemId must reference an existing problem.');
  }

  problems.forEach((problem, index) => {
    if (!isNonEmptyString(problem.id)) return;
    if (isStringArray(problem.attemptIds)) {
      problem.attemptIds.forEach((attemptId) => {
        const attempt = attemptById.get(attemptId);
        if (!attempt || attempt.problemId !== problem.id) {
          errors.push(`problems[${index}].attemptIds must reference attempts owned by problem ${problem.id}.`);
        }
      });
    }
    if (isStringArray(problem.exampleIds)) {
      problem.exampleIds.forEach((exampleId) => {
        const example = exampleById.get(exampleId);
        if (!example || example.problemId !== problem.id) {
          errors.push(`problems[${index}].exampleIds must reference examples owned by problem ${problem.id}.`);
        }
      });
    }
    if (problem.verificationId != null) {
      const verification = isNonEmptyString(problem.verificationId)
        ? verificationById.get(problem.verificationId)
        : undefined;
      if (!verification || verification.problemId !== problem.id) {
        errors.push(`problems[${index}].verificationId must reference a verification owned by problem ${problem.id}.`);
      }
    }
    if (problem.reviewId != null) {
      const review = isNonEmptyString(problem.reviewId) ? reviewById.get(problem.reviewId) : undefined;
      if (!review || review.problemId !== problem.id) {
        errors.push(`problems[${index}].reviewId must reference a review owned by problem ${problem.id}.`);
      }
    }
    if (isStringArray(problem.reviewIds)) {
      problem.reviewIds.forEach((reviewId) => {
        const review = reviewById.get(reviewId);
        if (!review || review.problemId !== problem.id) {
          errors.push(`problems[${index}].reviewIds must reference reviews owned by problem ${problem.id}.`);
        }
      });
    }
  });

  attempts.forEach((attempt, index) => {
    if (!isNonEmptyString(attempt.id)) errors.push(`attempts[${index}].id is required.`);
    if (
      attempt.runIdentity !== undefined &&
      (typeof attempt.runIdentity !== 'string' || !/^[a-f0-9]{64}$/u.test(attempt.runIdentity))
    ) {
      errors.push(`attempts[${index}].runIdentity must be a SHA-256 identity.`);
    }
    if (!isNonEmptyString(attempt.problemId)) errors.push(`attempts[${index}].problemId is required.`);
    if (!isNonEmptyString(attempt.strategy)) errors.push(`attempts[${index}].strategy is required.`);
    if (!includesValue(ATTEMPT_STATUSES, attempt.status)) {
      errors.push(`attempts[${index}].status must be one of ${ATTEMPT_STATUSES.join(', ')}.`);
    }
    if (!isNumber(attempt.createdAt) || !isNumber(attempt.updatedAt)) {
      errors.push(`attempts[${index}] needs finite createdAt and updatedAt.`);
    }
    if (isNonEmptyString(attempt.problemId) && !problemById.has(attempt.problemId)) {
      errors.push(`attempts[${index}].problemId must reference an existing problem.`);
    }
    if (attempt.recoveryCheckpoint != null) {
      try {
        const checkpoint = normalizeMathRecoveryCheckpoint(
          attempt.recoveryCheckpoint as unknown as MathRecoveryCheckpoint
        );
        const problem = isNonEmptyString(attempt.problemId) ? problemById.get(attempt.problemId) : undefined;
        if (
          problem &&
          isNonEmptyString(problem.statementHash) &&
          checkpoint.ledger.statementHash !== problem.statementHash
        ) {
          errors.push(`attempts[${index}].recoveryCheckpoint statementHash must match its problem.`);
        }
        if (isNonEmptyString(attempt.commit) && checkpoint.targetCommit !== attempt.commit) {
          errors.push(`attempts[${index}].recoveryCheckpoint targetCommit must match attempt commit.`);
        }
      } catch (error) {
        errors.push(`attempts[${index}].recoveryCheckpoint is invalid: ${String((error as Error).message || error)}.`);
      }
    }
    if (attempt.lessons != null) {
      try {
        const problem = isNonEmptyString(attempt.problemId) ? problemById.get(attempt.problemId) : undefined;
        let lessonStatementMismatch = false;
        for (const lesson of attempt.lessons as unknown as MathLesson[]) {
          const normalized = normalizeMathLesson(lesson);
          if (normalized.statementHash !== problem?.statementHash) lessonStatementMismatch = true;
        }
        if (problem && isNonEmptyString(problem.statementHash) && lessonStatementMismatch) {
          errors.push(`attempts[${index}].lessons statementHash must match its problem.`);
        }
      } catch (error) {
        errors.push(`attempts[${index}].lessons are invalid: ${String((error as Error).message || error)}.`);
      }
    }
  });

  const examplesByProblem = new Map<string, Record<string, unknown>[]>();
  examples.forEach((example, index) => {
    const problemId = typeof example.problemId === 'string' ? example.problemId : undefined;
    if (collectTerminalEvidence && problemId) {
      const list = examplesByProblem.get(problemId) || [];
      list.push(example);
      examplesByProblem.set(problemId, list);
    }
    if (!isNonEmptyString(example.id)) errors.push(`examples[${index}].id is required.`);
    if (!isNonEmptyString(example.problemId)) errors.push(`examples[${index}].problemId is required.`);
    if (!isNonEmptyString(example.input)) errors.push(`examples[${index}].input is required.`);
    if (!includesValue(EXAMPLE_KINDS, example.kind)) {
      errors.push(`examples[${index}].kind must be one of ${EXAMPLE_KINDS.join(', ')}.`);
    }
    if (!isStringArray(example.evidenceIds)) errors.push(`examples[${index}].evidenceIds must be a string array.`);
    if (!isNumber(example.createdAt)) errors.push(`examples[${index}].createdAt must be a finite number.`);
    if (isNonEmptyString(example.problemId) && !problemById.has(example.problemId)) {
      errors.push(`examples[${index}].problemId must reference an existing problem.`);
    }
  });

  const evidenceByProblem = new Map<string, MathematicsEvidence[]>();
  evidence.forEach((item, index) => {
    if (collectTerminalEvidence) {
      const typedItem = item as unknown as MathematicsEvidence;
      const list = evidenceByProblem.get(typedItem.problemId) || [];
      list.push(typedItem);
      evidenceByProblem.set(typedItem.problemId, list);
    }
    if (collectTerminalEvidence && isStringArray(item.evidenceIds)) {
      for (const evidenceId of item.evidenceIds) evidenceIdSet.add(evidenceId);
    }
    if (!isNonEmptyString(item.id)) errors.push(`evidence[${index}].id is required.`);
    if (!isNonEmptyString(item.problemId)) errors.push(`evidence[${index}].problemId is required.`);
    if (!includesValue(EVIDENCE_POLARITIES, item.polarity)) {
      errors.push(`evidence[${index}].polarity must be one of ${EVIDENCE_POLARITIES.join(', ')}.`);
    }
    if (!includesValue(EVIDENCE_STRENGTHS, item.strength)) {
      errors.push(`evidence[${index}].strength must be one of ${EVIDENCE_STRENGTHS.join(', ')}.`);
    }
    if (!includesValue(REPRODUCIBILITY_LEVELS, item.reproducibility)) {
      errors.push(`evidence[${index}].reproducibility must be one of ${REPRODUCIBILITY_LEVELS.join(', ')}.`);
    }
    for (const field of ['scope', 'method', 'observed', 'commit'] as const) {
      if (!isNonEmptyString(item[field])) errors.push(`evidence[${index}].${field} is required.`);
    }
    if (!isStringArray(item.inputRefs)) errors.push(`evidence[${index}].inputRefs must be a string array.`);
    if (!isStringArray(item.outputRefs)) errors.push(`evidence[${index}].outputRefs must be a string array.`);
    if (!isStringArray(item.evidenceIds) || item.evidenceIds.length === 0) {
      errors.push(`evidence[${index}].evidenceIds must contain at least one Science evidence id.`);
    }
    if (!isNumber(item.createdAt)) errors.push(`evidence[${index}].createdAt must be a finite number.`);
    if (item.polarity === 'supporting' && item.strength === 'refuting') {
      errors.push(`evidence[${index}] cannot use refuting strength for supporting evidence.`);
    }
    if (item.polarity === 'refuting' && item.strength === 'supporting') {
      errors.push(`evidence[${index}] cannot use supporting strength for refuting evidence.`);
    }
    if (isNonEmptyString(item.problemId) && !problemById.has(item.problemId)) {
      errors.push(`evidence[${index}].problemId must reference an existing problem.`);
    }
  });

  verifications.forEach((verification, index) => {
    if (!isNonEmptyString(verification.id)) errors.push(`verifications[${index}].id is required.`);
    if (!isNonEmptyString(verification.problemId)) errors.push(`verifications[${index}].problemId is required.`);
    if (!isNonEmptyString(verification.targetCommit)) errors.push(`verifications[${index}].targetCommit is required.`);
    if (!isNonEmptyString(verification.statementHash))
      errors.push(`verifications[${index}].statementHash is required.`);
    if (!isNumber(verification.goalsRemaining) || verification.goalsRemaining < 0) {
      errors.push(`verifications[${index}].goalsRemaining must be a non-negative number.`);
    }
    if (!isNumber(verification.sorryCount) || verification.sorryCount < 0) {
      errors.push(`verifications[${index}].sorryCount must be a non-negative number.`);
    }
    if (!isNumber(verification.admitCount) || verification.admitCount < 0) {
      errors.push(`verifications[${index}].admitCount must be a non-negative number.`);
    }
    if (!isStringArray(verification.axioms)) errors.push(`verifications[${index}].axioms must be a string array.`);
    if (!includesValue(VERIFICATION_STATUSES, verification.status)) {
      errors.push(`verifications[${index}].status must be one of ${VERIFICATION_STATUSES.join(', ')}.`);
    }
    if (!includesValue(VERIFIERS, verification.verifier)) {
      errors.push(`verifications[${index}].verifier must be one of ${VERIFIERS.join(', ')}.`);
    }
    if (verification.claim != null && !includesValue(VERIFICATION_CLAIMS, verification.claim)) {
      errors.push(`verifications[${index}].claim must be one of ${VERIFICATION_CLAIMS.join(', ')}.`);
    }
    if (!isRecord(verification.toolchain) || !isNonEmptyString(verification.toolchain.lean)) {
      errors.push(`verifications[${index}].toolchain.lean is required.`);
    }
    if (verification.status === 'kernel_verified') {
      if (verification.goalsRemaining !== 0)
        errors.push(`verifications[${index}] cannot be kernel_verified with open goals.`);
      if (verification.sorryCount !== 0 || verification.admitCount !== 0) {
        errors.push(`verifications[${index}] cannot be kernel_verified with sorry or admit.`);
      }
      if (!isNonEmptyString(verification.proofHash)) errors.push(`verifications[${index}] needs a proofHash.`);
    }
    if (isNonEmptyString(verification.problemId) && !problemById.has(verification.problemId)) {
      errors.push(`verifications[${index}].problemId must reference an existing problem.`);
    }
  });

  reviews.forEach((review, index) => {
    if (!isNonEmptyString(review.id)) errors.push(`reviews[${index}].id is required.`);
    if (!isNonEmptyString(review.problemId)) errors.push(`reviews[${index}].problemId is required.`);
    if (!isNonEmptyString(review.targetCommit)) errors.push(`reviews[${index}].targetCommit is required.`);
    if (!isNonEmptyString(review.statementHash)) errors.push(`reviews[${index}].statementHash is required.`);
    if (!isStringArray(review.issueIds)) errors.push(`reviews[${index}].issueIds must be a string array.`);
    if (!includesValue(REVIEW_STATUSES, review.status)) {
      errors.push(`reviews[${index}].status must be one of ${REVIEW_STATUSES.join(', ')}.`);
    }
    if (review.status === 'passed' && review.verdict !== 'passed') {
      errors.push(`reviews[${index}] cannot be passed without a passed verdict.`);
    }
    if (review.candidateReview != null) {
      try {
        const candidateReview = normalizeMathCandidateReview(review.candidateReview as unknown as MathCandidateReview);
        if (candidateReview.problemId !== review.problemId) {
          errors.push(`reviews[${index}].candidateReview.problemId must match review problemId.`);
        }
        if (candidateReview.statementHash !== review.statementHash) {
          errors.push(`reviews[${index}].candidateReview.statementHash must match review statementHash.`);
        }
        if (candidateReview.targetCommit !== review.targetCommit) {
          errors.push(`reviews[${index}].candidateReview.targetCommit must match review targetCommit.`);
        }
        if (
          isNonEmptyString(review.reviewerSessionId) &&
          candidateReview.reviewerSessionId !== review.reviewerSessionId
        ) {
          errors.push(`reviews[${index}].candidateReview.reviewerSessionId must match review reviewerSessionId.`);
        }
        if (candidateReview.verdict === 'sound' && (review.status !== 'passed' || review.verdict !== 'passed')) {
          errors.push(`reviews[${index}] sound candidateReview requires passed status and verdict.`);
        }
        if (candidateReview.verdict === 'gap' && review.status === 'passed') {
          errors.push(`reviews[${index}] gap candidateReview cannot use passed status.`);
        }
        if (candidateReview.verdict === 'wrong' && review.status !== 'refuted') {
          errors.push(`reviews[${index}] wrong candidateReview requires refuted status.`);
        }
      } catch (error) {
        errors.push(`reviews[${index}].candidateReview is invalid: ${String((error as Error).message || error)}.`);
      }
    }
    if (isNonEmptyString(review.problemId) && !problemById.has(review.problemId)) {
      errors.push(`reviews[${index}].problemId must reference an existing problem.`);
    }
  });

  const activeProblem = isNonEmptyString(value.activeProblemId) ? problemById.get(value.activeProblemId) : undefined;
  if (enforceTerminalEvidence)
    terminalProblems.forEach((problem) => {
      const statementHash = isNonEmptyString(problem.statementHash) ? problem.statementHash : undefined;
      if (!statementHash) {
        errors.push(`problem ${problem.id} cannot be ${problem.status} without an exact statementHash.`);
        return;
      }
      if (problem.status === 'verified' && !problem.problemContract) {
        errors.push(
          `problem ${problem.id} cannot be verified without an immutable MathProblemContract and official manifest identity.`
        );
      } else if (
        problem.status === 'verified' &&
        (!problem.problemContract?.officialManifestId || !problem.problemContract.officialManifestHash)
      ) {
        errors.push(`problem ${problem.id} cannot be verified without officialManifestId and officialManifestHash.`);
      }
      if (problem.status === 'refuted' && !problem.problemContract) {
        errors.push(`problem ${problem.id} cannot be refuted without an immutable MathProblemContract.`);
      } else if (
        problem.status === 'refuted' &&
        (!problem.problemContract?.formalNegationStatement || !problem.problemContract.leanNegationHash)
      ) {
        errors.push(`problem ${problem.id} cannot be refuted without a canonical Lean negation in its contract.`);
      } else if (
        problem.status === 'refuted' &&
        (!problem.problemContract?.officialManifestId || !problem.problemContract.officialManifestHash)
      ) {
        errors.push(`problem ${problem.id} cannot be refuted without officialManifestId and officialManifestHash.`);
      }
      const problemEvidence = evidenceByProblem.get(problem.id) || [];
      let hasSupporting = false;
      let hasRefuting = false;
      let hasFormalSupporting = false;
      for (const item of problemEvidence) {
        if (item.statementHash !== statementHash || item.commit === 'WORKTREE') continue;
        const reproducible =
          item.reproducibility === 'reproduced' ||
          item.reproducibility === 'independent' ||
          item.reproducibility === 'formal';
        if (!reproducible) continue;
        if (item.polarity === 'supporting' && (item.strength === 'supporting' || item.strength === 'formal')) {
          hasSupporting = true;
          if (item.strength === 'formal' && item.reproducibility === 'formal') {
            hasFormalSupporting = true;
          }
        } else if (item.polarity === 'refuting' && (item.strength === 'refuting' || item.strength === 'formal')) {
          hasRefuting = true;
        }
      }
      if (problem.status === 'verified') {
        const verification = isNonEmptyString(problem.verificationId)
          ? verificationById.get(problem.verificationId)
          : undefined;
        const hasMatchingKernelSupporting = Boolean(
          verification &&
          verification.problemId === problem.id &&
          verification.status === 'kernel_verified' &&
          verification.claim !== 'negation' &&
          verification.statementHash === statementHash &&
          verification.targetCommit !== 'WORKTREE'
        );
        if (!hasSupporting && !hasMatchingKernelSupporting) {
          errors.push(
            `problem ${problem.id} cannot be verified without reproducible supporting evidence for its statementHash.`
          );
        }
        if (hasRefuting) {
          errors.push(
            `problem ${problem.id} cannot be verified while the exact statement also has reproducible refuting evidence; resolve the conflict first.`
          );
        }
        if (
          !verification ||
          verification.problemId !== problem.id ||
          verification.status !== 'kernel_verified' ||
          verification.claim === 'negation' ||
          verification.statementHash !== statementHash ||
          verification.targetCommit === 'WORKTREE'
        ) {
          errors.push(`problem ${problem.id} cannot be verified without its matching kernel verification.`);
        }
        const reviewIds = isStringArray(problem.reviewIds) ? problem.reviewIds : [];
        const teamCandidateReviews: MathCandidateReview[] = [];
        const receiptCandidateReviews: MathCandidateReview[] = [];
        for (const reviewId of reviewIds) {
          const review = reviewById.get(reviewId);
          if (review?.candidateReview) {
            receiptCandidateReviews.push(review.candidateReview as unknown as MathCandidateReview);
          }
          if (
            review?.problemId === problem.id &&
            review.status === 'passed' &&
            review.verdict === 'passed' &&
            isRecord(review.candidateReview)
          ) {
            teamCandidateReviews.push(review.candidateReview as unknown as MathCandidateReview);
          }
        }
        let reviewTargetCommit: string | undefined;
        if (reviewIds.length > 0) {
          try {
            const gate = aggregateMathCandidateReviews(teamCandidateReviews);
            reviewTargetCommit = gate.targetCommit;
            if (!gate.canAdvance || gate.problemId !== problem.id || gate.statementHash !== statementHash) {
              errors.push(`problem ${problem.id} cannot be verified without one sound independent review.`);
            }
          } catch (error) {
            errors.push(
              `problem ${problem.id} has an invalid review gate: ${String((error as Error).message || error)}.`
            );
          }
        } else {
          const review = isNonEmptyString(problem.reviewId) ? reviewById.get(problem.reviewId) : undefined;
          if (
            !review ||
            review.problemId !== problem.id ||
            review.status !== 'passed' ||
            review.verdict !== 'passed' ||
            review.statementHash !== statementHash ||
            review.targetCommit === 'WORKTREE'
          ) {
            errors.push(`problem ${problem.id} cannot be verified without its matching passed review.`);
          }
          reviewTargetCommit = isNonEmptyString(review?.targetCommit) ? review.targetCommit : undefined;
        }
        if (verification && reviewTargetCommit && verification.targetCommit !== reviewTargetCommit) {
          errors.push(`problem ${problem.id} verification and review must target the same Git commit.`);
        }
        if (problem.problemContract) {
          let gateReceipts:
            | Readonly<{ localGateReceipt?: MathLocalGateReceipt; officialGateReceipt?: MathOfficialGateReceipt }>
            | undefined;
          try {
            gateReceipts = normalizedGateReceiptsFor(problem);
          } catch {
            // The structural problem validation above reports the precise receipt error.
          }
          const localGateReceipt = gateReceipts?.localGateReceipt;
          const officialGateReceipt = gateReceipts?.officialGateReceipt;
          if (!localGateReceipt || !officialGateReceipt) {
            errors.push(`problem ${problem.id} cannot be verified without local and official gate receipts.`);
          } else {
            if (
              officialGateReceipt.localGateReceiptId !== localGateReceipt.receiptId ||
              officialGateReceipt.targetCommit !== localGateReceipt.targetCommit
            ) {
              errors.push(`problem ${problem.id} gate receipts must identify the same frozen candidate.`);
            }
            if (
              verification?.targetCommit !== officialGateReceipt.targetCommit ||
              reviewTargetCommit !== officialGateReceipt.targetCommit
            ) {
              errors.push(
                `problem ${problem.id} official receipt, kernel verification, and reviews must target one commit.`
              );
            }
            if (!isStringArray(problem.reviewIds) || problem.reviewIds.length < 1) {
              errors.push(`problem ${problem.id} Team verification requires one receipt-bound review.`);
            } else {
              try {
                const gate = aggregateMathCandidateReviews(receiptCandidateReviews);
                if (gate.problemId !== problem.id || gate.localGateReceiptId !== localGateReceipt.receiptId) {
                  errors.push(`problem ${problem.id} reviews must reference its local gate receipt.`);
                }
              } catch {
                // The review validation above reports the precise gate error.
              }
            }
          }
        }
      }
      if (problem.status === 'refuted') {
        if (hasFormalSupporting) {
          errors.push(
            `problem ${problem.id} cannot be refuted while the exact statement also has formal supporting evidence; resolve the conflict first.`
          );
        }
        const negationVerification = isNonEmptyString(problem.verificationId)
          ? verificationById.get(problem.verificationId)
          : undefined;
        let localGateReceipt: MathLocalGateReceipt | undefined;
        let officialGateReceipt: MathOfficialGateReceipt | undefined;
        try {
          ({ localGateReceipt, officialGateReceipt } = normalizedGateReceiptsFor(problem));
        } catch {
          // The structural receipt validation above reports the precise error.
        }
        const contract = problem.problemContract;
        const hasFormalNegation = Boolean(
          contract?.formalNegationStatement &&
          contract.leanNegationHash &&
          negationVerification &&
          negationVerification.problemId === problem.id &&
          negationVerification.status === 'kernel_verified' &&
          negationVerification.claim === 'negation' &&
          negationVerification.statementHash === statementHash &&
          negationVerification.targetCommit !== 'WORKTREE' &&
          negationVerification.goalsRemaining === 0 &&
          negationVerification.sorryCount === 0 &&
          negationVerification.admitCount === 0 &&
          isStringArray(negationVerification.axioms) &&
          negationVerification.axioms.length === 0 &&
          localGateReceipt?.claim === 'negation' &&
          localGateReceipt.receiptId === negationVerification.id &&
          localGateReceipt.targetCommit === negationVerification.targetCommit &&
          localGateReceipt.statementHash === statementHash &&
          localGateReceipt.leanStatementHash === contract.leanNegationHash &&
          officialGateReceipt?.claim === 'negation' &&
          officialGateReceipt.localGateReceiptId === localGateReceipt.receiptId &&
          officialGateReceipt.targetCommit === localGateReceipt.targetCommit &&
          officialGateReceipt.problemId === problem.id &&
          officialGateReceipt.leanStatementHash === contract.leanNegationHash
        );
        if (!hasRefuting && !hasFormalNegation) {
          errors.push(`problem ${problem.id} cannot be refuted without reproducible refuting evidence.`);
        }
        if (!hasFormalNegation) {
          errors.push(
            `problem ${problem.id} needs a contract-bound Lean negation and matching local and official receipts.`
          );
        }
      }
    });

  if (enforceTerminalEvidence && value.status === 'verified') {
    if (!terminalProblemStatuses.has('verified')) {
      errors.push('portfolio cannot be verified without a verified problem and matching formal gate receipts.');
    }
    if (!isNonEmptyString(value.activeProblemId)) {
      errors.push('portfolio cannot be verified without an activeProblemId bound to the verified problem.');
    } else if (activeProblem?.status !== 'verified') {
      errors.push('portfolio activeProblemId must reference the verified problem when portfolio status is verified.');
    }
  }
  if (enforceTerminalEvidence && value.status === 'refuted') {
    if (!terminalProblemStatuses.has('refuted')) {
      errors.push('portfolio cannot be refuted without a refuted problem and matching formal-negation receipts.');
    }
    if (!isNonEmptyString(value.activeProblemId)) {
      errors.push('portfolio cannot be refuted without an activeProblemId bound to the refuted problem.');
    } else if (activeProblem?.status !== 'refuted') {
      errors.push('portfolio activeProblemId must reference the refuted problem when portfolio status is refuted.');
    }
  }

  if (!isStringArray(value.blockers)) errors.push('blockers must be a string array.');
  if (!Array.isArray(value.nextActions)) {
    errors.push('nextActions must be an array.');
  } else {
    value.nextActions.forEach((action, index) => {
      if (!isRecord(action) || !isNonEmptyString(action.id) || !isNonEmptyString(action.label)) {
        errors.push(`nextActions[${index}] needs id and label.`);
      }
      if (
        isRecord(action) &&
        !includesValue(['formalize', 'search', 'verify', 'review', 'decision'] as const, action.kind)
      ) {
        errors.push(`nextActions[${index}].kind is invalid.`);
      }
      if (isRecord(action) && !includesValue(['now', 'next', 'later'] as const, action.priority)) {
        errors.push(`nextActions[${index}].priority is invalid.`);
      }
    });
  }

  return { ok: errors.length === 0, errors };
}

export function readMathematicsPortfolio(metadata: unknown): MathematicsPortfolio | undefined {
  if (!isRecord(metadata)) return undefined;
  const candidate = metadata.mathematics;
  if (!isRecord(candidate)) return undefined;
  // Keep old v1 projections readable while making the new evidence ledger
  // explicit in all newly emitted portfolio objects.
  const legacyEvidenceOmitted = !Object.prototype.hasOwnProperty.call(candidate, 'evidence');
  const validation = validateMathematicsPortfolio(candidate, {
    allowLegacyEvidenceOmission: legacyEvidenceOmitted,
  });
  return validation.ok ? normalizeValidatedMathematicsPortfolio(candidate, legacyEvidenceOmitted) : undefined;
}

/** Build a stable intake ranking without mutating the durable portfolio. */
export function deriveMathematicsFeasibilityRanking(
  portfolio: MathematicsPortfolio,
  generatedAt = Date.now()
): MathematicsFeasibilityRanking {
  if (!Number.isFinite(generatedAt) || generatedAt <= 0) {
    throw new TypeError('Mathematics feasibility ranking generatedAt must be a positive timestamp');
  }
  const inputs = portfolio.problems.flatMap((problem) =>
    problem.feasibility
      ? [
          {
            ...problem.feasibility,
            candidateId: problem.id,
          } satisfies MathFeasibilitySignals,
        ]
      : []
  );
  return Object.freeze({ generatedAt, candidates: rankMathFeasibilityCandidates(inputs) });
}

/** Remove legacy projection-only fields after the caller has validated the portfolio. */
export function normalizeValidatedMathematicsPortfolio(
  candidate: Record<string, unknown>,
  legacyEvidenceOmitted = false
): MathematicsPortfolio {
  if (!legacyEvidenceOmitted && !Object.prototype.hasOwnProperty.call(candidate, 'lessons')) {
    return candidate as unknown as MathematicsPortfolio;
  }
  const { lessons: _legacyPortfolioLessons, ...withoutLegacyLessons } = candidate;
  return (legacyEvidenceOmitted
    ? { ...withoutLegacyLessons, evidence: [] }
    : withoutLegacyLessons) as unknown as MathematicsPortfolio;
}

type MathematicsPromptSources = Readonly<{
  reusablePremises: readonly MathematicsReusablePremise[];
  lessonById: ReadonlyMap<string, MathLesson>;
}>;

type MathematicsPromptSourceAttempt = Readonly<{
  attempt: MathematicsAttempt;
  checkpoint: MathRecoveryCheckpoint;
}>;

const compareAttempts = (left: MathematicsPromptSourceAttempt, right: MathematicsPromptSourceAttempt): number =>
  right.checkpoint.updatedAt - left.checkpoint.updatedAt ||
  right.attempt.updatedAt - left.attempt.updatedAt ||
  right.attempt.createdAt - left.attempt.createdAt ||
  left.attempt.id.localeCompare(right.attempt.id);

const compareRankedPremises = (left: MathematicsRankedPremise, right: MathematicsRankedPremise): number =>
  right.relevanceScore - left.relevanceScore ||
  Number(left.requiresRecheck) - Number(right.requiresRecheck) ||
  left.premise.declarationName.localeCompare(right.premise.declarationName) ||
  left.attemptId.localeCompare(right.attemptId);

const compareAccessiblePremises = (
  left: MathematicsRankedAccessiblePremise,
  right: MathematicsRankedAccessiblePremise
): number =>
  right.relevanceScore - left.relevanceScore ||
  left.declarationName.localeCompare(right.declarationName) ||
  left.sourceModule.localeCompare(right.sourceModule);

const compareRankedLessons = (left: MathematicsRankedLesson, right: MathematicsRankedLesson): number =>
  right.relevanceScore - left.relevanceScore ||
  right.lesson.createdAt - left.lesson.createdAt ||
  left.lesson.lessonId.localeCompare(right.lesson.lessonId);

const deriveMathematicsPromptSources = (
  portfolio: MathematicsPortfolio,
  includeReusablePremises: boolean,
  includeLessons: boolean,
  problemId?: string
): MathematicsPromptSources => {
  const attempts: MathematicsPromptSourceAttempt[] = [];
  const lessonById = new Map<string, MathLesson>();
  let attemptsOrdered = true;
  for (const attempt of portfolio.attempts) {
    if (problemId !== undefined && attempt.problemId !== problemId) continue;
    if (includeLessons) {
      for (const value of attempt.lessons ?? []) {
        const lesson = normalizeMathLesson(value);
        const previous = lessonById.get(lesson.lessonId);
        if (!previous || lesson.createdAt > previous.createdAt) lessonById.set(lesson.lessonId, lesson);
      }
    }
    if (!includeReusablePremises || !attempt.recoveryCheckpoint?.ledger.semiProofCheckpoint) continue;
    const entry = { attempt, checkpoint: normalizeMathRecoveryCheckpoint(attempt.recoveryCheckpoint) };
    if (attempts.length > 0 && compareAttempts(attempts[attempts.length - 1], entry) > 0) attemptsOrdered = false;
    attempts.push(entry);
  }
  if (!includeReusablePremises || attempts.length === 0) {
    return { reusablePremises: Object.freeze([]), lessonById };
  }
  if (!attemptsOrdered) attempts.sort(compareAttempts);
  const problemById = new Map<string, MathematicsProblem>();
  for (const problem of portfolio.problems) problemById.set(problem.id, problem);
  const seen = new Set<string>();
  const reusable: MathematicsReusablePremise[] = [];
  for (const { attempt, checkpoint } of attempts) {
    const semiProof = checkpoint.ledger.semiProofCheckpoint!;
    const selectionCommit = problemById.get(attempt.problemId)?.routeSelection?.selectionCommit;
    for (const lemma of semiProof.verifiedLemmas) {
      const key = `${lemma.theoremName}\u0000${lemma.proofHash}`;
      if (seen.has(key)) continue;
      seen.add(key);
      const sourceCommit = semiProof.targetCommit;
      reusable.push(
        Object.freeze({
          problemId: attempt.problemId,
          attemptId: attempt.id,
          routeFingerprint: semiProof.routeFingerprint,
          planNodeId: lemma.planNodeId,
          sourceCommit,
          premise: mathVerifiedLemmaToPremiseCandidate(
            lemma,
            sourceCommit,
            `Reuse the kernel-verified ${lemma.theoremName} declaration for plan node ${lemma.planNodeId}.`
          ),
          requiresRecheck: selectionCommit !== sourceCommit,
        })
      );
      if (reusable.length >= 32) {
        return { reusablePremises: Object.freeze(reusable), lessonById };
      }
    }
  }
  return { reusablePremises: Object.freeze(reusable), lessonById };
};

export function deriveMathematicsReusablePremises(
  portfolio: MathematicsPortfolio
): readonly MathematicsReusablePremise[] {
  return deriveMathematicsPromptSources(portfolio, true, false).reusablePremises;
}

/** Select a small set of verified route mechanisms for discovery-time transfer. */
export function deriveMathematicsMechanismCapsules(
  portfolio: MathematicsPortfolio,
  input: Readonly<{
    problemId: string;
    routeFingerprint: string;
    query: readonly string[];
    limit?: number;
  }>
): readonly MathematicsMechanismCapsule[] {
  const queryTokens = symbolicMathTokens([input.routeFingerprint, ...input.query]);
  const mechanismCandidates: MathematicsMechanismCapsule[] = [];
  for (const sourceProblem of portfolio.problems) {
    if (sourceProblem.id === input.problemId || !sourceProblem.routeCards?.length) continue;
    for (const card of sourceProblem.routeCards) {
      const mechanismTokens = symbolicMathTokens([
        sourceProblem.title,
        sourceProblem.informalStatement,
        sourceProblem.researchContract?.objective ?? '',
        card.structuralCommitment,
        card.decisiveLemma,
        card.falsificationSignal,
      ]);
      const identifierOverlap = setIntersectionSize(queryTokens, mechanismTokens);
      let relevanceScore = Math.min(8, identifierOverlap);
      const matchReasons: string[] = identifierOverlap ? [`identifier_overlap:${identifierOverlap}`] : [];
      if (sourceProblem.routeSelection?.primaryFingerprint === card.routeFingerprint) {
        relevanceScore += 3;
        matchReasons.push('selected_route');
      }
      if (card.assessment?.probeOutcome === 'supported' || card.assessment?.probeOutcome === 'kernel_verified') {
        relevanceScore += 2;
        matchReasons.push('supported_route');
      }
      if (relevanceScore <= 0) continue;
      mechanismCandidates.push(
        Object.freeze({
          sourceProblemId: sourceProblem.id,
          sourceProblemTitle: sourceProblem.title,
          routeFingerprint: card.routeFingerprint,
          structuralCommitment: card.structuralCommitment,
          decisiveLemma: card.decisiveLemma,
          falsificationSignal: card.falsificationSignal,
          relevanceScore,
          matchReasons: Object.freeze(matchReasons),
        })
      );
    }
  }
  const limit = Number.isSafeInteger(input.limit)
    ? Math.max(0, Math.min(mechanismCandidates.length, Number(input.limit)))
    : 3;
  return Object.freeze(
    mechanismCandidates
      .toSorted(
        (left, right) =>
          right.relevanceScore - left.relevanceScore ||
          left.sourceProblemId.localeCompare(right.sourceProblemId) ||
          left.routeFingerprint.localeCompare(right.routeFingerprint)
      )
      .slice(0, limit)
  );
}

export function deriveMathematicsPromptPack(
  portfolio: MathematicsPortfolio,
  input: MathematicsPromptQuery,
  accessiblePremises: readonly MathematicsAccessiblePremise[] = [],
  upstreamPremises: readonly MathematicsUpstreamPremise[] = [],
  upstreamSearchAttempts: readonly MathematicsUpstreamSearchAttempt[] = [],
  upstreamPackages: readonly MathematicsUpstreamPackage[] = [],
  upstreamPackageSearchAttempts: readonly MathematicsUpstreamPackageSearchAttempt[] = [],
  installedPackagePremises: readonly MathematicsInstalledPackagePremise[] = [],
  installedPackageSearchAttempts: readonly MathematicsInstalledPackageSearchAttempt[] = [],
  upstreamSearchProvenance: readonly MathematicsUpstreamSearchProvenance[] = [],
  memoryScope: 'portfolio' | 'same_problem' = 'portfolio'
): MathematicsPromptPack {
  const problemId = boundedPromptText(input.problemId, 'promptQuery.problemId', 128);
  const routeFingerprint = normalizeMathRouteFingerprint(input.routeFingerprint);
  const queryMode = input.routeCoverage ? 'route_coverage' : 'node';
  const planNodeId = input.planNodeId ? boundedPromptText(input.planNodeId, 'promptQuery.planNodeId', 128) : undefined;
  const goal = input.goal ? boundedPromptText(input.goal, 'promptQuery.goal', 4000) : undefined;
  const failureKind = input.failureKind;
  if (
    failureKind !== undefined &&
    !['unknown_identifier', 'type_mismatch', 'instance_synthesis_failed', 'unsolved_goals', 'tactic_failed'].includes(
      failureKind
    )
  ) {
    throw new TypeError('Mathematics promptQuery.failureKind is invalid');
  }
  const failureDiagnostic = input.failureDiagnostic
    ? boundedPromptText(input.failureDiagnostic, 'promptQuery.failureDiagnostic', 4000)
    : undefined;
  if (queryMode === 'node' && (!planNodeId || !goal)) {
    throw new TypeError('Mathematics node promptQuery requires planNodeId and goal');
  }
  if (queryMode === 'route_coverage' && planNodeId) {
    throw new TypeError('Mathematics route-coverage promptQuery must not select one planNodeId');
  }
  const importModulesSet = new Set<string>();
  const importSet = new Set<string>();
  const importModulesValues: string[] = [];
  for (const value of input.importModules ?? []) {
    const moduleName = boundedPromptText(value, 'promptQuery.importModules', 256);
    if (importModulesSet.has(moduleName)) continue;
    importModulesSet.add(moduleName);
    importModulesValues.push(moduleName);
    importSet.add(moduleName.toLowerCase());
  }
  const importModules = Object.freeze(importModulesValues);
  const sourceFile = input.sourceFile ? boundedPromptText(input.sourceFile, 'promptQuery.sourceFile', 1024) : undefined;
  const upstreamQueryValues = MATHEMATICS_UPSTREAM_PREMISE_SOURCES.flatMap((source) => {
    const value = input.upstreamQueries?.[source];
    return value ? [boundedPromptText(value, `promptQuery.upstreamQueries.${source}`, 2000)] : [];
  });
  const packageQueryValues = (input.packageQueries ?? []).map((value, index) =>
    boundedPromptText(value, `promptQuery.packageQueries.${index}`, 256)
  );
  const installedPackageScopes = (input.installedPackageScopes ?? []).map((value, index) =>
    boundedPromptText(value, `promptQuery.installedPackageScopes.${index}`, 128)
  );
  const installedPackageQuery = input.installedPackageQuery
    ? boundedPromptText(input.installedPackageQuery, 'promptQuery.installedPackageQuery', 1000)
    : undefined;
  if (installedPackageQuery && installedPackageScopes.length === 0) {
    throw new TypeError('Mathematics installedPackageQuery requires installedPackageScopes');
  }
  const premiseLimit = boundedPromptLimit(input.premiseLimit, 4, 6, 'promptQuery.premiseLimit');
  const lessonLimit = boundedPromptLimit(input.lessonLimit, 2, 2, 'promptQuery.lessonLimit');
  const problem = portfolio.problems.find((candidate) => candidate.id === problemId);
  if (!problem) throw new TypeError(`Mathematics promptQuery problem ${problemId} is not in the portfolio`);
  const routeCard =
    queryMode === 'route_coverage'
      ? problem.routeCards?.find((candidate) => candidate.routeFingerprint === routeFingerprint)
      : undefined;
  if (queryMode === 'route_coverage' && !routeCard) {
    throw new TypeError(`Mathematics promptQuery route ${routeFingerprint} is not attached to problem ${problemId}`);
  }
  const routeNodeLimit = boundedPromptLimit(input.routeNodeLimit, 3, 4, 'promptQuery.routeNodeLimit');
  const premiseSchedule = routeCard ? mathPremiseRouteSchedule(routeCard) : undefined;
  const coverage = premiseSchedule?.coverage;
  const planNodeIds = Object.freeze(
    premiseSchedule ? premiseSchedule.gapNodeIds.slice(0, routeNodeLimit) : [planNodeId!]
  );
  const planNodeIdSet = new Set(planNodeIds);
  const targetNodes = routeCard?.planNodes.filter((node) => planNodeIdSet.has(node.id)) ?? [];
  const queryValues = [
    goal ?? '',
    planNodeId ?? '',
    routeFingerprint,
    problem.title,
    problem.informalStatement,
    problem.researchContract?.objective ?? '',
    problem.researchContract?.activeBottleneck ?? '',
    failureKind ?? '',
    failureDiagnostic ?? '',
  ];
  if (routeCard) {
    queryValues.push(routeCard.premiseBundle.strategySketch, routeCard.premiseBundle.leanSkeleton);
  }
  const targetNodeTokens = new Map<string, ReadonlySet<string>>();
  for (const node of targetNodes) {
    queryValues.push(node.id, node.informalClaim, node.provisionalLeanStatement);
    targetNodeTokens.set(node.id, symbolicMathTokens([node.id, node.informalClaim, node.provisionalLeanStatement]));
  }
  queryValues.push(
    ...importModules,
    sourceFile ?? '',
    ...upstreamQueryValues,
    ...packageQueryValues,
    ...installedPackageScopes,
    installedPackageQuery ?? ''
  );
  const queryTokens = symbolicMathTokens(queryValues);
  const promptSources = deriveMathematicsPromptSources(
    portfolio,
    !(queryMode === 'route_coverage' && planNodeIds.length === 0),
    true,
    memoryScope === 'same_problem' ? problemId : undefined
  );
  const scoredPremises = (
    queryMode === 'route_coverage' && planNodeIds.length === 0 ? [] : promptSources.reusablePremises
  ).map((candidate): MathematicsRankedPremise => {
    const matchReasons: string[] = [];
    let relevanceScore = 0;
    if (candidate.problemId === problemId) {
      relevanceScore += 3;
      matchReasons.push('same_problem');
    }
    if (candidate.routeFingerprint === routeFingerprint) {
      relevanceScore += 6;
      matchReasons.push('same_route');
    }
    if (planNodeIdSet.has(candidate.planNodeId)) {
      relevanceScore += 10;
      matchReasons.push('same_plan_node');
    }
    let moduleOverlap = 0;
    for (const moduleName of candidate.premise.importModules ?? []) {
      if (importSet.has(moduleName.toLowerCase())) moduleOverlap += 1;
    }
    if (moduleOverlap) {
      relevanceScore += Math.min(4, moduleOverlap * 2);
      matchReasons.push(`module_overlap:${moduleOverlap}`);
    }
    const premiseTokens = symbolicMathTokens([
      candidate.premise.declarationName,
      candidate.premise.declarationType,
      candidate.premise.intendedUse,
      ...(candidate.premise.importModules ?? []),
    ]);
    const identifierOverlap = setIntersectionSize(queryTokens, premiseTokens);
    if (identifierOverlap) {
      relevanceScore += Math.min(8, identifierOverlap);
      matchReasons.push(`identifier_overlap:${identifierOverlap}`);
    }
    const targetNodeMatches: Array<{ nodeId: string; overlap: number; exact: boolean }> = [];
    for (const node of targetNodes) {
      const overlap = setIntersectionSize(premiseTokens, targetNodeTokens.get(node.id)!);
      const exact = node.id === candidate.planNodeId;
      if (!exact && overlap === 0) continue;
      const match = { nodeId: node.id, overlap, exact };
      let insertionIndex = 0;
      while (insertionIndex < targetNodeMatches.length) {
        const current = targetNodeMatches[insertionIndex];
        const comparison =
          Number(current.exact) - Number(match.exact) ||
          current.overlap - match.overlap ||
          match.nodeId.localeCompare(current.nodeId);
        if (comparison < 0) break;
        insertionIndex += 1;
      }
      if (insertionIndex < 2) targetNodeMatches.splice(insertionIndex, 0, match);
      if (targetNodeMatches.length > 2) targetNodeMatches.pop();
    }
    const targetPlanNodeIds: string[] = [];
    for (const match of targetNodeMatches) targetPlanNodeIds.push(match.nodeId);
    if (queryMode === 'node' && targetPlanNodeIds.length === 0) targetPlanNodeIds.push(planNodeId!);
    if (candidate.requiresRecheck) {
      relevanceScore -= 2;
      matchReasons.push('requires_recheck');
    }
    return Object.freeze({
      ...candidate,
      relevanceScore,
      matchReasons: Object.freeze(matchReasons),
      targetPlanNodeIds: Object.freeze(targetPlanNodeIds),
    });
  });
  const rankedPremises: MathematicsRankedPremise[] = [];
  for (const premise of scoredPremises) {
    let insertionIndex = 0;
    while (
      insertionIndex < rankedPremises.length &&
      compareRankedPremises(premise, rankedPremises[insertionIndex]) >= 0
    ) {
      insertionIndex += 1;
    }
    if (insertionIndex < premiseLimit) rankedPremises.splice(insertionIndex, 0, premise);
    if (rankedPremises.length > premiseLimit) rankedPremises.pop();
  }
  const scoredAccessiblePremises = (
    queryMode === 'route_coverage' && planNodeIds.length === 0 ? [] : accessiblePremises
  ).map((candidate): MathematicsRankedAccessiblePremise => {
    const matchReasons: string[] = [];
    let relevanceScore = 0;
    const candidateModule = candidate.sourceModule.toLowerCase();
    if (importSet.has(candidateModule)) {
      relevanceScore += 5;
      matchReasons.push('imported_module');
    }
    if (sourceFile && candidate.sourceFile === sourceFile) {
      relevanceScore += 6;
      matchReasons.push('same_source_file');
    }
    const premiseTokens = symbolicMathTokens([
      candidate.declarationName,
      candidate.declarationType,
      candidate.sourceModule,
      candidate.sourceFile,
    ]);
    const identifierOverlap = setIntersectionSize(queryTokens, premiseTokens);
    if (identifierOverlap) {
      relevanceScore += Math.min(8, identifierOverlap);
      matchReasons.push(`identifier_overlap:${identifierOverlap}`);
    }
    const targetPlanNodeIds: string[] = [];
    for (const node of targetNodes) {
      const overlap = setIntersectionSize(premiseTokens, targetNodeTokens.get(node.id)!);
      if (overlap === 0) continue;
      relevanceScore += Math.min(4, overlap);
      targetPlanNodeIds.push(node.id);
    }
    if (queryMode === 'node' && targetPlanNodeIds.length === 0) targetPlanNodeIds.push(planNodeId!);
    return Object.freeze({
      ...candidate,
      relevanceScore,
      matchReasons: Object.freeze(matchReasons),
      targetPlanNodeIds: Object.freeze(targetPlanNodeIds.slice(0, 2)),
    });
  });
  const rankedAccessiblePremises: MathematicsRankedAccessiblePremise[] = [];
  for (const premise of scoredAccessiblePremises) {
    let insertionIndex = 0;
    while (
      insertionIndex < rankedAccessiblePremises.length &&
      compareAccessiblePremises(premise, rankedAccessiblePremises[insertionIndex]) >= 0
    ) {
      insertionIndex += 1;
    }
    if (insertionIndex < rankedAccessiblePremises.length || rankedAccessiblePremises.length < premiseLimit) {
      rankedAccessiblePremises.splice(insertionIndex, 0, premise);
    }
    if (rankedAccessiblePremises.length > premiseLimit) rankedAccessiblePremises.pop();
  }
  const scoredUpstreamPremises = (
    queryMode === 'route_coverage' && planNodeIds.length === 0 ? [] : upstreamPremises
  ).map((candidate): MathematicsRankedUpstreamPremise => {
    const matchReasons = [`upstream:${candidate.source}`, `provider_rank:${candidate.providerRank}`];
    let relevanceScore = Math.max(1, 5 - candidate.providerRank);
    if (candidate.sourceModule && importSet.has(candidate.sourceModule.toLowerCase())) {
      relevanceScore += 5;
      matchReasons.push('imported_module');
    }
    const premiseTokens = symbolicMathTokens([
      candidate.declarationName,
      candidate.declarationType,
      candidate.sourceModule ?? '',
    ]);
    const identifierOverlap = setIntersectionSize(queryTokens, premiseTokens);
    if (identifierOverlap) {
      relevanceScore += Math.min(8, identifierOverlap);
      matchReasons.push(`identifier_overlap:${identifierOverlap}`);
    }
    const targetPlanNodeIds: string[] = [];
    for (const node of targetNodes) {
      const overlap = setIntersectionSize(premiseTokens, targetNodeTokens.get(node.id)!);
      if (overlap === 0) continue;
      relevanceScore += Math.min(4, overlap);
      targetPlanNodeIds.push(node.id);
    }
    if (queryMode === 'node' && targetPlanNodeIds.length === 0) targetPlanNodeIds.push(planNodeId!);
    return Object.freeze({
      ...candidate,
      relevanceScore,
      matchReasons: Object.freeze(matchReasons),
      targetPlanNodeIds: Object.freeze(targetPlanNodeIds.slice(0, 2)),
    });
  });
  const scoredInstalledPackagePremises = (
    queryMode === 'route_coverage' && planNodeIds.length === 0 ? [] : installedPackagePremises
  ).map((candidate): MathematicsRankedInstalledPackagePremise => {
    const matchReasons = [
      `installed_package:${candidate.packageName}`,
      `provider_rank:${candidate.providerRank}`,
      'import_required',
    ];
    let relevanceScore = Math.max(3, 8 - candidate.providerRank);
    const premiseTokens = symbolicMathTokens([
      candidate.packageName,
      candidate.declarationName,
      candidate.declarationType,
      candidate.sourceModule,
    ]);
    const identifierOverlap = setIntersectionSize(queryTokens, premiseTokens);
    if (identifierOverlap) {
      relevanceScore += Math.min(10, identifierOverlap * 2);
      matchReasons.push(`identifier_overlap:${identifierOverlap}`);
    }
    const targetPlanNodeIds: string[] = [];
    for (const node of targetNodes) {
      const overlap = setIntersectionSize(premiseTokens, targetNodeTokens.get(node.id)!);
      if (overlap === 0) continue;
      relevanceScore += Math.min(4, overlap);
      targetPlanNodeIds.push(node.id);
    }
    if (queryMode === 'node' && targetPlanNodeIds.length === 0) targetPlanNodeIds.push(planNodeId!);
    return Object.freeze({
      ...candidate,
      relevanceScore,
      matchReasons: Object.freeze(matchReasons),
      targetPlanNodeIds: Object.freeze(targetPlanNodeIds.slice(0, 2)),
    });
  });
  const sortedSupplemental = [
    ...rankedAccessiblePremises.map((premise) => ({ kind: 'accessible' as const, premise })),
    ...scoredInstalledPackagePremises.map((premise) => ({ kind: 'installed' as const, premise })),
    ...scoredUpstreamPremises.map((premise) => ({ kind: 'upstream' as const, premise })),
  ].toSorted(
    (left, right) =>
      right.premise.relevanceScore - left.premise.relevanceScore ||
      (left.kind === 'accessible' ? 0 : left.kind === 'installed' ? 1 : 2) -
        (right.kind === 'accessible' ? 0 : right.kind === 'installed' ? 1 : 2) ||
      left.premise.declarationName.localeCompare(right.premise.declarationName)
  );
  // An explicit package or upstream lookup must remain observable even when
  // retained local premises already fill the compact shared budget.
  const reservedSupplemental =
    sortedSupplemental.find((candidate) => candidate.kind === 'installed') ??
    sortedSupplemental.find((candidate) => candidate.kind === 'upstream');
  const selectedRankedPremises = rankedPremises.slice(0, premiseLimit - Number(Boolean(reservedSupplemental)));
  const supplementalBudget = Math.max(0, premiseLimit - selectedRankedPremises.length);
  const selectedSupplemental = [
    ...(reservedSupplemental ? [reservedSupplemental] : []),
    ...sortedSupplemental.filter((candidate) => candidate !== reservedSupplemental),
  ].slice(0, supplementalBudget);
  const selectedAccessiblePremises = Object.freeze(
    selectedSupplemental.flatMap((candidate) => (candidate.kind === 'accessible' ? [candidate.premise] : []))
  );
  const selectedUpstreamPremises = Object.freeze(
    selectedSupplemental.flatMap((candidate) => (candidate.kind === 'upstream' ? [candidate.premise] : []))
  );
  const selectedInstalledPackagePremises = Object.freeze(
    selectedSupplemental.flatMap((candidate) => (candidate.kind === 'installed' ? [candidate.premise] : []))
  );
  // Scan and rank mechanism capsules once.  The omitted count used to trigger
  // a second full portfolio scan with an effectively unbounded limit.
  const allMechanismCapsules =
    memoryScope === 'same_problem'
      ? []
      : deriveMathematicsMechanismCapsules(portfolio, {
          problemId,
          routeFingerprint,
          query: queryValues,
          limit: Number.MAX_SAFE_INTEGER,
        });
  const mechanismCapsuleLimit = 3;
  const rankedMechanismCapsules = Object.freeze(allMechanismCapsules.slice(0, mechanismCapsuleLimit));
  const rankedLessonBuckets = new Map<string, MathematicsRankedLesson[]>();
  for (const lesson of promptSources.lessonById.values()) {
    const matchReasons: string[] = [];
    let relevanceScore = 0;
    if (problem.statementHash && lesson.statementHash === problem.statementHash) {
      relevanceScore += 6;
      matchReasons.push('same_statement');
    }
    if (lesson.routeFingerprint === routeFingerprint) {
      relevanceScore += 5;
      matchReasons.push('same_route');
    }
    const lessonTokens = symbolicMathTokens([
      lesson.trigger,
      lesson.failedPattern,
      lesson.rootCause,
      lesson.reusableRule,
    ]);
    const identifierOverlap = setIntersectionSize(queryTokens, lessonTokens);
    if (identifierOverlap) {
      relevanceScore += Math.min(6, identifierOverlap);
      matchReasons.push(`identifier_overlap:${identifierOverlap}`);
    }
    const ranked: MathematicsRankedLesson = Object.freeze({
      lesson,
      relevanceScore,
      matchReasons: Object.freeze(matchReasons),
    });
    const category = ranked.lesson.disposition === 'reuse' ? 'reuse' : 'avoid';
    const bucket = rankedLessonBuckets.get(category) ?? [];
    const insertionIndex = bucket.findIndex((candidate) => compareRankedLessons(ranked, candidate) < 0);
    if (insertionIndex >= 0) bucket.splice(insertionIndex, 0, ranked);
    else if (bucket.length < lessonLimit) bucket.push(ranked);
    if (bucket.length > lessonLimit) bucket.pop();
    rankedLessonBuckets.set(category, bucket);
  }
  const rankedLessons = [...rankedLessonBuckets.values()].flat().toSorted(compareRankedLessons);
  const selectedLessons = selectDiverseMathLessons(rankedLessons, lessonLimit);
  return Object.freeze({
    problemId,
    routeFingerprint,
    queryMode,
    ...(planNodeId ? { planNodeId } : {}),
    planNodeIds,
    ...(coverage ? { coverage } : {}),
    premises: Object.freeze(selectedRankedPremises),
    accessiblePremises: selectedAccessiblePremises,
    upstreamPremises: selectedUpstreamPremises,
    upstreamSearchAttempts: Object.freeze([...upstreamSearchAttempts]),
    upstreamSearchProvenance: Object.freeze([...upstreamSearchProvenance]),
    upstreamPackages: Object.freeze([...upstreamPackages]),
    upstreamPackageSearchAttempts: Object.freeze([...upstreamPackageSearchAttempts]),
    installedPackagePremises: selectedInstalledPackagePremises,
    installedPackageSearchAttempts: Object.freeze([...installedPackageSearchAttempts]),
    mechanismCapsules: Object.freeze(rankedMechanismCapsules),
    lessons: selectedLessons,
    omittedPremiseCount: Math.max(0, scoredPremises.length - selectedRankedPremises.length),
    omittedAccessiblePremiseCount: Math.max(0, scoredAccessiblePremises.length - selectedAccessiblePremises.length),
    omittedUpstreamPremiseCount: Math.max(0, scoredUpstreamPremises.length - selectedUpstreamPremises.length),
    omittedInstalledPackagePremiseCount: Math.max(
      0,
      scoredInstalledPackagePremises.length - selectedInstalledPackagePremises.length
    ),
    omittedMechanismCapsuleCount: Math.max(0, allMechanismCapsules.length - rankedMechanismCapsules.length),
    omittedLessonCount: Math.max(0, promptSources.lessonById.size - selectedLessons.length),
  });
}

function selectDiverseMathLessons(
  ranked: readonly MathematicsRankedLesson[],
  limit: number
): readonly MathematicsRankedLesson[] {
  const selected: MathematicsRankedLesson[] = [];
  const selectedSet = new Set<MathematicsRankedLesson>();
  const dispositions = new Set<string>();
  for (const candidate of ranked) {
    const category = candidate.lesson.disposition === 'reuse' ? 'reuse' : 'avoid';
    if (dispositions.has(category)) continue;
    selected.push(candidate);
    selectedSet.add(candidate);
    dispositions.add(category);
    if (selected.length >= limit) return Object.freeze(selected);
  }
  for (const candidate of ranked) {
    if (selectedSet.has(candidate)) continue;
    selected.push(candidate);
    selectedSet.add(candidate);
    if (selected.length >= limit) break;
  }
  return Object.freeze(selected);
}

const MATH_SYMBOLIC_STOP_TOKENS = new Set([
  'an',
  'and',
  'apply',
  'by',
  'exact',
  'for',
  'from',
  'goal',
  'have',
  'lemma',
  'of',
  'proof',
  'show',
  'that',
  'the',
  'theorem',
  'this',
  'to',
  'use',
  'using',
  'with',
]);

export function symbolicMathTokens(values: readonly string[]): ReadonlySet<string> {
  const tokens = new Set<string>();
  for (const value of values) {
    const normalized = value.normalize('NFC').replaceAll('<->', '↔').replaceAll('->', '→').replaceAll('<=', '≤').replaceAll('>=', '≥').replaceAll('!=', '≠');
    for (const [match] of normalized.matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_'.]*|\p{N}+|[\p{Sm}∈∉⊆⊂∪∩∀∃¬]/gu)) {
      const token = match.toLowerCase();
      for (const component of new Set([token, ...token.split('.'), ...token.split(/[._]/u)])) {
        if (component && component !== '_' && !MATH_SYMBOLIC_STOP_TOKENS.has(component)) tokens.add(component);
      }
    }
  }
  return tokens;
}

function setIntersectionSize(left: ReadonlySet<string>, right: ReadonlySet<string>): number {
  const values = left.size <= right.size ? left : right;
  const lookup = values === left ? right : left;
  let count = 0;
  for (const value of values) if (lookup.has(value)) count += 1;
  return count;
}

function boundedPromptText(value: unknown, field: string, maximumLength: number): string {
  if (typeof value !== 'string' || !value.trim()) throw new TypeError(`Mathematics ${field} is required`);
  const normalized = value.trim();
  if (normalized.length > maximumLength) {
    throw new TypeError(`Mathematics ${field} must contain at most ${maximumLength} characters`);
  }
  return normalized;
}

function boundedPromptLimit(value: unknown, fallback: number, maximum: number, field: string): number {
  const normalized = value === undefined ? fallback : Number(value);
  if (!Number.isSafeInteger(normalized) || normalized < 1 || normalized > maximum) {
    throw new TypeError(`Mathematics ${field} must be between 1 and ${maximum}`);
  }
  return normalized;
}

const MATHEMATICS_VERIFICATION_EVENT_KINDS = new Set<MathematicsVerificationEventKind>([
  'session.opened',
  'toolchain.resolved',
  'formula.submitted',
  'goal.opened',
  'goal.rewritten',
  'goal.branched',
  'goal.closed',
  'file.opened',
  'check.draft_checked',
  'diagnostic.emitted',
  'check.kernel_checked',
  'receipt.published',
  'session.closed',
]);

const isOptionalString = (value: unknown): boolean => value === undefined || typeof value === 'string';

const isFiniteNonNegativeNumber = (value: unknown): value is number =>
  typeof value === 'number' && Number.isFinite(value) && value >= 0;

const isGoalStatePayload = (value: Record<string, unknown>): boolean =>
  isNonEmptyString(value.stateId) &&
  typeof value.target === 'string' &&
  isStringArray(value.hypotheses) &&
  isOptionalString(value.theoremName);

const isMathematicsVerificationEventPayload = (
  kind: MathematicsVerificationEventKind,
  payload: Record<string, unknown>
): boolean => {
  if (kind === 'session.opened') {
    return (
      isNonEmptyString(payload.projectRoot) &&
      isFiniteNonNegativeNumber(payload.itemCount) &&
      isFiniteNonNegativeNumber(payload.uniqueFileCount)
    );
  }
  if (kind === 'toolchain.resolved') {
    return (
      (payload.command === 'lake' || payload.command === 'lean') &&
      isNonEmptyString(payload.executable) &&
      isOptionalString(payload.lakeFile) &&
      (payload.available === undefined || typeof payload.available === 'boolean')
    );
  }
  if (kind === 'formula.submitted') {
    return (
      isNonEmptyString(payload.formulaId) &&
      isNonEmptyString(payload.formula) &&
      payload.authority === 'agent' &&
      isOptionalString(payload.label) &&
      isOptionalString(payload.theoremName) &&
      isOptionalString(payload.sourcePath)
    );
  }
  if (kind === 'goal.opened') {
    return isGoalStatePayload(payload) && (payload.authority === 'agent' || payload.authority === 'lean-process');
  }
  if (kind === 'goal.rewritten') {
    return (
      isGoalStatePayload(payload) &&
      isNonEmptyString(payload.parentStateId) &&
      typeof payload.previousTarget === 'string' &&
      (payload.authority === 'agent' || payload.authority === 'lean-process')
    );
  }
  if (kind === 'goal.branched') {
    return (
      isGoalStatePayload(payload) &&
      isNonEmptyString(payload.parentStateId) &&
      isOptionalString(payload.branchLabel) &&
      (payload.authority === 'agent' || payload.authority === 'lean-process')
    );
  }
  if (kind === 'goal.closed') {
    return (
      isNonEmptyString(payload.stateId) &&
      isOptionalString(payload.parentStateId) &&
      isOptionalString(payload.target) &&
      isOptionalString(payload.theoremName) &&
      (payload.status === 'draft_closed' || payload.status === 'kernel_verified') &&
      (payload.authority === 'agent' || payload.authority === 'lean-kernel') &&
      (payload.status !== 'kernel_verified' || payload.authority === 'lean-kernel')
    );
  }
  if (kind === 'file.opened') {
    return (
      isNonEmptyString(payload.proofPath) &&
      isNonEmptyString(payload.proofHash) &&
      isFiniteNonNegativeNumber(payload.bytes) &&
      isFiniteNonNegativeNumber(payload.checkCount)
    );
  }
  if (kind === 'check.draft_checked') {
    return (
      isNonEmptyString(payload.proofPath) &&
      (payload.status === 'accepted' || payload.status === 'rejected') &&
      isFiniteNonNegativeNumber(payload.sorryCount) &&
      isFiniteNonNegativeNumber(payload.admitCount) &&
      isStringArray(payload.axioms)
    );
  }
  if (kind === 'diagnostic.emitted') {
    return (
      ['git', 'safety', 'process', 'stdout', 'stderr', 'agent'].includes(String(payload.source)) &&
      ['info', 'warning', 'error'].includes(String(payload.severity)) &&
      isNonEmptyString(payload.message) &&
      isOptionalString(payload.proofPath) &&
      isOptionalString(payload.stateId)
    );
  }
  if (kind === 'check.kernel_checked') {
    return (
      isNonEmptyString(payload.proofPath) &&
      ['pending', 'kernel_verified', 'failed', 'blocked', 'unavailable'].includes(String(payload.status)) &&
      (payload.exitCode === null || (typeof payload.exitCode === 'number' && Number.isInteger(payload.exitCode))) &&
      (payload.signal === null || typeof payload.signal === 'string') &&
      typeof payload.timedOut === 'boolean' &&
      typeof payload.aborted === 'boolean' &&
      isFiniteNonNegativeNumber(payload.durationMs)
    );
  }
  if (kind === 'receipt.published') {
    return (
      isNonEmptyString(payload.receiptId) &&
      isNonEmptyString(payload.checkId) &&
      isNonEmptyString(payload.proofPath) &&
      isOptionalString(payload.theoremName) &&
      ['pending', 'kernel_verified', 'failed', 'blocked', 'unavailable'].includes(String(payload.status))
    );
  }
  return (
    ['pending', 'kernel_verified', 'failed', 'blocked', 'unavailable'].includes(String(payload.status)) &&
    isFiniteNonNegativeNumber(payload.resultCount) &&
    isFiniteNonNegativeNumber(payload.durationMs)
  );
};

const isMathematicsVerificationEvent = (value: unknown): value is MathematicsVerificationEvent => {
  if (
    !isRecord(value) ||
    value.schema !== MATHEMATICS_VERIFICATION_EVENT_SCHEMA ||
    !isNonEmptyString(value.eventId) ||
    !isNonEmptyString(value.sessionId) ||
    !isFiniteNonNegativeNumber(value.timestamp) ||
    typeof value.kind !== 'string' ||
    !MATHEMATICS_VERIFICATION_EVENT_KINDS.has(value.kind as MathematicsVerificationEventKind) ||
    !isRecord(value.payload)
  ) {
    return false;
  }
  return isMathematicsVerificationEventPayload(value.kind as MathematicsVerificationEventKind, value.payload);
};

const isMathematicsVerificationCapability = (value: unknown): value is MathematicsVerificationCapability =>
  isRecord(value) &&
  typeof value.available === 'boolean' &&
  (value.command === undefined || value.command === 'lake' || value.command === 'lean') &&
  isOptionalString(value.executable) &&
  isOptionalString(value.version) &&
  isOptionalString(value.reason) &&
  (value.sandboxBackends === undefined ||
    (Array.isArray(value.sandboxBackends) &&
      value.sandboxBackends.every(
        (backend) => backend === 'unshare' || backend === 'bwrap' || backend === 'docker' || backend === 'podman'
      ))) &&
  value.batchCertification === true &&
  typeof value.liveGoals === 'boolean' &&
  typeof value.persistentSession === 'boolean';

export function readMathematicsVerificationTrace(value: unknown): MathematicsVerificationTrace | undefined {
  if (!isRecord(value)) return undefined;
  const candidate = isRecord(value.verificationTrace) ? value.verificationTrace : value;
  if (
    candidate.schema !== MATHEMATICS_VERIFICATION_TRACE_SCHEMA ||
    candidate.version !== 1 ||
    (candidate.runIdentity !== undefined &&
      (typeof candidate.runIdentity !== 'string' || !/^[a-f0-9]{64}$/u.test(candidate.runIdentity))) ||
    typeof candidate.updatedAt !== 'number' ||
    !Number.isFinite(candidate.updatedAt) ||
    !Array.isArray(candidate.events)
  ) {
    return undefined;
  }
  const events: MathematicsVerificationEvent[] = [];
  const retainedEventStart = Math.max(0, candidate.events.length - 2_000);
  for (let index = 0; index < candidate.events.length; index += 1) {
    const event = candidate.events[index];
    if (!isMathematicsVerificationEvent(event)) return undefined;
    if (index >= retainedEventStart) events.push(event);
  }
  if (candidate.capability !== undefined && !isMathematicsVerificationCapability(candidate.capability)) {
    return undefined;
  }
  const capability = candidate.capability as MathematicsVerificationCapability | undefined;
  return {
    schema: MATHEMATICS_VERIFICATION_TRACE_SCHEMA,
    version: 1,
    updatedAt: candidate.updatedAt,
    ...(typeof candidate.runIdentity === 'string' ? { runIdentity: candidate.runIdentity } : {}),
    ...(capability ? { capability } : {}),
    events,
  };
}

const summarizeMathematicsEvidenceInto = (
  portfolio: Pick<MathematicsPortfolio, 'evidence'>,
  problemId?: string,
  statementHash?: string
): MathematicsEvidenceSummary => {
  const supporting: MathematicsEvidence[] = [];
  const refuting: MathematicsEvidence[] = [];
  const context: MathematicsEvidence[] = [];
  const exactStatementSupporting: MathematicsEvidence[] = [];
  const exactStatementRefuting: MathematicsEvidence[] = [];
  const evidenceIds = new Set<string>();
  let qualifiedSupporting = 0;
  let reproducibleRefuting = 0;
  for (const item of Array.isArray(portfolio.evidence) ? portfolio.evidence : []) {
    if (isStringArray(item.evidenceIds)) for (const evidenceId of item.evidenceIds) evidenceIds.add(evidenceId);
    if (problemId && item.problemId !== problemId) continue;
    if (item.polarity === 'supporting') {
      supporting.push(item);
      if (!statementHash || item.statementHash === statementHash) {
        exactStatementSupporting.push(item);
        if (isQualifiedSupportingEvidence(item)) qualifiedSupporting += 1;
      }
    } else if (item.polarity === 'refuting') {
      refuting.push(item);
      if (!statementHash || item.statementHash === statementHash) {
        exactStatementRefuting.push(item);
        if (isReproducibleRefutingEvidence(item)) reproducibleRefuting += 1;
      }
    } else {
      context.push(item);
    }
  }
  return {
    problemId,
    statementHash,
    supporting,
    refuting,
    context,
    exactStatementSupporting,
    exactStatementRefuting,
    counts: {
      total: supporting.length + refuting.length + context.length,
      supporting: supporting.length,
      refuting: refuting.length,
      context: context.length,
      exactStatementSupporting: exactStatementSupporting.length,
      exactStatementRefuting: exactStatementRefuting.length,
      qualifiedSupporting,
      reproducibleRefuting,
    },
    evidenceIds,
  };
};

const hasLinkedScienceEvidence = (item: MathematicsEvidence): boolean =>
  item.evidenceIds.length > 0 && isNonEmptyString(item.commit) && item.commit !== 'WORKTREE';

const isQualifiedSupportingEvidence = (item: MathematicsEvidence): boolean =>
  item.polarity === 'supporting' &&
  ['supporting', 'formal'].includes(item.strength) &&
  ['reproduced', 'independent', 'formal'].includes(item.reproducibility) &&
  hasLinkedScienceEvidence(item);

const isReproducibleRefutingEvidence = (item: MathematicsEvidence): boolean =>
  item.polarity === 'refuting' &&
  ['refuting', 'formal'].includes(item.strength) &&
  ['reproduced', 'independent', 'formal'].includes(item.reproducibility) &&
  hasLinkedScienceEvidence(item);

/**
 * Computes the evidence gates without mutating the portfolio. The server can
 * use this result before accepting a terminal `verified` or `refuted` state,
 * while the renderer can use the same result to explain what is missing.
 */
export function getMathematicsTerminalGateReadiness(
  portfolio: MathematicsPortfolio,
  problemId?: string,
  options: {
    problem?: MathematicsPortfolio['problems'][number];
    evidenceSummary?: MathematicsEvidenceSummary;
    evidenceByProblem?: ReadonlyMap<string, MathematicsPortfolio['evidence'][number][]>;
    evidenceIds?: ReadonlySet<string>;
    reviewById?: ReadonlyMap<string, MathematicsPortfolio['reviews'][number]>;
    reviewsById?: ReadonlyMap<string, MathematicsPortfolio['reviews'][number][]>;
    verificationsById?: ReadonlyMap<string, MathematicsPortfolio['verifications'][number][]>;
    verifiedOfficialReceiptIds?: ReadonlySet<string>;
  } = {}
): MathematicsTerminalGateReadiness {
  const targetProblemId = problemId || portfolio.activeProblemId;
  const problem =
    options.problem?.id === targetProblemId
      ? options.problem
      : portfolio.problems.find((item) => item.id === targetProblemId);
  const statementHash = problem?.statementHash;
  const suppliedEvidenceSummary = options.evidenceSummary;
  const reusableEvidenceSummary =
    suppliedEvidenceSummary &&
    suppliedEvidenceSummary.problemId === problem?.id &&
    suppliedEvidenceSummary.statementHash === statementHash
      ? suppliedEvidenceSummary
      : undefined;
  const indexedEvidence = reusableEvidenceSummary
    ? undefined
    : problem?.id && options.evidenceByProblem?.get(problem.id);
  const evidenceSummary =
    reusableEvidenceSummary ??
    summarizeMathematicsEvidenceInto(
      indexedEvidence ? { evidence: indexedEvidence } : portfolio,
      indexedEvidence ? undefined : problem?.id,
      statementHash
    );
  const evidenceIdSet = options.evidenceIds ?? evidenceSummary.evidenceIds;
  const exactRefuting = evidenceSummary.exactStatementRefuting;
  const exactRefutingIds = new Set<string>();
  for (const item of exactRefuting) {
    if (!isReproducibleRefutingEvidence(item)) continue;
    if (problem && statementHash) {
      for (const evidenceId of item.evidenceIds) exactRefutingIds.add(evidenceId);
    }
  }
  const recordedEvidence = evidenceSummary.counts;
  const hasFormalSupportingEvidence = evidenceSummary.exactStatementSupporting.some(
    (item) => isQualifiedSupportingEvidence(item) && item.strength === 'formal' && item.reproducibility === 'formal'
  );
  const hasFormalRefutingEvidence = evidenceSummary.exactStatementRefuting.some(
    (item) => isReproducibleRefutingEvidence(item) && item.strength === 'formal' && item.reproducibility === 'formal'
  );
  let reviewById = options.reviewById;
  let reviewsById = options.reviewsById;
  const indexCandidateReviews = Boolean(problem?.reviewIds?.length) && !reviewById;
  const indexLegacyReviews = !problem?.reviewIds?.length && Boolean(problem?.reviewId) && !reviewsById;
  if (indexCandidateReviews || indexLegacyReviews) {
    const indexedReviewById = indexCandidateReviews ? new Map<string, MathematicsReview>() : undefined;
    const indexedReviewsById = indexLegacyReviews ? new Map<string, MathematicsReview[]>() : undefined;
    for (const review of portfolio.reviews) {
      if (indexedReviewById && !indexedReviewById.has(review.id)) indexedReviewById.set(review.id, review);
      if (indexedReviewsById) {
        const reviews = indexedReviewsById.get(review.id);
        if (reviews) reviews.push(review);
        else indexedReviewsById.set(review.id, [review]);
      }
    }
    reviewById ??= indexedReviewById;
    reviewsById ??= indexedReviewsById;
  }
  const verifyMissing: string[] = [];
  const refuteMissing: string[] = [];

  if (!problem) {
    verifyMissing.push('an active problem');
    refuteMissing.push('an active problem');
  }
  if (!statementHash) {
    verifyMissing.push('an exact statementHash');
    refuteMissing.push('an exact statementHash');
  }
  const matchingVerificationTargetCommits = new Set<string>();
  let matchingVerificationCount = 0;
  let matchingNegationVerification: MathematicsVerification | undefined;
  if (problem) {
    const verificationCandidates =
      problem.verificationId && options.verificationsById
        ? (options.verificationsById.get(problem.verificationId) ?? [])
        : portfolio.verifications;
    for (const item of verificationCandidates) {
      if (
        item.id !== problem.verificationId ||
        item.problemId !== problem.id ||
        item.status !== 'kernel_verified' ||
        item.targetCommit === 'WORKTREE' ||
        !statementHash ||
        item.statementHash !== statementHash ||
        item.goalsRemaining !== 0 ||
        item.sorryCount !== 0 ||
        item.admitCount !== 0 ||
        item.axioms.length !== 0
      ) {
        continue;
      }
      if (item.claim === 'negation') {
        if (!matchingNegationVerification) matchingNegationVerification = item;
      } else {
        matchingVerificationCount += 1;
        matchingVerificationTargetCommits.add(item.targetCommit);
      }
    }
  }
  const hasKernelVerification = matchingVerificationCount > 0;
  if (!hasKernelVerification) verifyMissing.push('matching Lean kernel verification');

  const candidateReviews: MathCandidateReview[] = [];
  for (const reviewId of problem?.reviewIds ?? []) {
    const candidateReview = reviewById?.get(reviewId)?.candidateReview;
    if (candidateReview) candidateReviews.push(candidateReview);
  }
  let teamReviewGate: ReturnType<typeof aggregateMathCandidateReviews> | undefined;
  let hasPassedReview = false;
  if (problem?.reviewIds?.length) {
    try {
      teamReviewGate = aggregateMathCandidateReviews(candidateReviews);
      hasPassedReview =
        teamReviewGate.canAdvance &&
        teamReviewGate.problemId === problem.id &&
        teamReviewGate.statementHash === statementHash &&
        matchingVerificationTargetCommits.has(teamReviewGate.targetCommit);
    } catch {
      hasPassedReview = false;
    }
  } else {
    const matchingReviews = problem?.reviewId ? reviewsById?.get(problem.reviewId) : undefined;
    hasPassedReview = Boolean(
      problem &&
      problem.reviewId &&
      matchingReviews?.some(
        (item) =>
          item.problemId === problem.id &&
          item.status === 'passed' &&
          item.verdict === 'passed' &&
          Boolean(statementHash) &&
          item.statementHash === statementHash &&
          matchingVerificationTargetCommits.has(item.targetCommit)
      )
    );
  }
  if (!hasPassedReview) verifyMissing.push('passed independent review for the same commit');

  // A terminal Team verification must never silently downgrade to a local
  // kernel check when the caller omits its immutable contract.
  const requiresOfficialGate = problem?.status === 'verified' || Boolean(problem?.problemContract);
  let hasOfficialVerification = !requiresOfficialGate;
  if (problem?.problemContract && problem.localGateReceipt && problem.officialGateReceipt && teamReviewGate) {
    try {
      const contract = normalizeMathProblemContract(problem.problemContract);
      const localReceipt = normalizeMathLocalGateReceipt(problem.localGateReceipt);
      const officialReceipt = normalizeMathOfficialGateReceipt(problem.officialGateReceipt);
      hasOfficialVerification =
        Boolean(options.verifiedOfficialReceiptIds?.has(officialReceipt.receiptId)) &&
        (localReceipt.claim || 'statement') === 'statement' &&
        (officialReceipt.claim || 'statement') === 'statement' &&
        officialReceipt.statementHash === statementHash &&
        officialReceipt.statementHash === contract.statementHash &&
        officialReceipt.targetCommit === localReceipt.targetCommit &&
        officialReceipt.routeFingerprint === localReceipt.routeFingerprint &&
        officialReceipt.localGateReceiptId === localReceipt.receiptId &&
        officialReceipt.theoremName === localReceipt.theoremName &&
        officialReceipt.proofHash === localReceipt.proofHash &&
        officialReceipt.theoremDeclarationHash === localReceipt.theoremDeclarationHash &&
        officialReceipt.command === contract.officialVerificationCommand &&
        (officialReceipt.sourceDeclarationHash === undefined ||
          officialReceipt.sourceDeclarationHash === localReceipt.sourceDeclarationHash) &&
        officialReceipt.problemId === contract.problemId &&
        officialReceipt.officialManifestId === contract.officialManifestId &&
        officialReceipt.officialManifestHash === contract.officialManifestHash &&
        officialReceipt.leanStatementHash === contract.leanStatementHash &&
        teamReviewGate.canAdvance &&
        teamReviewGate.localGateReceiptId === localReceipt.receiptId &&
        teamReviewGate.targetCommit === officialReceipt.targetCommit &&
        matchingVerificationTargetCommits.has(officialReceipt.targetCommit);
    } catch {
      hasOfficialVerification = false;
    }
  }
  if (!hasOfficialVerification) verifyMissing.push('matching official comparator receipt for the reviewed commit');

  const listedExampleIds = new Set(problem?.exampleIds ?? []);
  const hasReproducibleCounterexample = Boolean(
    problem &&
    portfolio.examples.some((example) => {
      const listed = listedExampleIds.has(example.id);
      const witnessEvidence = example.evidenceIds.every((id) => evidenceIdSet.has(id));
      return (
        example.problemId === problem.id &&
        example.kind === 'counterexample' &&
        listed &&
        witnessEvidence &&
        isNonEmptyString(example.observed) &&
        isNonEmptyString(example.scope) &&
        isNonEmptyString(example.replayCommand) &&
        example.evidenceIds.some((id) => exactRefutingIds.has(id))
      );
    })
  );
  let hasFormalRefutation = false;
  if (
    problem?.problemContract &&
    matchingNegationVerification &&
    problem.localGateReceipt &&
    problem.officialGateReceipt
  ) {
    try {
      const contract = normalizeMathProblemContract(problem.problemContract);
      const localReceipt = normalizeMathLocalGateReceipt(problem.localGateReceipt);
      const officialReceipt = normalizeMathOfficialGateReceipt(problem.officialGateReceipt);
      hasFormalRefutation =
        Boolean(contract.formalNegationStatement && contract.leanNegationHash) &&
        Boolean(options.verifiedOfficialReceiptIds?.has(officialReceipt.receiptId)) &&
        localReceipt.claim === 'negation' &&
        officialReceipt.claim === 'negation' &&
        localReceipt.receiptId === matchingNegationVerification.id &&
        localReceipt.targetCommit === matchingNegationVerification.targetCommit &&
        localReceipt.statementHash === statementHash &&
        localReceipt.leanStatementHash === contract.leanNegationHash &&
        officialReceipt.localGateReceiptId === localReceipt.receiptId &&
        officialReceipt.targetCommit === localReceipt.targetCommit &&
        officialReceipt.theoremName === localReceipt.theoremName &&
        officialReceipt.proofHash === localReceipt.proofHash &&
        officialReceipt.theoremDeclarationHash === localReceipt.theoremDeclarationHash &&
        (officialReceipt.sourceDeclarationHash === undefined ||
          officialReceipt.sourceDeclarationHash === localReceipt.sourceDeclarationHash) &&
        officialReceipt.statementHash === statementHash &&
        officialReceipt.problemId === problem.id &&
        officialReceipt.officialManifestId === contract.officialManifestId &&
        officialReceipt.officialManifestHash === contract.officialManifestHash &&
        officialReceipt.leanStatementHash === contract.leanNegationHash;
    } catch {
      hasFormalRefutation = false;
    }
  }
  if (!hasFormalRefutation) {
    refuteMissing.push('a contract-bound Lean negation with a verified official comparator receipt');
  }
  const evidence: MathematicsEvidenceCounts = {
    ...recordedEvidence,
    qualifiedSupporting: Math.max(recordedEvidence.qualifiedSupporting, hasKernelVerification ? 1 : 0),
    reproducibleRefuting: Math.max(recordedEvidence.reproducibleRefuting, hasFormalRefutation ? 1 : 0),
  };
  const hasConflictingEvidence =
    (hasFormalSupportingEvidence || hasKernelVerification) && (hasFormalRefutingEvidence || hasFormalRefutation);
  if (evidence.qualifiedSupporting === 0) verifyMissing.push('exact-statement supporting evidence');
  if (evidence.reproducibleRefuting === 0) refuteMissing.push('reproducible exact-statement refuting evidence');
  if (recordedEvidence.reproducibleRefuting > 0) {
    verifyMissing.push('resolve reproducible refuting evidence for the exact statement');
  }
  if (hasConflictingEvidence) {
    const conflictMessage = 'resolve conflicting supporting and refuting evidence for the exact statement';
    verifyMissing.push(conflictMessage);
    refuteMissing.push(conflictMessage);
  }

  let decision: MathematicsEvidenceDecision;
  if (hasConflictingEvidence) {
    decision = {
      disposition: 'inconclusive',
      basis: 'conflicting_evidence',
      reason: 'conflicting_evidence',
    };
  } else if (problem?.status === 'verified' && verifyMissing.length === 0) {
    decision = {
      disposition: 'verified',
      basis: 'supporting_evidence',
      reason: 'verified_by_supporting_evidence',
    };
  } else if (problem?.status === 'refuted' && refuteMissing.length === 0) {
    decision = {
      disposition: 'refuted',
      basis: 'refuting_evidence',
      reason: 'refuted_by_formal_negation',
    };
  } else if (evidence.exactStatementSupporting > 0) {
    decision = {
      disposition: 'inconclusive',
      basis: 'supporting_evidence',
      reason: 'supporting_evidence_not_verified',
    };
  } else if (evidence.exactStatementRefuting > 0) {
    decision = {
      disposition: 'inconclusive',
      basis: 'refuting_evidence',
      reason: 'refuting_evidence_not_decisive',
    };
  } else {
    decision = {
      disposition: 'inconclusive',
      basis: 'insufficient_evidence',
      reason: 'insufficient_evidence',
    };
  }

  return {
    problemId: problem?.id,
    statementHash,
    evidence,
    decision,
    hasKernelVerification,
    hasPassedReview,
    hasOfficialVerification,
    hasReproducibleCounterexample,
    hasFormalRefutation,
    hasConflictingEvidence,
    canVerify: verifyMissing.length === 0,
    canRefute: refuteMissing.length === 0,
    verifyMissing,
    refuteMissing,
  };
}

export function buildInitialMathematicsPortfolio(input: {
  title: string;
  projectRoot?: string;
  updatedAt: number;
  nextActionLabel: string;
}): MathematicsPortfolio {
  return {
    schema: MATHEMATICS_PORTFOLIO_SCHEMA,
    version: 1,
    title: input.title,
    stage: 'intake',
    status: 'planning',
    updatedAt: input.updatedAt,
    projectRoot: input.projectRoot,
    problems: [],
    attempts: [],
    examples: [],
    evidence: [],
    verifications: [],
    reviews: [],
    blockers: [],
    nextActions: [
      {
        id: 'understand-problem',
        label: input.nextActionLabel,
        kind: 'search',
        priority: 'now',
        owner: 'agent',
      },
    ],
  };
}

export function buildMathematicsConversationExtra(projectRoot?: string): MathematicsConversationExtra {
  return {
    enabled: true,
    mode: MATHEMATICS_MODE_ID,
    schema: MATHEMATICS_PORTFOLIO_SCHEMA,
    projectRoot,
    defaultSkill: MATHEMATICS_SKILL_NAME,
  };
}
