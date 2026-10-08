/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  buildFinancialFactorConversationExtra as buildSharedFinancialFactorConversationExtra,
  buildFinancialFactorModePrompt as buildSharedFinancialFactorModePrompt,
  FINANCIAL_FACTOR_PROMPT_CONTRACT_VERSION as SHARED_FINANCIAL_FACTOR_PROMPT_CONTRACT_VERSION,
} from "../../contracts/index";

export const FINANCIAL_FACTOR_MODE_ID = 'financial_factor';
export const FINANCIAL_FACTOR_SKILL_NAME = 'financial-factor-discovery';
export const FINANCIAL_FACTOR_REFERENCE_SKILL_NAME = 'wq-alpha-research';
export const FINANCIAL_FACTOR_DISCOVERY_SKILL_NAME = 'financial-factor-discovery';
export const FINANCIAL_FACTOR_MINING_PLUGIN_ID = 'financial-factor-mining' as const;
export const FINANCIAL_FACTOR_PROMPT_CONTRACT_VERSION = SHARED_FINANCIAL_FACTOR_PROMPT_CONTRACT_VERSION;
export const FINANCIAL_FACTOR_SKILL_PATH = 'resources/skills/financial-factor-discovery/SKILL.md';
export const FINANCIAL_FACTOR_PORTFOLIO_SCHEMA = 'deepscientist.financial_factor.portfolio.v1' as const;
export const FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID = 'financial_factor_portfolio' as const;
export const LEGACY_FINANCIAL_FACTOR_PORTFOLIO_SCHEMA = 'deepscientist.factor_portfolio.v1' as const;
export const FINANCIAL_FACTOR_PORTFOLIO_PATH = 'factor-research/portfolio.json' as const;
/** The single writer for the lightweight XAlpha-style factor handoff. */
export const FINANCIAL_FACTOR_SUBMISSION_SCHEMA = 'deepscientist.financial_factor.submission.v1' as const;
export const FINANCIAL_FACTOR_SUBMISSION_ARTIFACT_ID = 'financial_factor_submission' as const;
export const FINANCIAL_FACTOR_SUBMISSION_PATH = 'factor-research/submissions.json' as const;
export const FINANCIAL_FACTOR_PROTOCOL_SCHEMA = 'deepscientist.financial_factor.protocol.v1' as const;
export const FINANCIAL_FACTOR_EVALUATION_SCHEMA = 'deepscientist.financial_factor.evaluation.v1' as const;
export const FINANCIAL_FACTOR_POOL_SCHEMA = 'deepscientist.financial_factor.pool.v1' as const;
export const FINANCIAL_FACTOR_CAMPAIGN_SCHEMA = 'deepscientist.financial_factor.campaign.v1' as const;
export const FINANCIAL_FACTOR_TRANSITION_SCHEMA = 'deepscientist.financial_factor.transition.v1' as const;
export const FINANCIAL_FACTOR_VALIDATION_SCHEMA = 'deepscientist.financial_factor.validation.v1' as const;
export const FINANCIAL_FACTOR_PROTOCOL_DIRECTORY = 'factor-research/protocols' as const;
export const FINANCIAL_FACTOR_EVALUATION_DIRECTORY = 'factor-research/runs' as const;
export const FINANCIAL_FACTOR_POOL_DIRECTORY = 'factor-research/pools' as const;
export const FINANCIAL_FACTOR_CAMPAIGN_DIRECTORY = 'factor-research/campaigns' as const;
export const FINANCIAL_FACTOR_TRAJECTORY_DIRECTORY = 'factor-research/trajectories' as const;
export const FINANCIAL_FACTOR_VALIDATION_DIRECTORY = 'factor-research/validations' as const;
export const FINANCIAL_FACTOR_TIMESERIES_SCHEMA = 'deepscientist.financial_factor.timeseries.v1' as const;
export const FINANCIAL_FACTOR_TIMESERIES_DIRECTORY = 'factor-research/factors' as const;

export type FinancialFactorExecutionMode = 'manual' | 'continuous';
export type FinancialFactorAutomationPolicy = 'verify_only' | 'submit_qualified';
export type FinancialFactorStage =
  | 'scope'
  | 'ideation'
  | 'linting'
  | 'simulation'
  | 'screening'
  | 'registration'
  | 'submission'
  | 'complete';
export type FinancialFactorPortfolioStatus = 'planning' | 'running' | 'needs_decision' | 'blocked' | 'complete';
export type FinancialFactorStatus =
  | 'idea'
  | 'linted'
  | 'simulated'
  | 'qualified'
  | 'submit_pending'
  | 'active'
  | 'hold'
  | 'rejected'
  | 'failed';
export type FinancialFactorLifecycle =
  | 'research'
  | 'qualified'
  | 'shadow'
  | 'paper'
  | 'production'
  | 'suspended'
  | 'retired';
export type FinancialFactorSubmissionStatus =
  | 'not_submitted'
  | 'queued'
  | 'submitted'
  | 'verifying'
  | 'active'
  | 'rejected'
  | 'failed';

export interface FinancialFactorSubmission {
  status: FinancialFactorSubmissionStatus;
  platform?: string;
  externalId?: string;
  submittedAt?: number;
  verifiedAt?: number;
  receiptHash?: string;
  lastError?: string;
  nextRetryAt?: number;
  updatedAt: number;
}

export type FinancialFactorResearchSubmissionStatus = 'complete' | 'partial' | 'blocked';

export interface FinancialFactorResearchSubmissionRole {
  id: string;
  label: string;
  kind: 'xalpha' | 'generic';
  lane?: string;
  status: 'planned' | 'running' | 'completed' | 'blocked';
  summary?: string;
  branch?: string;
  worktreePath?: string;
  headCommit?: string;
}

export interface FinancialFactorResearchSubmissionMetric {
  name: string;
  value?: number;
  unit?: string;
  basis?: 'measured' | 'literature' | 'estimated' | 'pending';
}

const measuredFinancialFactorMetric = (
  name: string,
  value: number | undefined,
  unit?: string
): FinancialFactorResearchSubmissionMetric[] =>
  value == null || !Number.isFinite(value) ? [] : [{ name, value, ...(unit ? { unit } : {}), basis: 'measured' }];

export type FinancialFactorEvaluationEvidenceStatus = 'attested' | 'recorded' | 'missing';

export interface FinancialFactorResearchEvaluationRef {
  evaluationId: string;
  factorId?: string;
  protocolId?: string;
  datasetSnapshotId?: string;
  datasetContentSha256?: string;
  status: FinancialFactorEvaluationEvidenceStatus;
  resultHash?: string;
  receiptId?: string;
  warnings: string[];
}

export interface FinancialFactorResearchSubmissionArtifact {
  id: string;
  label: string;
  kind: 'chart' | 'table' | 'code' | 'data' | 'report' | 'other';
  path?: string;
  artifactId?: string;
  artifactVersion?: number;
}

export interface FinancialFactorResearchSubmission {
  schema: typeof FINANCIAL_FACTOR_SUBMISSION_SCHEMA;
  version: 1;
  submissionId: string;
  title: string;
  objective: string;
  status: FinancialFactorResearchSubmissionStatus;
  asOf?: string;
  factor?: {
    id?: string;
    name?: string;
    expression?: string;
    hypothesis?: string;
  };
  evaluationId?: string;
  evaluation?: FinancialFactorResearchEvaluationRef;
  roles: FinancialFactorResearchSubmissionRole[];
  metrics: FinancialFactorResearchSubmissionMetric[];
  artifacts: FinancialFactorResearchSubmissionArtifact[];
  limitations: string[];
  nextActions: string[];
  sourceRefs: string[];
  createdAt: number;
  updatedAt: number;
}

export interface FinancialFactorEvaluationProtocol {
  schema: typeof FINANCIAL_FACTOR_PROTOCOL_SCHEMA;
  version: 1;
  protocolId: string;
  title: string;
  objective: string;
  source: 'system' | 'agent' | 'user';
  status: 'draft' | 'frozen';
  dataset: {
    datasetId: string;
    snapshotId: string;
    backend: 'table' | 'qlib' | 'external';
    sourcePath?: string;
    contentSha256?: string;
  };
  columns: {
    date: string;
    asset: string;
    factor: string;
    futureReturn: string;
    industry?: string;
    size?: string;
    availableAt?: string;
  };
  splits: Array<{
    id: string;
    role: 'development' | 'validation' | 'feedback' | 'locked_test';
    start: string;
    end: string;
    sourcePath?: string;
    contentSha256?: string;
  }>;
  evaluation: {
    frequency: string;
    quantiles: number;
    annualizationFactor: number;
    minimumCoverage: number;
    costBps: number;
  };
  pool?: FinancialFactorPoolPolicy;
  metrics: string[];
  createdAt: number;
  frozenAt?: number;
}

export interface FinancialFactorPoolPolicy {
  maxFactors: number;
  maximumCorrelation: number;
  maxPerFamily: number;
  stabilityFolds: number;
  minimumPositiveFolds: number;
  /** Omitted by legacy protocols. New protocols require a strictly greater development-pool gain. */
  minimumMarginalDevelopmentGain?: number;
  /** Omitted by legacy protocols. Counts folds where adding the candidate improves the incumbent pool. */
  minimumMarginalPositiveFolds?: number;
  /** Omitted by legacy protocols. Compares the best single factor with forward-selected pool prefixes. */
  selectPoolSizeOnValidation?: boolean;
  ridgeLambdas: number[];
  embargoTradingDays: number;
  splitPurgeTradingDays: number;
  selectionRankIcWeight: number;
  selectionIcWeight: number;
}

export interface FinancialFactorPoolCandidateSpec {
  id: string;
  name: string;
  column: string;
  expression: string;
  family: string;
  hypothesis?: string;
  complexity?: number;
  semanticAlignment?: {
    status: 'passed' | 'warning' | 'failed';
    rationale?: string;
  };
}

export interface FinancialFactorPoolCandidateStatistics {
  direction: -1 | 1;
  coverage: number;
  meanIc: number;
  rankIc: number;
  selectionScore: number;
  icir?: number;
  worstFoldIc: number;
  positiveFoldCount: number;
  foldIcs: number[];
}

export type FinancialFactorPoolExclusionReason =
  | 'duplicate_expression'
  | 'insufficient_coverage'
  | 'unstable_direction'
  | 'family_limit'
  | 'correlated_signal'
  | 'insufficient_marginal_gain'
  | 'unstable_marginal_gain'
  | 'validation_pool_limit'
  | 'factor_limit';

export interface FinancialFactorPoolCandidateDecision {
  candidate: FinancialFactorPoolCandidateSpec;
  statistics: FinancialFactorPoolCandidateStatistics;
  selected: boolean;
  selectionOrder?: number;
  exclusionReason?: FinancialFactorPoolExclusionReason;
  duplicateOf?: string;
  maximumSelectedCorrelation?: number;
  incumbentDevelopmentIc?: number;
  candidatePoolDevelopmentIc?: number;
  marginalDevelopmentGain?: number;
  marginalDevelopmentFoldGains?: number[];
  positiveMarginalFoldCount?: number;
}

export interface FinancialFactorPoolRidgeScore {
  lambda: number;
  factorCount?: number;
  meanIc: number;
  worstFoldIc: number;
  foldIcs: number[];
}

export interface FinancialFactorPoolModel {
  schema: typeof FINANCIAL_FACTOR_POOL_SCHEMA;
  version: 1;
  poolId: string;
  name: string;
  runId: string;
  protocolId: string;
  datasetSnapshotId: string;
  datasetContentSha256: string;
  inputPath: string;
  developmentSplitId: string;
  validationSplitId: string;
  lambdaSelectionSplitId: string;
  weightFitSplitIds: string[];
  policy: FinancialFactorPoolPolicy;
  candidateDecisions: FinancialFactorPoolCandidateDecision[];
  selectedFactors: Array<{
    candidate: FinancialFactorPoolCandidateSpec;
    statistics: FinancialFactorPoolCandidateStatistics;
    weight: number;
  }>;
  ridge: {
    lambda: number;
    factorCount?: number;
    scores: FinancialFactorPoolRidgeScore[];
  };
  calibration: {
    metrics: FinancialFactorResearchSubmissionMetric[];
    checks: FinancialFactorCheck[];
    warnings: string[];
  };
  fitBoundary: {
    developmentStart: string;
    developmentEnd: string;
    validationStart: string;
    validationEnd: string;
    developmentLastFitDate: string;
    validationLastFitDate: string;
    splitPurgeTradingDays: number;
    lockedTestUsed: false;
  };
  fitRequestHash: string;
  modelHash: string;
  receiptId?: string;
  receiptPath?: string;
  createdAt: number;
}

export type FinancialFactorResearchTransitionKind = 'NEW' | 'IMPROVE' | 'COMBINE' | 'PIVOT' | 'STOP';
export type FinancialFactorResearchAssessment = 'positive' | 'mixed' | 'negative' | 'terminal';

export const FINANCIAL_FACTOR_SEARCH_WEAKNESS_AXES = [
  'predictiveness',
  'stability',
  'coverage',
  'turnover',
  'novelty',
  'economic_logic',
] as const;

export type FinancialFactorSearchWeaknessAxis = (typeof FINANCIAL_FACTOR_SEARCH_WEAKNESS_AXES)[number];

export interface FinancialFactorSearchWeakness {
  axis: FinancialFactorSearchWeaknessAxis;
  severity: 1 | 2 | 3;
  evidenceId: string;
  summary: string;
}

export interface FinancialFactorResearchContext {
  mechanismId: string;
  operation: FinancialFactorEvolutionOperation;
  hypothesisCard: FinancialFactorHypothesisCard;
  edit: {
    motif: string;
    changedComponents: string[];
    rationale: string;
    expectedEffect: string;
  };
  weaknesses: FinancialFactorSearchWeakness[];
}

export interface FinancialFactorEditMemory {
  key: string;
  motif: string;
  operation: FinancialFactorEvolutionOperation;
  parentMechanismFamilies: string[];
  attempts: number;
  positive: number;
  mixed: number;
  negative: number;
  frontierImprovements: number;
  confidence: 'low' | 'medium' | 'high';
  disposition: 'prefer' | 'avoid' | 'uncertain';
  candidateIds: string[];
}

export interface FinancialFactorMechanismMemory {
  mechanismId: string;
  mechanismFamily: string;
  hypothesis: string;
  attempts: number;
  positive: number;
  mixed: number;
  negative: number;
  frontierImprovements: number;
  candidateIds: string[];
  weaknessAxes: FinancialFactorSearchWeaknessAxis[];
}

export interface FinancialFactorParentSuggestion {
  candidateId: string;
  mechanismId?: string;
  mechanismFamily: string;
  score: number;
  assessment: Exclude<FinancialFactorResearchAssessment, 'terminal'>;
  childCount: number;
  ancestryCandidateIds: string[];
  attemptedEditMotifs: string[];
  reasonCodes: Array<
    'quality' | 'frontier_gain' | 'underexplored_family' | 'low_reuse' | 'repairable_gap' | 'lineage_uncertainty'
  >;
}

export interface FinancialFactorCrossoverSuggestion {
  candidateIds: [string, string];
  mechanismFamilies: [string, string];
  score: number;
  reason: string;
}

export interface FinancialFactorSearchGuidance {
  evidenceScope: 'development_only' | 'feedback_only';
  policy: {
    minimumMemoryObservations: 2;
    preferPositiveRate: 0.67;
    avoidNegativeRate: 0.75;
    maximumParentSuggestions: 3;
  };
  status: 'active' | 'stopped';
  recommendedTransition: {
    kind: FinancialFactorResearchTransitionKind;
    candidateIds: string[];
    reason: string;
  };
  parentSuggestions: FinancialFactorParentSuggestion[];
  crossoverSuggestions: FinancialFactorCrossoverSuggestion[];
  editMemory: FinancialFactorEditMemory[];
  mechanismMemory: FinancialFactorMechanismMemory[];
  avoidedEditMotifs: string[];
  underexploredMechanismFamilies: string[];
  legacyUnstructuredTransitionCount: number;
}

export interface FinancialFactorResearchCampaign {
  schema: typeof FINANCIAL_FACTOR_CAMPAIGN_SCHEMA;
  version: 1;
  campaignId: string;
  runId: string;
  protocolId: string;
  /** @deprecated Legacy campaigns used development directly as search feedback. */
  developmentSplitId?: string;
  feedbackSplitId?: string;
  objective: string;
  baseCommit: string;
  candidateBudget: number;
  maxConcurrency: number;
  mechanismFamilies?: string[];
  createdAt: number;
}

export interface FinancialFactorResearchTransition {
  schema: typeof FINANCIAL_FACTOR_TRANSITION_SCHEMA;
  version: 1;
  transitionId: string;
  campaignId: string;
  runId: string;
  protocolId: string;
  sequence: number;
  kind: FinancialFactorResearchTransitionKind;
  candidateId?: string;
  parentCandidateIds: string[];
  mechanismFamily?: string;
  researchContext?: FinancialFactorResearchContext;
  assessment: FinancialFactorResearchAssessment;
  summary: string;
  /** @deprecated Legacy transitions used development directly as search feedback. */
  developmentSplitId?: string;
  feedbackSplitId?: string;
  executionsUsed: number;
  remainingBudget: number;
  frontierImproved: boolean;
  sourceDelivery?: {
    branch: string;
    headCommit: string;
    agentId?: string;
    taskId?: string;
  };
  evidenceIds: string[];
  requestHash: string;
  createdAt: number;
}

export interface FinancialFactorValidationCandidateResult {
  candidate: FinancialFactorPoolCandidateSpec;
  evaluationId: string;
  status: 'succeeded' | 'partial' | 'failed';
  lineage: {
    transitionId: string;
    sequence: number;
    kind: Exclude<FinancialFactorResearchTransitionKind, 'STOP'>;
    assessment: Exclude<FinancialFactorResearchAssessment, 'negative' | 'terminal'>;
    parentCandidateIds: string[];
    mechanismFamily: string;
    researchContext?: FinancialFactorResearchContext;
    sourceDelivery: NonNullable<FinancialFactorResearchTransition['sourceDelivery']>;
    /** @deprecated Present only for validation bundles created from legacy development-feedback campaigns. */
    developmentEvidenceIds?: string[];
    feedbackEvidenceIds?: string[];
  };
  metrics: FinancialFactorResearchSubmissionMetric[];
  checks: FinancialFactorCheck[];
  warnings: string[];
  timeSeries?: FinancialFactorTimeSeries;
  error?: string;
}

export interface FinancialFactorValidationBundle {
  schema: typeof FINANCIAL_FACTOR_VALIDATION_SCHEMA;
  version: 1;
  validationId: string;
  campaignId: string;
  runId: string;
  protocolId: string;
  splitId: string;
  searchClosed: true;
  datasetSnapshotId: string;
  datasetContentSha256: string;
  inputPath: string;
  trajectoryHash: string;
  requestHash: string;
  resultHash: string;
  candidates: FinancialFactorValidationCandidateResult[];
  receiptId?: string;
  receiptPath?: string;
  createdAt: number;
}

export interface FinancialFactorEvaluationRow {
  date: string;
  asset: string;
  factorValue?: number;
  futureReturn?: number;
  industry?: string;
  size?: number;
  availableAt?: string;
}

export interface FinancialFactorEvaluationRecord {
  schema: typeof FINANCIAL_FACTOR_EVALUATION_SCHEMA;
  version: 1;
  evaluationId: string;
  runId: string;
  factor: {
    id: string;
    name: string;
    expression?: string;
    hypothesis?: string;
  };
  pool?: {
    poolId: string;
    modelHash: string;
    selectedFactorIds: string[];
    weights: number[];
  };
  protocolId: string;
  datasetSnapshotId: string;
  /** Hash of the exact local table evaluated, even when the protocol only named a logical snapshot. */
  datasetContentSha256?: string;
  splitId: string;
  status: 'succeeded' | 'partial' | 'failed';
  evidenceStatus: Exclude<FinancialFactorEvaluationEvidenceStatus, 'missing'>;
  inputPath: string;
  resultPath: string;
  seriesPath?: string;
  resultHash: string;
  receiptId?: string;
  receiptPath?: string;
  metrics: FinancialFactorResearchSubmissionMetric[];
  checks: FinancialFactorCheck[];
  warnings: string[];
  timeSeries?: FinancialFactorTimeSeries;
  generatedAt: number;
}

export interface FinancialFactorEvaluationSummary {
  metrics: FinancialFactorResearchSubmissionMetric[];
  checks: FinancialFactorCheck[];
  warnings: string[];
  timeSeries?: FinancialFactorTimeSeries;
}

export interface FinancialFactorResearchSubmissionBundle {
  schema: typeof FINANCIAL_FACTOR_SUBMISSION_SCHEMA;
  version: 1;
  updatedAt: number;
  submissions: FinancialFactorResearchSubmission[];
}

export interface FinancialFactorMetricContext {
  contractId: string;
  evaluationId: string;
  dataset?: string;
  sampleStart?: string;
  sampleEnd?: string;
  costModel?: string;
  baselineCommit?: string;
  evaluationCode?: FinancialFactorEvaluationCode;
}

export type FinancialFactorEvaluationRuntime = 'python' | 'node' | 'r' | 'notebook';

export interface FinancialFactorEvaluationCode {
  /** Project-relative source path. Absolute paths and parent traversal are invalid. */
  path: string;
  runtime?: FinancialFactorEvaluationRuntime;
  entrypoint?: string;
  sha256?: string;
}

export interface FinancialFactorMetric {
  name: string;
  value: number;
  unit?: string;
  direction?: 'maximize' | 'minimize';
  evidenceIds: string[];
}

export interface FinancialFactorCheck {
  id: string;
  label: string;
  status: 'passed' | 'warning' | 'failed' | 'not_run';
  value?: number | string;
  threshold?: number | string;
  detail?: string;
  evidenceIds?: string[];
}

export interface FinancialFactorHypothesisCard {
  mechanism: string;
  expectedSign: string;
  expectedHorizon: string;
  requiredData: string;
  failureCondition: string;
  knownAnalogs?: string[];
}

export const FINANCIAL_FACTOR_EVOLUTION_OPERATIONS = [
  'seed',
  'mutation',
  'crossover',
  'refinement',
  'repair',
  'novelty',
] as const;

export type FinancialFactorEvolutionOperation = (typeof FINANCIAL_FACTOR_EVOLUTION_OPERATIONS)[number];

export interface FinancialFactorLineage {
  parentFactorIds: string[];
  operation: FinancialFactorEvolutionOperation;
  generation?: number;
  cycleId?: string;
  mechanismIds?: string[];
  archetypeIds?: string[];
  mutationSummary?: string;
  memoryRefs?: string[];
}

export const FINANCIAL_FACTOR_PROMOTION_CHECK_IDS = [
  'hypothesis_consistency',
  'static_integrity',
  'prefix_invariance',
  'walk_forward_stability',
  'cost_after_turnover',
  'portfolio_redundancy',
  'portfolio_marginal_value',
  'frozen_oos',
  // Point-in-time availability is a promotion gate, not an informational
  // warning.  A factor without row-level as-of evidence must remain blocked.
  'future_leakage_audit',
] as const;

export type FinancialFactorPromotionCheckId = (typeof FINANCIAL_FACTOR_PROMOTION_CHECK_IDS)[number];

export interface FinancialFactorPromotionAssessment {
  status: 'eligible' | 'not_ready' | 'blocked';
  eligible: boolean;
  hypothesisCardComplete: boolean;
  passedCount: number;
  requiredCount: number;
  missingCheckIds: FinancialFactorPromotionCheckId[];
  blockingCheckIds: FinancialFactorPromotionCheckId[];
  missingEvidenceCheckIds: FinancialFactorPromotionCheckId[];
}

export interface FinancialFactorPromotionMutationIssue {
  factorId: string;
  code: 'promotion_contract_incomplete';
  message: string;
  assessment: FinancialFactorPromotionAssessment;
}

export interface FinancialFactorSettings {
  market?: string;
  region?: string;
  universe?: string;
  delay?: number;
  frequency?: string;
  holdingPeriod?: string;
  neutralization?: string;
  truncation?: number;
  decay?: number;
  nanHandling?: string;
}

export interface FinancialFactorArtifactRef {
  artifactId: string;
  artifactVersion?: number;
  role: 'table' | 'figure' | 'dataset' | 'code' | 'log' | 'report' | 'timeseries' | 'notebook' | 'other';
  label?: string;
  path?: string;
  runId?: string;
  generatedAt?: number;
  evidenceIds?: string[];
}

export type FinancialFactorSeriesKind =
  | 'cumulative_pnl'
  | 'benchmark'
  | 'rank_ic'
  | 'drawdown'
  | 'turnover'
  | 'exposure'
  | 'coverage'
  | 'other';

export type FinancialFactorPeriodKind = 'is' | 'oos' | 'shadow' | 'live' | 'other';

export interface FinancialFactorTimeSeriesItem {
  id: string;
  label: string;
  kind: FinancialFactorSeriesKind;
  unit?: string;
  points: Array<[timestamp: string, value: number]>;
}

export interface FinancialFactorTimeSeriesPeriod {
  kind: FinancialFactorPeriodKind;
  label?: string;
  start: string;
  end: string;
}

export interface FinancialFactorNotebookSummary {
  path: string;
  title: string;
  kernel?: string;
  codeCellCount: number;
  executedCellCount: number;
  failedCellCount: number;
  generatedAt: number;
}

export interface FinancialFactorTimeSeries {
  schema: typeof FINANCIAL_FACTOR_TIMESERIES_SCHEMA;
  version: 1;
  factorId: string;
  runId: string;
  contractId: string;
  evaluationId: string;
  frequency: string;
  generatedAt: number;
  periods?: FinancialFactorTimeSeriesPeriod[];
  series: FinancialFactorTimeSeriesItem[];
  notebook?: FinancialFactorNotebookSummary;
}

export type FinancialFactorChartSeriesSummary = {
  id: string;
  label: string;
  unit?: string;
  pointCount: number;
  startAt: string;
  endAt: string;
  startValue: number;
  latestValue: number;
  change: number;
  minimum: number;
  maximum: number;
};

export type FinancialFactorChartOverview = {
  startAt?: string;
  endAt?: string;
  pointCount: number;
  seriesCount: number;
  series: FinancialFactorChartSeriesSummary[];
};

export type FinancialFactorDerivedMetricKey =
  | 'period_change'
  | 'max_drawdown'
  | 'mean_rank_ic'
  | 'average_turnover'
  | 'minimum_coverage'
  | 'maximum_pe';

export type FinancialFactorDerivedMetric = {
  key: FinancialFactorDerivedMetricKey;
  value: number;
  unit?: string;
  sourceSeriesId: string;
};

export type FinancialFactorTimeAxisGranularity = 'day' | 'month' | 'year';

export type FinancialFactorTimeAxis = {
  granularity: FinancialFactorTimeAxisGranularity;
  minInterval?: number;
  pointCount: number;
  dense: boolean;
  startAt?: string;
  endAt?: string;
};

const DAY_MS = 24 * 60 * 60 * 1_000;
const YEAR_MS = 365.25 * DAY_MS;

export const buildFinancialFactorTimeAxis = (
  series: FinancialFactorTimeSeriesItem[],
  frequency?: string
): FinancialFactorTimeAxis => {
  const timestamps = series
    .flatMap((item) => item.points.map(([timestamp]) => Date.parse(timestamp)))
    .filter(Number.isFinite);
  const start = timestamps.length ? Math.min(...timestamps) : undefined;
  const end = timestamps.length ? Math.max(...timestamps) : undefined;
  const span = start != null && end != null ? end - start : 0;
  const normalizedFrequency = (frequency || '').trim().toLowerCase();
  const minInterval = normalizedFrequency.includes('year')
    ? 365 * DAY_MS
    : normalizedFrequency.includes('quarter')
      ? 84 * DAY_MS
      : normalizedFrequency.includes('month')
        ? 28 * DAY_MS
        : normalizedFrequency.includes('week')
          ? 7 * DAY_MS
          : normalizedFrequency.includes('day') || normalizedFrequency === 'daily'
            ? DAY_MS
            : undefined;
  const pointCount = Math.max(0, ...series.map((item) => item.points.length));
  return {
    granularity: span >= 3 * YEAR_MS ? 'year' : span >= 120 * DAY_MS ? 'month' : 'day',
    minInterval,
    pointCount,
    dense: pointCount >= 800,
    startAt: start != null ? new Date(start).toISOString() : undefined,
    endAt: end != null ? new Date(end).toISOString() : undefined,
  };
};

export const FINANCIAL_FACTOR_RESEARCH_PHASE_IDS = ['memory', 'route', 'evolve', 'validate', 'consolidate'] as const;

export type FinancialFactorResearchPhaseId = (typeof FINANCIAL_FACTOR_RESEARCH_PHASE_IDS)[number];
export type FinancialFactorResearchPhaseStatus = 'complete' | 'current' | 'upcoming';

export type FinancialFactorResearchPhase = {
  id: FinancialFactorResearchPhaseId;
  status: FinancialFactorResearchPhaseStatus;
};

const RESEARCH_PHASE_BY_STAGE: Record<FinancialFactorStage, number> = {
  scope: 0,
  ideation: 1,
  linting: 2,
  simulation: 2,
  screening: 3,
  registration: 3,
  submission: 4,
  complete: 4,
};

/** Visible XAlpha loop derived from the canonical Portfolio stage. */
export const buildFinancialFactorResearchLoop = (
  stage: FinancialFactorStage,
  portfolioStatus?: FinancialFactorPortfolioStatus
): FinancialFactorResearchPhase[] => {
  const currentIndex = RESEARCH_PHASE_BY_STAGE[stage];
  const campaignComplete = stage === 'complete' || portfolioStatus === 'complete';
  return FINANCIAL_FACTOR_RESEARCH_PHASE_IDS.map((id, index) => ({
    id,
    status: campaignComplete || index < currentIndex ? 'complete' : index === currentIndex ? 'current' : 'upcoming',
  }));
};

export const buildFinancialFactorChartOverview = (
  series: FinancialFactorTimeSeriesItem[]
): FinancialFactorChartOverview => {
  const summaries = series.flatMap((item): FinancialFactorChartSeriesSummary[] => {
    if (!item.points.length) return [];
    const first = item.points[0];
    const last = item.points[item.points.length - 1];
    let minimum = first[1];
    let maximum = first[1];
    item.points.forEach(([, value]) => {
      minimum = Math.min(minimum, value);
      maximum = Math.max(maximum, value);
    });
    return [
      {
        id: item.id,
        label: item.label,
        unit: item.unit,
        pointCount: item.points.length,
        startAt: first[0],
        endAt: last[0],
        startValue: first[1],
        latestValue: last[1],
        change: last[1] - first[1],
        minimum,
        maximum,
      },
    ];
  });
  const starts = summaries.map((item) => Date.parse(item.startAt)).filter(Number.isFinite);
  const ends = summaries.map((item) => Date.parse(item.endAt)).filter(Number.isFinite);
  return {
    startAt: starts.length ? new Date(Math.min(...starts)).toISOString() : undefined,
    endAt: ends.length ? new Date(Math.max(...ends)).toISOString() : undefined,
    pointCount: Math.max(0, ...summaries.map((item) => item.pointCount)),
    seriesCount: summaries.length,
    series: summaries,
  };
};

const meanSeriesValue = (series: FinancialFactorTimeSeriesItem): number =>
  series.points.reduce((total, [, value]) => total + value, 0) / series.points.length;

const maximumDrawdownFromCumulativeSeries = (series: FinancialFactorTimeSeriesItem): number | undefined => {
  if (!series.points.length) return undefined;
  const percentUnit = (series.unit || '').trim().toLowerCase().includes('percent');
  const scale = percentUnit ? 100 : 1;
  let peak = Number.NEGATIVE_INFINITY;
  let maximumDrawdown = 0;
  for (const [, cumulativeValue] of series.points) {
    const wealth = 1 + cumulativeValue / scale;
    if (!Number.isFinite(wealth) || wealth <= 0) return undefined;
    peak = Math.max(peak, wealth);
    maximumDrawdown = Math.min(maximumDrawdown, wealth / peak - 1);
  }
  return percentUnit ? maximumDrawdown * 100 : maximumDrawdown;
};

const isPriceEarningsSeries = (series: FinancialFactorTimeSeriesItem): boolean =>
  series.kind === 'other' &&
  /(?:^|\b)(?:p\/?e|pe|price[\s_-]*earnings)(?:\b|$)|市盈率/iu.test(`${series.id} ${series.label}`);

/**
 * Derive compact, reviewable metrics only from submitted series values. The
 * function never fills unavailable metrics with zero and never queries a data
 * provider, so the factor workspace can render the same result offline.
 */
export const deriveFinancialFactorTimeSeriesMetrics = (
  data: FinancialFactorTimeSeries
): FinancialFactorDerivedMetric[] => {
  const metrics: FinancialFactorDerivedMetric[] = [];
  const cumulative = data.series.find((series) => series.kind === 'cumulative_pnl');
  const explicitDrawdown = data.series.find((series) => series.kind === 'drawdown');
  const rankIc = data.series.find((series) => series.kind === 'rank_ic');
  const turnover = data.series.find((series) => series.kind === 'turnover');
  const coverage = data.series.find((series) => series.kind === 'coverage');
  const priceEarnings = data.series.find(isPriceEarningsSeries);

  if (cumulative?.points.length) {
    const first = cumulative.points[0][1];
    const last = cumulative.points[cumulative.points.length - 1][1];
    metrics.push({
      key: 'period_change',
      value: last - first,
      unit: cumulative.unit,
      sourceSeriesId: cumulative.id,
    });
  }

  if (explicitDrawdown?.points.length) {
    const values = explicitDrawdown.points.map(([, value]) => value);
    metrics.push({
      key: 'max_drawdown',
      value: values.some((value) => value < 0) ? Math.min(...values) : Math.max(...values),
      unit: explicitDrawdown.unit,
      sourceSeriesId: explicitDrawdown.id,
    });
  } else if (cumulative) {
    const value = maximumDrawdownFromCumulativeSeries(cumulative);
    if (value != null) {
      metrics.push({
        key: 'max_drawdown',
        value,
        unit: cumulative.unit,
        sourceSeriesId: cumulative.id,
      });
    }
  }

  if (rankIc?.points.length) {
    metrics.push({
      key: 'mean_rank_ic',
      value: meanSeriesValue(rankIc),
      unit: rankIc.unit,
      sourceSeriesId: rankIc.id,
    });
  }
  if (turnover?.points.length) {
    metrics.push({
      key: 'average_turnover',
      value: meanSeriesValue(turnover),
      unit: turnover.unit,
      sourceSeriesId: turnover.id,
    });
  }
  if (coverage?.points.length) {
    metrics.push({
      key: 'minimum_coverage',
      value: Math.min(...coverage.points.map(([, value]) => value)),
      unit: coverage.unit,
      sourceSeriesId: coverage.id,
    });
  }
  if (priceEarnings?.points.length) {
    metrics.push({
      key: 'maximum_pe',
      value: Math.max(...priceEarnings.points.map(([, value]) => value)),
      unit: priceEarnings.unit,
      sourceSeriesId: priceEarnings.id,
    });
  }

  return metrics;
};

export interface FinancialFactorCandidate {
  id: string;
  name: string;
  expression: string;
  family?: string;
  hypothesis: string;
  hypothesisCard?: FinancialFactorHypothesisCard;
  lineage?: FinancialFactorLineage;
  selectionReason: string;
  decisionReason: string;
  status: FinancialFactorStatus;
  settings?: FinancialFactorSettings;
  metrics?: FinancialFactorMetric[];
  metricContext?: FinancialFactorMetricContext;
  checks: FinancialFactorCheck[];
  evidenceIds: string[];
  artifacts?: FinancialFactorArtifactRef[];
  lifecycle?: FinancialFactorLifecycle;
  submission?: FinancialFactorSubmission;
  /** @deprecated Read-only compatibility fields. New writers should use submission. */
  externalId?: string;
  /** @deprecated Read-only compatibility fields. New writers should use submission. */
  externalStatus?: string;
  /** @deprecated Read-only compatibility fields. New writers should use submission. */
  verifiedAt?: number;
  updatedAt: number;
}

export type FinancialFactorLineageIssueCode = 'missing_parent' | 'self_parent' | 'cycle' | 'generation_order';

export interface FinancialFactorLineageIssue {
  code: FinancialFactorLineageIssueCode;
  factorId: string;
  parentFactorId?: string;
}

export interface FinancialFactorLineageNode {
  factorId: string;
  parentFactorIds: string[];
  childFactorIds: string[];
  missingParentFactorIds: string[];
  generation: number;
  operation: FinancialFactorEvolutionOperation;
}

export interface FinancialFactorLineageEdge {
  id: string;
  sourceFactorId: string;
  targetFactorId: string;
}

export interface FinancialFactorLineageGraph {
  nodes: FinancialFactorLineageNode[];
  edges: FinancialFactorLineageEdge[];
  issues: FinancialFactorLineageIssue[];
  maxGeneration: number;
}

export interface FinancialFactorBatch {
  id: string;
  label: string;
  status: 'planned' | 'running' | 'completed' | 'blocked' | 'cancelled';
  factorIds: string[];
  objective?: string;
  decisionReason?: string;
  startedAt?: number;
  updatedAt: number;
}

export interface FinancialFactorAction {
  id: string;
  label: string;
  kind: 'research' | 'verification' | 'decision' | 'submission';
  priority: 'now' | 'next' | 'later';
  owner?: 'agent' | 'user';
}

export interface FinancialFactorPortfolio {
  schema: typeof FINANCIAL_FACTOR_PORTFOLIO_SCHEMA;
  version: 1;
  title: string;
  stage: FinancialFactorStage;
  status: FinancialFactorPortfolioStatus;
  updatedAt: number;
  context: {
    objective: string;
    projectRoot?: string;
    executionMode: FinancialFactorExecutionMode;
    automationPolicy: FinancialFactorAutomationPolicy;
    market?: string;
    region?: string;
    universe?: string;
    delay?: number;
    dataFamilies?: string[];
  };
  batches: FinancialFactorBatch[];
  factors: FinancialFactorCandidate[];
  blockers: string[];
  nextActions: FinancialFactorAction[];
}

/**
 * Derives the visible ancestry graph from the canonical Portfolio. The graph is
 * deliberately not persisted: factor records remain the only lineage truth.
 */
export function buildFinancialFactorLineageGraph(
  factors: readonly Pick<FinancialFactorCandidate, 'id' | 'lineage'>[]
): FinancialFactorLineageGraph {
  const factorById = new Map(factors.map((factor) => [factor.id, factor]));
  const childIds = new Map<string, string[]>();
  const edges: FinancialFactorLineageEdge[] = [];
  const issues: FinancialFactorLineageIssue[] = [];

  for (const factor of factors) {
    for (const parentFactorId of factor.lineage?.parentFactorIds || []) {
      if (parentFactorId === factor.id) {
        issues.push({ code: 'self_parent', factorId: factor.id, parentFactorId });
        continue;
      }
      if (!factorById.has(parentFactorId)) {
        issues.push({ code: 'missing_parent', factorId: factor.id, parentFactorId });
        continue;
      }
      childIds.set(parentFactorId, [...(childIds.get(parentFactorId) || []), factor.id]);
      edges.push({
        id: `${parentFactorId}->${factor.id}`,
        sourceFactorId: parentFactorId,
        targetFactorId: factor.id,
      });
    }
  }

  const generationById = new Map<string, number>();
  const visiting = new Set<string>();
  const cycleFactors = new Set<string>();
  const resolveGeneration = (factorId: string): number => {
    const cached = generationById.get(factorId);
    if (cached != null) return cached;
    if (visiting.has(factorId)) {
      cycleFactors.add(factorId);
      return 0;
    }
    const factor = factorById.get(factorId);
    if (!factor) return 0;
    if (factor.lineage?.generation != null) {
      generationById.set(factorId, factor.lineage.generation);
      return factor.lineage.generation;
    }
    visiting.add(factorId);
    const parentGenerations = (factor.lineage?.parentFactorIds || [])
      .filter((parentFactorId) => factorById.has(parentFactorId) && parentFactorId !== factorId)
      .map(resolveGeneration);
    visiting.delete(factorId);
    const generation = parentGenerations.length ? Math.max(...parentGenerations) + 1 : 0;
    generationById.set(factorId, generation);
    return generation;
  };

  factors.forEach((factor) => resolveGeneration(factor.id));
  if (cycleFactors.size) {
    for (const factorId of cycleFactors) issues.push({ code: 'cycle', factorId });
  }

  for (const edge of edges) {
    const sourceGeneration = generationById.get(edge.sourceFactorId) || 0;
    const targetGeneration = generationById.get(edge.targetFactorId) || 0;
    if (targetGeneration <= sourceGeneration) {
      issues.push({
        code: 'generation_order',
        factorId: edge.targetFactorId,
        parentFactorId: edge.sourceFactorId,
      });
    }
  }

  const nodes = factors.map((factor) => ({
    factorId: factor.id,
    parentFactorIds: (factor.lineage?.parentFactorIds || []).filter(
      (parentFactorId) => factorById.has(parentFactorId) && parentFactorId !== factor.id
    ),
    childFactorIds: [...(childIds.get(factor.id) || [])],
    missingParentFactorIds: (factor.lineage?.parentFactorIds || []).filter(
      (parentFactorId) => !factorById.has(parentFactorId)
    ),
    generation: generationById.get(factor.id) || 0,
    operation: factor.lineage?.operation || 'seed',
  }));

  return {
    nodes,
    edges,
    issues,
    maxGeneration: Math.max(0, ...nodes.map((node) => node.generation)),
  };
}

export interface FinancialFactorProgressSummary {
  factorCount: number;
  pendingCount: number;
  qualifiedCount: number;
  promotionReadyCount: number;
  activeCount: number;
  rejectedCount: number;
  batchCount: number;
  blockerCount: number;
  currentBatchLabel?: string;
}

export interface LegacyFinancialFactorCheck {
  id: string;
  label: string;
  status: string;
  value?: number | string;
}

export interface LegacyFinancialFactorCandidate {
  id: string;
  name?: string;
  expression?: string;
  family?: string;
  hypothesis?: string;
  selectionReason?: string;
  decisionReason?: string;
  status?: string;
  checks: LegacyFinancialFactorCheck[];
  evidenceIds: string[];
}

/**
 * Read-only compatibility shape for project files produced before factor_registry
 * became the single writer. It must never be treated as a registered portfolio.
 */
export interface LegacyFinancialFactorPortfolio {
  schema: typeof LEGACY_FINANCIAL_FACTOR_PORTFOLIO_SCHEMA;
  title: string;
  portfolioId?: string;
  scienceArtifactId?: string;
  automationPolicy?: FinancialFactorAutomationPolicy;
  market?: string;
  universe?: string;
  factors: LegacyFinancialFactorCandidate[];
}

export interface FinancialFactorConversationExtra {
  enabled: true;
  mode: typeof FINANCIAL_FACTOR_MODE_ID;
  projectRoot?: string;
  focus: 'financial_factor_mining';
  defaultSkill: typeof FINANCIAL_FACTOR_SKILL_NAME;
  schema: typeof FINANCIAL_FACTOR_PORTFOLIO_SCHEMA;
  artifactId: typeof FINANCIAL_FACTOR_PORTFOLIO_ARTIFACT_ID;
  executionMode: FinancialFactorExecutionMode;
  automationPolicy: FinancialFactorAutomationPolicy;
  sopVersion: 1;
  rules: {
    userIntentFirst: true;
    avoidFabricatedBacktests: true;
    requireAssumptionLogging: true;
  };
}

export const buildFinancialFactorConversationExtra = (
  projectRoot?: string,
  executionMode: FinancialFactorExecutionMode = 'manual',
  automationPolicy: FinancialFactorAutomationPolicy = 'verify_only'
): FinancialFactorConversationExtra =>
  buildSharedFinancialFactorConversationExtra(projectRoot, executionMode, automationPolicy);

export function buildInitialFinancialFactorPortfolio(input: {
  title: string;
  objective: string;
  projectRoot?: string;
  executionMode?: FinancialFactorExecutionMode;
  automationPolicy?: FinancialFactorAutomationPolicy;
  updatedAt: number;
}): FinancialFactorPortfolio {
  return {
    schema: FINANCIAL_FACTOR_PORTFOLIO_SCHEMA,
    version: 1,
    title: input.title,
    stage: 'scope',
    status: 'planning',
    updatedAt: input.updatedAt,
    context: {
      objective: input.objective,
      projectRoot: input.projectRoot,
      executionMode: input.executionMode || 'manual',
      automationPolicy: input.automationPolicy || 'verify_only',
    },
    batches: [],
    factors: [],
    blockers: [],
    nextActions: [
      {
        id: 'define-factor-scope',
        label: 'Define the first factor research batch',
        kind: 'research',
        priority: 'now',
        owner: 'agent',
      },
    ],
  };
}

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Boolean(value && typeof value === 'object' && !Array.isArray(value));

const FACTOR_STAGES = new Set<FinancialFactorStage>([
  'scope',
  'ideation',
  'linting',
  'simulation',
  'screening',
  'registration',
  'submission',
  'complete',
]);
const FACTOR_PORTFOLIO_STATUSES = new Set<FinancialFactorPortfolioStatus>([
  'planning',
  'running',
  'needs_decision',
  'blocked',
  'complete',
]);
const FACTOR_STATUSES = new Set<FinancialFactorStatus>([
  'idea',
  'linted',
  'simulated',
  'qualified',
  'submit_pending',
  'active',
  'hold',
  'rejected',
  'failed',
]);
const FACTOR_LIFECYCLES = new Set<FinancialFactorLifecycle>([
  'research',
  'qualified',
  'shadow',
  'paper',
  'production',
  'suspended',
  'retired',
]);
const FACTOR_SUBMISSION_STATUSES = new Set<FinancialFactorSubmissionStatus>([
  'not_submitted',
  'queued',
  'submitted',
  'verifying',
  'active',
  'rejected',
  'failed',
]);
const FACTOR_ARTIFACT_ROLES = new Set<FinancialFactorArtifactRef['role']>([
  'table',
  'figure',
  'dataset',
  'code',
  'log',
  'report',
  'timeseries',
  'notebook',
  'other',
]);
const FACTOR_SERIES_KINDS = new Set<FinancialFactorSeriesKind>([
  'cumulative_pnl',
  'benchmark',
  'rank_ic',
  'drawdown',
  'turnover',
  'exposure',
  'coverage',
  'other',
]);
const FACTOR_PERIOD_KINDS = new Set<FinancialFactorPeriodKind>(['is', 'oos', 'shadow', 'live', 'other']);
const FACTOR_EVOLUTION_OPERATIONS = new Set<FinancialFactorEvolutionOperation>(FINANCIAL_FACTOR_EVOLUTION_OPERATIONS);
const PROMOTION_CHECK_ID_SET = new Set<string>(FINANCIAL_FACTOR_PROMOTION_CHECK_IDS);

const isNonEmptyString = (value: unknown): value is string => typeof value === 'string' && Boolean(value.trim());

const isFinancialFactorCheck = (value: unknown): value is FinancialFactorCheck =>
  isRecord(value) &&
  isNonEmptyString(value.id) &&
  isNonEmptyString(value.label) &&
  ['passed', 'warning', 'failed', 'not_run'].includes(String(value.status)) &&
  (value.value == null ||
    typeof value.value === 'string' ||
    (typeof value.value === 'number' && Number.isFinite(value.value))) &&
  (value.threshold == null ||
    typeof value.threshold === 'string' ||
    (typeof value.threshold === 'number' && Number.isFinite(value.threshold))) &&
  (value.detail == null || typeof value.detail === 'string') &&
  (value.evidenceIds == null ||
    (Array.isArray(value.evidenceIds) && value.evidenceIds.every((item) => typeof item === 'string')));

const isFinancialFactorHypothesisCard = (value: unknown): value is FinancialFactorHypothesisCard =>
  isRecord(value) &&
  isNonEmptyString(value.mechanism) &&
  isNonEmptyString(value.expectedSign) &&
  isNonEmptyString(value.expectedHorizon) &&
  isNonEmptyString(value.requiredData) &&
  isNonEmptyString(value.failureCondition) &&
  (value.knownAnalogs == null || (Array.isArray(value.knownAnalogs) && value.knownAnalogs.every(isNonEmptyString)));

const isFinancialFactorSearchWeaknessAxis = (value: unknown): value is FinancialFactorSearchWeaknessAxis =>
  FINANCIAL_FACTOR_SEARCH_WEAKNESS_AXES.includes(value as FinancialFactorSearchWeaknessAxis);

const isFinancialFactorSearchWeakness = (value: unknown): value is FinancialFactorSearchWeakness =>
  isRecord(value) &&
  isFinancialFactorSearchWeaknessAxis(value.axis) &&
  (value.severity === 1 || value.severity === 2 || value.severity === 3) &&
  isNonEmptyString(value.evidenceId) &&
  isNonEmptyString(value.summary);

export const isFinancialFactorResearchContext = (value: unknown): value is FinancialFactorResearchContext =>
  isRecord(value) &&
  isNonEmptyString(value.mechanismId) &&
  FACTOR_EVOLUTION_OPERATIONS.has(value.operation as FinancialFactorEvolutionOperation) &&
  isFinancialFactorHypothesisCard(value.hypothesisCard) &&
  isRecord(value.edit) &&
  isNonEmptyString(value.edit.motif) &&
  Array.isArray(value.edit.changedComponents) &&
  value.edit.changedComponents.length > 0 &&
  value.edit.changedComponents.length <= 12 &&
  value.edit.changedComponents.every(isNonEmptyString) &&
  new Set(value.edit.changedComponents).size === value.edit.changedComponents.length &&
  isNonEmptyString(value.edit.rationale) &&
  isNonEmptyString(value.edit.expectedEffect) &&
  Array.isArray(value.weaknesses) &&
  value.weaknesses.length <= FINANCIAL_FACTOR_SEARCH_WEAKNESS_AXES.length &&
  value.weaknesses.every(isFinancialFactorSearchWeakness) &&
  new Set(value.weaknesses.map((weakness) => weakness.axis)).size === value.weaknesses.length;

const isFinancialFactorLineage = (value: unknown): value is FinancialFactorLineage =>
  isRecord(value) &&
  Array.isArray(value.parentFactorIds) &&
  value.parentFactorIds.every(isNonEmptyString) &&
  new Set(value.parentFactorIds).size === value.parentFactorIds.length &&
  FACTOR_EVOLUTION_OPERATIONS.has(value.operation as FinancialFactorEvolutionOperation) &&
  (value.generation == null ||
    (typeof value.generation === 'number' && Number.isSafeInteger(value.generation) && value.generation >= 0)) &&
  (value.cycleId == null || isNonEmptyString(value.cycleId)) &&
  (value.mechanismIds == null || (Array.isArray(value.mechanismIds) && value.mechanismIds.every(isNonEmptyString))) &&
  (value.archetypeIds == null || (Array.isArray(value.archetypeIds) && value.archetypeIds.every(isNonEmptyString))) &&
  (value.mutationSummary == null || isNonEmptyString(value.mutationSummary)) &&
  (value.memoryRefs == null || (Array.isArray(value.memoryRefs) && value.memoryRefs.every(isNonEmptyString)));

const isFinancialFactorArtifactRef = (value: unknown): value is FinancialFactorArtifactRef => {
  if (!isRecord(value)) return false;
  return (
    typeof value.artifactId === 'string' &&
    Boolean(value.artifactId.trim()) &&
    FACTOR_ARTIFACT_ROLES.has(value.role as FinancialFactorArtifactRef['role']) &&
    (value.artifactVersion == null ||
      (typeof value.artifactVersion === 'number' &&
        Number.isInteger(value.artifactVersion) &&
        value.artifactVersion > 0)) &&
    (value.path == null || (typeof value.path === 'string' && Boolean(value.path.trim()))) &&
    (value.runId == null || (typeof value.runId === 'string' && Boolean(value.runId.trim()))) &&
    (value.generatedAt == null || (typeof value.generatedAt === 'number' && Number.isFinite(value.generatedAt))) &&
    (value.evidenceIds == null ||
      (Array.isArray(value.evidenceIds) && value.evidenceIds.every((item) => typeof item === 'string')))
  );
};

const isOptionalFiniteTimestamp = (value: unknown): boolean =>
  value == null || (typeof value === 'number' && Number.isFinite(value));

const isFinancialFactorSubmission = (value: unknown): value is FinancialFactorSubmission =>
  isRecord(value) &&
  FACTOR_SUBMISSION_STATUSES.has(value.status as FinancialFactorSubmissionStatus) &&
  typeof value.updatedAt === 'number' &&
  Number.isFinite(value.updatedAt) &&
  (value.platform == null || (typeof value.platform === 'string' && Boolean(value.platform.trim()))) &&
  (value.externalId == null || (typeof value.externalId === 'string' && Boolean(value.externalId.trim()))) &&
  (value.receiptHash == null || (typeof value.receiptHash === 'string' && Boolean(value.receiptHash.trim()))) &&
  (value.lastError == null || (typeof value.lastError === 'string' && Boolean(value.lastError.trim()))) &&
  isOptionalFiniteTimestamp(value.submittedAt) &&
  isOptionalFiniteTimestamp(value.verifiedAt) &&
  isOptionalFiniteTimestamp(value.nextRetryAt);

const isProjectRelativeEvaluationPath = (value: string): boolean =>
  Boolean(value.trim()) &&
  !value.startsWith('/') &&
  !/^[a-z]:[\\/]/iu.test(value) &&
  !value.split(/[\\/]+/u).includes('..') &&
  !value.includes('\0') &&
  !value.includes('\r') &&
  !value.includes('\n');

const isFinancialFactorEvaluationCode = (value: unknown): value is FinancialFactorEvaluationCode =>
  isRecord(value) &&
  typeof value.path === 'string' &&
  isProjectRelativeEvaluationPath(value.path) &&
  (value.runtime == null || ['python', 'node', 'r', 'notebook'].includes(String(value.runtime))) &&
  (value.entrypoint == null || (typeof value.entrypoint === 'string' && Boolean(value.entrypoint.trim()))) &&
  (value.sha256 == null || (typeof value.sha256 === 'string' && /^[a-f0-9]{64}$/iu.test(value.sha256)));

const isFinancialFactorMetricContext = (value: unknown): value is FinancialFactorMetricContext =>
  isRecord(value) &&
  typeof value.contractId === 'string' &&
  Boolean(value.contractId.trim()) &&
  typeof value.evaluationId === 'string' &&
  Boolean(value.evaluationId.trim()) &&
  (value.evaluationCode == null || isFinancialFactorEvaluationCode(value.evaluationCode));

const isFinancialFactorCandidate = (value: unknown): value is FinancialFactorCandidate => {
  if (!isRecord(value)) return false;
  return (
    typeof value.id === 'string' &&
    Boolean(value.id.trim()) &&
    typeof value.name === 'string' &&
    Boolean(value.name.trim()) &&
    typeof value.expression === 'string' &&
    Boolean(value.expression.trim()) &&
    typeof value.hypothesis === 'string' &&
    Boolean(value.hypothesis.trim()) &&
    (value.hypothesisCard == null || isFinancialFactorHypothesisCard(value.hypothesisCard)) &&
    (value.lineage == null || isFinancialFactorLineage(value.lineage)) &&
    typeof value.selectionReason === 'string' &&
    Boolean(value.selectionReason.trim()) &&
    typeof value.decisionReason === 'string' &&
    Boolean(value.decisionReason.trim()) &&
    FACTOR_STATUSES.has(value.status as FinancialFactorStatus) &&
    (value.lifecycle == null || FACTOR_LIFECYCLES.has(value.lifecycle as FinancialFactorLifecycle)) &&
    (value.submission == null || isFinancialFactorSubmission(value.submission)) &&
    typeof value.updatedAt === 'number' &&
    Number.isFinite(value.updatedAt) &&
    Array.isArray(value.checks) &&
    value.checks.every(isFinancialFactorCheck) &&
    Array.isArray(value.evidenceIds) &&
    value.evidenceIds.every((item) => typeof item === 'string') &&
    (!value.artifacts || (Array.isArray(value.artifacts) && value.artifacts.every(isFinancialFactorArtifactRef))) &&
    (value.metricContext == null || isFinancialFactorMetricContext(value.metricContext)) &&
    (!value.metrics ||
      (Array.isArray(value.metrics) &&
        (value.metrics.length === 0 || isFinancialFactorMetricContext(value.metricContext))))
  );
};

const isIsoLikeTimestamp = (value: unknown): value is string =>
  typeof value === 'string' && Boolean(value.trim()) && Number.isFinite(Date.parse(value));

const isFinancialFactorTimeSeriesItem = (value: unknown): value is FinancialFactorTimeSeriesItem => {
  if (!isRecord(value) || !Array.isArray(value.points) || value.points.length === 0) return false;
  let previousTimestamp = Number.NEGATIVE_INFINITY;
  for (const point of value.points) {
    if (!Array.isArray(point) || point.length !== 2 || !isIsoLikeTimestamp(point[0])) return false;
    if (typeof point[1] !== 'number' || !Number.isFinite(point[1])) return false;
    const timestamp = Date.parse(point[0]);
    if (timestamp <= previousTimestamp) return false;
    previousTimestamp = timestamp;
  }
  return (
    typeof value.id === 'string' &&
    Boolean(value.id.trim()) &&
    typeof value.label === 'string' &&
    Boolean(value.label.trim()) &&
    FACTOR_SERIES_KINDS.has(value.kind as FinancialFactorSeriesKind) &&
    (value.unit == null || typeof value.unit === 'string')
  );
};

const isFinancialFactorTimeSeriesPeriod = (value: unknown): value is FinancialFactorTimeSeriesPeriod =>
  isRecord(value) &&
  FACTOR_PERIOD_KINDS.has(value.kind as FinancialFactorPeriodKind) &&
  (value.label == null || typeof value.label === 'string') &&
  isIsoLikeTimestamp(value.start) &&
  isIsoLikeTimestamp(value.end) &&
  Date.parse(value.start) <= Date.parse(value.end);

const isFinancialFactorNotebookSummary = (value: unknown): value is FinancialFactorNotebookSummary =>
  isRecord(value) &&
  typeof value.path === 'string' &&
  Boolean(value.path.trim()) &&
  typeof value.title === 'string' &&
  Boolean(value.title.trim()) &&
  (value.kernel == null || typeof value.kernel === 'string') &&
  typeof value.codeCellCount === 'number' &&
  Number.isInteger(value.codeCellCount) &&
  value.codeCellCount >= 0 &&
  typeof value.executedCellCount === 'number' &&
  Number.isInteger(value.executedCellCount) &&
  value.executedCellCount >= 0 &&
  value.executedCellCount <= value.codeCellCount &&
  typeof value.failedCellCount === 'number' &&
  Number.isInteger(value.failedCellCount) &&
  value.failedCellCount >= 0 &&
  value.failedCellCount <= value.executedCellCount &&
  typeof value.generatedAt === 'number' &&
  Number.isFinite(value.generatedAt);

export function isFinancialFactorTimeSeries(value: unknown): value is FinancialFactorTimeSeries {
  if (!isRecord(value) || value.schema !== FINANCIAL_FACTOR_TIMESERIES_SCHEMA || value.version !== 1) return false;
  if (
    typeof value.factorId !== 'string' ||
    !value.factorId.trim() ||
    typeof value.runId !== 'string' ||
    !value.runId.trim() ||
    typeof value.contractId !== 'string' ||
    !value.contractId.trim() ||
    typeof value.evaluationId !== 'string' ||
    !value.evaluationId.trim() ||
    typeof value.frequency !== 'string' ||
    !value.frequency.trim() ||
    typeof value.generatedAt !== 'number' ||
    !Number.isFinite(value.generatedAt) ||
    !Array.isArray(value.series) ||
    value.series.length === 0 ||
    value.series.length > 16 ||
    !value.series.every(isFinancialFactorTimeSeriesItem) ||
    new Set(value.series.map((item) => item.id)).size !== value.series.length
  )
    return false;
  return (
    (value.periods == null ||
      (Array.isArray(value.periods) && value.periods.every(isFinancialFactorTimeSeriesPeriod))) &&
    (value.notebook == null || isFinancialFactorNotebookSummary(value.notebook))
  );
}

export function readFinancialFactorTimeSeries(value: unknown): FinancialFactorTimeSeries | undefined {
  if (!isRecord(value)) return undefined;
  const direct = value.financialFactorSeries;
  if (isFinancialFactorTimeSeries(direct)) return direct;
  return isFinancialFactorTimeSeries(value) ? value : undefined;
}

const FACTOR_PROTOCOL_SOURCES = new Set<FinancialFactorEvaluationProtocol['source']>(['system', 'agent', 'user']);
const FACTOR_PROTOCOL_STATUSES = new Set<FinancialFactorEvaluationProtocol['status']>(['draft', 'frozen']);
const FACTOR_DATASET_BACKENDS = new Set<FinancialFactorEvaluationProtocol['dataset']['backend']>([
  'table',
  'qlib',
  'external',
]);
const FACTOR_SPLIT_ROLES = new Set<FinancialFactorEvaluationProtocol['splits'][number]['role']>([
  'development',
  'validation',
  'feedback',
  'locked_test',
]);
const FACTOR_POOL_EXCLUSION_REASONS = new Set<FinancialFactorPoolExclusionReason>([
  'duplicate_expression',
  'insufficient_coverage',
  'unstable_direction',
  'family_limit',
  'correlated_signal',
  'insufficient_marginal_gain',
  'unstable_marginal_gain',
  'validation_pool_limit',
  'factor_limit',
]);
const FACTOR_RESEARCH_TRANSITION_KINDS = new Set<FinancialFactorResearchTransitionKind>([
  'NEW',
  'IMPROVE',
  'COMBINE',
  'PIVOT',
  'STOP',
]);
const FACTOR_RESEARCH_ASSESSMENTS = new Set<FinancialFactorResearchAssessment>([
  'positive',
  'mixed',
  'negative',
  'terminal',
]);

const hasExactlyOneFinancialFactorSearchSplit = (value: Record<string, unknown>): boolean =>
  Number(isNonEmptyString(value.developmentSplitId)) + Number(isNonEmptyString(value.feedbackSplitId)) === 1;

export const getFinancialFactorCampaignSearchSplitId = (campaign: FinancialFactorResearchCampaign): string =>
  campaign.feedbackSplitId || campaign.developmentSplitId || '';

export const getFinancialFactorTransitionSearchSplitId = (transition: FinancialFactorResearchTransition): string =>
  transition.feedbackSplitId || transition.developmentSplitId || '';

export const isFinancialFactorResearchCampaign = (value: unknown): value is FinancialFactorResearchCampaign =>
  isRecord(value) &&
  value.schema === FINANCIAL_FACTOR_CAMPAIGN_SCHEMA &&
  value.version === 1 &&
  ['campaignId', 'runId', 'protocolId', 'objective'].every((key) => isNonEmptyString(value[key])) &&
  hasExactlyOneFinancialFactorSearchSplit(value) &&
  typeof value.baseCommit === 'string' &&
  /^[a-f0-9]{7,64}$/iu.test(value.baseCommit) &&
  typeof value.candidateBudget === 'number' &&
  Number.isInteger(value.candidateBudget) &&
  value.candidateBudget >= 1 &&
  value.candidateBudget <= 100_000 &&
  typeof value.maxConcurrency === 'number' &&
  Number.isInteger(value.maxConcurrency) &&
  value.maxConcurrency >= 1 &&
  value.maxConcurrency <= 8 &&
  (value.mechanismFamilies == null ||
    (Array.isArray(value.mechanismFamilies) &&
      value.mechanismFamilies.length <= 64 &&
      value.mechanismFamilies.every(isNonEmptyString) &&
      new Set(value.mechanismFamilies).size === value.mechanismFamilies.length)) &&
  typeof value.createdAt === 'number' &&
  Number.isFinite(value.createdAt);

export const isFinancialFactorResearchTransition = (value: unknown): value is FinancialFactorResearchTransition =>
  isRecord(value) &&
  value.schema === FINANCIAL_FACTOR_TRANSITION_SCHEMA &&
  value.version === 1 &&
  ['transitionId', 'campaignId', 'runId', 'protocolId', 'summary'].every((key) => isNonEmptyString(value[key])) &&
  hasExactlyOneFinancialFactorSearchSplit(value) &&
  FACTOR_RESEARCH_TRANSITION_KINDS.has(value.kind as FinancialFactorResearchTransitionKind) &&
  FACTOR_RESEARCH_ASSESSMENTS.has(value.assessment as FinancialFactorResearchAssessment) &&
  (value.candidateId == null || isNonEmptyString(value.candidateId)) &&
  Array.isArray(value.parentCandidateIds) &&
  value.parentCandidateIds.every(isNonEmptyString) &&
  new Set(value.parentCandidateIds).size === value.parentCandidateIds.length &&
  (value.mechanismFamily == null || isNonEmptyString(value.mechanismFamily)) &&
  (value.researchContext == null || isFinancialFactorResearchContext(value.researchContext)) &&
  typeof value.sequence === 'number' &&
  Number.isInteger(value.sequence) &&
  value.sequence >= 1 &&
  typeof value.executionsUsed === 'number' &&
  Number.isInteger(value.executionsUsed) &&
  value.executionsUsed >= 0 &&
  typeof value.remainingBudget === 'number' &&
  Number.isInteger(value.remainingBudget) &&
  value.remainingBudget >= 0 &&
  typeof value.frontierImproved === 'boolean' &&
  (value.sourceDelivery == null ||
    (isRecord(value.sourceDelivery) &&
      isNonEmptyString(value.sourceDelivery.branch) &&
      typeof value.sourceDelivery.headCommit === 'string' &&
      /^[a-f0-9]{7,64}$/iu.test(value.sourceDelivery.headCommit) &&
      (value.sourceDelivery.agentId == null || isNonEmptyString(value.sourceDelivery.agentId)) &&
      (value.sourceDelivery.taskId == null || isNonEmptyString(value.sourceDelivery.taskId)))) &&
  Array.isArray(value.evidenceIds) &&
  value.evidenceIds.every(isNonEmptyString) &&
  new Set(value.evidenceIds).size === value.evidenceIds.length &&
  typeof value.requestHash === 'string' &&
  /^[a-f0-9]{64}$/u.test(value.requestHash) &&
  typeof value.createdAt === 'number' &&
  Number.isFinite(value.createdAt);

const canonicalSearchMemoryText = (value: string): string => value.trim().toLowerCase().replace(/\s+/gu, ' ');

export const buildFinancialFactorSearchGuidance = (
  campaign: FinancialFactorResearchCampaign,
  transitions: FinancialFactorResearchTransition[]
): FinancialFactorSearchGuidance => {
  const feedbackCampaign = Boolean(campaign.feedbackSplitId);
  const searchEvidenceName = feedbackCampaign ? 'feedback' : 'development';
  const completed = transitions.filter(
    (transition): transition is FinancialFactorResearchTransition & { candidateId: string; mechanismFamily: string } =>
      transition.kind !== 'STOP' && Boolean(transition.candidateId && transition.mechanismFamily)
  );
  const byCandidateId = new Map(completed.map((transition) => [transition.candidateId, transition]));
  const childCounts = new Map<string, number>();
  completed.forEach((transition) =>
    transition.parentCandidateIds.forEach((parentId) => childCounts.set(parentId, (childCounts.get(parentId) || 0) + 1))
  );
  const familyCounts = new Map<string, number>();
  completed.forEach((transition) =>
    familyCounts.set(transition.mechanismFamily, (familyCounts.get(transition.mechanismFamily) || 0) + 1)
  );
  const underexploredMechanismFamilies = (campaign.mechanismFamilies || [])
    .map((family) => ({ family, count: familyCounts.get(family) || 0 }))
    .toSorted((left, right) => left.count - right.count || left.family.localeCompare(right.family))
    .filter((entry, _index, entries) => entry.count === entries[0]?.count)
    .map((entry) => entry.family);

  const editGroups = new Map<string, FinancialFactorResearchTransition[]>();
  completed.forEach((transition) => {
    if (!transition.researchContext) return;
    const parentMechanismContexts = [
      ...new Set(
        transition.parentCandidateIds.flatMap((parentId) => {
          const parent = byCandidateId.get(parentId);
          const context = parent?.researchContext?.mechanismId || parent?.mechanismFamily;
          return context ? [context] : [];
        })
      ),
    ].toSorted();
    const key = [
      parentMechanismContexts.join('+') || `root:${transition.researchContext.mechanismId}`,
      transition.researchContext.operation,
      canonicalSearchMemoryText(transition.researchContext.edit.motif),
    ].join('::');
    editGroups.set(key, [...(editGroups.get(key) || []), transition]);
  });
  const editMemory = [...editGroups.entries()]
    .map(([key, attempts]): FinancialFactorEditMemory => {
      const positive = attempts.filter((transition) => transition.assessment === 'positive').length;
      const mixed = attempts.filter((transition) => transition.assessment === 'mixed').length;
      const negative = attempts.filter((transition) => transition.assessment === 'negative').length;
      const observationCount = attempts.length;
      const confidence = observationCount >= 4 ? 'high' : observationCount >= 2 ? 'medium' : 'low';
      const disposition =
        observationCount >= 2 && (positive + mixed) / observationCount >= 0.67
          ? 'prefer'
          : observationCount >= 2 && negative / observationCount >= 0.75
            ? 'avoid'
            : 'uncertain';
      const first = attempts[0];
      const parentMechanismFamilies = [
        ...new Set(
          attempts.flatMap((transition) =>
            transition.parentCandidateIds.flatMap((parentId) => {
              const parentFamily = byCandidateId.get(parentId)?.mechanismFamily;
              return parentFamily ? [parentFamily] : [];
            })
          )
        ),
      ].toSorted();
      return {
        key,
        motif: first.researchContext?.edit.motif || key,
        operation: first.researchContext?.operation || 'mutation',
        parentMechanismFamilies,
        attempts: observationCount,
        positive,
        mixed,
        negative,
        frontierImprovements: attempts.filter((transition) => transition.frontierImproved).length,
        confidence,
        disposition,
        candidateIds: attempts.map((transition) => transition.candidateId),
      };
    })
    .toSorted((left, right) => right.attempts - left.attempts || left.key.localeCompare(right.key));

  const mechanismGroups = new Map<string, FinancialFactorResearchTransition[]>();
  completed.forEach((transition) => {
    const mechanismId = transition.researchContext?.mechanismId;
    if (!mechanismId) return;
    mechanismGroups.set(mechanismId, [...(mechanismGroups.get(mechanismId) || []), transition]);
  });
  const mechanismMemory = [...mechanismGroups.entries()]
    .map(
      ([mechanismId, attempts]): FinancialFactorMechanismMemory => ({
        mechanismId,
        mechanismFamily: attempts[0].mechanismFamily,
        hypothesis: attempts[0].researchContext?.hypothesisCard.mechanism || mechanismId,
        attempts: attempts.length,
        positive: attempts.filter((transition) => transition.assessment === 'positive').length,
        mixed: attempts.filter((transition) => transition.assessment === 'mixed').length,
        negative: attempts.filter((transition) => transition.assessment === 'negative').length,
        frontierImprovements: attempts.filter((transition) => transition.frontierImproved).length,
        candidateIds: attempts.map((transition) => transition.candidateId),
        weaknessAxes: [
          ...new Set(
            attempts.flatMap(
              (transition) => transition.researchContext?.weaknesses.map((weakness) => weakness.axis) || []
            )
          ),
        ].toSorted(),
      })
    )
    .toSorted((left, right) => right.attempts - left.attempts || left.mechanismId.localeCompare(right.mechanismId));

  const ancestryFor = (candidateId: string): string[] => {
    const visited = new Set<string>();
    const visit = (currentId: string): void => {
      const current = byCandidateId.get(currentId);
      current?.parentCandidateIds.forEach((parentId) => {
        if (visited.has(parentId)) return;
        visited.add(parentId);
        visit(parentId);
      });
    };
    visit(candidateId);
    return [...visited].toSorted((left, right) => {
      const leftSequence = byCandidateId.get(left)?.sequence || 0;
      const rightSequence = byCandidateId.get(right)?.sequence || 0;
      return leftSequence - rightSequence || left.localeCompare(right);
    });
  };

  const parentSuggestions = completed
    .filter((transition) => transition.assessment === 'positive' || transition.assessment === 'mixed')
    .map((transition): FinancialFactorParentSuggestion => {
      const reasonCodes: FinancialFactorParentSuggestion['reasonCodes'] = ['quality'];
      let score = transition.assessment === 'positive' ? 3 : 1;
      if (transition.frontierImproved) {
        score += 2;
        reasonCodes.push('frontier_gain');
      }
      const childCount = childCounts.get(transition.candidateId) || 0;
      if (childCount <= 1) reasonCodes.push('low_reuse');
      score += 1 / (1 + childCount) - Math.log2(1 + childCount) * 0.75;
      if (underexploredMechanismFamilies.includes(transition.mechanismFamily)) {
        score += 1;
        reasonCodes.push('underexplored_family');
      }
      if (transition.researchContext?.weaknesses.length) {
        score += 0.5;
        reasonCodes.push('repairable_gap');
      }
      const mechanismAttempts = transition.researchContext?.mechanismId
        ? mechanismGroups.get(transition.researchContext.mechanismId)?.length || 0
        : familyCounts.get(transition.mechanismFamily) || 0;
      if (childCount === 0 && mechanismAttempts <= 2) {
        score += 0.75;
        reasonCodes.push('lineage_uncertainty');
      }
      const attemptedEditMotifs = [
        ...new Set(
          completed.flatMap((candidateTransition) =>
            candidateTransition.parentCandidateIds.includes(transition.candidateId) &&
            candidateTransition.researchContext?.edit.motif
              ? [candidateTransition.researchContext.edit.motif]
              : []
          )
        ),
      ].toSorted();
      const suggestion: FinancialFactorParentSuggestion = {
        candidateId: transition.candidateId,
        mechanismFamily: transition.mechanismFamily,
        score: Number(score.toFixed(6)),
        assessment: transition.assessment as Exclude<FinancialFactorResearchAssessment, 'terminal'>,
        childCount,
        ancestryCandidateIds: ancestryFor(transition.candidateId),
        attemptedEditMotifs,
        reasonCodes,
      };
      if (transition.researchContext?.mechanismId) {
        suggestion.mechanismId = transition.researchContext.mechanismId;
      }
      return suggestion;
    })
    .toSorted((left, right) => right.score - left.score || left.candidateId.localeCompare(right.candidateId))
    .slice(0, 6);

  const crossoverSuggestions = parentSuggestions
    .flatMap((left, leftIndex) =>
      parentSuggestions.slice(leftIndex + 1).flatMap((right) => {
        if (left.mechanismFamily === right.mechanismFamily) return [];
        if (
          left.ancestryCandidateIds.includes(right.candidateId) ||
          right.ancestryCandidateIds.includes(left.candidateId)
        )
          return [];
        return [
          {
            candidateIds: [left.candidateId, right.candidateId] as [string, string],
            mechanismFamilies: [left.mechanismFamily, right.mechanismFamily] as [string, string],
            score: Number((left.score + right.score).toFixed(6)),
            reason:
              'Distinct mechanism families and unrelated ancestry make this a useful crossover hypothesis; audit signal correlation before admission.',
          },
        ];
      })
    )
    .toSorted(
      (left, right) =>
        right.score - left.score || left.candidateIds.join('+').localeCompare(right.candidateIds.join('+'))
    )
    .slice(0, 3);

  const stopped = transitions.at(-1)?.kind === 'STOP';
  const budgetExhausted = (transitions.at(-1)?.remainingBudget ?? campaign.candidateBudget) === 0;
  const topParent = parentSuggestions[0];
  const topTransition = topParent ? byCandidateId.get(topParent.candidateId) : undefined;
  const topCrossover = crossoverSuggestions[0];
  const recentLocalRefinements =
    completed.length >= 2 && completed.slice(-2).every((transition) => transition.kind === 'IMPROVE');
  const recommendedTransition: FinancialFactorSearchGuidance['recommendedTransition'] =
    stopped || budgetExhausted
      ? {
          kind: 'STOP',
          candidateIds: [],
          reason: stopped ? 'Campaign is already stopped.' : 'Candidate budget is exhausted.',
        }
      : !topParent
        ? {
            kind: 'NEW',
            candidateIds: [],
            reason: `No positive or mixed ${searchEvidenceName} candidate is available as a parent.`,
          }
        : underexploredMechanismFamilies.length > 0 &&
            !underexploredMechanismFamilies.includes(topParent.mechanismFamily)
          ? {
              kind: 'PIVOT',
              candidateIds: [topParent.candidateId],
              reason: `Pivot from the strongest attributable parent toward an underexplored frozen mechanism family: ${underexploredMechanismFamilies.join(', ')}.`,
            }
          : topCrossover && !completed.some((transition) => transition.kind === 'COMBINE') && completed.length >= 4
            ? {
                kind: 'COMBINE',
                candidateIds: topCrossover.candidateIds,
                reason: topCrossover.reason,
              }
            : recentLocalRefinements
              ? {
                  kind: 'PIVOT',
                  candidateIds: [topParent.candidateId],
                  reason: `Two consecutive local refinements have already been attempted; use ${searchEvidenceName}-only residual or novelty evidence for a mechanism pivot.`,
                }
              : topTransition?.researchContext?.weaknesses.length
                ? {
                    kind: 'IMPROVE',
                    candidateIds: [topParent.candidateId],
                    reason: `Address the highest-severity ${searchEvidenceName} weakness: ${
                      topTransition.researchContext.weaknesses.toSorted(
                        (left, right) => right.severity - left.severity
                      )[0].axis
                    }.`,
                  }
                : {
                    kind: 'NEW',
                    candidateIds: [],
                    reason: `The strongest parents have no recorded ${searchEvidenceName} weakness; spend the next execution on an independent mechanism.`,
                  };

  return {
    evidenceScope: feedbackCampaign ? 'feedback_only' : 'development_only',
    policy: {
      minimumMemoryObservations: 2,
      preferPositiveRate: 0.67,
      avoidNegativeRate: 0.75,
      maximumParentSuggestions: 3,
    },
    status: stopped ? 'stopped' : 'active',
    recommendedTransition,
    parentSuggestions: parentSuggestions.slice(0, 3),
    crossoverSuggestions,
    editMemory,
    mechanismMemory,
    avoidedEditMotifs: editMemory.filter((memory) => memory.disposition === 'avoid').map((memory) => memory.motif),
    underexploredMechanismFamilies,
    legacyUnstructuredTransitionCount: completed.filter((transition) => !transition.researchContext).length,
  };
};

export const isFinancialFactorPoolPolicy = (value: unknown): value is FinancialFactorPoolPolicy =>
  isRecord(value) &&
  typeof value.maxFactors === 'number' &&
  Number.isInteger(value.maxFactors) &&
  value.maxFactors >= 1 &&
  value.maxFactors <= 40 &&
  typeof value.maximumCorrelation === 'number' &&
  Number.isFinite(value.maximumCorrelation) &&
  value.maximumCorrelation >= 0 &&
  value.maximumCorrelation < 1 &&
  typeof value.maxPerFamily === 'number' &&
  Number.isInteger(value.maxPerFamily) &&
  value.maxPerFamily >= 1 &&
  value.maxPerFamily <= value.maxFactors &&
  typeof value.stabilityFolds === 'number' &&
  Number.isInteger(value.stabilityFolds) &&
  value.stabilityFolds >= 2 &&
  value.stabilityFolds <= 12 &&
  typeof value.minimumPositiveFolds === 'number' &&
  Number.isInteger(value.minimumPositiveFolds) &&
  value.minimumPositiveFolds >= 1 &&
  value.minimumPositiveFolds <= value.stabilityFolds &&
  (value.minimumMarginalDevelopmentGain == null ||
    (typeof value.minimumMarginalDevelopmentGain === 'number' &&
      Number.isFinite(value.minimumMarginalDevelopmentGain) &&
      value.minimumMarginalDevelopmentGain >= 0 &&
      value.minimumMarginalDevelopmentGain <= 1)) &&
  (value.minimumMarginalPositiveFolds == null ||
    (typeof value.minimumMarginalPositiveFolds === 'number' &&
      Number.isInteger(value.minimumMarginalPositiveFolds) &&
      value.minimumMarginalPositiveFolds >= 1 &&
      value.minimumMarginalPositiveFolds <= value.stabilityFolds)) &&
  (value.selectPoolSizeOnValidation == null || typeof value.selectPoolSizeOnValidation === 'boolean') &&
  Array.isArray(value.ridgeLambdas) &&
  value.ridgeLambdas.length >= 1 &&
  value.ridgeLambdas.length <= 20 &&
  value.ridgeLambdas.every((lambda) => typeof lambda === 'number' && Number.isFinite(lambda) && lambda > 0) &&
  typeof value.embargoTradingDays === 'number' &&
  Number.isInteger(value.embargoTradingDays) &&
  value.embargoTradingDays >= 0 &&
  value.embargoTradingDays <= 252 &&
  typeof value.splitPurgeTradingDays === 'number' &&
  Number.isInteger(value.splitPurgeTradingDays) &&
  value.splitPurgeTradingDays >= 0 &&
  value.splitPurgeTradingDays <= 252 &&
  typeof value.selectionRankIcWeight === 'number' &&
  Number.isFinite(value.selectionRankIcWeight) &&
  value.selectionRankIcWeight >= 0 &&
  value.selectionRankIcWeight <= 1 &&
  typeof value.selectionIcWeight === 'number' &&
  Number.isFinite(value.selectionIcWeight) &&
  value.selectionIcWeight >= 0 &&
  value.selectionIcWeight <= 1 &&
  Math.abs(value.selectionRankIcWeight + value.selectionIcWeight - 1) < 1e-8;

export function isFinancialFactorEvaluationProtocol(value: unknown): value is FinancialFactorEvaluationProtocol {
  if (!isRecord(value) || value.schema !== FINANCIAL_FACTOR_PROTOCOL_SCHEMA || value.version !== 1) return false;
  if (
    typeof value.protocolId !== 'string' ||
    !value.protocolId.trim() ||
    typeof value.title !== 'string' ||
    !value.title.trim() ||
    typeof value.objective !== 'string' ||
    !value.objective.trim() ||
    !FACTOR_PROTOCOL_SOURCES.has(value.source as FinancialFactorEvaluationProtocol['source']) ||
    !FACTOR_PROTOCOL_STATUSES.has(value.status as FinancialFactorEvaluationProtocol['status']) ||
    !isRecord(value.dataset) ||
    typeof value.dataset.datasetId !== 'string' ||
    !value.dataset.datasetId.trim() ||
    typeof value.dataset.snapshotId !== 'string' ||
    !value.dataset.snapshotId.trim() ||
    !FACTOR_DATASET_BACKENDS.has(value.dataset.backend as FinancialFactorEvaluationProtocol['dataset']['backend']) ||
    !isRecord(value.columns) ||
    !['date', 'asset', 'factor', 'futureReturn'].every(
      (key) =>
        typeof (value.columns as Record<string, unknown>)[key] === 'string' &&
        Boolean(String((value.columns as Record<string, unknown>)[key]).trim())
    ) ||
    (value.columns.availableAt != null && !isNonEmptyString(value.columns.availableAt)) ||
    !Array.isArray(value.splits) ||
    value.splits.length === 0 ||
    !isRecord(value.evaluation) ||
    typeof value.createdAt !== 'number' ||
    !Number.isFinite(value.createdAt) ||
    !Array.isArray(value.metrics) ||
    !value.metrics.every((metric) => typeof metric === 'string' && Boolean(metric.trim()))
  )
    return false;
  const evaluation = value.evaluation;
  const splitIds = value.splits.map((split) => (isRecord(split) ? split.id : undefined));
  const orderedSplits = value.splits
    .filter(isRecord)
    .toSorted((left, right) => Date.parse(String(left.start)) - Date.parse(String(right.start)));
  return (
    new Set(splitIds).size === splitIds.length &&
    value.splits.every(
      (split) =>
        isRecord(split) &&
        typeof split.id === 'string' &&
        Boolean(split.id.trim()) &&
        FACTOR_SPLIT_ROLES.has(split.role as FinancialFactorEvaluationProtocol['splits'][number]['role']) &&
        isIsoLikeTimestamp(split.start) &&
        isIsoLikeTimestamp(split.end) &&
        Date.parse(split.start) <= Date.parse(split.end) &&
        (split.sourcePath == null || (typeof split.sourcePath === 'string' && Boolean(split.sourcePath.trim()))) &&
        (split.contentSha256 == null ||
          (typeof split.contentSha256 === 'string' && /^[a-f0-9]{64}$/u.test(split.contentSha256)))
    ) &&
    orderedSplits.every(
      (split, index) =>
        index === 0 || Date.parse(String(orderedSplits[index - 1].end)) < Date.parse(String(split.start))
    ) &&
    typeof evaluation.frequency === 'string' &&
    Boolean(evaluation.frequency.trim()) &&
    typeof evaluation.quantiles === 'number' &&
    Number.isInteger(evaluation.quantiles) &&
    evaluation.quantiles >= 2 &&
    evaluation.quantiles <= 20 &&
    typeof evaluation.annualizationFactor === 'number' &&
    Number.isFinite(evaluation.annualizationFactor) &&
    evaluation.annualizationFactor > 0 &&
    typeof evaluation.minimumCoverage === 'number' &&
    evaluation.minimumCoverage >= 0 &&
    evaluation.minimumCoverage <= 1 &&
    typeof evaluation.costBps === 'number' &&
    Number.isFinite(evaluation.costBps) &&
    evaluation.costBps >= 0 &&
    (value.pool == null || isFinancialFactorPoolPolicy(value.pool))
  );
}

export const readFinancialFactorEvaluationProtocol = (value: unknown): FinancialFactorEvaluationProtocol | undefined =>
  isFinancialFactorEvaluationProtocol(value) ? value : undefined;

export function isFinancialFactorEvaluationRecord(value: unknown): value is FinancialFactorEvaluationRecord {
  return (
    isRecord(value) &&
    value.schema === FINANCIAL_FACTOR_EVALUATION_SCHEMA &&
    value.version === 1 &&
    typeof value.evaluationId === 'string' &&
    Boolean(value.evaluationId.trim()) &&
    typeof value.runId === 'string' &&
    Boolean(value.runId.trim()) &&
    isRecord(value.factor) &&
    typeof value.factor.id === 'string' &&
    Boolean(value.factor.id.trim()) &&
    typeof value.factor.name === 'string' &&
    Boolean(value.factor.name.trim()) &&
    (value.pool == null ||
      (isRecord(value.pool) &&
        typeof value.pool.poolId === 'string' &&
        Boolean(value.pool.poolId.trim()) &&
        typeof value.pool.modelHash === 'string' &&
        /^[a-f0-9]{64}$/u.test(value.pool.modelHash) &&
        Array.isArray(value.pool.selectedFactorIds) &&
        value.pool.selectedFactorIds.length > 0 &&
        value.pool.selectedFactorIds.every((id) => typeof id === 'string' && Boolean(id.trim())) &&
        Array.isArray(value.pool.weights) &&
        value.pool.weights.length === value.pool.selectedFactorIds.length &&
        value.pool.weights.every((weight) => typeof weight === 'number' && Number.isFinite(weight)))) &&
    typeof value.protocolId === 'string' &&
    Boolean(value.protocolId.trim()) &&
    typeof value.datasetSnapshotId === 'string' &&
    Boolean(value.datasetSnapshotId.trim()) &&
    (value.datasetContentSha256 == null ||
      (typeof value.datasetContentSha256 === 'string' && /^[a-f0-9]{64}$/u.test(value.datasetContentSha256))) &&
    typeof value.splitId === 'string' &&
    Boolean(value.splitId.trim()) &&
    ['succeeded', 'partial', 'failed'].includes(String(value.status)) &&
    ['attested', 'recorded'].includes(String(value.evidenceStatus)) &&
    typeof value.inputPath === 'string' &&
    typeof value.resultPath === 'string' &&
    typeof value.resultHash === 'string' &&
    /^[a-f0-9]{64}$/u.test(value.resultHash) &&
    Array.isArray(value.metrics) &&
    Array.isArray(value.checks) &&
    Array.isArray(value.warnings) &&
    typeof value.generatedAt === 'number' &&
    Number.isFinite(value.generatedAt) &&
    (value.timeSeries == null || isFinancialFactorTimeSeries(value.timeSeries))
  );
}

export const readFinancialFactorEvaluationRecord = (value: unknown): FinancialFactorEvaluationRecord | undefined =>
  isFinancialFactorEvaluationRecord(value) ? value : undefined;

const isFinancialFactorPoolCandidateSpec = (value: unknown): value is FinancialFactorPoolCandidateSpec =>
  isRecord(value) &&
  ['id', 'name', 'column', 'expression', 'family'].every(
    (key) => typeof value[key] === 'string' && Boolean(String(value[key]).trim())
  ) &&
  (value.hypothesis == null || typeof value.hypothesis === 'string') &&
  (value.complexity == null || (typeof value.complexity === 'number' && Number.isFinite(value.complexity))) &&
  (value.semanticAlignment == null ||
    (isRecord(value.semanticAlignment) &&
      ['passed', 'warning', 'failed'].includes(String(value.semanticAlignment.status)) &&
      (value.semanticAlignment.rationale == null || typeof value.semanticAlignment.rationale === 'string')));

const isFinancialFactorPoolCandidateStatistics = (value: unknown): value is FinancialFactorPoolCandidateStatistics =>
  isRecord(value) &&
  (value.direction === -1 || value.direction === 1) &&
  typeof value.coverage === 'number' &&
  ['coverage', 'meanIc', 'rankIc', 'selectionScore', 'worstFoldIc'].every(
    (key) => typeof value[key] === 'number' && Number.isFinite(value[key])
  ) &&
  (value.icir == null || (typeof value.icir === 'number' && Number.isFinite(value.icir))) &&
  value.coverage >= 0 &&
  value.coverage <= 1 &&
  typeof value.positiveFoldCount === 'number' &&
  Number.isInteger(value.positiveFoldCount) &&
  value.positiveFoldCount >= 0 &&
  Array.isArray(value.foldIcs) &&
  value.positiveFoldCount <= value.foldIcs.length &&
  value.foldIcs.every((item) => typeof item === 'number' && Number.isFinite(item));

const isFinancialFactorSubmissionMetric = (value: unknown): value is FinancialFactorResearchSubmissionMetric =>
  isRecord(value) &&
  isNonEmptyString(value.name) &&
  (value.value == null || (typeof value.value === 'number' && Number.isFinite(value.value))) &&
  (value.unit == null || typeof value.unit === 'string') &&
  (value.basis == null || ['measured', 'literature', 'estimated', 'pending'].includes(String(value.basis)));

export function isFinancialFactorPoolModel(value: unknown): value is FinancialFactorPoolModel {
  if (
    !isRecord(value) ||
    value.schema !== FINANCIAL_FACTOR_POOL_SCHEMA ||
    value.version !== 1 ||
    ![
      'poolId',
      'name',
      'runId',
      'protocolId',
      'datasetSnapshotId',
      'inputPath',
      'developmentSplitId',
      'validationSplitId',
      'lambdaSelectionSplitId',
    ].every((key) => typeof value[key] === 'string' && Boolean(String(value[key]).trim())) ||
    !Array.isArray(value.weightFitSplitIds) ||
    value.weightFitSplitIds.length < 1 ||
    !value.weightFitSplitIds.every((splitId) => typeof splitId === 'string' && Boolean(splitId.trim())) ||
    value.lambdaSelectionSplitId !== value.validationSplitId ||
    !value.weightFitSplitIds.includes(value.developmentSplitId) ||
    !value.weightFitSplitIds.includes(value.validationSplitId) ||
    typeof value.datasetContentSha256 !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(value.datasetContentSha256) ||
    !isFinancialFactorPoolPolicy(value.policy) ||
    !Array.isArray(value.candidateDecisions) ||
    !Array.isArray(value.selectedFactors) ||
    value.selectedFactors.length < 1 ||
    value.selectedFactors.length > value.policy.maxFactors ||
    !isRecord(value.ridge) ||
    typeof value.ridge.lambda !== 'number' ||
    !Number.isFinite(value.ridge.lambda) ||
    !Array.isArray(value.ridge.scores) ||
    !isRecord(value.calibration) ||
    !Array.isArray(value.calibration.metrics) ||
    !Array.isArray(value.calibration.checks) ||
    !Array.isArray(value.calibration.warnings) ||
    !isRecord(value.fitBoundary) ||
    !isIsoLikeTimestamp(value.fitBoundary.developmentStart) ||
    !isIsoLikeTimestamp(value.fitBoundary.developmentEnd) ||
    !isIsoLikeTimestamp(value.fitBoundary.validationStart) ||
    !isIsoLikeTimestamp(value.fitBoundary.validationEnd) ||
    !isIsoLikeTimestamp(value.fitBoundary.developmentLastFitDate) ||
    !isIsoLikeTimestamp(value.fitBoundary.validationLastFitDate) ||
    Date.parse(value.fitBoundary.developmentStart) > Date.parse(value.fitBoundary.developmentEnd) ||
    Date.parse(value.fitBoundary.developmentEnd) >= Date.parse(value.fitBoundary.validationStart) ||
    Date.parse(value.fitBoundary.validationStart) > Date.parse(value.fitBoundary.validationEnd) ||
    Date.parse(value.fitBoundary.developmentLastFitDate) < Date.parse(value.fitBoundary.developmentStart) ||
    Date.parse(value.fitBoundary.developmentLastFitDate) > Date.parse(value.fitBoundary.developmentEnd) ||
    Date.parse(value.fitBoundary.validationLastFitDate) < Date.parse(value.fitBoundary.validationStart) ||
    Date.parse(value.fitBoundary.validationLastFitDate) > Date.parse(value.fitBoundary.validationEnd) ||
    value.fitBoundary.splitPurgeTradingDays !== value.policy.splitPurgeTradingDays ||
    value.fitBoundary.lockedTestUsed !== false ||
    typeof value.fitRequestHash !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(value.fitRequestHash) ||
    typeof value.modelHash !== 'string' ||
    !/^[a-f0-9]{64}$/u.test(value.modelHash) ||
    typeof value.createdAt !== 'number' ||
    !Number.isFinite(value.createdAt)
  )
    return false;
  const policy = value.policy as FinancialFactorPoolPolicy;
  const ridge = value.ridge as FinancialFactorPoolModel['ridge'];
  const calibration = value.calibration as FinancialFactorPoolModel['calibration'];
  const selectedFactors = value.selectedFactors as FinancialFactorPoolModel['selectedFactors'];
  const candidateIds = value.candidateDecisions.map((decision) =>
    isRecord(decision) && isRecord(decision.candidate) ? decision.candidate.id : undefined
  );
  const selectedIds = value.selectedFactors.map((selected) =>
    isRecord(selected) && isRecord(selected.candidate) ? selected.candidate.id : undefined
  );
  const selectedDecisions = new Map(
    value.candidateDecisions.flatMap(
      (decision): Array<[string, Record<string, unknown>]> =>
        isRecord(decision) &&
        decision.selected === true &&
        isRecord(decision.candidate) &&
        typeof decision.candidate.id === 'string'
          ? [[decision.candidate.id, decision]]
          : []
    )
  );
  return (
    new Set(candidateIds).size === candidateIds.length &&
    new Set(selectedIds).size === selectedIds.length &&
    selectedDecisions.size === value.selectedFactors.length &&
    value.candidateDecisions.every(
      (decision) =>
        isRecord(decision) &&
        isFinancialFactorPoolCandidateSpec(decision.candidate) &&
        isFinancialFactorPoolCandidateStatistics(decision.statistics) &&
        decision.statistics.foldIcs.length === policy.stabilityFolds &&
        typeof decision.selected === 'boolean' &&
        (decision.selectionOrder == null ||
          (typeof decision.selectionOrder === 'number' &&
            Number.isInteger(decision.selectionOrder) &&
            decision.selectionOrder >= 1 &&
            decision.selectionOrder <= policy.maxFactors)) &&
        (decision.selected
          ? decision.exclusionReason == null && decision.duplicateOf == null
          : FACTOR_POOL_EXCLUSION_REASONS.has(decision.exclusionReason as FinancialFactorPoolExclusionReason)) &&
        (decision.duplicateOf == null ||
          (decision.exclusionReason === 'duplicate_expression' && isNonEmptyString(decision.duplicateOf))) &&
        (decision.maximumSelectedCorrelation == null ||
          (typeof decision.maximumSelectedCorrelation === 'number' &&
            Number.isFinite(decision.maximumSelectedCorrelation) &&
            decision.maximumSelectedCorrelation >= 0 &&
            decision.maximumSelectedCorrelation <= 1)) &&
        ['incumbentDevelopmentIc', 'candidatePoolDevelopmentIc', 'marginalDevelopmentGain'].every(
          (key) =>
            decision[key] == null || (typeof decision[key] === 'number' && Number.isFinite(decision[key] as number))
        ) &&
        (decision.marginalDevelopmentFoldGains == null ||
          (Array.isArray(decision.marginalDevelopmentFoldGains) &&
            decision.marginalDevelopmentFoldGains.length === policy.stabilityFolds &&
            decision.marginalDevelopmentFoldGains.every(
              (gain) => typeof gain === 'number' && Number.isFinite(gain)
            ))) &&
        (decision.positiveMarginalFoldCount == null ||
          (typeof decision.positiveMarginalFoldCount === 'number' &&
            Number.isInteger(decision.positiveMarginalFoldCount) &&
            decision.positiveMarginalFoldCount >= 0 &&
            decision.positiveMarginalFoldCount <= policy.stabilityFolds))
    ) &&
    selectedFactors.every((selected) => {
      if (
        !isRecord(selected) ||
        !isFinancialFactorPoolCandidateSpec(selected.candidate) ||
        !isFinancialFactorPoolCandidateStatistics(selected.statistics) ||
        typeof selected.weight !== 'number' ||
        !Number.isFinite(selected.weight)
      )
        return false;
      const decision = selectedDecisions.get(selected.candidate.id);
      return (
        Boolean(decision) &&
        JSON.stringify(decision?.candidate) === JSON.stringify(selected.candidate) &&
        JSON.stringify(decision?.statistics) === JSON.stringify(selected.statistics)
      );
    }) &&
    Math.abs(selectedFactors.reduce((total, selected) => total + Math.abs(selected.weight), 0) - 1) < 1e-8 &&
    policy.ridgeLambdas.includes(ridge.lambda) &&
    ridge.scores.every(
      (score) =>
        isRecord(score) &&
        typeof score.lambda === 'number' &&
        Number.isFinite(score.lambda) &&
        (score.factorCount == null ||
          (typeof score.factorCount === 'number' &&
            Number.isInteger(score.factorCount) &&
            score.factorCount >= 1 &&
            score.factorCount <= policy.maxFactors)) &&
        typeof score.meanIc === 'number' &&
        Number.isFinite(score.meanIc) &&
        typeof score.worstFoldIc === 'number' &&
        Number.isFinite(score.worstFoldIc) &&
        Array.isArray(score.foldIcs) &&
        score.foldIcs.length > 0 &&
        score.foldIcs.length <= policy.stabilityFolds &&
        score.foldIcs.every((item) => typeof item === 'number' && Number.isFinite(item)) &&
        policy.ridgeLambdas.includes(score.lambda)
    ) &&
    (ridge.factorCount == null ||
      (Number.isInteger(ridge.factorCount) && ridge.factorCount === selectedFactors.length)) &&
    ridge.scores.some(
      (score) => score.lambda === ridge.lambda && (ridge.factorCount == null || score.factorCount === ridge.factorCount)
    ) &&
    calibration.metrics.every(isFinancialFactorSubmissionMetric) &&
    calibration.checks.every(isFinancialFactorCheck) &&
    calibration.warnings.every((warning) => typeof warning === 'string') &&
    (value.receiptId == null || isNonEmptyString(value.receiptId)) &&
    (value.receiptPath == null ||
      (typeof value.receiptPath === 'string' && isProjectRelativeEvaluationPath(value.receiptPath)))
  );
}

export const readFinancialFactorPoolModel = (value: unknown): FinancialFactorPoolModel | undefined =>
  isFinancialFactorPoolModel(value) ? value : undefined;

const isFinancialFactorValidationCandidateResult = (
  value: unknown
): value is FinancialFactorValidationCandidateResult =>
  isRecord(value) &&
  isFinancialFactorPoolCandidateSpec(value.candidate) &&
  isNonEmptyString(value.evaluationId) &&
  ['succeeded', 'partial', 'failed'].includes(String(value.status)) &&
  isRecord(value.lineage) &&
  isNonEmptyString(value.lineage.transitionId) &&
  typeof value.lineage.sequence === 'number' &&
  Number.isInteger(value.lineage.sequence) &&
  value.lineage.sequence >= 1 &&
  ['NEW', 'IMPROVE', 'COMBINE', 'PIVOT'].includes(String(value.lineage.kind)) &&
  ['positive', 'mixed'].includes(String(value.lineage.assessment)) &&
  Array.isArray(value.lineage.parentCandidateIds) &&
  value.lineage.parentCandidateIds.every(isNonEmptyString) &&
  isNonEmptyString(value.lineage.mechanismFamily) &&
  (value.lineage.researchContext == null || isFinancialFactorResearchContext(value.lineage.researchContext)) &&
  isRecord(value.lineage.sourceDelivery) &&
  isNonEmptyString(value.lineage.sourceDelivery.branch) &&
  typeof value.lineage.sourceDelivery.headCommit === 'string' &&
  /^[a-f0-9]{7,64}$/iu.test(value.lineage.sourceDelivery.headCommit) &&
  (value.lineage.sourceDelivery.agentId == null || isNonEmptyString(value.lineage.sourceDelivery.agentId)) &&
  (value.lineage.sourceDelivery.taskId == null || isNonEmptyString(value.lineage.sourceDelivery.taskId)) &&
  Number(Array.isArray(value.lineage.developmentEvidenceIds)) +
    Number(Array.isArray(value.lineage.feedbackEvidenceIds)) ===
    1 &&
  (Array.isArray(value.lineage.developmentEvidenceIds)
    ? value.lineage.developmentEvidenceIds.length > 0 && value.lineage.developmentEvidenceIds.every(isNonEmptyString)
    : Array.isArray(value.lineage.feedbackEvidenceIds) &&
      value.lineage.feedbackEvidenceIds.length > 0 &&
      value.lineage.feedbackEvidenceIds.every(isNonEmptyString)) &&
  Array.isArray(value.metrics) &&
  value.metrics.every(isFinancialFactorSubmissionMetric) &&
  Array.isArray(value.checks) &&
  value.checks.every(isFinancialFactorCheck) &&
  Array.isArray(value.warnings) &&
  value.warnings.every((warning) => typeof warning === 'string') &&
  (value.timeSeries == null || isFinancialFactorTimeSeries(value.timeSeries)) &&
  (value.error == null || isNonEmptyString(value.error));

export const isFinancialFactorValidationBundle = (value: unknown): value is FinancialFactorValidationBundle =>
  isRecord(value) &&
  value.schema === FINANCIAL_FACTOR_VALIDATION_SCHEMA &&
  value.version === 1 &&
  ['validationId', 'campaignId', 'runId', 'protocolId', 'splitId', 'datasetSnapshotId', 'inputPath'].every((key) =>
    isNonEmptyString(value[key])
  ) &&
  value.searchClosed === true &&
  typeof value.datasetContentSha256 === 'string' &&
  /^[a-f0-9]{64}$/u.test(value.datasetContentSha256) &&
  typeof value.trajectoryHash === 'string' &&
  /^[a-f0-9]{64}$/u.test(value.trajectoryHash) &&
  typeof value.requestHash === 'string' &&
  /^[a-f0-9]{64}$/u.test(value.requestHash) &&
  typeof value.resultHash === 'string' &&
  /^[a-f0-9]{64}$/u.test(value.resultHash) &&
  Array.isArray(value.candidates) &&
  value.candidates.length >= 1 &&
  value.candidates.length <= 3 &&
  value.candidates.every(isFinancialFactorValidationCandidateResult) &&
  new Set(value.candidates.map((candidate) => candidate.candidate.id)).size === value.candidates.length &&
  (value.receiptId == null || isNonEmptyString(value.receiptId)) &&
  (value.receiptPath == null ||
    (typeof value.receiptPath === 'string' && isProjectRelativeEvaluationPath(value.receiptPath))) &&
  typeof value.createdAt === 'number' &&
  Number.isFinite(value.createdAt);

export const readFinancialFactorValidationBundle = (value: unknown): FinancialFactorValidationBundle | undefined =>
  isFinancialFactorValidationBundle(value) ? value : undefined;

const mean = (values: number[]): number | undefined =>
  values.length ? values.reduce((total, value) => total + value, 0) / values.length : undefined;

const standardDeviation = (values: number[]): number | undefined => {
  if (values.length < 2) return undefined;
  const average = mean(values);
  if (average == null) return undefined;
  return Math.sqrt(values.reduce((total, value) => total + (value - average) ** 2, 0) / (values.length - 1));
};

const pearson = (left: number[], right: number[]): number | undefined => {
  if (left.length !== right.length || left.length < 2) return undefined;
  const leftMean = mean(left);
  const rightMean = mean(right);
  if (leftMean == null || rightMean == null) return undefined;
  let covariance = 0;
  let leftVariance = 0;
  let rightVariance = 0;
  for (let index = 0; index < left.length; index += 1) {
    const leftDelta = left[index] - leftMean;
    const rightDelta = right[index] - rightMean;
    covariance += leftDelta * rightDelta;
    leftVariance += leftDelta ** 2;
    rightVariance += rightDelta ** 2;
  }
  if (leftVariance === 0 || rightVariance === 0) return undefined;
  return covariance / Math.sqrt(leftVariance * rightVariance);
};

const ranks = (values: number[]): number[] => {
  const indexed = values.map((value, index) => ({ value, index })).toSorted((a, b) => a.value - b.value);
  const result = Array<number>(values.length);
  for (let start = 0; start < indexed.length; ) {
    let end = start + 1;
    while (end < indexed.length && indexed[end].value === indexed[start].value) end += 1;
    const rank = (start + end - 1) / 2 + 1;
    for (let index = start; index < end; index += 1) result[indexed[index].index] = rank;
    start = end;
  }
  return result;
};

export const evaluateFinancialFactorRows = (input: {
  evaluationId: string;
  factorId: string;
  protocol: FinancialFactorEvaluationProtocol;
  splitId: string;
  rows: FinancialFactorEvaluationRow[];
  generatedAt: number;
}): FinancialFactorEvaluationSummary => {
  const split = input.protocol.splits.find((item) => item.id === input.splitId);
  if (!split) throw new Error(`Unknown evaluation split: ${input.splitId}.`);
  const splitStart = Date.parse(split.start);
  const splitEnd = Date.parse(split.end);
  const scopedRows = input.rows.filter((row) => {
    const timestamp = Date.parse(row.date);
    return Number.isFinite(timestamp) && timestamp >= splitStart && timestamp <= splitEnd;
  });
  const rowsByDate = new Map<string, FinancialFactorEvaluationRow[]>();
  scopedRows.forEach((row) => rowsByDate.set(row.date, [...(rowsByDate.get(row.date) || []), row]));
  const dates = [...rowsByDate.keys()].toSorted((left, right) => Date.parse(left) - Date.parse(right));
  const icPoints: Array<[string, number]> = [];
  const rankIcPoints: Array<[string, number]> = [];
  const turnoverPoints: Array<[string, number]> = [];
  const coveragePoints: Array<[string, number]> = [];
  const spreadReturns: Array<[string, number]> = [];
  let previousTopAssets = new Set<string>();

  dates.forEach((date) => {
    const rows = rowsByDate.get(date) || [];
    const labelEligible = rows.filter((row): row is FinancialFactorEvaluationRow & { futureReturn: number } =>
      Number.isFinite(row.futureReturn)
    );
    const valid = labelEligible.filter(
      (row): row is FinancialFactorEvaluationRow & { factorValue: number; futureReturn: number } =>
        Number.isFinite(row.factorValue)
    );
    // A purged split tail has no eligible forward labels. It is outside the
    // predictive evaluation surface and must not turn otherwise valid factor
    // coverage into zero.
    if (labelEligible.length) coveragePoints.push([date, valid.length / labelEligible.length]);
    if (valid.length < 2) return;
    const factorValues = valid.map((row) => row.factorValue);
    const futureReturns = valid.map((row) => row.futureReturn);
    const ic = pearson(factorValues, futureReturns);
    const rankIc = pearson(ranks(factorValues), ranks(futureReturns));
    if (ic != null) icPoints.push([date, ic]);
    if (rankIc != null) rankIcPoints.push([date, rankIc]);
    const ordered = [...valid].toSorted((left, right) => left.factorValue - right.factorValue);
    const bucketSize = Math.max(1, Math.floor(ordered.length / input.protocol.evaluation.quantiles));
    const bottom = ordered.slice(0, bucketSize);
    const top = ordered.slice(-bucketSize);
    const topReturn = mean(top.map((row) => row.futureReturn));
    const bottomReturn = mean(bottom.map((row) => row.futureReturn));
    if (topReturn != null && bottomReturn != null) spreadReturns.push([date, topReturn - bottomReturn]);
    const topAssets = new Set(top.map((row) => row.asset));
    if (previousTopAssets.size) {
      const retained = [...topAssets].filter((asset) => previousTopAssets.has(asset)).length;
      turnoverPoints.push([date, 1 - retained / Math.max(1, topAssets.size)]);
    }
    previousTopAssets = topAssets;
  });

  let wealth = 1;
  let peak = 1;
  let maximumDrawdown = 0;
  const cumulativePoints: Array<[string, number]> = [];
  const netReturns: number[] = [];
  // Turnover starts on the first rebalance date, which is not necessarily the
  // first spread date (the initial portfolio has no prior holdings).  Align by
  // the actual trading date instead of relying on array indexes; the latter
  // silently charged the next day's turnover to the previous day's return.
  const turnoverByDate = new Map(turnoverPoints);
  spreadReturns.forEach(([date, grossReturn]) => {
    const turnover = turnoverByDate.get(date) || 0;
    const netReturn = grossReturn - turnover * (input.protocol.evaluation.costBps / 10_000);
    netReturns.push(netReturn);
    wealth *= Math.max(0, 1 + netReturn);
    peak = Math.max(peak, wealth);
    maximumDrawdown = Math.min(maximumDrawdown, wealth / peak - 1);
    cumulativePoints.push([date, (wealth - 1) * 100]);
  });

  const evidenceId = `evaluation:${input.evaluationId}`;
  const icValues = icPoints.map((point) => point[1]);
  const rankIcValues = rankIcPoints.map((point) => point[1]);
  const averageIc = mean(icValues);
  const averageRankIc = mean(rankIcValues);
  const icDeviation = standardDeviation(icValues);
  const rankIcDeviation = standardDeviation(rankIcValues);
  const netMean = mean(netReturns);
  const netDeviation = standardDeviation(netReturns);
  const annualization = input.protocol.evaluation.annualizationFactor;
  const annualizedReturn =
    cumulativePoints.length && wealth > 0 ? wealth ** (annualization / cumulativePoints.length) - 1 : undefined;
  const metrics = [
    ...measuredFinancialFactorMetric('IC', averageIc),
    ...measuredFinancialFactorMetric('RankIC', averageRankIc),
    ...measuredFinancialFactorMetric(
      'ICIR',
      averageIc != null && icDeviation ? (averageIc / icDeviation) * Math.sqrt(annualization) : undefined
    ),
    ...measuredFinancialFactorMetric(
      'RankICIR',
      averageRankIc != null && rankIcDeviation
        ? (averageRankIc / rankIcDeviation) * Math.sqrt(annualization)
        : undefined
    ),
    ...measuredFinancialFactorMetric('Annualized return', annualizedReturn == null ? undefined : annualizedReturn * 100, 'percent'),
    ...measuredFinancialFactorMetric(
      'Sharpe',
      netMean != null && netDeviation ? (netMean / netDeviation) * Math.sqrt(annualization) : undefined
    ),
    ...measuredFinancialFactorMetric('Maximum drawdown', maximumDrawdown * 100, 'percent'),
    ...measuredFinancialFactorMetric('Average turnover', mean(turnoverPoints.map((point) => point[1])), 'ratio'),
    ...measuredFinancialFactorMetric(
      'Minimum coverage',
      coveragePoints.length ? Math.min(...coveragePoints.map((point) => point[1])) : undefined,
      'ratio'
    ),
  ];
  const minimumCoverage = coveragePoints.length ? Math.min(...coveragePoints.map((point) => point[1])) : 0;
  const materializedSignalRows = scopedRows.filter((row) => Number.isFinite(row.factorValue));
  const availabilityAudit = input.protocol.columns.availableAt
    ? (() => {
        const invalidRows = materializedSignalRows.filter((row) => {
          if (!row.availableAt) return true;
          const availableTimestamp = Date.parse(row.availableAt);
          const signalTimestamp = Date.parse(row.date);
          return (
            !Number.isFinite(availableTimestamp) ||
            !Number.isFinite(signalTimestamp) ||
            availableTimestamp > signalTimestamp
          );
        });
        const passed = materializedSignalRows.length > 0 && invalidRows.length === 0;
        return {
          id: 'future_leakage_audit',
          label: 'Materialized signal as-of audit',
          status: passed ? ('passed' as const) : ('failed' as const),
          value: `${materializedSignalRows.length - invalidRows.length}/${materializedSignalRows.length} rows available by signal time`,
          threshold: 'all materialized signal rows',
          detail:
            'Checks only the materialized signal-row availability timestamp against its signal timestamp. It does not prove complete announcement, revision, lag, or upstream field lineage.',
          evidenceIds: [evidenceId],
        };
      })()
    : {
        id: 'future_leakage_audit',
        label: 'Materialized signal as-of audit',
        status: 'not_run' as const,
        detail:
          'The protocol has no availableAt column. Table evaluation cannot prove point-in-time availability without row-level availability metadata.',
      };
  const warnings: string[] = [];
  if (!scopedRows.length) warnings.push('No rows fall inside the selected evaluation split.');
  if (!rankIcPoints.length) warnings.push('RankIC is unavailable because no date has enough finite observations.');
  if (minimumCoverage < input.protocol.evaluation.minimumCoverage) {
    warnings.push('Observed coverage is below the frozen protocol threshold.');
  }
  if (availabilityAudit.status === 'failed') {
    warnings.push('Materialized signal availability is missing, invalid, or later than the signal timestamp.');
  }
  const checks: FinancialFactorCheck[] = [
    {
      id: 'data_coverage',
      label: 'Data coverage',
      status: minimumCoverage >= input.protocol.evaluation.minimumCoverage ? 'passed' : 'failed',
      value: minimumCoverage,
      threshold: input.protocol.evaluation.minimumCoverage,
      evidenceIds: [evidenceId],
    },
    {
      id: 'frozen_protocol',
      label: 'Frozen evaluation protocol',
      status: input.protocol.status === 'frozen' ? 'passed' : 'warning',
      detail: input.protocol.status === 'frozen' ? undefined : 'The evaluation protocol was not frozen.',
      evidenceIds: [evidenceId],
    },
    availabilityAudit,
  ];
  const series: FinancialFactorTimeSeriesItem[] = [
    ...(cumulativePoints.length
      ? [
          {
            id: input.factorId,
            label: input.factorId,
            kind: 'cumulative_pnl' as const,
            unit: 'percent',
            points: cumulativePoints,
          },
        ]
      : []),
    ...(rankIcPoints.length
      ? [{ id: `${input.factorId}-rank-ic`, label: 'RankIC', kind: 'rank_ic' as const, points: rankIcPoints }]
      : []),
    ...(turnoverPoints.length
      ? [
          {
            id: `${input.factorId}-turnover`,
            label: 'Turnover',
            kind: 'turnover' as const,
            unit: 'ratio',
            points: turnoverPoints,
          },
        ]
      : []),
    ...(coveragePoints.length
      ? [
          {
            id: `${input.factorId}-coverage`,
            label: 'Coverage',
            kind: 'coverage' as const,
            unit: 'ratio',
            points: coveragePoints,
          },
        ]
      : []),
  ];
  const timeSeries: FinancialFactorTimeSeries | undefined = series.length
    ? {
        schema: FINANCIAL_FACTOR_TIMESERIES_SCHEMA,
        version: 1,
        factorId: input.factorId,
        runId: input.evaluationId,
        contractId: input.protocol.protocolId,
        evaluationId: input.evaluationId,
        frequency: input.protocol.evaluation.frequency,
        generatedAt: input.generatedAt,
        periods: [
          {
            kind: split.role === 'locked_test' ? 'oos' : split.role === 'development' ? 'is' : 'oos',
            label: split.id,
            start: split.start,
            end: split.end,
          },
        ],
        series,
      }
    : undefined;
  return { metrics, checks, warnings, ...(timeSeries ? { timeSeries } : {}) };
};

export function isFinancialFactorPortfolio(value: unknown): value is FinancialFactorPortfolio {
  if (!isRecord(value) || value.schema !== FINANCIAL_FACTOR_PORTFOLIO_SCHEMA || value.version !== 1) return false;
  if (
    typeof value.title !== 'string' ||
    !value.title.trim() ||
    !FACTOR_STAGES.has(value.stage as FinancialFactorStage) ||
    !FACTOR_PORTFOLIO_STATUSES.has(value.status as FinancialFactorPortfolioStatus) ||
    typeof value.updatedAt !== 'number' ||
    !Number.isFinite(value.updatedAt) ||
    !isRecord(value.context) ||
    typeof value.context.objective !== 'string' ||
    !['manual', 'continuous'].includes(String(value.context.executionMode)) ||
    !['verify_only', 'submit_qualified'].includes(String(value.context.automationPolicy))
  )
    return false;
  return (
    Array.isArray(value.batches) &&
    Array.isArray(value.factors) &&
    value.factors.every(isFinancialFactorCandidate) &&
    Array.isArray(value.blockers) &&
    Array.isArray(value.nextActions)
  );
}

export function readFinancialFactorPortfolio(metadata: unknown): FinancialFactorPortfolio | undefined {
  if (!isRecord(metadata)) return undefined;
  const direct = metadata.financialFactor;
  if (isFinancialFactorPortfolio(direct)) return direct;
  return isFinancialFactorPortfolio(metadata) ? metadata : undefined;
}

const submissionStatusValues = new Set<FinancialFactorResearchSubmissionStatus>(['complete', 'partial', 'blocked']);
const roleKindValues = new Set<FinancialFactorResearchSubmissionRole['kind']>(['xalpha', 'generic']);
const roleStatusValues = new Set<FinancialFactorResearchSubmissionRole['status']>([
  'planned',
  'running',
  'completed',
  'blocked',
]);

const boundedText = (value: unknown, fallback = ''): string =>
  typeof value === 'string' && value.trim() ? value.trim().slice(0, 1000) : fallback;

const isFinancialFactorResearchEvaluationRef = (value: unknown): value is FinancialFactorResearchEvaluationRef =>
  isRecord(value) &&
  Boolean(boundedText(value.evaluationId)) &&
  ['attested', 'recorded', 'missing'].includes(String(value.status)) &&
  Array.isArray(value.warnings) &&
  value.warnings.every((warning) => typeof warning === 'string');

export function isFinancialFactorResearchSubmission(value: unknown): value is FinancialFactorResearchSubmission {
  if (!isRecord(value) || value.schema !== FINANCIAL_FACTOR_SUBMISSION_SCHEMA || value.version !== 1) return false;
  if (
    !boundedText(value.submissionId) ||
    !boundedText(value.title) ||
    !boundedText(value.objective) ||
    !submissionStatusValues.has(value.status as FinancialFactorResearchSubmissionStatus) ||
    typeof value.createdAt !== 'number' ||
    !Number.isFinite(value.createdAt) ||
    typeof value.updatedAt !== 'number' ||
    !Number.isFinite(value.updatedAt) ||
    !Array.isArray(value.roles) ||
    !Array.isArray(value.metrics) ||
    !Array.isArray(value.artifacts) ||
    !Array.isArray(value.limitations) ||
    !Array.isArray(value.nextActions) ||
    !Array.isArray(value.sourceRefs)
  )
    return false;
  return (
    value.roles.every(
      (role) =>
        isRecord(role) &&
        Boolean(boundedText(role.id)) &&
        Boolean(boundedText(role.label)) &&
        roleKindValues.has(role.kind as FinancialFactorResearchSubmissionRole['kind']) &&
        roleStatusValues.has(role.status as FinancialFactorResearchSubmissionRole['status'])
    ) &&
    value.metrics.every(
      (metric) =>
        isRecord(metric) &&
        Boolean(boundedText(metric.name)) &&
        (metric.value == null || (typeof metric.value === 'number' && Number.isFinite(metric.value)))
    ) &&
    value.artifacts.every(
      (artifact) =>
        isRecord(artifact) &&
        Boolean(boundedText(artifact.id)) &&
        Boolean(boundedText(artifact.label)) &&
        ['chart', 'table', 'code', 'data', 'report', 'other'].includes(String(artifact.kind))
    ) &&
    value.limitations.every((item) => typeof item === 'string') &&
    value.nextActions.every((item) => typeof item === 'string') &&
    value.sourceRefs.every((item) => typeof item === 'string') &&
    (value.evaluationId == null || Boolean(boundedText(value.evaluationId))) &&
    (value.evaluation == null || isFinancialFactorResearchEvaluationRef(value.evaluation))
  );
}

export function readFinancialFactorResearchSubmission(value: unknown): FinancialFactorResearchSubmission | undefined {
  if (!isRecord(value)) return undefined;
  const candidate = value.financialFactorSubmission ?? value.submission ?? value;
  return isFinancialFactorResearchSubmission(candidate) ? candidate : undefined;
}

export function readFinancialFactorResearchSubmissionBundle(
  value: unknown
): FinancialFactorResearchSubmissionBundle | undefined {
  if (!isRecord(value) || value.schema !== FINANCIAL_FACTOR_SUBMISSION_SCHEMA || value.version !== 1) return undefined;
  if (
    typeof value.updatedAt !== 'number' ||
    !Number.isFinite(value.updatedAt) ||
    !Array.isArray(value.submissions) ||
    !value.submissions.every(isFinancialFactorResearchSubmission)
  )
    return undefined;
  return value as unknown as FinancialFactorResearchSubmissionBundle;
}

const optionalString = (value: unknown): string | undefined =>
  typeof value === 'string' && value.trim() ? value.trim() : undefined;

const readLegacyCheck = (value: unknown, index: number): LegacyFinancialFactorCheck | undefined => {
  if (!isRecord(value)) return undefined;
  const label = optionalString(value.label) || optionalString(value.name) || optionalString(value.id);
  if (!label) return undefined;
  const rawValue = value.value;
  return {
    id: optionalString(value.id) || optionalString(value.name) || `legacy-check-${index + 1}`,
    label,
    status: optionalString(value.status) || 'unknown',
    ...(typeof rawValue === 'number' || typeof rawValue === 'string' ? { value: rawValue } : {}),
  };
};

const readLegacyCandidate = (value: unknown): LegacyFinancialFactorCandidate | undefined => {
  if (!isRecord(value)) return undefined;
  const id = optionalString(value.id);
  if (!id) return undefined;
  const rawChecks = Array.isArray(value.checks) ? value.checks : [];
  const rawEvidenceIds = Array.isArray(value.evidenceIds)
    ? value.evidenceIds
    : Array.isArray(value.evidence_ids)
      ? value.evidence_ids
      : [];
  return {
    id,
    name: optionalString(value.name),
    expression: optionalString(value.expression) || optionalString(value.formula),
    family: optionalString(value.family),
    hypothesis: optionalString(value.hypothesis) || optionalString(value.mechanism_hypothesis),
    selectionReason: optionalString(value.selectionReason) || optionalString(value.selection_reason),
    decisionReason: optionalString(value.decisionReason) || optionalString(value.decision_reason),
    status: optionalString(value.status),
    checks: rawChecks
      .map((check, index) => readLegacyCheck(check, index))
      .filter((check): check is LegacyFinancialFactorCheck => Boolean(check)),
    evidenceIds: rawEvidenceIds.filter((item): item is string => typeof item === 'string' && Boolean(item.trim())),
  };
};

export function readLegacyFinancialFactorPortfolio(metadata: unknown): LegacyFinancialFactorPortfolio | undefined {
  if (!isRecord(metadata)) return undefined;
  const direct = isRecord(metadata.financialFactorLegacy) ? metadata.financialFactorLegacy : metadata;
  if (direct.schema !== LEGACY_FINANCIAL_FACTOR_PORTFOLIO_SCHEMA || !Array.isArray(direct.factors)) return undefined;
  const factors = direct.factors
    .map(readLegacyCandidate)
    .filter((factor): factor is LegacyFinancialFactorCandidate => Boolean(factor));
  if (!factors.length && direct.factors.length) return undefined;
  const universe = isRecord(direct.universe) ? direct.universe : undefined;
  const automationPolicy = optionalString(direct.automationPolicy) || optionalString(direct.automation_policy);
  return {
    schema: LEGACY_FINANCIAL_FACTOR_PORTFOLIO_SCHEMA,
    title: optionalString(direct.title) || 'Financial factor portfolio',
    portfolioId: optionalString(direct.portfolioId) || optionalString(direct.portfolio_id),
    scienceArtifactId: optionalString(direct.scienceArtifactId) || optionalString(direct.science_artifact_id),
    automationPolicy:
      automationPolicy === 'verify_only' || automationPolicy === 'submit_qualified' ? automationPolicy : undefined,
    market: optionalString(universe?.market) || optionalString(direct.market),
    universe: optionalString(universe?.index) || optionalString(universe?.universe),
    factors,
  };
}

export function summarizeFinancialFactorPortfolio(portfolio: FinancialFactorPortfolio): FinancialFactorProgressSummary {
  const currentBatch = portfolio.batches
    .toSorted((left, right) => right.updatedAt - left.updatedAt)
    .find((batch) => batch.status === 'running' || batch.status === 'planned');
  return {
    factorCount: portfolio.factors.length,
    pendingCount: portfolio.factors.filter((factor) =>
      ['idea', 'linted', 'simulated', 'submit_pending', 'hold'].includes(factor.status)
    ).length,
    qualifiedCount: portfolio.factors.filter((factor) => factor.status === 'qualified').length,
    promotionReadyCount: portfolio.factors.filter((factor) => evaluateFinancialFactorPromotion(factor).eligible).length,
    activeCount: portfolio.factors.filter((factor) => factor.status === 'active').length,
    rejectedCount: portfolio.factors.filter((factor) => ['rejected', 'failed'].includes(factor.status)).length,
    batchCount: portfolio.batches.length,
    blockerCount: portfolio.blockers.length,
    currentBatchLabel: currentBatch?.label,
  };
}

export function evaluateFinancialFactorPromotion(
  candidate: Pick<FinancialFactorCandidate, 'checks' | 'evidenceIds' | 'hypothesisCard'>
): FinancialFactorPromotionAssessment {
  const checksById = new Map<string, FinancialFactorCheck[]>();
  candidate.checks.forEach((check) => {
    checksById.set(check.id, [...(checksById.get(check.id) || []), check]);
  });
  const evidenceIds = new Set(candidate.evidenceIds);
  const missingCheckIds: FinancialFactorPromotionCheckId[] = [];
  const blockingCheckIds: FinancialFactorPromotionCheckId[] = [];
  const missingEvidenceCheckIds: FinancialFactorPromotionCheckId[] = [];
  let passedCount = 0;
  for (const id of FINANCIAL_FACTOR_PROMOTION_CHECK_IDS) {
    const matchingChecks = checksById.get(id) || [];
    const check = matchingChecks[0];
    if (!check || check.status === 'not_run') {
      missingCheckIds.push(id);
      continue;
    }
    if (matchingChecks.length !== 1 || check.status !== 'passed') {
      blockingCheckIds.push(id);
      continue;
    }
    const checkEvidenceIds = check.evidenceIds?.filter(isNonEmptyString) || [];
    if (!checkEvidenceIds.length || checkEvidenceIds.some((evidenceId) => !evidenceIds.has(evidenceId))) {
      missingEvidenceCheckIds.push(id);
      continue;
    }
    passedCount += 1;
  }
  const hypothesisCardComplete = isFinancialFactorHypothesisCard(candidate.hypothesisCard);
  const eligible = hypothesisCardComplete && passedCount === FINANCIAL_FACTOR_PROMOTION_CHECK_IDS.length;
  return {
    status: eligible ? 'eligible' : blockingCheckIds.length || missingEvidenceCheckIds.length ? 'blocked' : 'not_ready',
    eligible,
    hypothesisCardComplete,
    passedCount,
    requiredCount: FINANCIAL_FACTOR_PROMOTION_CHECK_IDS.length,
    missingCheckIds,
    blockingCheckIds,
    missingEvidenceCheckIds,
  };
}

const financialFactorPromotionLevel = (candidate: FinancialFactorCandidate): number => {
  const statusLevel =
    candidate.status === 'active'
      ? 3
      : candidate.status === 'submit_pending'
        ? 2
        : candidate.status === 'qualified'
          ? 1
          : 0;
  const lifecycleLevel =
    candidate.lifecycle === 'production'
      ? 3
      : candidate.lifecycle === 'paper' || candidate.lifecycle === 'shadow'
        ? 2
        : candidate.lifecycle === 'qualified'
          ? 1
          : 0;
  const submissionLevel =
    candidate.submission?.status === 'active'
      ? 3
      : candidate.submission && ['submitted', 'verifying'].includes(candidate.submission.status)
        ? 2
        : candidate.submission?.status === 'queued'
          ? 1
          : 0;
  return Math.max(statusLevel, lifecycleLevel, submissionLevel);
};

export function inspectFinancialFactorPromotionMutation(
  next: FinancialFactorPortfolio,
  previous?: FinancialFactorPortfolio
): FinancialFactorPromotionMutationIssue[] {
  const previousById = new Map(previous?.factors.map((candidate) => [candidate.id, candidate]) || []);
  return next.factors.flatMap((candidate): FinancialFactorPromotionMutationIssue[] => {
    const nextLevel = financialFactorPromotionLevel(candidate);
    const previousLevel = previousById.has(candidate.id)
      ? financialFactorPromotionLevel(previousById.get(candidate.id) as FinancialFactorCandidate)
      : 0;
    if (nextLevel === 0 || nextLevel <= previousLevel) return [];
    const assessment = evaluateFinancialFactorPromotion(candidate);
    if (assessment.eligible) return [];
    return [
      {
        factorId: candidate.id,
        code: 'promotion_contract_incomplete',
        message: `Factor ${candidate.id} cannot advance until its Hypothesis Card Lite and all named promotion checks have traceable evidence receipts.`,
        assessment,
      },
    ];
  });
}

export function assertFinancialFactorPromotionMutation(
  next: FinancialFactorPortfolio,
  previous?: FinancialFactorPortfolio
): void {
  const issues = inspectFinancialFactorPromotionMutation(next, previous);
  if (!issues.length) return;
  const issue = issues[0];
  throw new Error(`${issue.message} Search score is ranking evidence only and cannot satisfy promotion eligibility.`);
}

export function partitionFinancialFactorChecks(checks: readonly FinancialFactorCheck[]): {
  promotion: FinancialFactorCheck[];
  search: FinancialFactorCheck[];
} {
  const promotion = checks.filter((check) => PROMOTION_CHECK_ID_SET.has(check.id));
  const search = checks.filter((check) => !PROMOTION_CHECK_ID_SET.has(check.id));
  return { promotion, search };
}

export type FinancialFactorExportPortfolio = FinancialFactorPortfolio | LegacyFinancialFactorPortfolio;

export const resolveFinancialFactorSubmission = (factor: FinancialFactorCandidate): FinancialFactorSubmission => {
  if (factor.submission) return factor.submission;
  const normalizedStatus = factor.externalStatus?.trim().toLocaleLowerCase();
  const status: FinancialFactorSubmissionStatus =
    normalizedStatus === 'active'
      ? 'active'
      : normalizedStatus === 'rejected'
        ? 'rejected'
        : normalizedStatus === 'failed' || normalizedStatus === 'error'
          ? 'failed'
          : normalizedStatus === 'verifying' || normalizedStatus === 'pending_verification'
            ? 'verifying'
            : factor.externalId || normalizedStatus === 'submitted' || normalizedStatus === 'pending'
              ? 'submitted'
              : 'not_submitted';
  return {
    status,
    ...(factor.externalId ? { externalId: factor.externalId } : {}),
    ...(factor.verifiedAt == null ? {} : { verifiedAt: factor.verifiedAt }),
    updatedAt: factor.verifiedAt ?? factor.updatedAt,
  };
};

/** Creates an export-only view without mutating the canonical factor registry portfolio. */
export const selectFinancialFactorExportPortfolio = (
  portfolio: FinancialFactorExportPortfolio,
  factorIds?: readonly string[]
): FinancialFactorExportPortfolio => {
  if (!factorIds) return portfolio;
  const selectedIds = new Set(factorIds);
  if (portfolio.schema === LEGACY_FINANCIAL_FACTOR_PORTFOLIO_SCHEMA) {
    return { ...portfolio, factors: portfolio.factors.filter((factor) => selectedIds.has(factor.id)) };
  }
  return {
    ...portfolio,
    factors: portfolio.factors.filter((factor) => selectedIds.has(factor.id)),
    batches: portfolio.batches
      .map((batch) => ({ ...batch, factorIds: batch.factorIds.filter((factorId) => selectedIds.has(factorId)) }))
      .filter((batch) => batch.factorIds.length > 0),
  };
};

const financialFactorCsvCell = (value: unknown): string => `"${String(value ?? '').replaceAll('"', '""')}"`;

export const buildFinancialFactorExportFileStem = (title: string): string => {
  const normalized = title
    .normalize('NFKC')
    .replace(/[^a-z0-9\u4e00-\u9fff_-]+/giu, '-')
    .replace(/^-+|-+$/gu, '');
  return normalized || 'financial-factors';
};

/** Lossless project export. External platform submission remains a separate, one-factor action. */
export const buildFinancialFactorExportJson = (portfolio: FinancialFactorExportPortfolio): string =>
  `${JSON.stringify(portfolio, null, 2)}\n`;

/** Flat spreadsheet export for reviewing and comparing every registered factor. */
export const buildFinancialFactorExportCsv = (portfolio: FinancialFactorExportPortfolio): string => {
  const header = [
    'id',
    'name',
    'status',
    'family',
    'expression',
    'hypothesis',
    'selection_reason',
    'decision_reason',
    'metric_contract_id',
    'evaluation_id',
    'evaluation_code',
    'metrics',
    'checks',
    'evidence_ids',
    'external_id',
    'external_status',
    'lifecycle',
    'submitted_at',
    'verified_at',
    'receipt_hash',
    'submission_error',
    'updated_at',
  ];
  const rows = portfolio.factors.map((factor) => {
    const registered = 'updatedAt' in factor ? factor : undefined;
    const submission = registered ? resolveFinancialFactorSubmission(registered) : undefined;
    return [
      factor.id,
      factor.name,
      factor.status,
      factor.family,
      factor.expression,
      factor.hypothesis,
      factor.selectionReason,
      factor.decisionReason,
      registered?.metricContext?.contractId,
      registered?.metricContext?.evaluationId,
      registered?.metricContext?.evaluationCode?.path,
      registered?.metrics?.map((metric) => `${metric.name}=${metric.value}${metric.unit || ''}`).join('; '),
      factor.checks
        .map((check) => `${check.label}=${check.status}${check.value == null ? '' : `:${check.value}`}`)
        .join('; '),
      factor.evidenceIds.join('; '),
      submission?.externalId,
      submission?.status,
      registered?.lifecycle,
      submission?.submittedAt ? new Date(submission.submittedAt).toISOString() : '',
      submission?.verifiedAt ? new Date(submission.verifiedAt).toISOString() : '',
      submission?.receiptHash,
      submission?.lastError,
      registered?.updatedAt ? new Date(registered.updatedAt).toISOString() : '',
    ];
  });
  return `\uFEFF${[header, ...rows].map((row) => row.map(financialFactorCsvCell).join(',')).join('\r\n')}\r\n`;
};

export const buildFinancialFactorModePrompt = (
  projectRoot?: string,
  _preferredLocale?: string,
  executionMode: FinancialFactorExecutionMode = 'manual',
  automationPolicy: FinancialFactorAutomationPolicy = 'verify_only'
): string => buildSharedFinancialFactorModePrompt(projectRoot, _preferredLocale, executionMode, automationPolicy);

export const isFinancialFactorConversationExtra = (
  extra: unknown
): extra is { financial_factor: FinancialFactorConversationExtra } => {
  if (!extra || typeof extra !== 'object' || Array.isArray(extra)) return false;
  const value = (extra as Record<string, unknown>).financial_factor;
  if (!value || typeof value !== 'object' || Array.isArray(value)) return false;
  const record = value as Partial<FinancialFactorConversationExtra> & Record<string, unknown>;
  return record.enabled === true && record.mode === FINANCIAL_FACTOR_MODE_ID;
};
