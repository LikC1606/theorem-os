/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

export const TARGET_DISCOVERY_MODE_ID = 'target_discovery' as const;
export const TARGET_DISCOVERY_SKILL_NAME = 'deepscientist-target-discovery' as const;
export const TARGET_DISCOVERY_PORTFOLIO_SCHEMA = 'deepscientist.target_discovery.portfolio.v1' as const;
export const TARGET_DISCOVERY_PORTFOLIO_ARTIFACT_ID = 'target_discovery_portfolio' as const;
export const TARGET_DISCOVERY_PORTFOLIO_PATH = 'target-discovery/portfolio.json' as const;
export const TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH = 'target-discovery/candidates.csv' as const;
export const TARGET_DISCOVERY_MECHANISM_MAP_PATH = 'target-discovery/mechanism-map.md' as const;
export const TARGET_DISCOVERY_IMPORT_RECEIPT_PATH = 'target-discovery/import-receipt.json' as const;
export const TARGET_DISCOVERY_IMPORT_RECEIPT_SCHEMA = 'deepscientist.target_discovery.import_receipt.v1' as const;

export type TargetDiscoveryStage =
  | 'intake'
  | 'data_audit'
  | 'branching'
  | 'screening'
  | 'triage'
  | 'validation_design'
  | 'complete';

export type TargetDiscoveryStatus = 'planning' | 'running' | 'needs_decision' | 'blocked' | 'complete';
export type TargetCandidateStatus = 'advance' | 'needs_evidence' | 'hold' | 'reject';
export type TargetEvidenceKind = 'computed' | 'parsed' | 'hypothesis';
export type TargetCandidateOrigin = 'computed' | 'parsed' | 'literature_seeded' | 'model_proposed' | 'control';
export type TargetDiscoveryGenerationLane =
  | 'human_genetics'
  | 'patient_state'
  | 'perturbation_inverse_design'
  | 'mechanistic_path'
  | 'understudied_space'
  | 'translational_control'
  | 'other';
export type TargetInnovationIntent =
  | 'de_novo_entity'
  | 'contextual_population'
  | 'incremental'
  | 'reproduction'
  | 'not_required';
export type TargetNoveltyDimension =
  | 'entity'
  | 'context'
  | 'mechanism'
  | 'modality'
  | 'population'
  | 'data'
  | 'validation';
export type TargetNoveltyLevel = 'known' | 'incremental' | 'possibly_novel' | 'not_checked';
export type TargetValidationKind =
  | 'internal'
  | 'temporal'
  | 'external'
  | 'orthogonal'
  | 'perturbational'
  | 'prospective'
  | 'negative_control';
export type TargetValidationStatus = 'passed' | 'mixed' | 'failed' | 'not_run';

export interface TargetEvidenceChannelScore {
  key: string;
  label: string;
  score: number;
  maxScore: number;
  evidenceKind: TargetEvidenceKind;
  evidenceIds: string[];
  rationale?: string;
  missing?: boolean;
}

export type TargetChannelEvidenceSupportState =
  | 'missing'
  | 'unlinked'
  | 'evidence_only'
  | 'validation_passed'
  | 'validation_mixed'
  | 'validation_failed';

export interface TargetChannelEvidenceSupport {
  state: TargetChannelEvidenceSupportState;
  evidenceCount: number;
  linkedValidationResults: TargetValidationResult[];
  completedValidationResults: TargetValidationResult[];
}

export interface TargetValidationStep {
  id: string;
  label: string;
  assay?: string;
  expectedSignal?: string;
  failureInterpretation?: string;
  status?: 'planned' | 'ready' | 'running' | 'passed' | 'failed';
}

export interface TargetExternalIdentifier {
  namespace: string;
  value: string;
  url?: string;
}

export interface TargetCandidateDetail {
  biologicalRationale?: string;
  mechanism?: string;
  diseaseContext?: string;
  tractability?: string;
  safety?: string;
  biomarkerStrategy?: string;
  translationalContext?: string;
  limitations?: string[];
}

export interface TargetValidationResult {
  id: string;
  kind: TargetValidationKind;
  dataset: string;
  version?: string;
  context?: string;
  split?: string;
  endpoint?: string;
  metric: string;
  value?: number | string;
  unit?: string;
  direction?: 'higher_better' | 'lower_better' | 'descriptive';
  comparator?: string;
  threshold?: number | string;
  sampleSize?: number | string;
  uncertainty?: string;
  pValue?: number;
  adjustedPValue?: number;
  status: TargetValidationStatus;
  interpretation?: string;
  limitations?: string[];
  evidenceIds: string[];
}

export interface TargetValidationSummary {
  headline?: string;
  conclusion?: string;
  passed?: number;
  mixed?: number;
  failed?: number;
  notRun?: number;
}

export interface TargetCandidateArtifactRef {
  artifactId: string;
  artifactVersion?: number;
  role: 'figure' | 'table' | 'dataset' | 'analysis' | 'structure' | 'other';
  label?: string;
  caption?: string;
  evidenceIds?: string[];
}

export interface TargetDiscoveryResearchPolicy {
  innovationIntent?: TargetInnovationIntent;
  innovationScope?: string;
  requiredNoveltyDimensions?: TargetNoveltyDimension[];
  directCollisionPolicy?: 'reject' | 'hold' | 'allow_as_comparator';
  clinicalProgramPolicy?: 'exclude_matching' | 'hold_matching' | 'allow_context';
  patientDataRequired?: boolean;
  individualExposureRequired?: boolean;
  independentValidationRequired?: boolean;
  independentAuditRequired?: boolean;
  minUniquePatients?: number;
  minIndependentCohorts?: number;
  minIndependentGenerationLanes?: number;
}

export interface TargetCandidateNoveltyReview {
  collisionStatus: 'not_checked' | 'direct_collision' | 'adjacent_collision' | 'no_direct_collision_found';
  clinicalProgramStatus: 'not_checked' | 'none_found' | 'direct_collision' | 'adjacent_collision';
  dimensions: Partial<Record<TargetNoveltyDimension, TargetNoveltyLevel>>;
  searchCutoffDate?: string;
  closestPrior?: string;
  closestPriorEvidenceIds?: string[];
}

export interface TargetCandidateGenerationRecord {
  lane: TargetDiscoveryGenerationLane;
  branchIds: string[];
  rationale: string;
  desiredState?: string;
  cheapTest: string;
  killCriterion: string;
}

export interface TargetCandidatePatientEvidence {
  analysisRunIds: string[];
  computedEvidenceIds: string[];
  uniquePatientCount: number;
  independentCohortCount: number;
  exposureMeasurement:
    | 'individual_measured'
    | 'individual_biomarker'
    | 'sample_proxy'
    | 'cohort_proxy'
    | 'geography_or_ancestry_proxy'
    | 'none';
  discoveryCohortIds: string[];
  validationCohortIds: string[];
}

export interface TargetCandidate {
  id: string;
  symbol: string;
  name?: string;
  aliases?: string[];
  identifiers?: TargetExternalIdentifier[];
  interventionDirection?: 'inhibit' | 'activate' | 'degrade' | 'replace' | 'unknown';
  proposedModality?: string;
  origin?: TargetCandidateOrigin;
  rank: number;
  priorityIndex: number;
  maxPriorityIndex: number;
  coverage: number;
  rankStability?: number;
  status: TargetCandidateStatus;
  summary?: string;
  detail?: TargetCandidateDetail;
  channelScores: TargetEvidenceChannelScore[];
  evidenceIds: string[];
  opposingEvidenceIds: string[];
  gaps: string[];
  validationPlan: TargetValidationStep[];
  validationResults?: TargetValidationResult[];
  validationSummary?: TargetValidationSummary;
  artifacts?: TargetCandidateArtifactRef[];
  noveltyReview?: TargetCandidateNoveltyReview;
  generation?: TargetCandidateGenerationRecord;
  patientEvidence?: TargetCandidatePatientEvidence;
  auditArtifactId?: string;
}

export interface TargetDiscoveryBranch {
  id: string;
  label: string;
  paradigm: string;
  generationLane?: TargetDiscoveryGenerationLane;
  mechanism?: string;
  desiredState?: string;
  falsifiableReadout?: string;
  required?: boolean;
  status: 'proposed' | 'screening' | 'active' | 'pruned' | 'complete';
  rationale?: string;
  proxyMetric?: string;
  score?: number;
  maxScore?: number;
  candidateIds: string[];
  evidenceIds: string[];
  pruneReason?: string;
}

export interface TargetSourceHealth {
  id: string;
  label: string;
  status: 'ready' | 'degraded' | 'blocked' | 'not_checked';
  detail?: string;
  checkedAt?: number;
  evidenceIds?: string[];
}

export interface TargetDiscoveryAction {
  id: string;
  label: string;
  kind: 'analysis' | 'decision' | 'data' | 'validation';
  priority: 'now' | 'next' | 'later';
  owner?: 'agent' | 'user' | 'collaborator';
}

export interface TargetDiscoveryPortfolio {
  schema: typeof TARGET_DISCOVERY_PORTFOLIO_SCHEMA;
  version: 1;
  title: string;
  stage: TargetDiscoveryStage;
  status: TargetDiscoveryStatus;
  updatedAt: number;
  context: {
    disease: string;
    phenotype?: string;
    organism: string;
    tissue?: string;
    population?: string;
    objective: string;
    projectRoot?: string;
    researchPolicy?: TargetDiscoveryResearchPolicy;
  };
  branches: TargetDiscoveryBranch[];
  candidates: TargetCandidate[];
  sourceHealth: TargetSourceHealth[];
  blockers: string[];
  nextActions: TargetDiscoveryAction[];
  scoringNote?: string;
}

export interface TargetDiscoveryProgressSummary {
  candidateCount: number;
  advanceCount: number;
  validationCount: number;
  blockerCount: number;
  sourceReadyCount: number;
  sourceCount: number;
  branchCount: number;
  coveredBranchCount?: number;
  requiredBranchCount?: number;
  unresolvedRequiredBranchCount?: number;
  generationLaneCount?: number;
  leadingCoverage?: number;
  topTargets: string[];
}

export interface TargetDiscoveryRankingQuality {
  candidateCount: number;
  uniqueRankCount: number;
  uniqueScoreCount: number;
  scoreUniquenessRatio: number;
  dominantScoreFraction: number;
  saturated: boolean;
}

export interface TargetDiscoveryIntegrityDiagnostic {
  severity: 'error' | 'warning';
  code:
    | 'stage_requires_candidates'
    | 'duplicate_candidate_id'
    | 'duplicate_rank'
    | 'invalid_candidate_score'
    | 'candidate_score_missing_evidence'
    | 'advance_missing_validation_evidence'
    | 'advance_high_computed_score_unverified'
    | 'unknown_branch_candidate'
    | 'unlinked_candidate'
    | 'low_score_discrimination'
    | 'advance_missing_novelty_review'
    | 'advance_novelty_collision'
    | 'advance_novelty_dimension_failed'
    | 'advance_clinical_program_collision'
    | 'advance_missing_patient_analysis'
    | 'advance_patient_threshold_failed'
    | 'advance_proxy_only_exposure'
    | 'advance_missing_independent_validation'
    | 'advance_missing_independent_audit'
    | 'advance_missing_generation_record'
    | 'advance_invalid_generation_branch'
    | 'generation_branch_membership_mismatch'
    | 'required_branch_unresolved'
    | 'insufficient_generation_diversity'
    | 'invalid_research_policy';
  message: string;
}

export interface TargetDiscoveryIntegrityReport {
  valid: boolean;
  quality: TargetDiscoveryRankingQuality;
  diagnostics: TargetDiscoveryIntegrityDiagnostic[];
}

export interface TargetDiscoveryImportReceipt {
  schema: typeof TARGET_DISCOVERY_IMPORT_RECEIPT_SCHEMA;
  sourcePath: typeof TARGET_DISCOVERY_CANDIDATE_REGISTRY_PATH;
  sourceSha256: string;
  importedAt: number;
  mode: 'merge' | 'replace';
  importedCandidateCount: number;
  portfolioCandidateCount: number;
  candidateIdsSha256: string;
}

export interface TargetDiscoveryConversationExtra {
  enabled: true;
  mode: typeof TARGET_DISCOVERY_MODE_ID;
  projectRoot?: string;
  schema: typeof TARGET_DISCOVERY_PORTFOLIO_SCHEMA;
  defaultSkill: typeof TARGET_DISCOVERY_SKILL_NAME;
}

export function buildInitialTargetDiscoveryPortfolio(input: {
  title: string;
  objective: string;
  nextActionLabel: string;
  scoringNote: string;
  projectRoot?: string;
  updatedAt: number;
}): TargetDiscoveryPortfolio {
  return {
    schema: TARGET_DISCOVERY_PORTFOLIO_SCHEMA,
    version: 1,
    title: input.title,
    stage: 'intake',
    status: 'planning',
    updatedAt: input.updatedAt,
    context: {
      disease: '',
      organism: 'Homo sapiens',
      objective: input.objective,
      projectRoot: input.projectRoot,
    },
    branches: [],
    candidates: [],
    sourceHealth: [],
    blockers: [],
    nextActions: [
      {
        id: 'initialize-target-discovery',
        label: input.nextActionLabel,
        kind: 'analysis',
        priority: 'now',
        owner: 'agent',
      },
    ],
    scoringNote: input.scoringNote,
  };
}

const isRecord = (value: unknown): value is Record<string, unknown> =>
  Boolean(value && typeof value === 'object' && !Array.isArray(value));

const TARGET_DISCOVERY_STAGES = new Set<TargetDiscoveryStage>([
  'intake',
  'data_audit',
  'branching',
  'screening',
  'triage',
  'validation_design',
  'complete',
]);
const TARGET_DISCOVERY_STATUSES = new Set<TargetDiscoveryStatus>([
  'planning',
  'running',
  'needs_decision',
  'blocked',
  'complete',
]);

const hasTargetDiscoveryPortfolioShape = (value: unknown): value is Record<string, unknown> => {
  if (!isRecord(value) || value.schema !== TARGET_DISCOVERY_PORTFOLIO_SCHEMA || value.version !== 1) return false;
  if (
    !isRecord(value.context) ||
    typeof value.title !== 'string' ||
    !value.title.trim() ||
    typeof value.updatedAt !== 'number' ||
    !Number.isFinite(value.updatedAt) ||
    !TARGET_DISCOVERY_STAGES.has(value.stage as TargetDiscoveryStage) ||
    !TARGET_DISCOVERY_STATUSES.has(value.status as TargetDiscoveryStatus) ||
    typeof value.context.disease !== 'string' ||
    typeof value.context.organism !== 'string' ||
    typeof value.context.objective !== 'string'
  )
    return false;
  return (
    Array.isArray(value.branches) &&
    Array.isArray(value.candidates) &&
    Array.isArray(value.sourceHealth) &&
    Array.isArray(value.blockers) &&
    Array.isArray(value.nextActions)
  );
};

const normalizeTargetDiscoveryBlockers = (value: unknown[]): string[] | undefined => {
  const blockers: string[] = [];
  for (const blocker of value) {
    if (typeof blocker === 'string') {
      blockers.push(blocker);
      continue;
    }
    if (!isRecord(blocker) || typeof blocker.summary !== 'string') return undefined;
    blockers.push(blocker.summary);
  }
  return blockers;
};

const normalizeTargetDiscoveryCandidates = (value: unknown[]): unknown[] =>
  value.map((candidate) => {
    if (!isRecord(candidate) || !Array.isArray(candidate.channelScores)) return candidate;
    const channelScores = candidate.channelScores.flatMap((channel, index) => {
      if (!isRecord(channel)) return [];
      const standardKey = typeof channel.key === 'string' ? channel.key.trim() : '';
      const legacyKey = typeof channel.id === 'string' ? channel.id.trim() : '';
      const evidenceIds = Array.isArray(channel.evidenceIds)
        ? channel.evidenceIds.filter((item): item is string => typeof item === 'string')
        : [];
      return [
        {
          ...channel,
          key: standardKey || legacyKey || `channel-${index + 1}`,
          evidenceIds,
        },
      ];
    });
    return {
      ...candidate,
      channelScores,
      evidenceIds: Array.isArray(candidate.evidenceIds)
        ? candidate.evidenceIds.filter((item): item is string => typeof item === 'string')
        : [],
    };
  });

export function isTargetDiscoveryPortfolio(value: unknown): value is TargetDiscoveryPortfolio {
  if (!hasTargetDiscoveryPortfolioShape(value)) return false;
  const blockers = value.blockers;
  return Array.isArray(blockers) && blockers.every((blocker: unknown) => typeof blocker === 'string');
}

export function summarizeTargetDiscoveryPortfolio(portfolio: TargetDiscoveryPortfolio): TargetDiscoveryProgressSummary {
  const ranked = portfolio.candidates.toSorted((a, b) => a.rank - b.rank);
  const visibleBranches = portfolio.branches.filter((branch) => branch.status !== 'pruned');
  const requiredBranches = visibleBranches.filter((branch) => branch.required);
  const coveredBranches = visibleBranches.filter((branch) => branch.candidateIds.length > 0);
  const generationLanes = new Set(
    portfolio.candidates
      .map((candidate) => candidate.generation?.lane)
      .filter((lane): lane is TargetDiscoveryGenerationLane => Boolean(lane))
  );
  return {
    candidateCount: portfolio.candidates.length,
    advanceCount: portfolio.candidates.filter((candidate) => candidate.status === 'advance').length,
    validationCount: portfolio.candidates.reduce(
      (count, candidate) =>
        count + (candidate.validationResults || []).filter((result) => result.status !== 'not_run').length,
      0
    ),
    blockerCount: portfolio.blockers.length,
    sourceReadyCount: portfolio.sourceHealth.filter((source) => source.status === 'ready').length,
    sourceCount: portfolio.sourceHealth.length,
    branchCount: portfolio.branches.length,
    coveredBranchCount: coveredBranches.length,
    requiredBranchCount: requiredBranches.length,
    unresolvedRequiredBranchCount: requiredBranches.filter((branch) => branch.candidateIds.length === 0).length,
    generationLaneCount: generationLanes.size,
    leadingCoverage: ranked[0]?.coverage,
    topTargets: ranked.slice(0, 3).map((candidate) => candidate.symbol),
  };
}

const stagesRequiringCandidates = new Set<TargetDiscoveryStage>([
  'screening',
  'triage',
  'validation_design',
  'complete',
]);

export function summarizeTargetChannelEvidenceSupport(
  candidate: TargetCandidate,
  channel: TargetEvidenceChannelScore
): TargetChannelEvidenceSupport {
  const evidenceIds = new Set(channel.evidenceIds);
  const linkedValidationResults = (candidate.validationResults || []).filter((result) =>
    result.evidenceIds.some((evidenceId) => evidenceIds.has(evidenceId))
  );
  const completedValidationResults = linkedValidationResults.filter((result) => result.status !== 'not_run');
  const completedStatuses = new Set(completedValidationResults.map((result) => result.status));
  let state: TargetChannelEvidenceSupportState;
  if (channel.missing) state = 'missing';
  else if (!channel.evidenceIds.length) state = 'unlinked';
  else if (completedStatuses.has('mixed') || (completedStatuses.has('passed') && completedStatuses.has('failed')))
    state = 'validation_mixed';
  else if (completedStatuses.has('passed')) state = 'validation_passed';
  else if (completedStatuses.has('failed')) state = 'validation_failed';
  else state = 'evidence_only';
  return {
    state,
    evidenceCount: channel.evidenceIds.length,
    linkedValidationResults,
    completedValidationResults,
  };
}

export function inspectTargetDiscoveryPortfolio(portfolio: TargetDiscoveryPortfolio): TargetDiscoveryIntegrityReport {
  const diagnostics: TargetDiscoveryIntegrityDiagnostic[] = [];
  const candidateIds = new Set<string>();
  const ranks = new Set<number>();
  const scoreCounts = new Map<number, number>();
  const policy = portfolio.context.researchPolicy;
  const branchById = new Map(portfolio.branches.map((branch) => [branch.id, branch]));
  const observedGenerationLanes = new Set<TargetDiscoveryGenerationLane>();
  let advanceCandidateCount = 0;

  if (policy) {
    const innovationRequired = Boolean(
      policy.innovationIntent && !['not_required', 'reproduction'].includes(policy.innovationIntent)
    );
    const policyProblems: string[] = [];
    if (innovationRequired) {
      if (!policy.innovationScope?.trim()) policyProblems.push('innovationScope');
      if (!policy.requiredNoveltyDimensions?.length) policyProblems.push('requiredNoveltyDimensions');
      if (!policy.directCollisionPolicy) policyProblems.push('directCollisionPolicy');
      if (!policy.clinicalProgramPolicy) policyProblems.push('clinicalProgramPolicy');
      if (policy.innovationIntent === 'de_novo_entity' && !policy.requiredNoveltyDimensions?.includes('entity')) {
        policyProblems.push('entity novelty requirement');
      }
      if (
        policy.innovationIntent === 'contextual_population' &&
        !policy.requiredNoveltyDimensions?.some((dimension) => ['context', 'population'].includes(dimension))
      ) {
        policyProblems.push('context or population novelty requirement');
      }
    }
    if (policy.patientDataRequired) {
      if (!Number.isInteger(policy.minUniquePatients) || (policy.minUniquePatients || 0) <= 0) {
        policyProblems.push('positive minUniquePatients');
      }
      if (!Number.isInteger(policy.minIndependentCohorts) || (policy.minIndependentCohorts || 0) <= 0) {
        policyProblems.push('positive minIndependentCohorts');
      }
    }
    const minimumGenerationLanes = policy.minIndependentGenerationLanes;
    if (minimumGenerationLanes != null) {
      if (!Number.isInteger(minimumGenerationLanes) || minimumGenerationLanes < 1 || minimumGenerationLanes > 3) {
        policyProblems.push('minIndependentGenerationLanes between 1 and 3');
      }
    }
    if ((innovationRequired || policy.patientDataRequired) && policy.independentAuditRequired !== true) {
      policyProblems.push('independentAuditRequired=true');
    }
    if (policyProblems.length) {
      diagnostics.push({
        severity: 'error',
        code: 'invalid_research_policy',
        message: `The target research policy is incomplete: ${policyProblems.join(', ')}.`,
      });
    }
  }

  if (stagesRequiringCandidates.has(portfolio.stage) && portfolio.candidates.length === 0) {
    diagnostics.push({
      severity: 'error',
      code: 'stage_requires_candidates',
      message: `Target stage ${portfolio.stage} requires at least one registered candidate.`,
    });
  }

  for (const candidate of portfolio.candidates) {
    if (candidateIds.has(candidate.id)) {
      diagnostics.push({
        severity: 'error',
        code: 'duplicate_candidate_id',
        message: `Candidate id ${candidate.id} is duplicated.`,
      });
    }
    candidateIds.add(candidate.id);
    if (ranks.has(candidate.rank)) {
      diagnostics.push({
        severity: 'error',
        code: 'duplicate_rank',
        message: `Candidate rank ${candidate.rank} is duplicated.`,
      });
    }
    ranks.add(candidate.rank);
    if (
      !Number.isFinite(candidate.priorityIndex) ||
      !Number.isFinite(candidate.maxPriorityIndex) ||
      candidate.priorityIndex < 0 ||
      candidate.maxPriorityIndex < candidate.priorityIndex ||
      !Number.isFinite(candidate.coverage) ||
      candidate.coverage < 0 ||
      candidate.coverage > 1
    ) {
      diagnostics.push({
        severity: 'error',
        code: 'invalid_candidate_score',
        message: `Candidate ${candidate.id} has an invalid score, maximum, or coverage value.`,
      });
    }
    scoreCounts.set(candidate.priorityIndex, (scoreCounts.get(candidate.priorityIndex) || 0) + 1);
    if (candidate.generation) {
      const declaredBranchIds = new Set(candidate.generation.branchIds);
      const actualBranchIds = new Set(
        portfolio.branches.filter((branch) => branch.candidateIds.includes(candidate.id)).map((branch) => branch.id)
      );
      const missingMemberships = [...declaredBranchIds].filter((branchId) => !actualBranchIds.has(branchId));
      const extraMemberships = [...actualBranchIds].filter((branchId) => !declaredBranchIds.has(branchId));
      if (missingMemberships.length || extraMemberships.length) {
        const details = [
          missingMemberships.length ? `missing from ${missingMemberships.join(', ')}` : '',
          extraMemberships.length ? `unexpectedly linked to ${extraMemberships.join(', ')}` : '',
        ].filter(Boolean);
        diagnostics.push({
          severity: 'error',
          code: 'generation_branch_membership_mismatch',
          message: `Candidate ${candidate.id} generation branches do not match branch membership (${details.join('; ')}).`,
        });
      }
    }
    if (candidate.status === 'advance') {
      advanceCandidateCount += 1;
      if (candidate.generation?.lane) observedGenerationLanes.add(candidate.generation.lane);
    }

    for (const channel of candidate.channelScores) {
      if (!channel.missing && !channel.evidenceIds.length) {
        diagnostics.push({
          severity: candidate.status === 'advance' ? 'error' : 'warning',
          code: 'candidate_score_missing_evidence',
          message: `Candidate ${candidate.id} score channel ${channel.key} has no linked evidence and must not be treated as decision-grade.`,
        });
      }
    }

    if (candidate.status === 'advance') {
      const completedValidationWithEvidence = (candidate.validationResults || []).filter(
        (result) => result.status !== 'not_run' && result.evidenceIds.length > 0
      );
      if (!completedValidationWithEvidence.length) {
        diagnostics.push({
          severity: 'error',
          code: 'advance_missing_validation_evidence',
          message: `Candidate ${candidate.id} cannot advance without at least one completed, evidence-linked validation result.`,
        });
      }
      for (const channel of candidate.channelScores) {
        const support = summarizeTargetChannelEvidenceSupport(candidate, channel);
        const highComputedScore =
          !channel.missing &&
          channel.evidenceKind === 'computed' &&
          channel.maxScore > 0 &&
          channel.score / channel.maxScore >= 0.8;
        if (highComputedScore && support.state !== 'validation_passed' && support.state !== 'validation_mixed') {
          diagnostics.push({
            severity: 'error',
            code: 'advance_high_computed_score_unverified',
            message: `Candidate ${candidate.id} channel ${channel.key} claims replicated or orthogonal computed support without a linked passed or mixed validation result.`,
          });
        }
      }
    }

    if (candidate.status !== 'advance' || !policy) continue;
    const innovationRequired = Boolean(
      policy.innovationIntent && !['not_required', 'reproduction'].includes(policy.innovationIntent)
    );
    if (innovationRequired) {
      const generation = candidate.generation;
      if (
        !generation ||
        !Array.isArray(generation.branchIds) ||
        !generation.branchIds.length ||
        typeof generation.rationale !== 'string' ||
        !generation.rationale.trim() ||
        typeof generation.cheapTest !== 'string' ||
        !generation.cheapTest.trim() ||
        typeof generation.killCriterion !== 'string' ||
        !generation.killCriterion.trim()
      ) {
        diagnostics.push({
          severity: 'error',
          code: 'advance_missing_generation_record',
          message: `Candidate ${candidate.id} cannot advance as an innovation without its generation route, rationale, cheapest test, and kill criterion.`,
        });
      } else if (
        generation.branchIds.some((branchId) => {
          const branch = branchById.get(branchId);
          return !branch || branch.status === 'pruned';
        })
      ) {
        diagnostics.push({
          severity: 'error',
          code: 'advance_invalid_generation_branch',
          message: `Candidate ${candidate.id} references a missing or pruned mechanism branch in its generation record.`,
        });
      }
      const novelty = candidate.noveltyReview;
      if (!novelty || novelty.collisionStatus === 'not_checked' || novelty.clinicalProgramStatus === 'not_checked') {
        diagnostics.push({
          severity: 'error',
          code: 'advance_missing_novelty_review',
          message: `Candidate ${candidate.id} cannot advance before prior-work and clinical-program collision review.`,
        });
      } else {
        if (novelty.collisionStatus === 'direct_collision') {
          diagnostics.push({
            severity: 'error',
            code: 'advance_novelty_collision',
            message: `Candidate ${candidate.id} directly collides with prior work and cannot occupy an innovation advance slot.`,
          });
        }
        const missingDimensions = (policy.requiredNoveltyDimensions || []).filter(
          (dimension) => novelty.dimensions[dimension] !== 'possibly_novel'
        );
        if (missingDimensions.length) {
          diagnostics.push({
            severity: 'error',
            code: 'advance_novelty_dimension_failed',
            message: `Candidate ${candidate.id} does not satisfy required novelty dimensions: ${missingDimensions.join(', ')}.`,
          });
        }
        const clinicalCollisionBlocked =
          novelty.clinicalProgramStatus === 'direct_collision' &&
          (policy.innovationIntent === 'de_novo_entity' || policy.clinicalProgramPolicy !== 'allow_context');
        if (clinicalCollisionBlocked) {
          diagnostics.push({
            severity: 'error',
            code: 'advance_clinical_program_collision',
            message: `Candidate ${candidate.id} has a matching clinical program excluded by the promotion policy.`,
          });
        }
      }
    }

    if (policy.patientDataRequired) {
      const patient = candidate.patientEvidence;
      const computedChannelEvidenceIds = new Set(
        candidate.channelScores
          .filter((channel) => channel.evidenceKind === 'computed' && !channel.missing)
          .flatMap((channel) => channel.evidenceIds)
      );
      const hasComputedChannel = patient?.computedEvidenceIds.some((evidenceId) =>
        computedChannelEvidenceIds.has(evidenceId)
      );
      if (!patient || !patient.analysisRunIds.length || !patient.computedEvidenceIds.length || !hasComputedChannel) {
        diagnostics.push({
          severity: 'error',
          code: 'advance_missing_patient_analysis',
          message: `Candidate ${candidate.id} cannot advance without a real patient-level run and computed evidence.`,
        });
      } else {
        const minPatients = Math.max(1, policy.minUniquePatients || 0);
        const minCohorts = Math.max(policy.independentValidationRequired ? 2 : 1, policy.minIndependentCohorts || 0);
        if (patient.uniquePatientCount < minPatients || patient.independentCohortCount < minCohorts) {
          diagnostics.push({
            severity: 'error',
            code: 'advance_patient_threshold_failed',
            message: `Candidate ${candidate.id} does not meet the frozen unique-patient or independent-cohort threshold.`,
          });
        }
        if (
          policy.individualExposureRequired &&
          !['individual_measured', 'individual_biomarker'].includes(patient.exposureMeasurement)
        ) {
          diagnostics.push({
            severity: 'error',
            code: 'advance_proxy_only_exposure',
            message: `Candidate ${candidate.id} uses only cohort, geography, ancestry, or other proxy exposure evidence.`,
          });
        }
        const hasIndependentValidation =
          patient.discoveryCohortIds.length > 0 &&
          patient.validationCohortIds.length > 0 &&
          candidate.validationResults?.some(
            (result) =>
              ['external', 'orthogonal', 'perturbational', 'prospective'].includes(result.kind) &&
              result.status !== 'not_run' &&
              result.evidenceIds.length > 0
          );
        if (policy.independentValidationRequired && !hasIndependentValidation) {
          diagnostics.push({
            severity: 'error',
            code: 'advance_missing_independent_validation',
            message: `Candidate ${candidate.id} cannot advance without a non-overlapping completed validation result.`,
          });
        }
      }
    }

    if (policy.independentAuditRequired && !candidate.auditArtifactId?.trim()) {
      diagnostics.push({
        severity: 'error',
        code: 'advance_missing_independent_audit',
        message: `Candidate ${candidate.id} cannot advance before an independent audit artifact is linked.`,
      });
    }
  }

  const linkedCandidateIds = new Set<string>();
  for (const branch of portfolio.branches) {
    for (const candidateId of branch.candidateIds) {
      linkedCandidateIds.add(candidateId);
      if (!candidateIds.has(candidateId)) {
        diagnostics.push({
          severity: 'error',
          code: 'unknown_branch_candidate',
          message: `Branch ${branch.id} references unknown candidate ${candidateId}.`,
        });
      }
    }
  }
  if (portfolio.branches.some((branch) => branch.status !== 'pruned')) {
    const unlinked = [...candidateIds].filter((candidateId) => !linkedCandidateIds.has(candidateId));
    if (unlinked.length) {
      diagnostics.push({
        severity: 'warning',
        code: 'unlinked_candidate',
        message: `${unlinked.length} candidate(s) are not linked to a research branch.`,
      });
    }
  }

  if (stagesRequiringCandidates.has(portfolio.stage)) {
    for (const branch of portfolio.branches) {
      if (branch.required && branch.status !== 'pruned' && branch.candidateIds.length === 0) {
        diagnostics.push({
          severity: 'error',
          code: 'required_branch_unresolved',
          message: `Required mechanism branch ${branch.id} has no candidate and has not been explicitly pruned.`,
        });
      }
    }
  }

  const innovationRequired = Boolean(
    policy?.innovationIntent && !['not_required', 'reproduction'].includes(policy.innovationIntent)
  );
  const minimumGenerationLanes = policy?.minIndependentGenerationLanes ?? 2;
  if (
    innovationRequired &&
    advanceCandidateCount > 0 &&
    portfolio.candidates.length >= 2 &&
    observedGenerationLanes.size < minimumGenerationLanes
  ) {
    diagnostics.push({
      severity: policy?.minIndependentGenerationLanes == null ? 'warning' : 'error',
      code: 'insufficient_generation_diversity',
      message: `The advance frontier uses ${observedGenerationLanes.size} independent generation lane(s); the frozen policy expects at least ${minimumGenerationLanes}.`,
    });
  }

  const candidateCount = portfolio.candidates.length;
  const uniqueScoreCount = scoreCounts.size;
  const dominantScoreCount = Math.max(0, ...scoreCounts.values());
  const scoreUniquenessRatio = candidateCount ? uniqueScoreCount / candidateCount : 0;
  const dominantScoreFraction = candidateCount ? dominantScoreCount / candidateCount : 0;
  const saturated =
    candidateCount >= 10 && (uniqueScoreCount <= 1 || dominantScoreFraction >= 0.8 || scoreUniquenessRatio < 0.05);
  if (saturated) {
    diagnostics.push({
      severity: 'warning',
      code: 'low_score_discrimination',
      message:
        'The candidate ranking has very low score discrimination. Review clipping, caps, ties, and deterministic tie-breakers before treating it as a final ranking.',
    });
  }

  return {
    valid: diagnostics.every((item) => item.severity !== 'error'),
    quality: {
      candidateCount,
      uniqueRankCount: ranks.size,
      uniqueScoreCount,
      scoreUniquenessRatio,
      dominantScoreFraction,
      saturated,
    },
    diagnostics,
  };
}

export function readTargetDiscoveryPortfolio(metadata: unknown): TargetDiscoveryPortfolio | undefined {
  if (!isRecord(metadata)) return undefined;
  const direct = metadata.targetDiscovery;
  const candidate = hasTargetDiscoveryPortfolioShape(direct)
    ? direct
    : hasTargetDiscoveryPortfolioShape(metadata)
      ? metadata
      : undefined;
  if (!candidate) return undefined;
  const blockers = normalizeTargetDiscoveryBlockers(candidate.blockers as unknown[]);
  if (!blockers) return undefined;
  const candidates = normalizeTargetDiscoveryCandidates(candidate.candidates as unknown[]);
  return { ...candidate, blockers, candidates } as unknown as TargetDiscoveryPortfolio;
}

export function buildTargetDiscoveryModePrompt(): string {
  return [
    '# Target Discovery Overlay',
    'Use $deepscientist-target-discovery with Science Mode before substantive work. This overlay only activates and routes the mode: follow the staged Skill SOP and progressively read the smallest named reference needed for the current step.',
    'Keep retrieved evidence, computed results, hypotheses, biological designs, and validation claims distinct. One target_portfolio is the canonical candidate state. If a required Skill, tool, dataset, or compute capability is unavailable, report it and narrow the claim rather than improvising.',
    'Use the bound project and preserve real run, QC, and audit receipts in Project Git. Before Team dispatch, record source, data, tool, credential, compute, and network readiness once. Reuse it across Workers; do not repeat missing-capability probes or replace evidence with consensus.',
    'When a research_team role contract exists, obey it. Otherwise work as one Agent. Publish only the strongest label supported by registered evidence.',
  ].join('\n\n');
}

export function buildTargetDiscoveryConversationExtra(projectRoot?: string): TargetDiscoveryConversationExtra {
  return {
    enabled: true,
    mode: TARGET_DISCOVERY_MODE_ID,
    projectRoot,
    schema: TARGET_DISCOVERY_PORTFOLIO_SCHEMA,
    defaultSkill: TARGET_DISCOVERY_SKILL_NAME,
  };
}
