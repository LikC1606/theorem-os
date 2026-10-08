/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { CompetitionEngineDiscoveryError, discoverCompetitionEngineLaunch } from "../competition-runtime/engineDiscovery";
import {
  CompetitionEngineClientError,
  CompetitionEngineJsonlClient,
  type CompetitionEngineCommandResult,
  type CompetitionEngineLaunch,
  type CompetitionEngineRequestOptions,
} from "../competition-runtime/jsonlClient";
import { isRecord } from "../competition-runtime/protocol";
import {
  DEFAULT_IOAI_COMPETITION_EVALUATION_PROFILE,
  getIoaiCompetitionEvaluationProfileContract,
  isIoaiCompetitionEvaluationProfile,
  isIoaiCompetitionEvaluationProfileContract,
  type IoaiCompetitionEvaluationProfile,
  type IoaiCompetitionEvaluationProfileContract,
} from "../../common/chat/ioaiCompetition";
import {
  assertCompetitionCandidateLane,
  assertUniqueCompetitionCandidateIdentities,
  parseCompetitionCandidateIdentity,
  type CompetitionCandidateIdentity,
} from "./candidateAttribution";

export const COMPETITION_FRONTIER_SNAPSHOT_SCHEMA = 'deepscientist.ioai.competition.frontier-snapshot.v1';

export type CandidateEvidenceAssessment = {
  schema: 'deepscientist.ioai.competition.candidate-evidence-assessment.v1';
  eligible: boolean;
  reason: string;
  execution_mode: 'executable' | 'static-evaluator-fixture' | 'unknown';
  attempt_status: string | null;
  source_manifest_hash: string | null;
  receipt_hash: string | null;
};

export type FrontierCandidate = CompetitionCandidateIdentity & {
  trial_id: string;
  trial_ref: string;
  profile: IoaiCompetitionEvaluationProfile;
  candidate_type: 'single' | 'ensemble';
  search_round: number;
  lane: string;
  status: string;
  operator: string;
  hypothesis: string;
  strategy_summary: string;
  rank: number | null;
  valid: boolean | null;
  score: number | null;
  direction: string | null;
  failure_kind: string | null;
  packet_hash: string | null;
  candidate_execution_mode: 'executable' | 'static-evaluator-fixture';
  candidate_evidence: CandidateEvidenceAssessment;
};

type OptimizationDecision = {
  policy_version: 1;
  route: 'explore' | 'exploit' | 'fusion' | 'debug' | 'stop';
  reason: string;
  incumbent_history: Array<{ round: number; trial_id: string; score: number }>;
  plateau_rounds: number;
  plateau_patience: number;
  min_delta: number;
  early_stop: boolean;
  novelty_preserved_ids: string[];
  halving: { survivor_ids: string[]; eliminated_ids: string[]; invalid_ids: string[] };
};

type CaseEvidenceCandidate = {
  trial_id: string;
  candidate_type: 'single' | 'ensemble';
  case_scores: Record<string, number>;
  observed_case_count: number;
  expected_case_count: number;
  missing_case_ids: string[];
  error_case_ids: string[];
  case_mean: number | null;
  case_stdev: number | null;
  case_range: number | null;
  repeat_seed_count: number;
  behavior_signature: string[];
};

type CaseEvidence = {
  evidence_version: 1;
  profile: IoaiCompetitionEvaluationProfile;
  direction: 'maximize' | 'minimize';
  case_ids: string[];
  best_score_by_case: Record<string, number>;
  candidates: Record<string, CaseEvidenceCandidate>;
  error_clusters: Array<{ cluster_id: string; signature: string[]; trial_ids: string[] }>;
  behavior_correlations: Array<{
    left_trial_id: string;
    right_trial_id: string;
    overlap_case_ids: string[];
    correlation: number | null;
    behavioral_diversity: number | null;
    reason: string | null;
  }>;
  evidence_hash: string;
};

export type FrontierBudget = {
  limits: Record<string, number>;
  spent_submissions: number;
  spent_tokens: number;
  spent_compute_seconds: number;
  active_claim_ids: string[];
  remaining: Record<string, number>;
};

export type FrontierFailures = {
  invalid_result_count: number;
  failed_lifecycle_count: number;
  cancelled_count: number;
  by_kind: Record<string, number>;
};

export type CompetitionTaskFingerprint = {
  schema: 'deepscientist.ioai.task-fingerprint.v1';
  task_id: string;
  task_family: string;
  modality: string;
  output_kind: string;
  metric_direction: 'maximize' | 'minimize' | 'unknown';
  validation_case_count: number;
  repeat_seed_count: number;
  artifact_extensions: string[];
  artifact_category_counts: Record<string, number>;
  recommended_lenses: string[];
  evidence_basis: string[];
};

export type FrontierSnapshotPayload = {
  seal_id: string;
  task_id: string;
  task_fingerprint: CompetitionTaskFingerprint;
  profile: IoaiCompetitionEvaluationProfile;
  profile_contract: IoaiCompetitionEvaluationProfileContract;
  final_evidence_eligible: boolean;
  canonical_evidence_eligible: boolean;
  frontier_revision: number;
  checkpoint_hash: string;
  checkpoint_ref: string;
  snapshot_hash: string;
  incumbent: FrontierCandidate | null;
  runner_up: FrontierCandidate | null;
  candidates: FrontierCandidate[];
  optimization: OptimizationDecision;
  case_evidence: CaseEvidence;
  lanes: Record<string, number>;
  lifecycle: Record<string, number>;
  failures: FrontierFailures;
  budget: FrontierBudget;
};

type FrontierSnapshotError = {
  code: string;
  message: string;
  retryable: boolean;
  engine_code?: string;
};

export type CompetitionFrontierSnapshot =
  | ({
      schema: typeof COMPETITION_FRONTIER_SNAPSHOT_SCHEMA;
      status: 'ready';
      official_submission_enabled: false;
      diagnostics?: { stderr: string };
    } & FrontierSnapshotPayload)
  | {
      schema: typeof COMPETITION_FRONTIER_SNAPSHOT_SCHEMA;
      status: 'ready';
      state: 'empty';
      seal_id: string;
      task_id: string;
      profile: IoaiCompetitionEvaluationProfile;
      profile_contract: IoaiCompetitionEvaluationProfileContract;
      final_evidence_eligible: false;
      canonical_evidence_eligible: false;
      frontier_revision: 0;
      official_submission_enabled: false;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_FRONTIER_SNAPSHOT_SCHEMA;
      status: 'unavailable';
      official_submission_enabled: false;
      error: FrontierSnapshotError;
      diagnostics?: { stderr: string };
    };

export type CompetitionFrontierSnapshotOptions = CompetitionEngineRequestOptions & {
  projectRoot: string;
  sealId: string;
  taskId: string;
  profile?: IoaiCompetitionEvaluationProfile;
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestSnapshot?: (
    launch: CompetitionEngineLaunch,
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

export type CompetitionFrontierToolResult = {
  content: [{ type: 'text'; text: string }];
  isError?: true;
};

class FrontierSnapshotValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'FrontierSnapshotValidationError';
  }
}

export async function readCompetitionFrontierSnapshot(
  options: CompetitionFrontierSnapshotOptions
): Promise<CompetitionFrontierSnapshot> {
  let requestIdentity: { sealId: string; taskId: string; profile: IoaiCompetitionEvaluationProfile } | undefined;
  try {
    const projectRoot = requiredInput(options.projectRoot, 'project_root');
    const sealId = requiredInput(options.sealId, 'seal_id');
    const taskId = requiredInput(options.taskId, 'task_id');
    const profile = requestProfile(options.profile);
    requestIdentity = { sealId, taskId, profile };
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const requestSnapshot = options.requestSnapshot ?? defaultSnapshotRequest;
    const response = await requestSnapshot(
      launch,
      {
        project_root: projectRoot,
        seal_id: sealId,
        task_id: taskId,
        profile,
      },
      { timeoutMs: options.timeoutMs, signal: options.signal }
    );
    const snapshot = parseCompetitionFrontierPayload(response.result, { sealId, taskId, profile });
    return {
      schema: COMPETITION_FRONTIER_SNAPSHOT_SCHEMA,
      status: 'ready',
      ...snapshot,
      official_submission_enabled: false,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailableSnapshot(error, requestIdentity);
  }
}

export function formatCompetitionFrontierSnapshot(
  snapshot: CompetitionFrontierSnapshot
): CompetitionFrontierToolResult {
  const result: CompetitionFrontierToolResult = {
    content: [{ type: 'text', text: JSON.stringify(snapshot, null, 2) }],
  };
  if (snapshot.status === 'unavailable') result.isError = true;
  return result;
}

async function defaultSnapshotRequest(
  launch: CompetitionEngineLaunch,
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request('frontier_snapshot', params, options);
}

export function parseCompetitionFrontierPayload(
  result: Record<string, unknown>,
  expected: { sealId: string; taskId: string; profile: IoaiCompetitionEvaluationProfile }
): FrontierSnapshotPayload {
  if (result.snapshot_version !== 1) invalid('snapshot_version must be 1');
  if (result.official_submission_enabled !== false) {
    throw new FrontierSnapshotValidationError(
      'unsafe_official_submission_capability',
      'frontier snapshot must keep official submission disabled'
    );
  }
  const sealId = requiredString(result, 'seal_id');
  const taskId = requiredString(result, 'task_id');
  if (sealId !== expected.sealId || taskId !== expected.taskId || result.profile !== expected.profile) {
    throw new FrontierSnapshotValidationError(
      'frontier_identity_mismatch',
      'frontier snapshot identity does not match the request'
    );
  }
  if (!isIoaiCompetitionEvaluationProfile(result.profile)) invalid('profile is invalid');
  const profile = result.profile;
  if (!isIoaiCompetitionEvaluationProfileContract(result.profile_contract, profile)) {
    invalid('profile_contract is invalid');
  }
  const profileContract = getIoaiCompetitionEvaluationProfileContract(profile);
  if (result.final_evidence_eligible !== profileContract.final_evidence_eligible) {
    invalid('final_evidence_eligible is inconsistent');
  }
  const rawCandidates = result.candidates;
  if (!Array.isArray(rawCandidates)) invalid('candidates must be an array');
  const candidates = rawCandidates.map((candidate, index) =>
    parseCandidate(candidate, `candidates[${index}]`, profile)
  );
  if (new Set(candidates.map((candidate) => candidate.trial_id)).size !== candidates.length) {
    invalid('candidates contain duplicate trial_id values');
  }
  assertUniqueCompetitionCandidateIdentities(candidates, 'candidates', invalid);
  const candidateIds = new Set(candidates.map((candidate) => candidate.trial_id));
  const incumbent = parseOptionalCandidate(result.incumbent, 'incumbent', profile);
  const runnerUp = parseOptionalCandidate(result.runner_up, 'runner_up', profile);
  if (incumbent && !candidateIds.has(incumbent.trial_id)) invalid('incumbent is absent from candidates');
  if (runnerUp && !candidateIds.has(runnerUp.trial_id)) invalid('runner_up is absent from candidates');
  if (incumbent) assertCandidateIdentityMatches(candidates, incumbent, 'incumbent');
  if (runnerUp) assertCandidateIdentityMatches(candidates, runnerUp, 'runner_up');
  const canonicalEvidenceEligible = requiredBoolean(result, 'canonical_evidence_eligible');
  const expectedCanonicalEligibility = Boolean(
    profileContract.final_evidence_eligible && incumbent?.candidate_evidence.eligible
  );
  if (canonicalEvidenceEligible !== expectedCanonicalEligibility) {
    invalid('canonical_evidence_eligible is inconsistent');
  }
  const failures = requiredRecord(result, 'failures');
  const budget = requiredRecord(result, 'budget');
  const optimization = parseOptimization(result.optimization, candidates);
  const caseEvidence = parseCaseEvidence(result.case_evidence, profile, candidates);
  return {
    seal_id: sealId,
    task_id: taskId,
    task_fingerprint: parseCompetitionTaskFingerprint(result.task_fingerprint, taskId),
    profile,
    profile_contract: profileContract,
    final_evidence_eligible: profileContract.final_evidence_eligible,
    canonical_evidence_eligible: canonicalEvidenceEligible,
    frontier_revision: requiredCount(result, 'frontier_revision'),
    checkpoint_hash: requiredHash(result, 'checkpoint_hash'),
    checkpoint_ref: requiredRelativeRef(result, 'checkpoint_ref'),
    snapshot_hash: requiredHash(result, 'snapshot_hash'),
    incumbent,
    runner_up: runnerUp,
    candidates,
    optimization,
    case_evidence: caseEvidence,
    lanes: countRecord(requiredRecord(result, 'lanes'), 'lanes'),
    lifecycle: countRecord(requiredRecord(result, 'lifecycle'), 'lifecycle'),
    failures: {
      invalid_result_count: requiredCount(failures, 'invalid_result_count'),
      failed_lifecycle_count: requiredCount(failures, 'failed_lifecycle_count'),
      cancelled_count: requiredCount(failures, 'cancelled_count'),
      by_kind: countRecord(requiredRecord(failures, 'by_kind'), 'failures.by_kind'),
    },
    budget: {
      limits: numericRecord(requiredRecord(budget, 'limits'), 'budget.limits'),
      spent_submissions: requiredNonNegativeNumber(budget, 'spent_submissions'),
      spent_tokens: requiredNonNegativeNumber(budget, 'spent_tokens'),
      spent_compute_seconds: requiredNonNegativeNumber(budget, 'spent_compute_seconds'),
      active_claim_ids: stringArray(budget.active_claim_ids, 'budget.active_claim_ids'),
      remaining: numericRecord(requiredRecord(budget, 'remaining'), 'budget.remaining'),
    },
  };
}

export function parseCompetitionTaskFingerprint(value: unknown, expectedTaskId: string): CompetitionTaskFingerprint {
  if (!isRecord(value) || value.schema !== 'deepscientist.ioai.task-fingerprint.v1') {
    invalid('task_fingerprint schema is invalid');
  }
  const taskId = requiredString(value, 'task_id', 'task_fingerprint');
  if (taskId !== expectedTaskId) invalid('task_fingerprint task identity is inconsistent');
  const metricDirection = value.metric_direction;
  if (!['maximize', 'minimize', 'unknown'].includes(String(metricDirection))) {
    invalid('task_fingerprint.metric_direction is invalid');
  }
  return {
    schema: 'deepscientist.ioai.task-fingerprint.v1',
    task_id: taskId,
    task_family: requiredString(value, 'task_family', 'task_fingerprint'),
    modality: requiredString(value, 'modality', 'task_fingerprint'),
    output_kind: requiredString(value, 'output_kind', 'task_fingerprint'),
    metric_direction: metricDirection as CompetitionTaskFingerprint['metric_direction'],
    validation_case_count: requiredCount(value, 'validation_case_count'),
    repeat_seed_count: requiredCount(value, 'repeat_seed_count'),
    artifact_extensions: stringArray(value.artifact_extensions, 'task_fingerprint.artifact_extensions'),
    artifact_category_counts: countRecord(
      requiredRecord(value, 'artifact_category_counts'),
      'task_fingerprint.artifact_category_counts'
    ),
    recommended_lenses: stringArray(value.recommended_lenses, 'task_fingerprint.recommended_lenses'),
    evidence_basis: stringArray(value.evidence_basis, 'task_fingerprint.evidence_basis'),
  };
}

function parseOptionalCandidate(
  value: unknown,
  field: string,
  profile: IoaiCompetitionEvaluationProfile
): FrontierCandidate | null {
  return value === null ? null : parseCandidate(value, field, profile);
}

function parseCandidate(value: unknown, field: string, profile: IoaiCompetitionEvaluationProfile): FrontierCandidate {
  if (!isRecord(value)) invalid(`${field} must be an object or null`);
  if (value.profile !== profile) {
    throw new FrontierSnapshotValidationError(
      'frontier_identity_mismatch',
      `${field}.profile does not match the request`
    );
  }
  const identity = parseCompetitionCandidateIdentity(value, field, invalid);
  const candidateType = value.candidate_type;
  if (candidateType !== 'single' && candidateType !== 'ensemble') {
    invalid(`${field}.candidate_type must be single or ensemble`);
  }
  const valid = optionalBoolean(value.valid, `${field}.valid`);
  const candidateExecutionMode = value.candidate_execution_mode;
  if (candidateExecutionMode !== 'executable' && candidateExecutionMode !== 'static-evaluator-fixture') {
    invalid(`${field}.candidate_execution_mode is invalid`);
  }
  const candidateEvidence = parseCandidateEvidence(value.candidate_evidence, `${field}.candidate_evidence`);
  if (candidateEvidence.execution_mode !== 'unknown' && candidateEvidence.execution_mode !== candidateExecutionMode) {
    invalid(`${field}.candidate evidence execution mode is inconsistent`);
  }
  if (candidateEvidence.eligible && valid !== true) {
    invalid(`${field}.candidate evidence cannot be eligible for an invalid result`);
  }
  const candidate: FrontierCandidate = {
    ...identity,
    trial_id: requiredString(value, 'trial_id', field),
    trial_ref: requiredString(value, 'trial_ref', field),
    profile,
    candidate_type: candidateType,
    search_round: requiredCount(value, 'search_round'),
    lane: requiredString(value, 'lane', field),
    status: requiredString(value, 'status', field),
    operator: requiredString(value, 'operator', field),
    hypothesis: requiredString(value, 'hypothesis', field),
    strategy_summary: requiredString(value, 'strategy_summary', field),
    rank: optionalPositiveInteger(value.rank, `${field}.rank`),
    valid,
    score: optionalFiniteNumber(value.score, `${field}.score`),
    direction: optionalString(value.direction, `${field}.direction`),
    failure_kind: optionalString(value.failure_kind, `${field}.failure_kind`),
    packet_hash: optionalHash(value.packet_hash, `${field}.packet_hash`),
    candidate_execution_mode: candidateExecutionMode,
    candidate_evidence: candidateEvidence,
  };
  assertCompetitionCandidateLane(identity, candidate.lane, candidate.operator, field, invalid);
  return candidate;
}

function parseCandidateEvidence(value: unknown, field: string): CandidateEvidenceAssessment {
  if (!isRecord(value)) invalid(`${field} must be an object`);
  if (value.schema !== 'deepscientist.ioai.competition.candidate-evidence-assessment.v1') {
    invalid(`${field}.schema is invalid`);
  }
  const eligible = requiredBoolean(value, 'eligible');
  const executionMode = value.execution_mode;
  if (!['executable', 'static-evaluator-fixture', 'unknown'].includes(String(executionMode))) {
    invalid(`${field}.execution_mode is invalid`);
  }
  const attemptStatus = optionalString(value.attempt_status, `${field}.attempt_status`);
  const sourceManifestHash = optionalHash(value.source_manifest_hash, `${field}.source_manifest_hash`);
  const receiptHash = optionalHash(value.receipt_hash, `${field}.receipt_hash`);
  if (
    eligible &&
    (executionMode !== 'executable' ||
      attemptStatus !== 'passed' ||
      sourceManifestHash === null ||
      receiptHash === null)
  ) {
    invalid(`${field} lacks passing hashed executable evidence`);
  }
  return {
    schema: 'deepscientist.ioai.competition.candidate-evidence-assessment.v1',
    eligible,
    reason: requiredString(value, 'reason', field),
    execution_mode: executionMode as CandidateEvidenceAssessment['execution_mode'],
    attempt_status: attemptStatus,
    source_manifest_hash: sourceManifestHash,
    receipt_hash: receiptHash,
  };
}

function parseOptimization(value: unknown, candidates: readonly FrontierCandidate[]): OptimizationDecision {
  if (!isRecord(value) || value.policy_version !== 1) invalid('optimization must be a policy v1 object');
  const route = value.route;
  if (!['explore', 'exploit', 'fusion', 'debug', 'stop'].includes(String(route))) {
    invalid('optimization.route is invalid');
  }
  const candidateIds = new Set(candidates.map((candidate) => candidate.trial_id));
  const historyValue = value.incumbent_history;
  if (!Array.isArray(historyValue)) invalid('optimization.incumbent_history must be an array');
  const incumbentHistory = historyValue.map((item, index) => {
    if (!isRecord(item)) invalid(`optimization.incumbent_history[${index}] must be an object`);
    const trialId = requiredString(item, 'trial_id', `optimization.incumbent_history[${index}]`);
    if (!candidateIds.has(trialId)) invalid('optimization history references an unknown trial');
    const score = item.score;
    if (typeof score !== 'number' || !Number.isFinite(score)) invalid('optimization history score must be finite');
    return { round: requiredCount(item, 'round'), trial_id: trialId, score };
  });
  if (new Set(incumbentHistory.map((item) => item.round)).size !== incumbentHistory.length) {
    invalid('optimization history contains duplicate rounds');
  }
  const halving = requiredRecord(value, 'halving');
  const survivorIds = knownIdArray(halving.survivor_ids, 'optimization.halving.survivor_ids', candidateIds);
  const eliminatedIds = knownIdArray(halving.eliminated_ids, 'optimization.halving.eliminated_ids', candidateIds);
  const invalidIds = knownIdArray(halving.invalid_ids, 'optimization.halving.invalid_ids', candidateIds);
  const partition = [...survivorIds, ...eliminatedIds, ...invalidIds];
  if (new Set(partition).size !== partition.length) invalid('optimization halving groups overlap');
  const noveltyPreservedIds = knownIdArray(
    value.novelty_preserved_ids,
    'optimization.novelty_preserved_ids',
    new Set(survivorIds)
  );
  if (noveltyPreservedIds.some((id) => candidates.find((candidate) => candidate.trial_id === id)?.lane !== 'novelty')) {
    invalid('optimization novelty preservation references a non-novelty candidate');
  }
  const plateauPatience = requiredCount(value, 'plateau_patience');
  if (plateauPatience < 1) invalid('optimization.plateau_patience must be positive');
  const minDelta = value.min_delta;
  if (typeof minDelta !== 'number' || !Number.isFinite(minDelta) || minDelta < 0) {
    invalid('optimization.min_delta must be finite and non-negative');
  }
  const earlyStop = value.early_stop;
  if (typeof earlyStop !== 'boolean' || earlyStop !== (route === 'stop')) {
    invalid('optimization.early_stop is inconsistent with route');
  }
  return {
    policy_version: 1,
    route: route as OptimizationDecision['route'],
    reason: requiredString(value, 'reason', 'optimization'),
    incumbent_history: incumbentHistory,
    plateau_rounds: requiredCount(value, 'plateau_rounds'),
    plateau_patience: plateauPatience,
    min_delta: minDelta,
    early_stop: earlyStop,
    novelty_preserved_ids: noveltyPreservedIds,
    halving: { survivor_ids: survivorIds, eliminated_ids: eliminatedIds, invalid_ids: invalidIds },
  };
}

function parseCaseEvidence(
  value: unknown,
  profile: IoaiCompetitionEvaluationProfile,
  frontierCandidates: readonly FrontierCandidate[]
): CaseEvidence {
  if (!isRecord(value) || value.evidence_version !== 1 || value.profile !== profile) {
    invalid('case_evidence identity is invalid');
  }
  const direction = value.direction;
  if (direction !== 'maximize' && direction !== 'minimize') invalid('case_evidence.direction is invalid');
  const caseIds = stringArray(value.case_ids, 'case_evidence.case_ids');
  const caseIdSet = new Set(caseIds);
  const bestScores = finiteRecord(requiredRecord(value, 'best_score_by_case'), 'case_evidence.best_score_by_case');
  if (Object.keys(bestScores).some((caseId) => !caseIdSet.has(caseId))) {
    invalid('case_evidence best scores reference unknown cases');
  }
  const rawCandidates = requiredRecord(value, 'candidates');
  const frontierById = new Map(frontierCandidates.map((candidate) => [candidate.trial_id, candidate]));
  if (Object.keys(rawCandidates).length !== frontierById.size) invalid('case_evidence candidate set is incomplete');
  const candidates: Record<string, CaseEvidenceCandidate> = {};
  for (const [trialId, raw] of Object.entries(rawCandidates)) {
    if (!frontierById.has(trialId) || !isRecord(raw) || raw.trial_id !== trialId) {
      invalid('case_evidence contains an unknown candidate');
    }
    const candidateType = raw.candidate_type;
    if (candidateType !== 'single' && candidateType !== 'ensemble') invalid('case_evidence candidate_type is invalid');
    if (candidateType !== frontierById.get(trialId)?.candidate_type)
      invalid('case_evidence candidate_type is inconsistent');
    const caseScores = finiteRecord(
      requiredRecord(raw, 'case_scores'),
      `case_evidence.candidates.${trialId}.case_scores`
    );
    if (Object.keys(caseScores).some((caseId) => !caseIdSet.has(caseId)))
      invalid('case evidence score references unknown case');
    const missingCaseIds = knownIdArray(raw.missing_case_ids, 'missing_case_ids', caseIdSet);
    const errorCaseIds = knownIdArray(raw.error_case_ids, 'error_case_ids', new Set(Object.keys(caseScores)));
    if (requiredCount(raw, 'observed_case_count') !== Object.keys(caseScores).length)
      invalid('observed case count is inconsistent');
    if (requiredCount(raw, 'expected_case_count') !== caseIds.length) invalid('expected case count is inconsistent');
    if (missingCaseIds.length + Object.keys(caseScores).length !== caseIds.length)
      invalid('missing case set is inconsistent');
    candidates[trialId] = {
      trial_id: trialId,
      candidate_type: candidateType,
      case_scores: caseScores,
      observed_case_count: Object.keys(caseScores).length,
      expected_case_count: caseIds.length,
      missing_case_ids: missingCaseIds,
      error_case_ids: errorCaseIds,
      case_mean: optionalFiniteNumber(raw.case_mean, 'case_mean'),
      case_stdev: optionalNonNegativeNumber(raw.case_stdev, 'case_stdev'),
      case_range: optionalNonNegativeNumber(raw.case_range, 'case_range'),
      repeat_seed_count: requiredCount(raw, 'repeat_seed_count'),
      behavior_signature: stringArray(raw.behavior_signature, 'behavior_signature'),
    };
  }
  const errorClusters = value.error_clusters;
  if (!Array.isArray(errorClusters)) invalid('case_evidence.error_clusters must be an array');
  const parsedClusters = errorClusters.map((raw, index) => {
    if (!isRecord(raw) || typeof raw.cluster_id !== 'string' || !/^case-cluster-[0-9a-f]{12}$/u.test(raw.cluster_id)) {
      invalid(`case_evidence.error_clusters[${index}] is invalid`);
    }
    return {
      cluster_id: raw.cluster_id,
      signature: stringArray(raw.signature, `case_evidence.error_clusters[${index}].signature`),
      trial_ids: knownIdArray(
        raw.trial_ids,
        `case_evidence.error_clusters[${index}].trial_ids`,
        new Set(frontierById.keys())
      ),
    };
  });
  const correlations = value.behavior_correlations;
  if (!Array.isArray(correlations)) invalid('case_evidence.behavior_correlations must be an array');
  const parsedCorrelations = correlations.map((raw, index) => {
    if (!isRecord(raw)) invalid(`case_evidence.behavior_correlations[${index}] must be an object`);
    const left = requiredString(raw, 'left_trial_id');
    const right = requiredString(raw, 'right_trial_id');
    if (left === right || !frontierById.has(left) || !frontierById.has(right))
      invalid('case evidence correlation pair is invalid');
    const correlation = optionalBoundedNumber(raw.correlation, 'correlation', -1, 1);
    const diversity = optionalBoundedNumber(raw.behavioral_diversity, 'behavioral_diversity', 0, 2);
    if (
      (correlation === null) !== (diversity === null) ||
      (correlation !== null && Math.abs(diversity! - (1 - correlation)) > 1e-12)
    ) {
      invalid('case evidence correlation diversity is inconsistent');
    }
    return {
      left_trial_id: left,
      right_trial_id: right,
      overlap_case_ids: knownIdArray(raw.overlap_case_ids, 'overlap_case_ids', caseIdSet),
      correlation,
      behavioral_diversity: diversity,
      reason: optionalString(raw.reason, 'reason'),
    };
  });
  return {
    evidence_version: 1,
    profile,
    direction,
    case_ids: caseIds,
    best_score_by_case: bestScores,
    candidates,
    error_clusters: parsedClusters,
    behavior_correlations: parsedCorrelations,
    evidence_hash: requiredHash(value, 'evidence_hash'),
  };
}

function requestProfile(value: unknown): IoaiCompetitionEvaluationProfile {
  if (value === undefined) return DEFAULT_IOAI_COMPETITION_EVALUATION_PROFILE;
  if (!isIoaiCompetitionEvaluationProfile(value)) {
    throw new FrontierSnapshotValidationError('invalid_request', 'profile must be smoke, sprint, contest, or audit');
  }
  return value;
}

function assertCandidateIdentityMatches(
  candidates: readonly FrontierCandidate[],
  selected: FrontierCandidate,
  field: string
): void {
  const canonical = candidates.find((candidate) => candidate.trial_id === selected.trial_id);
  if (!canonical || JSON.stringify(canonical) !== JSON.stringify(selected)) {
    invalid(`${field} candidate differs from canonical candidates`);
  }
}

function requiredInput(value: unknown, field: string): string {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new FrontierSnapshotValidationError('invalid_request', `${field} must be a non-empty string`);
  }
  return value.trim();
}

function requiredRecord(source: Record<string, unknown>, key: string): Record<string, unknown> {
  const value = source[key];
  if (!isRecord(value)) invalid(`${key} must be an object`);
  return value;
}

function requiredString(source: Record<string, unknown>, key: string, prefix = ''): string {
  const value = source[key];
  if (typeof value !== 'string' || value.length === 0) invalid(`${prefix ? `${prefix}.` : ''}${key} is invalid`);
  return value;
}

function requiredCount(source: Record<string, unknown>, key: string): number {
  const value = source[key];
  if (!Number.isSafeInteger(value) || Number(value) < 0) invalid(`${key} must be a non-negative integer`);
  return Number(value);
}

function requiredBoolean(source: Record<string, unknown>, key: string): boolean {
  const value = source[key];
  if (typeof value !== 'boolean') invalid(`${key} must be a boolean`);
  return value;
}

function requiredNonNegativeNumber(source: Record<string, unknown>, key: string): number {
  const value = source[key];
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) {
    invalid(`${key} must be a finite non-negative number`);
  }
  return value;
}

function requiredHash(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !/^[0-9a-f]{64}$/u.test(value)) invalid(`${key} must be a SHA-256 hash`);
  return value;
}

function optionalHash(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || !/^[0-9a-f]{64}$/u.test(value)) invalid(`${field} must be a SHA-256 hash or null`);
  return value;
}

function requiredRelativeRef(source: Record<string, unknown>, key: string): string {
  const value = requiredString(source, key);
  const parts = value.split('/');
  if (value.startsWith('/') || value.includes('\\') || parts.includes('..') || parts.includes('.')) {
    invalid(`${key} must be a normalized relative path`);
  }
  return value;
}

function optionalPositiveInteger(value: unknown, field: string): number | null {
  if (value === null) return null;
  if (!Number.isSafeInteger(value) || Number(value) < 1) invalid(`${field} must be a positive integer or null`);
  return Number(value);
}

function optionalFiniteNumber(value: unknown, field: string): number | null {
  if (value === null) return null;
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${field} must be a finite number or null`);
  return value;
}

function optionalBoolean(value: unknown, field: string): boolean | null {
  if (value === null) return null;
  if (typeof value !== 'boolean') invalid(`${field} must be a boolean or null`);
  return value;
}

function optionalString(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || value.length === 0) invalid(`${field} must be a non-empty string or null`);
  return value;
}

function stringArray(value: unknown, field: string): string[] {
  if (!Array.isArray(value) || value.some((item) => typeof item !== 'string' || !item)) {
    invalid(`${field} must be a string array`);
  }
  const strings = value as string[];
  if (new Set(strings).size !== strings.length) invalid(`${field} contains duplicates`);
  return [...strings];
}

function countRecord(value: Record<string, unknown>, field: string): Record<string, number> {
  const result: Record<string, number> = {};
  for (const [key, count] of Object.entries(value)) {
    if (!key || !Number.isSafeInteger(count) || Number(count) < 0) invalid(`${field} contains an invalid count`);
    result[key] = Number(count);
  }
  return result;
}

function numericRecord(value: Record<string, unknown>, field: string): Record<string, number> {
  const result: Record<string, number> = {};
  for (const [key, number] of Object.entries(value)) {
    if (!key || typeof number !== 'number' || !Number.isFinite(number) || number < 0) {
      invalid(`${field} contains an invalid number`);
    }
    result[key] = number;
  }
  return result;
}

function finiteRecord(value: Record<string, unknown>, field: string): Record<string, number> {
  const result: Record<string, number> = {};
  for (const [key, number] of Object.entries(value)) {
    if (!key || typeof number !== 'number' || !Number.isFinite(number)) {
      invalid(`${field} contains an invalid number`);
    }
    result[key] = number;
  }
  return result;
}

function knownIdArray(value: unknown, field: string, known: ReadonlySet<string>): string[] {
  const values = stringArray(value, field);
  if (values.some((item) => !known.has(item))) invalid(`${field} references an unknown identity`);
  return values;
}

function optionalNonNegativeNumber(value: unknown, field: string): number | null {
  const number = optionalFiniteNumber(value, field);
  if (number !== null && number < 0) invalid(`${field} must be non-negative or null`);
  return number;
}

function optionalBoundedNumber(value: unknown, field: string, minimum: number, maximum: number): number | null {
  const number = optionalFiniteNumber(value, field);
  if (number !== null && (number < minimum || number > maximum)) {
    invalid(`${field} must be between ${minimum} and ${maximum}`);
  }
  return number;
}

function unavailableSnapshot(
  error: unknown,
  identity?: { sealId: string; taskId: string; profile: IoaiCompetitionEvaluationProfile }
): CompetitionFrontierSnapshot {
  if (error instanceof CompetitionEngineDiscoveryError) return buildUnavailable(error.code, error.message, false);
  if (error instanceof CompetitionEngineClientError) {
    if (error.engineCode === 'not_found' && error.message.startsWith('competition checkpoint not found:') && identity) {
      return {
        schema: COMPETITION_FRONTIER_SNAPSHOT_SCHEMA,
        status: 'ready',
        state: 'empty',
        seal_id: identity.sealId,
        task_id: identity.taskId,
        profile: identity.profile,
        profile_contract: getIoaiCompetitionEvaluationProfileContract(identity.profile),
        final_evidence_eligible: false,
        canonical_evidence_eligible: false,
        frontier_revision: 0,
        official_submission_enabled: false,
        ...(error.diagnostic ? { diagnostics: { stderr: error.diagnostic } } : {}),
      };
    }
    return buildUnavailable(error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof FrontierSnapshotValidationError) return buildUnavailable(error.code, error.message, false);
  return buildUnavailable('frontier_snapshot_failed', 'IOAI frontier snapshot failed', false);
}

function buildUnavailable(
  code: string,
  message: string,
  retryable: boolean,
  diagnostic = '',
  engineCode?: string
): CompetitionFrontierSnapshot {
  return {
    schema: COMPETITION_FRONTIER_SNAPSHOT_SCHEMA,
    status: 'unavailable',
    official_submission_enabled: false,
    error: { code, message, retryable, ...(engineCode ? { engine_code: engineCode } : {}) },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}

function invalid(message: string): never {
  throw new FrontierSnapshotValidationError('invalid_frontier_snapshot', message);
}
