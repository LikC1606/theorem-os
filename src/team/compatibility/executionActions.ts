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
  assertUniqueCompetitionCandidateIdentities,
  parseCompetitionCandidateIdentity,
  type CompetitionCandidateIdentity,
} from "./candidateAttribution";

export const COMPETITION_EXECUTION_ACTION_SCHEMA = 'deepscientist.ioai.competition.execution-action.v1';

export type CompetitionTrialRunRequest = {
  action: 'trial_run';
  projectRoot: string;
  sealId: string;
  taskId: string;
  profile?: IoaiCompetitionEvaluationProfile;
  candidatePath: string;
  candidateSha256?: string;
  expectedFrontierRevision: number;
  idempotencyKey: string;
};

export type CompetitionTrialBatchRequest = {
  action: 'trial_batch';
  projectRoot: string;
  sealId: string;
  taskId: string;
  profile?: IoaiCompetitionEvaluationProfile;
  batchPath: string;
  maxWorkers: number;
  expectedFrontierRevision: number;
  idempotencyKey: string;
};

export type CompetitionReportGenerateRequest = {
  action: 'report_generate';
  projectRoot: string;
  sealId: string;
  taskId: string;
  profile?: IoaiCompetitionEvaluationProfile;
  expectedFrontierRevision: number;
  idempotencyKey: string;
};

export type CompetitionTuneCreateRequest = {
  action: 'tune_create';
  projectRoot: string;
  sealId: string;
  taskId: string;
  studyId: string;
  ideaId: string;
  durableLineId: string;
  parentCandidateId: string;
  direction: 'maximize' | 'minimize';
  searchSpace: Record<string, unknown>;
  seed?: number;
  nStartupTrials?: number;
};

export type CompetitionTuneAskRequest = {
  action: 'tune_ask';
  projectRoot: string;
  sealId: string;
  taskId: string;
  studyId: string;
};

export type CompetitionTuneTellRequest = {
  action: 'tune_tell';
  projectRoot: string;
  studyId: string;
  candidateId: string;
  state: 'complete' | 'pruned' | 'failed';
  trialId?: string;
  packetHash?: string;
};

export type CompetitionTuneStatusRequest = {
  action: 'tune_status';
  projectRoot: string;
  studyId?: string;
};

export type CompetitionTuningRequest =
  | CompetitionTuneCreateRequest
  | CompetitionTuneAskRequest
  | CompetitionTuneTellRequest
  | CompetitionTuneStatusRequest;

export type CompetitionExecutionRequest =
  | CompetitionTrialRunRequest
  | CompetitionTrialBatchRequest
  | CompetitionReportGenerateRequest
  | CompetitionTuningRequest;

type IdempotentResult = {
  replayed: boolean;
  command_receipt_hash: string;
};

type TrialCandidateExecutionMode = 'executable' | 'static-evaluator-fixture';

type TrialCandidateAttempt = Record<string, unknown> & {
  schema: 'deepscientist.ioai.competition.attempt-receipt.v1';
  status: 'passed' | 'failed' | 'cache_reused';
  source_manifest_hash: string;
  receipt_hash: string | null;
  wall_clock_seconds: number | null;
};

type CompetitionRecoveryIntent = {
  schema: 'deepscientist.ioai.competition.recovery-intent.v1';
  route: 'recovery';
  purpose: 'minimum_valid_candidate';
  seal_id: string;
  task_id: string;
  candidate_id: string;
  source_frontier_revision: number;
  control_key: string;
};

type TrialResourceUsage = {
  wall_clock_seconds: number;
  candidate_attempt_seconds: number | null;
};

type TrialResultItem = CompetitionCandidateIdentity & {
  trial_id: string;
  trial_ref: string;
  profile: IoaiCompetitionEvaluationProfile;
  candidate_spec_sha256: string;
  candidate_spec_ref: string;
  candidate_type: 'single' | 'ensemble';
  valid: boolean;
  score: number | null;
  direction: 'maximize' | 'minimize';
  failure_kind: string | null;
  packet_hash: string;
  result_ref: string;
  cache_key: string;
  cache_hit: boolean;
  cache_entry_ref: string | null;
  candidate_execution_mode: TrialCandidateExecutionMode;
  candidate_attempt: TrialCandidateAttempt | null;
  recovery_intent: CompetitionRecoveryIntent | null;
  resource_usage: TrialResourceUsage;
};

type TrialResult = IdempotentResult & {
  action_version: 1;
  operation: 'run' | 'batch';
  seal_id: string;
  task_id: string;
  profile: IoaiCompetitionEvaluationProfile;
  profile_contract: IoaiCompetitionEvaluationProfileContract;
  final_evidence_eligible: boolean;
  mode: 'serial' | 'parallel';
  max_workers: number;
  trial_count: number;
  valid_count: number;
  invalid_count: number;
  cache_hits: number;
  cache_misses: number;
  frontier_revision: number;
  incumbent_id: string | null;
  incumbent_score: number | null;
  checkpoint_ref: string;
  results: TrialResultItem[];
  recovered_trial_ids: string[];
  abandoned_trial_ids: string[];
  official_submission_enabled: false;
};

type ReportResult = IdempotentResult & {
  action_version: 1;
  operation: 'generate';
  report_status: 'complete' | 'partial_blocked';
  report_id: string;
  seal_id: string;
  task_id: string;
  profile: IoaiCompetitionEvaluationProfile;
  profile_contract: IoaiCompetitionEvaluationProfileContract;
  final_evidence_eligible: boolean;
  frontier_revision: number;
  report_manifest_hash: string;
  rendered_markdown_sha256: string;
  report_manifest_ref: string;
  report_ref: string;
  limitation_count: number;
  trial_count: number;
  official_submission_enabled: false;
};

type TuningResult = Record<string, unknown> & {
  action_version: 1;
  operation: 'create' | 'read' | 'ask' | 'tell' | 'status' | 'capability';
  official_submission_enabled: false;
};

type CompetitionExecutionPayload = TrialResult | ReportResult | TuningResult;

type CompetitionExecutionError = {
  code: string;
  message: string;
  retryable: boolean;
  engine_code?: string;
};

export type CompetitionExecutionActionResult =
  | {
      schema: typeof COMPETITION_EXECUTION_ACTION_SCHEMA;
      status: 'ready';
      action: CompetitionExecutionRequest['action'];
      official_submission_enabled: false;
      result: CompetitionExecutionPayload;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_EXECUTION_ACTION_SCHEMA;
      status: 'unavailable';
      action: CompetitionExecutionRequest['action'];
      official_submission_enabled: false;
      error: CompetitionExecutionError;
      diagnostics?: { stderr: string };
    };

export type CompetitionExecutionReaderOptions = CompetitionEngineRequestOptions & {
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestAction?: (
    launch: CompetitionEngineLaunch,
    action: CompetitionExecutionRequest['action'],
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

export type CompetitionExecutionToolResult = {
  content: [{ type: 'text'; text: string }];
  isError?: true;
};

class ExecutionActionValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'ExecutionActionValidationError';
  }
}

export async function readCompetitionExecutionAction(
  request: CompetitionExecutionRequest,
  options: CompetitionExecutionReaderOptions = {}
): Promise<CompetitionExecutionActionResult> {
  try {
    const params = requestParams(request);
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const requestAction = options.requestAction ?? defaultActionRequest;
    const response = await requestAction(launch, request.action, params, {
      timeoutMs: options.timeoutMs,
      signal: options.signal,
    });
    const result = parseExecutionResult(response.result, request);
    return {
      schema: COMPETITION_EXECUTION_ACTION_SCHEMA,
      status: 'ready',
      action: request.action,
      official_submission_enabled: false,
      result,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailableResult(request.action, error);
  }
}

export function formatCompetitionExecutionAction(
  result: CompetitionExecutionActionResult
): CompetitionExecutionToolResult {
  const formatted: CompetitionExecutionToolResult = {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) }],
  };
  if (result.status === 'unavailable') formatted.isError = true;
  return formatted;
}

async function defaultActionRequest(
  launch: CompetitionEngineLaunch,
  action: CompetitionExecutionRequest['action'],
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request(action, params, options);
}

function requestParams(request: CompetitionExecutionRequest): Record<string, unknown> {
  if (isTuningRequest(request)) return tuningRequestParams(request);
  const profile = requestProfile(request.profile);
  const params: Record<string, unknown> = {
    project_root: requiredInput(request.projectRoot, 'project_root'),
    seal_id: requiredSealInput(request.sealId, 'seal_id'),
    task_id: requiredInput(request.taskId, 'task_id'),
    profile,
    expected_frontier_revision: requestRevision(request.expectedFrontierRevision),
    idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
  };
  if (request.action === 'trial_run') {
    return {
      ...params,
      candidate_path: requiredInput(request.candidatePath, 'candidate_path'),
      ...(request.candidateSha256 === undefined
        ? {}
        : { candidate_sha256: requiredHashInput(request.candidateSha256, 'candidate_sha256') }),
    };
  }
  if (request.action === 'trial_batch') {
    return {
      ...params,
      batch_path: requiredInput(request.batchPath, 'batch_path'),
      max_workers: requestWorkers(request.maxWorkers),
    };
  }
  return params;
}

function parseExecutionResult(
  result: Record<string, unknown>,
  request: CompetitionExecutionRequest
): CompetitionExecutionPayload {
  if (result.action_version !== 1) invalid('action_version must be 1');
  if (result.official_submission_enabled !== false) {
    throw new ExecutionActionValidationError(
      'unsafe_official_submission_capability',
      'execution action must keep official submission disabled'
    );
  }
  if (isTuningRequest(request)) return parseTuningResult(result, request);
  if (request.action === 'report_generate') return parseReport(result, request);
  return parseTrial(result, request);
}

function isTuningRequest(request: CompetitionExecutionRequest): request is CompetitionTuningRequest {
  return request.action.startsWith('tune_');
}

function tuningRequestParams(request: CompetitionTuningRequest): Record<string, unknown> {
  const params: Record<string, unknown> = {
    project_root: requiredInput(request.projectRoot, 'project_root'),
  };
  if (request.action === 'tune_status' && request.studyId === undefined) return params;
  params.study_id = stableTuningId(request.studyId, 'study_id');
  if (request.action === 'tune_create') {
    if (!isRecord(request.searchSpace) || !Array.isArray(request.searchSpace.parameters)) {
      throw new ExecutionActionValidationError('invalid_request', 'search_space must contain a parameters array');
    }
    if (request.direction !== 'maximize' && request.direction !== 'minimize') {
      throw new ExecutionActionValidationError('invalid_request', 'direction must be maximize or minimize');
    }
    return {
      ...params,
      seal_id: requiredSealInput(request.sealId, 'seal_id'),
      task_id: requiredInput(request.taskId, 'task_id'),
      idea_id: stableTuningId(request.ideaId, 'idea_id'),
      durable_line_id: stableTuningId(request.durableLineId, 'durable_line_id'),
      parent_candidate_id: stableTuningId(request.parentCandidateId, 'parent_candidate_id'),
      direction: request.direction,
      search_space: request.searchSpace,
      ...(request.seed === undefined ? {} : { seed: requestNonnegativeInteger(request.seed, 'seed') }),
      ...(request.nStartupTrials === undefined
        ? {}
        : { n_startup_trials: requestPositiveInteger(request.nStartupTrials, 'n_startup_trials') }),
    };
  }
  if (request.action === 'tune_ask') {
    return {
      ...params,
      seal_id: requiredSealInput(request.sealId, 'seal_id'),
      task_id: requiredInput(request.taskId, 'task_id'),
    };
  }
  if (request.action === 'tune_tell') {
    if (request.state === 'complete' && (request.trialId === undefined || request.packetHash === undefined)) {
      throw new ExecutionActionValidationError(
        'invalid_request',
        'complete tune_tell requires trial_id and packet_hash'
      );
    }
    if (request.state !== 'complete' && (request.trialId !== undefined || request.packetHash !== undefined)) {
      throw new ExecutionActionValidationError(
        'invalid_request',
        'pruned or failed tune_tell cannot include trial_id or packet_hash'
      );
    }
    return {
      ...params,
      candidate_id: stableTuningId(request.candidateId, 'candidate_id'),
      state: request.state,
      ...(request.trialId === undefined ? {} : { trial_id: stableTuningId(request.trialId, 'trial_id') }),
      ...(request.packetHash === undefined
        ? {}
        : { packet_hash: requiredHashInput(request.packetHash, 'packet_hash') }),
    };
  }
  return params;
}

function parseTuningResult(result: Record<string, unknown>, request: CompetitionTuningRequest): TuningResult {
  const expected =
    request.action === 'tune_create'
      ? new Set(['create', 'read'])
      : request.action === 'tune_status' && request.studyId === undefined
        ? new Set(['capability'])
        : new Set([request.action.slice('tune_'.length)]);
  if (typeof result.operation !== 'string' || !expected.has(result.operation)) {
    identityMismatch('tuning operation does not match the request');
  }
  if (request.action === 'tune_status' && request.studyId === undefined) {
    parseTuningCapability(result.capability);
    return result as TuningResult;
  }
  if (request.action === 'tune_ask' || request.action === 'tune_tell') {
    const candidate = parseTuningCandidate(result.candidate, request);
    if (request.action === 'tune_tell') {
      const observation =
        result.observation === null ? null : parseCanonicalTuningObservation(result.observation, 'observation');
      if (request.state === 'complete') {
        if (observation === null || candidate.observation === null)
          invalid('complete tune_tell requires an observation');
        if (
          observation.candidateId !== request.candidateId.trim() ||
          observation.trialId !== request.trialId?.trim() ||
          observation.packetHash !== request.packetHash ||
          observation.sealId !== candidate.sealId ||
          observation.taskId !== candidate.taskId ||
          observation.value !== candidate.value ||
          JSON.stringify(result.observation) !==
            JSON.stringify((result.candidate as Record<string, unknown>).observation)
        ) {
          identityMismatch('canonical tuning observation does not match the request or candidate');
        }
      } else if (observation !== null || candidate.observation !== null) {
        invalid('pruned or failed tune_tell cannot return an observation');
      }
    }
    return result as TuningResult;
  }
  parseTuningCapability(result.capability);
  parseTuningStudy(result, request);
  return result as TuningResult;
}

function parseTuningCapability(value: unknown): void {
  if (!isRecord(value)) invalid('tuning capability must be an object');
  if (
    typeof value.available !== 'boolean' ||
    value.backend !== 'optuna_tpe' ||
    value.distribution !== 'optuna' ||
    value.fallback !== 'none' ||
    (value.version !== null && typeof value.version !== 'string') ||
    (value.reason !== null && typeof value.reason !== 'string')
  ) {
    invalid('tuning capability is invalid');
  }
}

function parseTuningStudy(
  result: Record<string, unknown>,
  request: CompetitionTuneCreateRequest | CompetitionTuneStatusRequest
): void {
  if (result.schema !== 'deepscientist.ioai.competition.tpe-study.v2' || result.backend !== 'optuna_tpe') {
    invalid('tuning study schema is invalid');
  }
  if (requiredString(result, 'study_id') !== request.studyId?.trim()) identityMismatch('study_id does not match');
  const sealId = requiredSealId(result, 'seal_id');
  const taskId = requiredString(result, 'task_id');
  const parentCandidateId = stableTuningId(requiredString(result, 'parent_candidate_id'), 'parent_candidate_id');
  const parentSearchLineageHash = requiredHash(result, 'parent_search_lineage_hash');
  const hash = requiredHash(result, 'search_space_hash');
  if (
    !isRecord(result.search_space) ||
    result.search_space.schema !== 'deepscientist.ioai.competition.search-space.v1'
  ) {
    invalid('tuning search_space is invalid');
  }
  if (!isRecord(result.counts)) invalid('tuning counts must be an object');
  for (const field of ['pending', 'complete', 'pruned', 'failed'])
    requiredRevision(result.counts[field], `counts.${field}`);
  if (!Array.isArray(result.pending)) invalid('tuning pending must be an array');
  if (request.action === 'tune_create') {
    if (sealId !== request.sealId.trim() || taskId !== request.taskId.trim()) {
      identityMismatch('tuning sealed task binding does not match');
    }
    if (requiredString(result, 'idea_id') !== request.ideaId.trim()) identityMismatch('idea_id does not match');
    if (requiredString(result, 'durable_line_id') !== request.durableLineId.trim()) {
      identityMismatch('durable_line_id does not match');
    }
    if (parentCandidateId !== request.parentCandidateId.trim()) {
      identityMismatch('parent_candidate_id does not match');
    }
    if (result.direction !== request.direction) identityMismatch('tuning direction does not match');
    requiredBoolean(result, 'created');
    requiredRelativeRef(result, 'storage_ref');
  }
  for (const candidate of result.pending) {
    const binding = parseTuningCandidate(candidate, {
      action: 'tune_status',
      projectRoot: request.projectRoot,
      studyId: request.studyId,
    });
    if (binding.sealId !== sealId || binding.taskId !== taskId) {
      identityMismatch('pending candidate sealed task binding does not match');
    }
    if (binding.searchSpaceHash !== hash) identityMismatch('pending search space does not match');
    if (
      binding.parentCandidateId !== parentCandidateId ||
      binding.parentSearchLineageHash !== parentSearchLineageHash
    ) {
      identityMismatch('pending parent search-lineage binding does not match');
    }
  }
}

function parseTuningCandidate(
  value: unknown,
  request: CompetitionTuneAskRequest | CompetitionTuneTellRequest | CompetitionTuneStatusRequest
): {
  sealId: string;
  taskId: string;
  searchSpaceHash: string;
  parentCandidateId: string;
  parentSearchLineageHash: string;
  value: number | null;
  observation: ParsedTuningObservation | null;
} {
  if (!isRecord(value)) invalid('tuning candidate must be an object');
  if (value.schema !== 'deepscientist.ioai.competition.tpe-candidate.v1' || value.backend !== 'optuna_tpe') {
    invalid('tuning candidate schema is invalid');
  }
  if (requiredString(value, 'study_id') !== request.studyId?.trim())
    identityMismatch('candidate study_id does not match');
  const sealId = requiredSealId(value, 'seal_id');
  const taskId = requiredString(value, 'task_id');
  stableTuningId(requiredString(value, 'candidate_id'), 'candidate_id');
  stableTuningId(requiredString(value, 'idea_id'), 'idea_id');
  stableTuningId(requiredString(value, 'durable_line_id'), 'durable_line_id');
  const parentCandidateId = stableTuningId(requiredString(value, 'parent_candidate_id'), 'parent_candidate_id');
  const parentSearchLineageHash = requiredHash(value, 'parent_search_lineage_hash');
  const searchSpaceHash = requiredHash(value, 'search_space_hash');
  requiredRevision(value.trial_number, 'trial_number');
  if (!isRecord(value.params) || !isRecord(value.search_space)) invalid('candidate parameter contract is invalid');
  const materialization = requiredRecord(value.materialization_binding, 'materialization_binding');
  if (materialization.schema !== 'deepscientist.ioai.competition.tpe-materialization.v1') {
    invalid('candidate materialization binding schema is invalid');
  }
  for (const field of [
    'study_id',
    'seal_id',
    'task_id',
    'candidate_id',
    'idea_id',
    'durable_line_id',
    'parent_candidate_id',
    'parent_search_lineage_hash',
  ]) {
    if (materialization[field] !== value[field]) identityMismatch(`materialization ${field} does not match candidate`);
  }
  if (requiredHash(materialization, 'search_space_hash') !== searchSpaceHash) {
    identityMismatch('materialization search space does not match candidate');
  }
  requiredHash(materialization, 'params_hash');
  if (!isRecord(materialization.params)) invalid('materialization params must be an object');
  if (!['pending', 'complete', 'pruned', 'failed'].includes(String(value.state))) invalid('candidate state is invalid');
  const candidateValue = value.value;
  const observation =
    value.observation === null ? null : parseCanonicalTuningObservation(value.observation, 'candidate.observation');
  if (value.state === 'complete') {
    if (typeof candidateValue !== 'number' || !Number.isFinite(candidateValue)) {
      invalid('complete candidate value must be finite');
    }
    if (observation !== null && observation.value !== candidateValue) {
      invalid('candidate observation value does not match');
    }
  } else if (candidateValue !== null || observation !== null) {
    invalid('non-complete candidate value and observation must be null');
  }
  if (request.action === 'tune_ask' && value.state !== 'pending') identityMismatch('asked candidate must be pending');
  if (request.action === 'tune_ask' && (sealId !== request.sealId.trim() || taskId !== request.taskId.trim())) {
    identityMismatch('candidate sealed task binding does not match');
  }
  if (request.action === 'tune_tell') {
    if (requiredString(value, 'candidate_id') !== request.candidateId.trim() || value.state !== request.state) {
      identityMismatch('told candidate identity or state does not match');
    }
  }
  return {
    sealId,
    taskId,
    searchSpaceHash,
    parentCandidateId,
    parentSearchLineageHash,
    value: typeof candidateValue === 'number' ? candidateValue : null,
    observation,
  };
}

type ParsedTuningObservation = {
  candidateId: string;
  trialId: string;
  packetHash: string;
  sealId: string;
  taskId: string;
  value: number;
};

function parseCanonicalTuningObservation(value: unknown, field: string): ParsedTuningObservation {
  const observation = requiredRecord(value, field);
  if (
    observation.schema !== 'deepscientist.ioai.competition.canonical-tuning-observation.v1' ||
    observation.profile !== 'contest'
  ) {
    invalid(`${field} schema or profile is invalid`);
  }
  const direction = observation.direction;
  if (direction !== 'maximize' && direction !== 'minimize') invalid(`${field} direction is invalid`);
  const sealId = requiredSealId(observation, 'seal_id');
  const taskId = requiredString(observation, 'task_id');
  requiredHash(observation, 'candidate_spec_hash');
  return {
    candidateId: stableTuningId(requiredString(observation, 'candidate_id'), 'candidate_id'),
    trialId: stableTuningId(requiredString(observation, 'trial_id'), 'trial_id'),
    packetHash: requiredHash(observation, 'packet_hash'),
    sealId,
    taskId,
    value: requiredFiniteNumber(observation, 'value'),
  };
}

function parseTrial(
  result: Record<string, unknown>,
  request: CompetitionTrialRunRequest | CompetitionTrialBatchRequest
): TrialResult {
  const expectedOperation = request.action === 'trial_run' ? 'run' : 'batch';
  if (result.operation !== expectedOperation) identityMismatch('trial operation does not match the request');
  const sealId = requiredSealId(result, 'seal_id');
  if (sealId !== request.sealId.trim()) identityMismatch('trial seal_id does not match the request');
  const taskId = requiredString(result, 'task_id');
  if (taskId !== request.taskId.trim()) identityMismatch('trial task_id does not match the request');
  const profileEvidence = parseProfileEvidence(result, requestProfile(request.profile), 'trial');
  const revision = requiredRevision(result.frontier_revision, 'frontier_revision');
  if (revision <= request.expectedFrontierRevision) invalid('trial frontier_revision must advance');
  const maxWorkers = resultWorkers(result.max_workers);
  if (request.action === 'trial_run' && maxWorkers !== 1) invalid('trial_run max_workers must be 1');
  if (request.action === 'trial_batch' && maxWorkers !== request.maxWorkers) {
    identityMismatch('trial max_workers does not match the request');
  }
  const mode = result.mode;
  if (mode !== 'serial' && mode !== 'parallel') invalid('trial mode must be serial or parallel');
  if (request.action === 'trial_run' && mode !== 'serial') invalid('trial_run mode must be serial');
  if (maxWorkers > 1 !== (mode === 'parallel')) invalid('trial mode and max_workers are inconsistent');
  const items = parseTrialItems(result.results, profileEvidence.profile);
  const trialCount = requiredCount(result, 'trial_count');
  const validCount = requiredCount(result, 'valid_count');
  const invalidCount = requiredCount(result, 'invalid_count');
  const cacheHits = requiredCount(result, 'cache_hits');
  const cacheMisses = requiredCount(result, 'cache_misses');
  if (trialCount !== items.length || validCount + invalidCount !== trialCount) {
    invalid('trial counts are inconsistent');
  }
  if (cacheHits + cacheMisses !== trialCount || items.filter((item) => item.cache_hit).length !== cacheHits) {
    invalid('trial cache counts are inconsistent');
  }
  if (items.filter((item) => item.valid).length !== validCount) invalid('valid_count is inconsistent');
  if (new Set(items.map((item) => item.direction)).size !== 1) invalid('trial result directions are inconsistent');
  const incumbentId = optionalCanonicalId(result.incumbent_id, 'incumbent_id', 'trial');
  const incumbentScore = optionalFiniteNumber(result.incumbent_score, 'incumbent_score');
  if ((incumbentId === null) !== (incumbentScore === null)) invalid('incumbent fields are inconsistent');
  return {
    action_version: 1,
    operation: expectedOperation,
    seal_id: sealId,
    task_id: taskId,
    ...profileEvidence,
    mode,
    max_workers: maxWorkers,
    trial_count: trialCount,
    valid_count: validCount,
    invalid_count: invalidCount,
    cache_hits: cacheHits,
    cache_misses: cacheMisses,
    frontier_revision: revision,
    incumbent_id: incumbentId,
    incumbent_score: incumbentScore,
    checkpoint_ref: requiredRelativeRef(result, 'checkpoint_ref'),
    results: items,
    recovered_trial_ids: canonicalIdArray(result.recovered_trial_ids, 'recovered_trial_ids', 'trial'),
    abandoned_trial_ids: canonicalIdArray(result.abandoned_trial_ids, 'abandoned_trial_ids', 'trial'),
    official_submission_enabled: false,
    ...parseIdempotency(result),
  };
}

function parseTrialItems(value: unknown, profile: IoaiCompetitionEvaluationProfile): TrialResultItem[] {
  if (!Array.isArray(value) || value.length === 0) invalid('results must be a non-empty array');
  const ids = new Set<string>();
  const items = value.map<TrialResultItem>((entry, index) => {
    if (!isRecord(entry)) invalid(`results[${index}] must be an object`);
    const field = `results[${index}]`;
    if (entry.profile !== profile) identityMismatch(`${field}.profile does not match the request`);
    const candidateIdentity = parseCompetitionCandidateIdentity(entry, field, invalid);
    const trialId = requiredCanonicalId(entry, 'trial_id', 'trial');
    if (ids.has(trialId)) invalid('results must contain unique trial_id values');
    ids.add(trialId);
    const direction = entry.direction;
    if (direction !== 'maximize' && direction !== 'minimize') invalid(`results[${index}].direction is invalid`);
    const valid = requiredBoolean(entry, 'valid');
    const score = optionalFiniteNumber(entry.score, `results[${index}].score`);
    const failureKind = optionalString(entry.failure_kind, `results[${index}].failure_kind`);
    if ((valid && (score === null || failureKind !== null)) || (!valid && (score !== null || failureKind === null))) {
      invalid(`results[${index}] validity fields are inconsistent`);
    }
    const resultRef = requiredRelativeRef(entry, 'result_ref');
    if (!resultRef.endsWith(`/trials/${trialId}/result.json`)) {
      invalid(`results[${index}].result_ref does not match trial_id`);
    }
    const candidateSpecRef = requiredRelativeRef(entry, 'candidate_spec_ref');
    if (!candidateSpecRef.endsWith(`/trials/${trialId}/candidate.json`)) {
      invalid(`results[${index}].candidate_spec_ref does not match trial_id`);
    }
    const candidateType = entry.candidate_type;
    if (candidateType !== 'single' && candidateType !== 'ensemble') {
      invalid(`${field}.candidate_type must be single or ensemble`);
    }
    const cacheHit = requiredBoolean(entry, 'cache_hit');
    const cacheEntryRef = optionalRelativeRef(entry.cache_entry_ref, `${field}.cache_entry_ref`);
    if (cacheHit && cacheEntryRef === null) {
      invalid(`${field}.cache_entry_ref is required for a cache hit`);
    }
    const candidateExecutionMode = entry.candidate_execution_mode;
    if (candidateExecutionMode !== 'executable' && candidateExecutionMode !== 'static-evaluator-fixture') {
      invalid(`${field}.candidate_execution_mode is invalid`);
    }
    const candidateAttempt = parseCandidateAttempt(
      entry.candidate_attempt,
      `${field}.candidate_attempt`,
      candidateExecutionMode,
      valid
    );
    const recoveryIntent = parseRecoveryIntent(entry.recovery_intent, `${field}.recovery_intent`, invalid);
    const resourceUsage = parseTrialResourceUsage(entry.resource_usage, `${field}.resource_usage`);
    if (
      candidateAttempt !== null &&
      candidateAttempt.wall_clock_seconds !== null &&
      candidateAttempt.wall_clock_seconds !== resourceUsage.candidate_attempt_seconds
    ) {
      invalid(`${field}.candidate attempt duration does not match resource usage`);
    }
    return {
      ...candidateIdentity,
      trial_id: trialId,
      trial_ref: requiredString(entry, 'trial_ref'),
      profile,
      candidate_spec_sha256: requiredHash(entry, 'candidate_spec_sha256'),
      candidate_spec_ref: candidateSpecRef,
      candidate_type: candidateType,
      valid,
      score,
      direction,
      failure_kind: failureKind,
      packet_hash: requiredHash(entry, 'packet_hash'),
      result_ref: resultRef,
      cache_key: requiredHash(entry, 'cache_key'),
      cache_hit: cacheHit,
      cache_entry_ref: cacheEntryRef,
      candidate_execution_mode: candidateExecutionMode,
      candidate_attempt: candidateAttempt,
      recovery_intent: recoveryIntent,
      resource_usage: resourceUsage,
    };
  });
  assertUniqueCompetitionCandidateIdentities(items, 'results', invalid);
  return items;
}

function parseRecoveryIntent(
  value: unknown,
  field: string,
  invalid: (message: string) => never
): CompetitionRecoveryIntent | null {
  if (value === null || value === undefined) return null;
  if (!isRecord(value)) invalid(`${field} must be an object or null`);
  const keys = Object.keys(value).toSorted();
  const expected = [
    'candidate_id',
    'control_key',
    'purpose',
    'route',
    'schema',
    'seal_id',
    'source_frontier_revision',
    'task_id',
  ];
  if (keys.length !== expected.length || keys.some((key, index) => key !== expected[index])) {
    invalid(`${field} fields are invalid`);
  }
  if (
    value.schema !== 'deepscientist.ioai.competition.recovery-intent.v1' ||
    value.route !== 'recovery' ||
    value.purpose !== 'minimum_valid_candidate'
  ) {
    invalid(`${field} schema or purpose is unsupported`);
  }
  if (
    typeof value.seal_id !== 'string' ||
    typeof value.task_id !== 'string' ||
    typeof value.candidate_id !== 'string' ||
    typeof value.control_key !== 'string' ||
    !/^[0-9a-f]{64}$/u.test(value.control_key) ||
    typeof value.source_frontier_revision !== 'number' ||
    !Number.isInteger(value.source_frontier_revision) ||
    value.source_frontier_revision < 0
  ) {
    invalid(`${field} contains invalid identity or revision fields`);
  }
  return value as CompetitionRecoveryIntent;
}

function parseCandidateAttempt(
  value: unknown,
  field: string,
  mode: TrialCandidateExecutionMode,
  valid: boolean
): TrialCandidateAttempt | null {
  if (value === null) {
    if (mode === 'executable' && valid) invalid(`${field} is required for valid executable evidence`);
    return null;
  }
  if (mode !== 'executable') invalid(`${field} is only valid for executable candidates`);
  if (!isRecord(value)) invalid(`${field} must be an object or null`);
  if (value.schema !== 'deepscientist.ioai.competition.attempt-receipt.v1') {
    invalid(`${field}.schema is invalid`);
  }
  const status = value.status;
  if (status !== 'passed' && status !== 'failed' && status !== 'cache_reused') {
    invalid(`${field}.status is invalid`);
  }
  if (valid && status !== 'passed' && status !== 'cache_reused') {
    invalid(`${field}.status cannot support valid evidence`);
  }
  const receiptHash = status === 'cache_reused' ? null : requiredHash(value, 'receipt_hash');
  const wallClockSeconds =
    status === 'cache_reused'
      ? null
      : requiredNonnegativeFiniteNumber(value.wall_clock_seconds, `${field}.wall_clock_seconds`);
  if (status === 'cache_reused' && optionalRelativeRef(value.cache_entry_ref, `${field}.cache_entry_ref`) === null) {
    invalid(`${field}.cache_entry_ref is required for cache reuse`);
  }
  return {
    ...value,
    schema: 'deepscientist.ioai.competition.attempt-receipt.v1',
    status,
    source_manifest_hash: requiredHash(value, 'source_manifest_hash'),
    receipt_hash: receiptHash,
    wall_clock_seconds: wallClockSeconds,
  };
}

function parseTrialResourceUsage(value: unknown, field: string): TrialResourceUsage {
  if (!isRecord(value)) invalid(`${field} must be an object`);
  return {
    wall_clock_seconds: requiredNonnegativeFiniteNumber(value.wall_clock_seconds, `${field}.wall_clock_seconds`),
    candidate_attempt_seconds: optionalNonnegativeFiniteNumber(
      value.candidate_attempt_seconds,
      `${field}.candidate_attempt_seconds`
    ),
  };
}

function parseReport(result: Record<string, unknown>, request: CompetitionReportGenerateRequest): ReportResult {
  if (result.operation !== 'generate') identityMismatch('report operation does not match the request');
  const sealId = requiredSealId(result, 'seal_id');
  if (sealId !== request.sealId.trim()) identityMismatch('report seal_id does not match the request');
  const taskId = requiredString(result, 'task_id');
  if (taskId !== request.taskId.trim()) identityMismatch('report task_id does not match the request');
  const profileEvidence = parseProfileEvidence(result, requestProfile(request.profile), 'report', true);
  const revision = requiredRevision(result.frontier_revision, 'frontier_revision');
  if (revision !== request.expectedFrontierRevision)
    identityMismatch('report frontier_revision does not match the request');
  const reportId = requiredCanonicalId(result, 'report_id', 'report');
  const reportStatus = result.report_status;
  if (reportStatus !== 'complete' && reportStatus !== 'partial_blocked') invalid('report_status is invalid');
  if (reportStatus === 'partial_blocked' && (revision !== 0 || result.final_evidence_eligible !== false)) {
    invalid('partial report must remain ineligible at frontier revision zero');
  }
  const manifestRef = requiredRelativeRef(result, 'report_manifest_ref');
  const reportRef = requiredRelativeRef(result, 'report_ref');
  const expectedReportRoot = `.deepscientist/competition/reports/${sealId}/${profileEvidence.profile}/${reportId}`;
  if (manifestRef !== `${expectedReportRoot}/report_manifest.json` || reportRef !== `${expectedReportRoot}/report.md`) {
    invalid('report refs do not match report_id');
  }
  return {
    action_version: 1,
    operation: 'generate',
    report_status: reportStatus,
    report_id: reportId,
    seal_id: sealId,
    task_id: taskId,
    ...profileEvidence,
    frontier_revision: revision,
    report_manifest_hash: requiredHash(result, 'report_manifest_hash'),
    rendered_markdown_sha256: requiredHash(result, 'rendered_markdown_sha256'),
    report_manifest_ref: manifestRef,
    report_ref: reportRef,
    limitation_count: requiredCount(result, 'limitation_count'),
    trial_count: requiredCount(result, 'trial_count'),
    official_submission_enabled: false,
    ...parseIdempotency(result),
  };
}

function requestProfile(value: unknown): IoaiCompetitionEvaluationProfile {
  if (value === undefined) return DEFAULT_IOAI_COMPETITION_EVALUATION_PROFILE;
  if (!isIoaiCompetitionEvaluationProfile(value)) {
    throw new ExecutionActionValidationError('invalid_request', 'profile must be smoke, sprint, contest, or audit');
  }
  return value;
}

function parseProfileEvidence(
  result: Record<string, unknown>,
  expectedProfile: IoaiCompetitionEvaluationProfile,
  label: string,
  allowFinalEvidenceDowngrade = false
): {
  profile: IoaiCompetitionEvaluationProfile;
  profile_contract: IoaiCompetitionEvaluationProfileContract;
  final_evidence_eligible: boolean;
} {
  if (!isIoaiCompetitionEvaluationProfile(result.profile)) invalid(`${label} profile is invalid`);
  if (result.profile !== expectedProfile) identityMismatch(`${label} profile does not match the request`);
  if (!isIoaiCompetitionEvaluationProfileContract(result.profile_contract, result.profile)) {
    invalid(`${label} profile_contract is invalid`);
  }
  const contract = getIoaiCompetitionEvaluationProfileContract(result.profile);
  const finalEvidenceEligible = requiredBoolean(result, 'final_evidence_eligible');
  if (
    (finalEvidenceEligible && !contract.final_evidence_eligible) ||
    (!allowFinalEvidenceDowngrade && finalEvidenceEligible !== contract.final_evidence_eligible)
  ) {
    invalid(`${label} final_evidence_eligible is inconsistent`);
  }
  return {
    profile: result.profile,
    profile_contract: contract,
    final_evidence_eligible: finalEvidenceEligible,
  };
}

function parseIdempotency(result: Record<string, unknown>): IdempotentResult {
  return {
    replayed: requiredBoolean(result, 'replayed'),
    command_receipt_hash: requiredHash(result, 'command_receipt_hash'),
  };
}

function requiredInput(value: unknown, field: string): string {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new ExecutionActionValidationError('invalid_request', `${field} must be a non-empty string`);
  }
  return value.trim();
}

function requiredHashInput(value: unknown, field: string): string {
  const normalized = requiredInput(value, field).toLowerCase();
  if (!/^[0-9a-f]{64}$/u.test(normalized)) {
    throw new ExecutionActionValidationError('invalid_request', `${field} must be a SHA-256 hash`);
  }
  return normalized;
}

function stableTuningId(value: unknown, field: string): string {
  const normalized = requiredInput(value, field);
  if (!/^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$/u.test(normalized)) {
    throw new ExecutionActionValidationError('invalid_request', `${field} must be a stable identifier`);
  }
  return normalized;
}

function requestNonnegativeInteger(value: unknown, field: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) {
    throw new ExecutionActionValidationError('invalid_request', `${field} must be a non-negative integer`);
  }
  return Number(value);
}

function requestPositiveInteger(value: unknown, field: string): number {
  const result = requestNonnegativeInteger(value, field);
  if (result < 1) throw new ExecutionActionValidationError('invalid_request', `${field} must be positive`);
  return result;
}

function requiredSealInput(value: unknown, field: string): string {
  const normalized = requiredInput(value, field);
  if (!/^tc-[0-9a-f]{12}$/u.test(normalized)) {
    throw new ExecutionActionValidationError('invalid_request', `${field} must be a canonical seal ID`);
  }
  return normalized;
}

function requiredString(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || value.length === 0) invalid(`${key} must be a non-empty string`);
  return value;
}

function requiredBoolean(source: Record<string, unknown>, key: string): boolean {
  const value = source[key];
  if (typeof value !== 'boolean') invalid(`${key} must be a boolean`);
  return value;
}

function requiredRecord(value: unknown, field: string): Record<string, unknown> {
  if (!isRecord(value)) invalid(`${field} must be an object`);
  return value;
}

function requiredFiniteNumber(source: Record<string, unknown>, key: string): number {
  const value = source[key];
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${key} must be a finite number`);
  return value;
}

function requiredCount(source: Record<string, unknown>, key: string): number {
  return requiredRevision(source[key], key);
}

function requiredRevision(value: unknown, field: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) invalid(`${field} must be a non-negative integer`);
  return Number(value);
}

function requestRevision(value: unknown): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) {
    throw new ExecutionActionValidationError(
      'invalid_request',
      'expected_frontier_revision must be a non-negative integer'
    );
  }
  return Number(value);
}

function requestWorkers(value: unknown): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1 || Number(value) > 32) {
    throw new ExecutionActionValidationError('invalid_request', 'max_workers must be an integer between 1 and 32');
  }
  return Number(value);
}

function resultWorkers(value: unknown): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1 || Number(value) > 32) {
    invalid('max_workers must be an integer between 1 and 32');
  }
  return Number(value);
}

function optionalFiniteNumber(value: unknown, field: string): number | null {
  if (value === null) return null;
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${field} must be a finite number or null`);
  return value;
}

function requiredNonnegativeFiniteNumber(value: unknown, field: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) {
    invalid(`${field} must be a non-negative finite number`);
  }
  return value;
}

function optionalNonnegativeFiniteNumber(value: unknown, field: string): number | null {
  if (value === null) return null;
  return requiredNonnegativeFiniteNumber(value, field);
}

function requiredHash(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !/^[0-9a-f]{64}$/u.test(value)) invalid(`${key} must be a SHA-256 hash`);
  return value;
}

function requiredSealId(source: Record<string, unknown>, key: string): string {
  const value = requiredString(source, key);
  if (!/^tc-[0-9a-f]{12}$/u.test(value)) invalid(`${key} must be a canonical seal ID`);
  return value;
}

function requiredCanonicalId(source: Record<string, unknown>, key: string, prefix: 'trial' | 'report'): string {
  const value = requiredString(source, key);
  if (!(prefix === 'trial' ? /^trial-[0-9a-f]{8}$/u : /^report-[0-9a-f]{8}$/u).test(value)) {
    invalid(`${key} must be a canonical ${prefix} ID`);
  }
  return value;
}

function optionalCanonicalId(value: unknown, field: string, prefix: 'trial' | 'report'): string | null {
  if (value === null) return null;
  if (
    typeof value !== 'string' ||
    !(prefix === 'trial' ? /^trial-[0-9a-f]{8}$/u : /^report-[0-9a-f]{8}$/u).test(value)
  ) {
    invalid(`${field} must be a canonical ${prefix} ID or null`);
  }
  return value;
}

function canonicalIdArray(value: unknown, field: string, prefix: 'trial' | 'report'): string[] {
  if (!Array.isArray(value) || value.some((item) => typeof item !== 'string')) invalid(`${field} must be an ID array`);
  const values = (value as string[]).map((item) => {
    if (!(prefix === 'trial' ? /^trial-[0-9a-f]{8}$/u : /^report-[0-9a-f]{8}$/u).test(item))
      invalid(`${field} contains an invalid ID`);
    return item;
  });
  if (new Set(values).size !== values.length) invalid(`${field} must contain unique IDs`);
  return values;
}

function requiredRelativeRef(source: Record<string, unknown>, key: string): string {
  const value = requiredString(source, key);
  if (
    value.startsWith('/') ||
    value.includes('\\') ||
    value.split('/').some((part) => part === '' || part === '.' || part === '..')
  ) {
    invalid(`${key} must be a normalized relative path`);
  }
  return value;
}

function optionalRelativeRef(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (
    typeof value !== 'string' ||
    value.length === 0 ||
    value.startsWith('/') ||
    value.includes('\\') ||
    value.split('/').some((part) => part === '' || part === '.' || part === '..')
  ) {
    invalid(`${field} must be a normalized relative path or null`);
  }
  return value;
}

function optionalString(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || value.length === 0) invalid(`${field} must be a non-empty string or null`);
  return value;
}

function unavailableResult(
  action: CompetitionExecutionRequest['action'],
  error: unknown
): CompetitionExecutionActionResult {
  if (error instanceof CompetitionEngineDiscoveryError) return unavailable(action, error.code, error.message, false);
  if (error instanceof CompetitionEngineClientError) {
    const code = error.engineCode === 'capability_unavailable' ? error.engineCode : error.code;
    return unavailable(action, code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof ExecutionActionValidationError) return unavailable(action, error.code, error.message, false);
  return unavailable(action, 'execution_action_failed', 'IOAI competition execution action failed', false);
}

function unavailable(
  action: CompetitionExecutionRequest['action'],
  code: string,
  message: string,
  retryable: boolean,
  diagnostic?: string,
  engineCode?: string
): CompetitionExecutionActionResult {
  return {
    schema: COMPETITION_EXECUTION_ACTION_SCHEMA,
    status: 'unavailable',
    action,
    official_submission_enabled: false,
    error: {
      code,
      message,
      retryable,
      ...(engineCode ? { engine_code: engineCode } : {}),
    },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}

function invalid(message: string): never {
  throw new ExecutionActionValidationError('invalid_execution_result', message);
}

function identityMismatch(message: string): never {
  throw new ExecutionActionValidationError('execution_identity_mismatch', message);
}
