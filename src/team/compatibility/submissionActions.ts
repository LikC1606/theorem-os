/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import { IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION } from "../../common/chat/ioaiCompetition";
import {
  CompetitionEngineClientError,
  CompetitionEngineJsonlClient,
  type CompetitionEngineCommandResult,
  type CompetitionEngineLaunch,
  type CompetitionEngineRequestOptions,
} from "../competition-runtime/jsonlClient";
import { CompetitionEngineDiscoveryError, discoverCompetitionEngineLaunch } from "../competition-runtime/engineDiscovery";

export const COMPETITION_OFFICIAL_SUBMISSION_ACTION_SCHEMA =
  'deepscientist.ioai.competition.official-submission-action.v1' as const;
export const KAGGLE_SUBMISSION_AUTHORIZATION_SCHEMA =
  'deepscientist.ioai.kaggle-notebook-submission-authorization.v1' as const;
export const KAGGLE_NOTEBOOK_SUBMISSION_TOOLS = Object.freeze([
  'save_notebook',
  'get_notebook_session_status',
  'create_code_competition_submission',
  'search_competition_submissions',
  'get_competition_submission',
] as const);

export type CompetitionOfficialSubmissionRequest = {
  action: 'official_submission';
  projectRoot: string;
  operation: 'authorize' | 'read' | 'prepare' | 'record';
  competitionId?: string;
  notebookRef?: string;
  deadlineUtc?: string;
  maxSubmissions?: number;
  protectedReserve?: number;
  authorizationPromptSha256?: string;
  sealId?: string;
  taskId?: string;
  trialId?: string;
  packetHash?: string;
  notebookPath?: string;
  notebookVersion?: string;
  roleId?: string;
  attemptKey?: string;
  promptHash?: string;
  evaluatorVersion?: string;
  useReserve?: boolean;
  attemptId?: string;
  notebookVersionId?: string;
  submissionId?: string;
  remoteStatus?: string;
  remoteReceiptPath?: string;
  score?: number;
  failureKind?: string;
  idempotencyKey?: string;
};

type OfficialSubmissionPayload = Record<string, unknown> & {
  action_version: 1;
  operation: CompetitionOfficialSubmissionRequest['operation'];
  competition_id: string;
  notebook_ref: string;
  authorization_hash: string;
  official_submission_enabled: true;
};

export type CompetitionOfficialSubmissionActionResult =
  | {
      schema: typeof COMPETITION_OFFICIAL_SUBMISSION_ACTION_SCHEMA;
      status: 'ready';
      action: 'official_submission';
      official_submission_enabled: true;
      result: OfficialSubmissionPayload;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_OFFICIAL_SUBMISSION_ACTION_SCHEMA;
      status: 'unavailable';
      action: 'official_submission';
      official_submission_enabled: false;
      error: { code: string; message: string; retryable: boolean; engine_code?: string };
      diagnostics?: { stderr: string };
    };

export type CompetitionOfficialSubmissionReaderOptions = CompetitionEngineRequestOptions & {
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestAction?: (
    launch: CompetitionEngineLaunch,
    action: 'official_submission',
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

export type CompetitionOfficialSubmissionToolResult = {
  content: [{ type: 'text'; text: string }];
  isError?: true;
};

class OfficialSubmissionValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'OfficialSubmissionValidationError';
  }
}

export async function readCompetitionOfficialSubmissionAction(
  request: CompetitionOfficialSubmissionRequest,
  options: CompetitionOfficialSubmissionReaderOptions = {}
): Promise<CompetitionOfficialSubmissionActionResult> {
  try {
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const requestAction = options.requestAction ?? defaultActionRequest;
    const response = await requestAction(launch, 'official_submission', requestParams(request), {
      timeoutMs: options.timeoutMs,
      signal: options.signal,
    });
    const result = parseResult(response.result, request);
    return {
      schema: COMPETITION_OFFICIAL_SUBMISSION_ACTION_SCHEMA,
      status: 'ready',
      action: 'official_submission',
      official_submission_enabled: true,
      result,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailable(error);
  }
}

export function formatCompetitionOfficialSubmissionAction(
  result: CompetitionOfficialSubmissionActionResult
): CompetitionOfficialSubmissionToolResult {
  const formatted: CompetitionOfficialSubmissionToolResult = {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) }],
  };
  if (result.status === 'unavailable') formatted.isError = true;
  return formatted;
}

async function defaultActionRequest(
  launch: CompetitionEngineLaunch,
  action: 'official_submission',
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request(action, params, options);
}

function requestParams(request: CompetitionOfficialSubmissionRequest): Record<string, unknown> {
  const base = {
    project_root: requiredText(request.projectRoot, 'project_root'),
    operation: request.operation,
  };
  if (request.operation === 'read') return base;
  const idempotency_key = requiredText(request.idempotencyKey, 'idempotency_key');
  if (request.operation === 'authorize') {
    return {
      ...base,
      competition_id: requiredText(request.competitionId, 'competition_id'),
      notebook_ref: requiredText(request.notebookRef, 'notebook_ref'),
      deadline_utc: requiredText(request.deadlineUtc, 'deadline_utc'),
      max_submissions: requiredCount(
        request.maxSubmissions,
        'max_submissions',
        1,
        IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION
      ),
      protected_reserve: requiredCount(
        request.protectedReserve,
        'protected_reserve',
        0,
        IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION - 1
      ),
      authorization_prompt_sha256: requiredHash(request.authorizationPromptSha256, 'authorization_prompt_sha256'),
      idempotency_key,
    };
  }
  if (request.operation === 'prepare') {
    return {
      ...base,
      competition_id: requiredText(request.competitionId, 'competition_id'),
      seal_id: requiredText(request.sealId, 'seal_id'),
      task_id: requiredText(request.taskId, 'task_id'),
      trial_id: requiredText(request.trialId, 'trial_id'),
      packet_hash: requiredHash(request.packetHash, 'packet_hash'),
      notebook_path: requiredText(request.notebookPath, 'notebook_path'),
      notebook_ref: requiredText(request.notebookRef, 'notebook_ref'),
      notebook_version: requiredText(request.notebookVersion, 'notebook_version'),
      role_id: requiredText(request.roleId, 'role_id'),
      attempt_key: requiredText(request.attemptKey, 'attempt_key'),
      prompt_hash: requiredHash(request.promptHash, 'prompt_hash'),
      evaluator_version: requiredText(request.evaluatorVersion, 'evaluator_version'),
      ...(request.useReserve === undefined ? {} : { use_reserve: requiredBoolean(request.useReserve, 'use_reserve') }),
      idempotency_key,
    };
  }
  return {
    ...base,
    attempt_id: requiredText(request.attemptId, 'attempt_id'),
    competition_id: requiredText(request.competitionId, 'competition_id'),
    notebook_ref: requiredText(request.notebookRef, 'notebook_ref'),
    notebook_version_id: requiredText(request.notebookVersionId, 'notebook_version_id'),
    submission_id: requiredText(request.submissionId, 'submission_id'),
    remote_status: requiredText(request.remoteStatus, 'remote_status'),
    remote_receipt_path: requiredText(request.remoteReceiptPath, 'remote_receipt_path'),
    ...(request.score === undefined ? {} : { score: requiredFinite(request.score, 'score') }),
    ...(request.failureKind === undefined ? {} : { failure_kind: requiredText(request.failureKind, 'failure_kind') }),
    idempotency_key,
  };
}

function parseResult(
  result: Record<string, unknown>,
  request: CompetitionOfficialSubmissionRequest
): OfficialSubmissionPayload {
  if (result.action_version !== 1) invalid('action_version must be 1');
  if (result.operation !== request.operation) invalid('operation does not match the request');
  if (result.official_submission_enabled !== true) {
    throw new OfficialSubmissionValidationError(
      'submission_authorization_missing',
      'official submission action must return its sealed authorization capability'
    );
  }
  requiredText(result.competition_id, 'competition_id');
  requiredText(result.notebook_ref, 'notebook_ref');
  requiredHash(result.authorization_hash, 'authorization_hash');
  requiredCount(result.remaining, 'remaining', 0, IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION);
  requiredCount(result.sent_count, 'sent_count', 0, IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION);
  if (request.operation === 'authorize' || request.operation === 'read') {
    if (result.status !== 'authorized') invalid('authorization status must be authorized');
    if (result.schema !== KAGGLE_SUBMISSION_AUTHORIZATION_SCHEMA) invalid('authorization schema is invalid');
    requiredText(result.deadline_utc, 'deadline_utc');
    const maxSubmissions = requiredCount(
      result.max_submissions,
      'max_submissions',
      1,
      IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION
    );
    const protectedReserve = requiredCount(
      result.protected_reserve,
      'protected_reserve',
      0,
      IOAI_COMPETITION_MAX_SUBMISSIONS_PER_QUESTION - 1
    );
    if (protectedReserve >= maxSubmissions) invalid('protected_reserve must be less than max_submissions');
    requiredHash(result.authorization_prompt_sha256, 'authorization_prompt_sha256');
    requiredText(result.lead_role_id, 'lead_role_id');
    exactTools(result.allowed_tools);
    if (result.quota_reservation !== 'before_remote_send') invalid('quota reservation policy is invalid');
    if (result.uncertain_response_policy !== 'poll_only_no_resend') invalid('uncertain response policy is invalid');
  } else if (request.operation === 'prepare') {
    if (result.status !== 'send_reserved') invalid('prepare status must reserve the remote send');
    requiredText(result.attempt_id, 'attempt_id');
    requiredText(result.remote_job_id, 'remote_job_id');
    requiredHash(result.payload_hash, 'payload_hash');
    requiredHash(result.prepared_hash, 'prepared_hash');
    requiredRelativeRef(result.prepared_ref, 'prepared_ref');
    const notebookSourceRef = requiredRelativeRef(result.notebook_source_ref, 'notebook_source_ref');
    const requestedNotebook = requiredRelativeRef(request.notebookPath, 'request.notebook_path');
    if (notebookSourceRef !== requestedNotebook) invalid('notebook source does not match the request');
    const notebookPath = requiredRelativeRef(result.notebook_path, 'notebook_path');
    if (!notebookPath.endsWith(`/source/${notebookSourceRef}`)) {
      invalid('notebook_path is not a canonical Candidate Attempt snapshot');
    }
    requiredHash(result.notebook_sha256, 'notebook_sha256');
    requiredCount(result.notebook_size_bytes, 'notebook_size_bytes', 0, Number.MAX_SAFE_INTEGER);
    requiredHash(result.candidate_source_manifest_hash, 'candidate_source_manifest_hash');
    requiredHash(result.candidate_receipt_hash, 'candidate_receipt_hash');
    exactTools(result.allowed_remote_sequence);
    if (result.quota_consumed_before_remote_send !== true) invalid('prepare must consume quota before send');
    if (result.uncertain_response_policy !== 'poll_only_no_resend') invalid('uncertain response policy is invalid');
  } else {
    if (!['scored', 'complete', 'failed'].includes(String(result.status))) {
      invalid('record status is invalid');
    }
    requiredText(result.attempt_id, 'attempt_id');
    requiredText(result.submission_id, 'submission_id');
    requiredText(result.notebook_version_id, 'notebook_version_id');
    requiredHash(result.receipt_hash, 'receipt_hash');
    requiredHash(result.remote_receipt_sha256, 'remote_receipt_sha256');
    requiredRelativeRef(result.receipt_ref, 'receipt_ref');
  }
  return result as OfficialSubmissionPayload;
}

function exactTools(value: unknown): void {
  if (
    !Array.isArray(value) ||
    value.length !== KAGGLE_NOTEBOOK_SUBMISSION_TOOLS.length ||
    !value.every((item, index) => item === KAGGLE_NOTEBOOK_SUBMISSION_TOOLS[index])
  ) {
    invalid('Kaggle MCP tool contract is invalid');
  }
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) invalid(`${field} must be a non-empty string`);
  return value.trim();
}

function requiredHash(value: unknown, field: string): string {
  const text = requiredText(value, field);
  if (!/^[0-9a-f]{64}$/u.test(text)) invalid(`${field} must be a SHA-256 hash`);
  return text;
}

function requiredCount(value: unknown, field: string, minimum: number, maximum: number): number {
  if (!Number.isSafeInteger(value) || Number(value) < minimum || Number(value) > maximum) {
    invalid(`${field} must be an integer within [${minimum}, ${maximum}]`);
  }
  return Number(value);
}

function requiredBoolean(value: unknown, field: string): boolean {
  if (typeof value !== 'boolean') invalid(`${field} must be a boolean`);
  return value;
}

function requiredFinite(value: unknown, field: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${field} must be finite`);
  return value;
}

function requiredRelativeRef(value: unknown, field: string): string {
  const text = requiredText(value, field);
  const parts = text.split('/');
  if (text.startsWith('/') || text.includes('\\') || parts.includes('.') || parts.includes('..')) {
    invalid(`${field} must be a normalized relative path`);
  }
  return text;
}

function unavailable(error: unknown): CompetitionOfficialSubmissionActionResult {
  if (error instanceof CompetitionEngineDiscoveryError) {
    return unavailableResult(error.code, error.message, false);
  }
  if (error instanceof CompetitionEngineClientError) {
    return unavailableResult(error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof OfficialSubmissionValidationError) {
    return unavailableResult(error.code, error.message, false);
  }
  return unavailableResult('official_submission_failed', 'Official submission action failed', false);
}

function unavailableResult(
  code: string,
  message: string,
  retryable: boolean,
  diagnostic = '',
  engineCode?: string
): CompetitionOfficialSubmissionActionResult {
  return {
    schema: COMPETITION_OFFICIAL_SUBMISSION_ACTION_SCHEMA,
    status: 'unavailable',
    action: 'official_submission',
    official_submission_enabled: false,
    error: { code, message, retryable, ...(engineCode ? { engine_code: engineCode } : {}) },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}

function invalid(message: string): never {
  throw new OfficialSubmissionValidationError('invalid_official_submission_result', message);
}
