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
import path from 'node:path';

export const COMPETITION_WORKFLOW_ACTION_SCHEMA = 'deepscientist.ioai.competition.workflow-action.v1';

export type CompetitionTaskImportRequest = {
  action: 'task_import';
  projectRoot: string;
  bundlePath: string;
  idempotencyKey: string;
};

export type CompetitionEnvironmentPreflightRequest = {
  action: 'environment_preflight';
  projectRoot: string;
  preflightPath: string;
};

export type CompetitionBootstrapRequest = {
  action: 'bootstrap_run';
  projectRoot: string;
  preflightPath: string;
  bundlePath: string;
  baselineCandidatePath: string;
  idempotencyKey: string;
};

export type CompetitionEvaluatorAuditRequest = {
  action: 'evaluator_audit';
  projectRoot: string;
  sealId: string;
  idempotencyKey: string;
};

export type CompetitionLockRequest =
  | {
      action: 'competition_lock';
      operation: 'arm';
      projectRoot: string;
      competitionId: string;
      systemId: string;
      authorizationPromptSha256: string;
      baselineAttemptLimit: number;
      idempotencyKey: string;
    }
  | {
      action: 'competition_lock';
      operation: 'read';
      projectRoot: string;
    };

export type CompetitionBaselineRequest =
  | {
      action: 'baseline_run';
      operation: 'run';
      projectRoot: string;
      sealId: string;
      candidatePath: string;
      idempotencyKey: string;
    }
  | {
      action: 'baseline_run';
      operation: 'read';
      projectRoot: string;
      sealId: string;
      runId: string;
    }
  | {
      action: 'baseline_run';
      operation: 'confirm';
      projectRoot: string;
      sealId: string;
      runId: string;
      idempotencyKey: string;
    };

export type CompetitionWorkflowRequest =
  | CompetitionEnvironmentPreflightRequest
  | CompetitionBootstrapRequest
  | CompetitionTaskImportRequest
  | CompetitionEvaluatorAuditRequest
  | CompetitionLockRequest
  | CompetitionBaselineRequest;

type IdempotentResult = {
  replayed: boolean;
  command_receipt_hash: string;
};

type TaskImportResult = IdempotentResult & {
  action_version: 1;
  operation: 'import';
  created: boolean;
  seal_id: string;
  seal_hash: string;
  question_count: number;
  unknown_count: number;
  readiness_blocker_count: number;
  contract_ready: boolean;
  strategy_ready: boolean;
  readiness_blockers: string[];
  manifest_ref: string;
  official_submission_enabled: false;
};

type EnvironmentIssue = {
  code: string;
  subject: string;
  message: string;
};

type EnvironmentImport = {
  module: string;
  distribution: string | null;
  symbols: string[];
  installed_version: string | null;
  required: boolean;
  import_ok: boolean;
  error_type: string | null;
  error_message: string | null;
};

type EnvironmentCsvTable = {
  path: string;
  size_bytes: number;
  sha256: string;
  columns: string[];
  row_count: number;
  non_empty_counts: Record<string, number>;
};

type EnvironmentPreflightResult = {
  action_version: 1;
  operation: 'inspect';
  receipt_version: 1;
  preflight_id: string;
  status: 'ready' | 'blocked';
  spec_sha256: string;
  environment_hash: string;
  observed_at: string;
  python: {
    executable: string;
    implementation: string;
    version: string;
    command_prefix: [string];
  };
  imports: EnvironmentImport[];
  data: {
    root: string;
    file_count: number;
    total_bytes: number;
    extension_counts: Record<string, number>;
    extension_bytes: Record<string, number>;
    top_level_files: Array<{ path: string; size_bytes: number }>;
    csv_tables: EnvironmentCsvTable[];
    required_globs: Array<{
      pattern: string;
      minimum_count: number;
      required: boolean;
      matched_count: number;
      passed: boolean;
    }>;
  };
  blockers: EnvironmentIssue[];
  warnings: EnvironmentIssue[];
  receipt_hash: string;
  receipt_ref: string;
  replayed: boolean;
  official_submission_enabled: false;
};

type EvaluatorAuditResult = IdempotentResult & {
  action_version: 1;
  operation: 'audit';
  audit_id: string;
  status: 'passed' | 'failed';
  seal_id: string;
  seal_hash: string;
  receipt_hash: string;
  receipt_ref: string;
  question_count: number;
  test_count: number;
  failed_test_count: number;
  artifact_integrity_passed: boolean;
  network_isolation_enforced: boolean;
  official_submission_enabled: false;
};

type BaselinePrimaryMetric = {
  metric_id: string;
  value: number;
  direction: 'maximize' | 'minimize';
};

type BaselineResult = {
  action_version: 1;
  operation: 'run' | 'read' | 'confirm';
  run_id: string;
  status: 'passed' | 'failed';
  baseline_id: string;
  seal_id: string;
  seal_hash: string;
  evaluator_audit_id: string;
  packet_hash: string;
  result_ref: string;
  baseline_ref: string | null;
  failure_kind: string | null;
  metrics_summary: Record<string, number>;
  primary_metric: BaselinePrimaryMetric | null;
  confirmed: boolean;
  confirmation_hash: string | null;
  confirmation_ref: string | null;
  metric_contract_ref: string | null;
  confirmation_mode: 'manual_post_run' | 'competition_lock' | null;
  competition_lock_hash: string | null;
  competition_lock_status: 'armed' | 'baseline_running' | 'baseline_confirmed' | 'baseline_exhausted' | null;
  baseline_attempts_remaining: number | null;
  official_submission_enabled: false;
  replayed?: boolean;
  command_receipt_hash?: string;
};

type CompetitionLockResult = {
  action_version: 1;
  operation: 'arm' | 'read';
  status: 'armed';
  schema: 'deepscientist.ioai.competition-lock.v1';
  competition_id: string;
  system_id: string;
  authorization_prompt_sha256: string;
  baseline_policy: 'auto_confirm_first_passing.v1';
  baseline_attempt_limit: number;
  attempt_count: number;
  baseline_attempts_remaining: number;
  state_status: 'armed' | 'baseline_running' | 'baseline_confirmed' | 'baseline_exhausted';
  bound_seal_id: string | null;
  confirmed_run_id: string | null;
  lock_hash: string;
  lock_ref: string;
  state_ref: string;
  armed_at: string;
  authorization_timing: 'before_task_import';
  post_start_human_baseline_confirmation: 'forbidden';
  official_submission_enabled: false;
  replayed?: boolean;
  command_receipt_hash?: string;
};

const BOOTSTRAP_STEPS = ['environment_preflight', 'task_import', 'evaluator_audit', 'baseline_run'] as const;
type BootstrapStep = (typeof BOOTSTRAP_STEPS)[number];

type BootstrapRunResult = {
  action_version: 1;
  bootstrap_version: 1;
  operation: 'advance';
  status: 'ready' | 'blocked' | 'confirmation_required';
  attempted_steps: BootstrapStep[];
  completed_steps: BootstrapStep[];
  replayed_steps: BootstrapStep[];
  next_step:
    | 'environment_preflight'
    | 'task_import'
    | 'evaluator_audit'
    | 'baseline_run'
    | 'baseline_confirmation'
    | 'search';
  baseline_candidate_ref: string | null;
  environment_preflight: EnvironmentPreflightResult;
  task_import: TaskImportResult | null;
  evaluator_audit: EvaluatorAuditResult | null;
  baseline_run: BaselineResult | null;
  official_submission_enabled: false;
};

type CompetitionWorkflowPayload =
  | EnvironmentPreflightResult
  | BootstrapRunResult
  | TaskImportResult
  | EvaluatorAuditResult
  | CompetitionLockResult
  | BaselineResult;

type CompetitionWorkflowError = {
  code: string;
  message: string;
  retryable: boolean;
  engine_code?: string;
};

export type CompetitionWorkflowActionResult =
  | {
      schema: typeof COMPETITION_WORKFLOW_ACTION_SCHEMA;
      status: 'ready';
      action: CompetitionWorkflowRequest['action'];
      official_submission_enabled: false;
      result: CompetitionWorkflowPayload;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_WORKFLOW_ACTION_SCHEMA;
      status: 'unavailable';
      action: CompetitionWorkflowRequest['action'];
      official_submission_enabled: false;
      error: CompetitionWorkflowError;
      diagnostics?: { stderr: string };
    };

export type CompetitionWorkflowReaderOptions = CompetitionEngineRequestOptions & {
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestAction?: (
    launch: CompetitionEngineLaunch,
    action: CompetitionWorkflowRequest['action'],
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

export type CompetitionWorkflowToolResult = {
  content: [{ type: 'text'; text: string }];
  isError?: true;
};

class WorkflowActionValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'WorkflowActionValidationError';
  }
}

export async function readCompetitionWorkflowAction(
  request: CompetitionWorkflowRequest,
  options: CompetitionWorkflowReaderOptions = {}
): Promise<CompetitionWorkflowActionResult> {
  try {
    const params = requestParams(request);
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const requestAction = options.requestAction ?? defaultActionRequest;
    const response = await requestAction(launch, request.action, params, {
      timeoutMs: options.timeoutMs,
      signal: options.signal,
    });
    const result = parseWorkflowResult(response.result, request);
    return {
      schema: COMPETITION_WORKFLOW_ACTION_SCHEMA,
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

export function formatCompetitionWorkflowAction(
  result: CompetitionWorkflowActionResult
): CompetitionWorkflowToolResult {
  const formatted: CompetitionWorkflowToolResult = {
    content: [{ type: 'text', text: JSON.stringify(result, null, 2) }],
  };
  if (result.status === 'unavailable') formatted.isError = true;
  return formatted;
}

async function defaultActionRequest(
  launch: CompetitionEngineLaunch,
  action: CompetitionWorkflowRequest['action'],
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request(action, params, options);
}

function requestParams(request: CompetitionWorkflowRequest): Record<string, unknown> {
  const projectRoot = requiredInput(request.projectRoot, 'project_root');
  if (request.action === 'environment_preflight') {
    return {
      project_root: projectRoot,
      preflight_path: requiredInput(request.preflightPath, 'preflight_path'),
    };
  }
  if (request.action === 'bootstrap_run') {
    return {
      project_root: projectRoot,
      preflight_path: requiredInput(request.preflightPath, 'preflight_path'),
      bundle_path: requiredInput(request.bundlePath, 'bundle_path'),
      baseline_candidate_path: requiredInput(request.baselineCandidatePath, 'baseline_candidate_path'),
      idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
    };
  }
  if (request.action === 'task_import') {
    return {
      project_root: projectRoot,
      bundle_path: requiredInput(request.bundlePath, 'bundle_path'),
      idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
    };
  }
  if (request.action === 'competition_lock') {
    if (request.operation === 'read') {
      return { project_root: projectRoot, operation: 'read' };
    }
    return {
      project_root: projectRoot,
      operation: 'arm',
      competition_id: requiredInput(request.competitionId, 'competition_id'),
      system_id: requiredInput(request.systemId, 'system_id'),
      authorization_prompt_sha256: requiredInput(request.authorizationPromptSha256, 'authorization_prompt_sha256'),
      baseline_attempt_limit: requiredAttemptLimitInput(request.baselineAttemptLimit),
      idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
    };
  }
  const sealId = requiredInput(request.sealId, 'seal_id');
  if (request.action === 'evaluator_audit') {
    return {
      project_root: projectRoot,
      seal_id: sealId,
      idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
    };
  }
  if (request.operation === 'run') {
    return {
      project_root: projectRoot,
      operation: 'run',
      seal_id: sealId,
      candidate_path: requiredInput(request.candidatePath, 'candidate_path'),
      idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
    };
  }
  if (request.operation === 'read') {
    return {
      project_root: projectRoot,
      operation: 'read',
      seal_id: sealId,
      run_id: requiredInput(request.runId, 'run_id'),
    };
  }
  return {
    project_root: projectRoot,
    operation: 'confirm',
    seal_id: sealId,
    run_id: requiredInput(request.runId, 'run_id'),
    idempotency_key: requiredInput(request.idempotencyKey, 'idempotency_key'),
  };
}

function parseWorkflowResult(
  result: Record<string, unknown>,
  request: CompetitionWorkflowRequest
): CompetitionWorkflowPayload {
  if (result.action_version !== 1) invalid('action_version must be 1');
  if (result.official_submission_enabled !== false) {
    throw new WorkflowActionValidationError(
      'unsafe_official_submission_capability',
      'workflow action must keep official submission disabled'
    );
  }
  if (request.action === 'task_import') return parseTaskImport(result);
  if (request.action === 'environment_preflight') return parseEnvironmentPreflight(result);
  if (request.action === 'bootstrap_run') return parseBootstrapRun(result, request);
  if (request.action === 'competition_lock') return parseCompetitionLock(result, request);
  if (request.action === 'evaluator_audit') return parseEvaluatorAudit(result, request.sealId.trim());
  return parseBaseline(result, request);
}

function parseBootstrapRun(result: Record<string, unknown>, request: CompetitionBootstrapRequest): BootstrapRunResult {
  if (result.bootstrap_version !== 1) invalid('bootstrap_version must be 1');
  if (result.operation !== 'advance') invalid('bootstrap_run operation must be advance');
  const status = result.status;
  if (status !== 'ready' && status !== 'blocked' && status !== 'confirmation_required') {
    invalid('bootstrap_run status is invalid');
  }
  const attemptedSteps = bootstrapStepArray(result.attempted_steps, 'attempted_steps');
  const completedSteps = bootstrapStepArray(result.completed_steps, 'completed_steps');
  const replayedSteps = bootstrapStepArray(result.replayed_steps, 'replayed_steps');
  const preflightRaw = requiredRecord(result, 'environment_preflight');
  const preflight = parseEnvironmentPreflight(preflightRaw);
  const taskRaw = nullableRecord(result.task_import, 'task_import');
  const task = taskRaw ? parseTaskImport(taskRaw) : null;
  const auditRaw = nullableRecord(result.evaluator_audit, 'evaluator_audit');
  const audit = auditRaw
    ? parseEvaluatorAudit(auditRaw, task?.seal_id ?? identityMismatch('bootstrap audit is missing its task seal'))
    : null;
  const baselineRaw = nullableRecord(result.baseline_run, 'baseline_run');
  const baseline = baselineRaw
    ? parseBaseline(baselineRaw, {
        action: 'baseline_run',
        operation: 'run',
        projectRoot: request.projectRoot,
        sealId: task?.seal_id ?? identityMismatch('bootstrap baseline is missing its task seal'),
        candidatePath: request.baselineCandidatePath,
        idempotencyKey: request.idempotencyKey,
      })
    : null;
  if (baselineRaw && typeof baselineRaw.replayed !== 'boolean') {
    invalid('bootstrap baseline_run must include replay evidence');
  }

  const expectedAttempted: BootstrapStep[] = ['environment_preflight'];
  const expectedCompleted: BootstrapStep[] = [];
  let expectedStatus: BootstrapRunResult['status'] = 'blocked';
  let expectedNext: BootstrapRunResult['next_step'] = 'environment_preflight';
  if (preflight.status === 'ready') {
    expectedCompleted.push('environment_preflight');
    if (!task) invalid('ready preflight must advance bootstrap to task_import');
    expectedAttempted.push('task_import');
    expectedNext = 'task_import';
    if (task.contract_ready) {
      expectedCompleted.push('task_import');
      if (!audit) invalid('contract-ready task must advance bootstrap to evaluator_audit');
      expectedAttempted.push('evaluator_audit');
      expectedNext = 'evaluator_audit';
      if (audit.status === 'passed') {
        expectedCompleted.push('evaluator_audit');
        if (!baseline) invalid('passed audit must advance bootstrap to baseline_run');
        expectedAttempted.push('baseline_run');
        expectedNext = 'baseline_run';
        if (baseline.status === 'passed') {
          expectedCompleted.push('baseline_run');
          expectedStatus = baseline.confirmed ? 'ready' : 'confirmation_required';
          expectedNext = baseline.confirmed ? 'search' : 'baseline_confirmation';
        }
      }
    }
  }
  const expectedReplayed = expectedAttempted.filter((step) => {
    const payload = {
      environment_preflight: preflight,
      task_import: task,
      evaluator_audit: audit,
      baseline_run: baseline,
    }[step];
    return Boolean(payload?.replayed);
  });
  if (
    !sameStringArray(attemptedSteps, expectedAttempted) ||
    !sameStringArray(completedSteps, expectedCompleted) ||
    !sameStringArray(replayedSteps, expectedReplayed)
  ) {
    invalid('bootstrap step evidence is inconsistent');
  }
  if (status !== expectedStatus || result.next_step !== expectedNext) {
    invalid('bootstrap status and next_step are inconsistent');
  }
  const baselineCandidateRef = optionalRelativeRef(result.baseline_candidate_ref, 'baseline_candidate_ref');
  if (Boolean(baseline) !== Boolean(baselineCandidateRef)) {
    invalid('bootstrap baseline candidate evidence is inconsistent');
  }
  return {
    action_version: 1,
    bootstrap_version: 1,
    operation: 'advance',
    status,
    attempted_steps: attemptedSteps,
    completed_steps: completedSteps,
    replayed_steps: replayedSteps,
    next_step: expectedNext,
    baseline_candidate_ref: baselineCandidateRef,
    environment_preflight: preflight,
    task_import: task,
    evaluator_audit: audit,
    baseline_run: baseline,
    official_submission_enabled: false,
  };
}

function parseEnvironmentPreflight(result: Record<string, unknown>): EnvironmentPreflightResult {
  if (result.operation !== 'inspect') invalid('environment_preflight operation must be inspect');
  if (result.receipt_version !== 1) invalid('environment preflight receipt_version must be 1');
  const preflightId = requiredCanonicalId(result, 'preflight_id', /^ep-[0-9a-f]{12}$/u);
  const status = result.status;
  if (status !== 'ready' && status !== 'blocked') invalid('environment preflight status is invalid');
  const python = requiredRecord(result, 'python');
  const executable = requiredString(python, 'executable');
  if (!path.win32.isAbsolute(executable) && !path.posix.isAbsolute(executable)) {
    invalid('environment preflight Python executable must be absolute');
  }
  const commandPrefix = stringArray(python.command_prefix, 'python.command_prefix');
  if (commandPrefix.length !== 1 || commandPrefix[0] !== executable) {
    invalid('environment preflight Python command_prefix must contain only the executable');
  }
  const imports = recordArray(result.imports, 'imports').map(parseEnvironmentImport);
  const data = parseEnvironmentData(requiredRecord(result, 'data'));
  const blockers = recordArray(result.blockers, 'blockers').map((value) => parseEnvironmentIssue(value, 'blocker'));
  const warnings = recordArray(result.warnings, 'warnings').map((value) => parseEnvironmentIssue(value, 'warning'));
  if ((status === 'ready') !== (blockers.length === 0)) {
    invalid('environment preflight status and blockers are inconsistent');
  }
  for (const dependency of imports) {
    if (dependency.import_ok !== (dependency.error_type === null && dependency.error_message === null)) {
      invalid(`environment import evidence is inconsistent for ${dependency.module}`);
    }
    if (
      dependency.required &&
      !dependency.import_ok &&
      !blockers.some((blocker) => blocker.code === 'required_import_failed' && blocker.subject === dependency.module)
    ) {
      invalid(`failed required import lacks a blocker: ${dependency.module}`);
    }
  }
  return {
    action_version: 1,
    operation: 'inspect',
    receipt_version: 1,
    preflight_id: preflightId,
    status,
    spec_sha256: requiredHash(result, 'spec_sha256'),
    environment_hash: requiredHash(result, 'environment_hash'),
    observed_at: requiredString(result, 'observed_at'),
    python: {
      executable,
      implementation: requiredString(python, 'implementation'),
      version: requiredString(python, 'version'),
      command_prefix: [executable],
    },
    imports,
    data,
    blockers,
    warnings,
    receipt_hash: requiredHash(result, 'receipt_hash'),
    receipt_ref: requiredRelativeRef(result, 'receipt_ref'),
    replayed: requiredBoolean(result, 'replayed'),
    official_submission_enabled: false,
  };
}

function parseEnvironmentImport(value: Record<string, unknown>): EnvironmentImport {
  return {
    module: requiredString(value, 'module'),
    distribution: optionalString(value.distribution, 'distribution'),
    symbols: stringArray(value.symbols, 'symbols'),
    installed_version: optionalString(value.installed_version, 'installed_version'),
    required: requiredBoolean(value, 'required'),
    import_ok: requiredBoolean(value, 'import_ok'),
    error_type: optionalString(value.error_type, 'error_type'),
    error_message: optionalString(value.error_message, 'error_message'),
  };
}

function parseEnvironmentData(value: Record<string, unknown>): EnvironmentPreflightResult['data'] {
  const csvTables = recordArray(value.csv_tables, 'data.csv_tables').map((table) => {
    const columns = stringArray(table.columns, 'data.csv_tables.columns');
    const rowCount = requiredCount(table, 'row_count');
    const nonEmptyCounts = integerRecord(requiredRecord(table, 'non_empty_counts'), 'non_empty_counts');
    if (
      Object.keys(nonEmptyCounts).length !== columns.length ||
      columns.some((column) => !(column in nonEmptyCounts) || nonEmptyCounts[column] > rowCount)
    ) {
      invalid('environment CSV non-empty counts are inconsistent');
    }
    return {
      path: relativeRef(requiredString(table, 'path'), 'data.csv_tables.path'),
      size_bytes: requiredCount(table, 'size_bytes'),
      sha256: requiredHash(table, 'sha256'),
      columns,
      row_count: rowCount,
      non_empty_counts: nonEmptyCounts,
    };
  });
  const topLevelFiles = recordArray(value.top_level_files, 'data.top_level_files').map((item) => ({
    path: relativeRef(requiredString(item, 'path'), 'data.top_level_files.path'),
    size_bytes: requiredCount(item, 'size_bytes'),
  }));
  const requiredGlobs = recordArray(value.required_globs, 'data.required_globs').map((item) => {
    const minimumCount = requiredCount(item, 'minimum_count');
    const matchedCount = requiredCount(item, 'matched_count');
    const passed = requiredBoolean(item, 'passed');
    if (passed !== matchedCount >= minimumCount) invalid('environment glob result is inconsistent');
    return {
      pattern: requiredString(item, 'pattern'),
      minimum_count: minimumCount,
      required: requiredBoolean(item, 'required'),
      matched_count: matchedCount,
      passed,
    };
  });
  return {
    root: relativeRef(requiredString(value, 'root'), 'data.root'),
    file_count: requiredCount(value, 'file_count'),
    total_bytes: requiredCount(value, 'total_bytes'),
    extension_counts: integerRecord(requiredRecord(value, 'extension_counts'), 'extension_counts'),
    extension_bytes: integerRecord(requiredRecord(value, 'extension_bytes'), 'extension_bytes'),
    top_level_files: topLevelFiles,
    csv_tables: csvTables,
    required_globs: requiredGlobs,
  };
}

function parseEnvironmentIssue(value: Record<string, unknown>, _label: string): EnvironmentIssue {
  return {
    code: requiredString(value, 'code'),
    subject: requiredString(value, 'subject'),
    message: requiredString(value, 'message'),
  };
}

function parseCompetitionLock(result: Record<string, unknown>, request: CompetitionLockRequest): CompetitionLockResult {
  if (result.operation !== request.operation) identityMismatch('competition lock operation does not match the request');
  if (result.status !== 'armed') invalid('competition lock status must be armed');
  if (result.schema !== 'deepscientist.ioai.competition-lock.v1') invalid('competition lock schema is invalid');
  if (result.baseline_policy !== 'auto_confirm_first_passing.v1')
    invalid('competition lock baseline policy is invalid');
  const stateStatus = result.state_status;
  if (!['armed', 'baseline_running', 'baseline_confirmed', 'baseline_exhausted'].includes(String(stateStatus))) {
    invalid('competition lock state_status is invalid');
  }
  const attemptLimit = requiredPositiveCount(result, 'baseline_attempt_limit', 50);
  const attemptCount = requiredCount(result, 'attempt_count');
  const attemptsRemaining = requiredCount(result, 'baseline_attempts_remaining');
  if (attemptCount + attemptsRemaining !== attemptLimit) invalid('competition lock attempt counts are inconsistent');
  const idempotency = request.operation === 'arm' ? parseIdempotency(result) : {};
  return {
    action_version: 1,
    operation: request.operation,
    status: 'armed',
    schema: 'deepscientist.ioai.competition-lock.v1',
    competition_id: requiredString(result, 'competition_id'),
    system_id: requiredString(result, 'system_id'),
    authorization_prompt_sha256: requiredHash(result, 'authorization_prompt_sha256'),
    baseline_policy: 'auto_confirm_first_passing.v1',
    baseline_attempt_limit: attemptLimit,
    attempt_count: attemptCount,
    baseline_attempts_remaining: attemptsRemaining,
    state_status: stateStatus as CompetitionLockResult['state_status'],
    bound_seal_id: optionalCanonicalId(result.bound_seal_id, 'bound_seal_id', /^tc-[0-9a-f]{12}$/u),
    confirmed_run_id: optionalCanonicalId(result.confirmed_run_id, 'confirmed_run_id', /^br-[0-9a-f]{8}$/u),
    lock_hash: requiredHash(result, 'lock_hash'),
    lock_ref: requiredRelativeRef(result, 'lock_ref'),
    state_ref: requiredRelativeRef(result, 'state_ref'),
    armed_at: requiredString(result, 'armed_at'),
    authorization_timing: requiredLiteral(result, 'authorization_timing', 'before_task_import'),
    post_start_human_baseline_confirmation: requiredLiteral(
      result,
      'post_start_human_baseline_confirmation',
      'forbidden'
    ),
    official_submission_enabled: false,
    ...idempotency,
  };
}

function parseTaskImport(result: Record<string, unknown>): TaskImportResult {
  if (result.operation !== 'import') invalid('task_import operation must be import');
  return {
    action_version: 1,
    operation: 'import',
    created: requiredBoolean(result, 'created'),
    seal_id: requiredSealId(result, 'seal_id'),
    seal_hash: requiredHash(result, 'seal_hash'),
    question_count: requiredCount(result, 'question_count'),
    unknown_count: requiredCount(result, 'unknown_count'),
    readiness_blocker_count: requiredCount(result, 'readiness_blocker_count'),
    contract_ready: requiredBoolean(result, 'contract_ready'),
    strategy_ready: requiredBoolean(result, 'strategy_ready'),
    readiness_blockers: stringArray(result.readiness_blockers, 'readiness_blockers'),
    manifest_ref: requiredRelativeRef(result, 'manifest_ref'),
    official_submission_enabled: false,
    ...parseIdempotency(result),
  };
}

function parseEvaluatorAudit(result: Record<string, unknown>, expectedSealId: string): EvaluatorAuditResult {
  if (result.operation !== 'audit') invalid('evaluator_audit operation must be audit');
  const sealId = requiredSealId(result, 'seal_id');
  if (sealId !== expectedSealId) identityMismatch('evaluator audit seal_id does not match the request');
  const status = result.status;
  if (status !== 'passed' && status !== 'failed') invalid('audit status must be passed or failed');
  return {
    action_version: 1,
    operation: 'audit',
    audit_id: requiredAuditId(result, 'audit_id'),
    status,
    seal_id: sealId,
    seal_hash: requiredHash(result, 'seal_hash'),
    receipt_hash: requiredHash(result, 'receipt_hash'),
    receipt_ref: requiredRelativeRef(result, 'receipt_ref'),
    question_count: requiredCount(result, 'question_count'),
    test_count: requiredCount(result, 'test_count'),
    failed_test_count: requiredCount(result, 'failed_test_count'),
    artifact_integrity_passed: requiredBoolean(result, 'artifact_integrity_passed'),
    network_isolation_enforced: requiredBoolean(result, 'network_isolation_enforced'),
    official_submission_enabled: false,
    ...parseIdempotency(result),
  };
}

function parseBaseline(result: Record<string, unknown>, request: CompetitionBaselineRequest): BaselineResult {
  if (result.operation !== request.operation) identityMismatch('baseline operation does not match the request');
  const sealId = requiredSealId(result, 'seal_id');
  if (sealId !== request.sealId.trim()) identityMismatch('baseline seal_id does not match the request');
  const runId = requiredRunId(result, 'run_id');
  if (request.operation !== 'run' && runId !== request.runId.trim()) {
    identityMismatch('baseline run_id does not match the request');
  }
  const status = result.status;
  if (status !== 'passed' && status !== 'failed') invalid('baseline status must be passed or failed');
  const confirmed = requiredBoolean(result, 'confirmed');
  const confirmationHash = optionalHash(result.confirmation_hash, 'confirmation_hash');
  const confirmationRef = optionalRelativeRef(result.confirmation_ref, 'confirmation_ref');
  const metricContractRef = optionalRelativeRef(result.metric_contract_ref, 'metric_contract_ref');
  if (confirmed !== Boolean(confirmationHash && confirmationRef && metricContractRef)) {
    invalid('baseline confirmation fields are inconsistent');
  }
  if (request.operation === 'confirm' && !confirmed) invalid('confirmed baseline action must open the baseline gate');
  const confirmationMode = result.confirmation_mode;
  if (confirmationMode !== null && confirmationMode !== 'manual_post_run' && confirmationMode !== 'competition_lock') {
    invalid('baseline confirmation_mode is invalid');
  }
  const competitionLockHash = optionalHash(result.competition_lock_hash, 'competition_lock_hash');
  const competitionLockStatus = result.competition_lock_status;
  if (
    competitionLockStatus !== null &&
    !['armed', 'baseline_running', 'baseline_confirmed', 'baseline_exhausted'].includes(String(competitionLockStatus))
  ) {
    invalid('baseline competition_lock_status is invalid');
  }
  const attemptsRemaining = optionalCount(result.baseline_attempts_remaining, 'baseline_attempts_remaining');
  if (confirmed !== (confirmationMode !== null)) invalid('baseline confirmation mode is inconsistent');
  if (confirmationMode === 'competition_lock' && !competitionLockHash)
    invalid('locked confirmation requires lock hash');
  if (confirmationMode === 'manual_post_run' && competitionLockHash)
    invalid('manual confirmation cannot claim a lock hash');
  if (Boolean(competitionLockHash) !== Boolean(competitionLockStatus && attemptsRemaining !== null)) {
    invalid('baseline competition lock fields are inconsistent');
  }
  const idempotency = request.operation === 'read' ? {} : parseIdempotency(result);
  return {
    action_version: 1,
    operation: request.operation,
    run_id: runId,
    status,
    baseline_id: requiredString(result, 'baseline_id'),
    seal_id: sealId,
    seal_hash: requiredHash(result, 'seal_hash'),
    evaluator_audit_id: requiredAuditId(result, 'evaluator_audit_id'),
    packet_hash: requiredHash(result, 'packet_hash'),
    result_ref: requiredRelativeRef(result, 'result_ref'),
    baseline_ref: optionalRelativeRef(result.baseline_ref, 'baseline_ref'),
    failure_kind: optionalString(result.failure_kind, 'failure_kind'),
    metrics_summary: numericRecord(requiredRecord(result, 'metrics_summary'), 'metrics_summary'),
    primary_metric: parsePrimaryMetric(result.primary_metric),
    confirmed,
    confirmation_hash: confirmationHash,
    confirmation_ref: confirmationRef,
    metric_contract_ref: metricContractRef,
    confirmation_mode: confirmationMode as BaselineResult['confirmation_mode'],
    competition_lock_hash: competitionLockHash,
    competition_lock_status: competitionLockStatus as BaselineResult['competition_lock_status'],
    baseline_attempts_remaining: attemptsRemaining,
    official_submission_enabled: false,
    ...idempotency,
  };
}

function parseIdempotency(result: Record<string, unknown>): IdempotentResult {
  return {
    replayed: requiredBoolean(result, 'replayed'),
    command_receipt_hash: requiredHash(result, 'command_receipt_hash'),
  };
}

function parsePrimaryMetric(value: unknown): BaselinePrimaryMetric | null {
  if (value === null) return null;
  if (!isRecord(value)) invalid('primary_metric must be an object or null');
  const direction = value.direction;
  if (direction !== 'maximize' && direction !== 'minimize') {
    invalid('primary_metric.direction must be maximize or minimize');
  }
  return {
    metric_id: requiredString(value, 'metric_id'),
    value: requiredFiniteNumber(value, 'value'),
    direction,
  };
}

function requiredInput(value: unknown, field: string): string {
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new WorkflowActionValidationError('invalid_request', `${field} must be a non-empty string`);
  }
  return value.trim();
}

function requiredAttemptLimitInput(value: unknown): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1 || Number(value) > 50) {
    throw new WorkflowActionValidationError(
      'invalid_request',
      'baseline_attempt_limit must be an integer within [1, 50]'
    );
  }
  return Number(value);
}

function requiredRecord(source: Record<string, unknown>, key: string): Record<string, unknown> {
  const value = source[key];
  if (!isRecord(value)) invalid(`${key} must be an object`);
  return value;
}

function nullableRecord(value: unknown, field: string): Record<string, unknown> | null {
  if (value === null) return null;
  if (!isRecord(value)) invalid(`${field} must be an object or null`);
  return value;
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

function requiredCount(source: Record<string, unknown>, key: string): number {
  const value = source[key];
  if (!Number.isSafeInteger(value) || Number(value) < 0) invalid(`${key} must be a non-negative integer`);
  return Number(value);
}

function requiredPositiveCount(source: Record<string, unknown>, key: string, maximum: number): number {
  const value = requiredCount(source, key);
  if (value < 1 || value > maximum) invalid(`${key} must be within [1, ${maximum}]`);
  return value;
}

function optionalCount(value: unknown, field: string): number | null {
  if (value === null) return null;
  if (!Number.isSafeInteger(value) || Number(value) < 0) invalid(`${field} must be a non-negative integer or null`);
  return Number(value);
}

function requiredFiniteNumber(source: Record<string, unknown>, key: string): number {
  const value = source[key];
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${key} must be a finite number`);
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

function requiredSealId(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !/^tc-[0-9a-f]{12}$/u.test(value)) invalid(`${key} must be a canonical seal ID`);
  return value;
}

function requiredAuditId(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !/^ea-[0-9a-f]{8}$/u.test(value)) invalid(`${key} must be a canonical audit ID`);
  return value;
}

function requiredRunId(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !/^br-[0-9a-f]{8}$/u.test(value))
    invalid(`${key} must be a canonical baseline run ID`);
  return value;
}

function requiredCanonicalId(source: Record<string, unknown>, key: string, pattern: RegExp): string {
  const value = source[key];
  if (typeof value !== 'string' || !pattern.test(value)) invalid(`${key} is not a canonical ID`);
  return value;
}

function optionalCanonicalId(value: unknown, field: string, pattern: RegExp): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || !pattern.test(value)) invalid(`${field} is not a canonical ID or null`);
  return value;
}

function requiredLiteral<T extends string>(source: Record<string, unknown>, key: string, literal: T): T {
  if (source[key] !== literal) invalid(`${key} must be ${literal}`);
  return literal;
}

function requiredRelativeRef(source: Record<string, unknown>, key: string): string {
  return relativeRef(requiredString(source, key), key);
}

function optionalRelativeRef(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || value.length === 0) invalid(`${field} must be a relative path or null`);
  return relativeRef(value, field);
}

function relativeRef(value: string, field: string): string {
  const parts = value.split('/');
  if (value.startsWith('/') || value.includes('\\') || parts.includes('..') || parts.includes('.')) {
    invalid(`${field} must be a normalized relative path`);
  }
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
  return [...(value as string[])];
}

function bootstrapStepArray(value: unknown, field: string): BootstrapStep[] {
  const steps = stringArray(value, field);
  if (steps.some((step) => !BOOTSTRAP_STEPS.includes(step as BootstrapStep)) || new Set(steps).size !== steps.length) {
    invalid(`${field} must contain unique bootstrap steps`);
  }
  return steps as BootstrapStep[];
}

function sameStringArray(left: readonly string[], right: readonly string[]): boolean {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function recordArray(value: unknown, field: string): Record<string, unknown>[] {
  if (!Array.isArray(value) || value.some((item) => !isRecord(item))) {
    invalid(`${field} must be an object array`);
  }
  return value as Record<string, unknown>[];
}

function integerRecord(value: Record<string, unknown>, field: string): Record<string, number> {
  const result: Record<string, number> = {};
  for (const [key, count] of Object.entries(value)) {
    if (!key || !Number.isSafeInteger(count) || Number(count) < 0) {
      invalid(`${field} contains an invalid count`);
    }
    result[key] = Number(count);
  }
  return result;
}

function numericRecord(value: Record<string, unknown>, field: string): Record<string, number> {
  const result: Record<string, number> = {};
  for (const [key, number] of Object.entries(value)) {
    if (!key || typeof number !== 'number' || !Number.isFinite(number)) {
      invalid(`${field} contains an invalid number`);
    }
    result[key] = number;
  }
  return result;
}

function unavailableResult(
  action: CompetitionWorkflowRequest['action'],
  error: unknown
): CompetitionWorkflowActionResult {
  if (error instanceof CompetitionEngineDiscoveryError) return unavailable(action, error.code, error.message, false);
  if (error instanceof CompetitionEngineClientError) {
    return unavailable(action, error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof WorkflowActionValidationError) return unavailable(action, error.code, error.message, false);
  return unavailable(action, 'workflow_action_failed', 'IOAI competition workflow action failed', false);
}

function unavailable(
  action: CompetitionWorkflowRequest['action'],
  code: string,
  message: string,
  retryable: boolean,
  diagnostic = '',
  engineCode?: string
): CompetitionWorkflowActionResult {
  return {
    schema: COMPETITION_WORKFLOW_ACTION_SCHEMA,
    status: 'unavailable',
    action,
    official_submission_enabled: false,
    error: { code, message, retryable, ...(engineCode ? { engine_code: engineCode } : {}) },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}

function identityMismatch(message: string): never {
  throw new WorkflowActionValidationError('workflow_identity_mismatch', message);
}

function invalid(message: string): never {
  throw new WorkflowActionValidationError('invalid_workflow_result', message);
}
