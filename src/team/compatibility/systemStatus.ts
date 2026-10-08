/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { CompetitionEngineDiscoveryError, discoverCompetitionEngineLaunch } from "../competition-runtime/engineDiscovery";
import {
  IOAI_COMPETITION_EVALUATION_PROFILES,
  IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY,
  IOAI_COMPETITION_EVALUATION_CACHE,
  IOAI_COMPETITION_BUDGET_SEMANTICS,
  IOAI_COMPETITION_PARALLELISM_POLICY,
  IOAI_COMPETITION_RUNTIME_TOPOLOGY_SCHEMA,
  IOAI_COMPETITION_SYSTEM_STATUS_SCHEMA,
  IOAI_COMPETITION_WRITE_COORDINATION,
  isIoaiCompetitionEvaluationProfileContract,
  type IoaiCompetitionSystemStatus,
} from "../../common/chat/ioaiCompetition";
import {
  CompetitionEngineClientError,
  CompetitionEngineJsonlClient,
  type CompetitionEngineCommandResult,
  type CompetitionEngineLaunch,
  type CompetitionEngineRequestOptions,
} from "../competition-runtime/jsonlClient";
import { isRecord } from "../competition-runtime/protocol";

export const COMPETITION_SYSTEM_STATUS_SCHEMA = IOAI_COMPETITION_SYSTEM_STATUS_SCHEMA;
export type CompetitionSystemStatus = IoaiCompetitionSystemStatus;

export type CompetitionSystemStatusReaderOptions = CompetitionEngineRequestOptions & {
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestStatus?: (
    launch: CompetitionEngineLaunch,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

export type CompetitionStatusToolResult = {
  content: [{ type: 'text'; text: string }];
  isError?: true;
};

class CompetitionStatusValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'CompetitionStatusValidationError';
  }
}

export async function readCompetitionSystemStatus(
  options: CompetitionSystemStatusReaderOptions = {}
): Promise<CompetitionSystemStatus> {
  try {
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const requestStatus = options.requestStatus ?? defaultStatusRequest;
    const response = await requestStatus(launch, {
      timeoutMs: options.timeoutMs,
      signal: options.signal,
    });
    const validated = parseEngineSystemStatus(response.result);
    return {
      schema: COMPETITION_SYSTEM_STATUS_SCHEMA,
      status: 'ready',
      ...validated,
      official_submission_enabled: false,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailableStatus(error);
  }
}

export function formatCompetitionSystemStatus(status: CompetitionSystemStatus): CompetitionStatusToolResult {
  const result: CompetitionStatusToolResult = {
    content: [{ type: 'text', text: JSON.stringify(status, null, 2) }],
  };
  if (status.status === 'unavailable') result.isError = true;
  return result;
}

async function defaultStatusRequest(
  launch: CompetitionEngineLaunch,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request('system_status', {}, options);
}

function parseEngineSystemStatus(
  result: Record<string, unknown>
): Omit<
  Extract<CompetitionSystemStatus, { status: 'ready' }>,
  'schema' | 'status' | 'official_submission_enabled' | 'diagnostics'
> {
  const engine = requiredRecord(result, 'engine');
  const python = requiredRecord(result, 'python');
  const platform = requiredRecord(result, 'platform');
  const capabilities = requiredRecord(result, 'capabilities');
  const networkIsolation = requiredRecord(capabilities, 'network_isolation');
  const candidateNetworkIsolation = requiredRecord(networkIsolation, 'candidate_execution');
  const runtimeTopology = requiredRecord(capabilities, 'runtime_topology');
  const parallelismPolicy = requiredRecord(capabilities, 'parallelism_policy');
  const budgetSemantics = requiredRecord(capabilities, 'budget_semantics');
  const evaluationProfiles = requiredRecord(capabilities, 'evaluation_profiles');
  const evaluationCache = requiredRecord(capabilities, 'evaluation_cache');
  if (capabilities.official_submission_enabled !== false) {
    throw new CompetitionStatusValidationError(
      'unsafe_official_submission_capability',
      'engine must keep official submission disabled'
    );
  }
  const actions = requiredStringArray(capabilities, 'actions');
  if (
    !actions.includes('system_status') ||
    !actions.includes('environment_preflight') ||
    !actions.includes('bootstrap_run')
  ) {
    throw new CompetitionStatusValidationError(
      'invalid_engine_status',
      'engine status does not advertise required bootstrap actions'
    );
  }
  const networkIsolationAppliesTo = requiredStringArray(candidateNetworkIsolation, 'applies_to');
  if (
    candidateNetworkIsolation.status !== 'enforced_per_run' ||
    candidateNetworkIsolation.backend !== 'python-sitecustomize.v1' ||
    candidateNetworkIsolation.self_check_required !== true ||
    candidateNetworkIsolation.security_boundary !== 'python_process_guard_not_os_namespace' ||
    !sameStringArray(networkIsolationAppliesTo, ['candidate_attempt', 'sealed_evaluator'])
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_network_isolation',
      'engine status does not require the verified Python execution network guard'
    );
  }
  const writeCoordination = requiredStringArray(runtimeTopology, 'write_coordination');
  if (
    runtimeTopology.schema !== IOAI_COMPETITION_RUNTIME_TOPOLOGY_SCHEMA ||
    runtimeTopology.mcp_gateway_owner !== 'core' ||
    runtimeTopology.adapter_process_model !== 'stateless_one_or_more' ||
    runtimeTopology.coordinator_scope !== 'project_root' ||
    runtimeTopology.canonical_state_owner !== 'python_coordinator' ||
    runtimeTopology.workspace_supervisor_required !== false ||
    !sameStringArray(writeCoordination, IOAI_COMPETITION_WRITE_COORDINATION) ||
    (runtimeTopology.write_coordination as unknown[]).length !== IOAI_COMPETITION_WRITE_COORDINATION.length
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_runtime_topology',
      'engine status does not preserve the stateless single-writer runtime topology'
    );
  }
  if (
    evaluationCache.schema !== IOAI_COMPETITION_EVALUATION_CACHE.schema ||
    evaluationCache.identity !== IOAI_COMPETITION_EVALUATION_CACHE.identity ||
    evaluationCache.profile_isolation !== true ||
    evaluationCache.hit_behavior !== IOAI_COMPETITION_EVALUATION_CACHE.hit_behavior ||
    evaluationCache.charges_current_token_usage !== true ||
    evaluationCache.evaluator_invocation_on_hit !== false
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_evaluation_cache',
      'engine status does not preserve profile-scoped attributable evaluation reuse'
    );
  }
  if (
    evaluationProfiles.schema !== IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY.schema ||
    evaluationProfiles.default !== IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY.default ||
    evaluationProfiles.frontier_isolation !== IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY.frontier_isolation ||
    evaluationProfiles.cross_profile_comparison !==
      IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY.cross_profile_comparison ||
    !hasExactEvaluationProfileContracts(evaluationProfiles.profiles)
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_evaluation_profiles',
      'engine status does not preserve isolated evaluation profile contracts'
    );
  }
  if (
    budgetSemantics.schema !== IOAI_COMPETITION_BUDGET_SEMANTICS.schema ||
    budgetSemantics.agent_reasoning_budget_owner !== IOAI_COMPETITION_BUDGET_SEMANTICS.agent_reasoning_budget_owner ||
    budgetSemantics.candidate_model_token_budget_owner !==
      IOAI_COMPETITION_BUDGET_SEMANTICS.candidate_model_token_budget_owner ||
    budgetSemantics.zero_candidate_token_limit_stops_agent_search !== false ||
    !sameStringArray(
      requiredStringArray(budgetSemantics, 'search_stop_sources'),
      IOAI_COMPETITION_BUDGET_SEMANTICS.search_stop_sources
    )
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_budget_semantics',
      'engine status does not separate Agent reasoning from candidate model token budgets'
    );
  }
  if (
    parallelismPolicy.schema !== IOAI_COMPETITION_PARALLELISM_POLICY.schema ||
    parallelismPolicy.reasoning_concurrency_owner !== IOAI_COMPETITION_PARALLELISM_POLICY.reasoning_concurrency_owner ||
    parallelismPolicy.experiment_concurrency_owner !==
      IOAI_COMPETITION_PARALLELISM_POLICY.experiment_concurrency_owner ||
    parallelismPolicy.task_acquisition_concurrency !==
      IOAI_COMPETITION_PARALLELISM_POLICY.task_acquisition_concurrency ||
    parallelismPolicy.sota_search_concurrency !== IOAI_COMPETITION_PARALLELISM_POLICY.sota_search_concurrency ||
    parallelismPolicy.agent_count_multiplier !== IOAI_COMPETITION_PARALLELISM_POLICY.agent_count_multiplier ||
    parallelismPolicy.cross_adapter_serialization !== IOAI_COMPETITION_PARALLELISM_POLICY.cross_adapter_serialization ||
    parallelismPolicy.process_limit_source !== IOAI_COMPETITION_PARALLELISM_POLICY.process_limit_source ||
    parallelismPolicy.cpu_limit_source !== IOAI_COMPETITION_PARALLELISM_POLICY.cpu_limit_source ||
    parallelismPolicy.gpu_limit_source !== IOAI_COMPETITION_PARALLELISM_POLICY.gpu_limit_source ||
    parallelismPolicy.gpu_assignment_owner !== IOAI_COMPETITION_PARALLELISM_POLICY.gpu_assignment_owner ||
    parallelismPolicy.token_limit_source !== IOAI_COMPETITION_PARALLELISM_POLICY.token_limit_source
  ) {
    throw new CompetitionStatusValidationError(
      'unsafe_parallelism_policy',
      'engine status does not preserve bounded two-layer competition parallelism'
    );
  }
  const engineName = requiredString(engine, 'name');
  if (engineName !== 'deepscientist-ioai-engine') {
    throw new CompetitionStatusValidationError('invalid_engine_status', 'unexpected competition engine identity');
  }
  return {
    engine: {
      name: engineName,
      version: requiredString(engine, 'version'),
    },
    python: {
      executable: requiredString(python, 'executable'),
      implementation: requiredString(python, 'implementation'),
      version: requiredString(python, 'version'),
    },
    platform: {
      os_name: requiredString(platform, 'os_name'),
      system: requiredString(platform, 'system'),
      machine: requiredString(platform, 'machine'),
    },
    capabilities: {
      actions,
      runtime_topology: {
        schema: IOAI_COMPETITION_RUNTIME_TOPOLOGY_SCHEMA,
        mcp_gateway_owner: 'core',
        adapter_process_model: 'stateless_one_or_more',
        coordinator_scope: 'project_root',
        canonical_state_owner: 'python_coordinator',
        write_coordination: [...IOAI_COMPETITION_WRITE_COORDINATION],
        workspace_supervisor_required: false,
      },
      parallelism_policy: { ...IOAI_COMPETITION_PARALLELISM_POLICY },
      budget_semantics: IOAI_COMPETITION_BUDGET_SEMANTICS,
      evaluation_profiles: IOAI_COMPETITION_EVALUATION_PROFILES_CAPABILITY,
      evaluation_cache: IOAI_COMPETITION_EVALUATION_CACHE,
    },
    network_isolation: {
      status: requiredString(networkIsolation, 'status'),
      reason: requiredString(networkIsolation, 'reason'),
      candidate_execution: {
        status: 'enforced_per_run',
        backend: 'python-sitecustomize.v1',
        self_check_required: true,
        applies_to: ['candidate_attempt', 'sealed_evaluator'],
        security_boundary: 'python_process_guard_not_os_namespace',
      },
    },
  };
}

function hasExactEvaluationProfileContracts(value: unknown): boolean {
  if (!isRecord(value) || Object.keys(value).length !== IOAI_COMPETITION_EVALUATION_PROFILES.length) return false;
  return IOAI_COMPETITION_EVALUATION_PROFILES.every((profile) =>
    isIoaiCompetitionEvaluationProfileContract(value[profile], profile)
  );
}

function requiredRecord(source: Record<string, unknown>, key: string): Record<string, unknown> {
  const value = source[key];
  if (!isRecord(value)) {
    throw new CompetitionStatusValidationError('invalid_engine_status', `engine status ${key} must be an object`);
  }
  return value;
}

function requiredString(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || value.trim().length === 0) {
    throw new CompetitionStatusValidationError(
      'invalid_engine_status',
      `engine status ${key} must be a non-empty string`
    );
  }
  return value;
}

function requiredStringArray(source: Record<string, unknown>, key: string): string[] {
  const value = source[key];
  if (!Array.isArray(value) || value.length === 0 || value.some((item) => typeof item !== 'string' || !item)) {
    throw new CompetitionStatusValidationError(
      'invalid_engine_status',
      `engine status ${key} must be a non-empty string array`
    );
  }
  return [...new Set(value)];
}

function sameStringArray(actual: readonly string[], expected: readonly string[]): boolean {
  return actual.length === expected.length && actual.every((value, index) => value === expected[index]);
}

function unavailableStatus(error: unknown): CompetitionSystemStatus {
  if (error instanceof CompetitionEngineDiscoveryError) {
    return buildUnavailable(error.code, error.message, false);
  }
  if (error instanceof CompetitionEngineClientError) {
    return buildUnavailable(error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof CompetitionStatusValidationError) {
    return buildUnavailable(error.code, error.message, false);
  }
  return buildUnavailable('preflight_failed', 'IOAI competition engine preflight failed', false);
}

function buildUnavailable(
  code: string,
  message: string,
  retryable: boolean,
  diagnostic = '',
  engineCode?: string
): CompetitionSystemStatus {
  return {
    schema: COMPETITION_SYSTEM_STATUS_SCHEMA,
    status: 'unavailable',
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
