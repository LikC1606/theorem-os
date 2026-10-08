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

export const COMPETITION_BENCHMARK_ACTION_SCHEMA = 'deepscientist.ioai.competition.benchmark-action.v1';

export type CompetitionBenchmarkRequest =
  | { action: 'benchmark_run'; projectRoot: string; sealId: string; taskId: string; runId: string }
  | { action: 'benchmark_read'; projectRoot: string; runId: string };

export type CompetitionBenchmarkObservation = {
  trial_id: string;
  cache_hit: boolean;
  scheduling_overhead_seconds: number;
  evaluator_wall_seconds: number;
  end_to_end_seconds: number;
  cpu_slots: number;
  gpu_slots: number;
  claimed_epoch: number;
  finished_epoch: number;
};

export type CompetitionBenchmarkProfile = {
  profile: 'sprint' | 'contest';
  case_count: number;
  frontier_revision: number;
  incumbent_id: string | null;
  trial_count: number;
  cache_hits: number;
  cache_misses: number;
  mean_scheduling_overhead_seconds: number;
  mean_evaluator_wall_seconds: number;
  mean_end_to_end_seconds: number;
  median_end_to_end_seconds: number;
  declared_peak_processes: number;
  declared_peak_cpu_slots: number;
  declared_peak_gpu_slots: number;
  utilization_basis: 'verified_packet_intervals_and_declared_slots';
  observations: CompetitionBenchmarkObservation[];
};

export type CompetitionBenchmarkPayload = {
  action_version: 1;
  operation: 'run' | 'read';
  run_id: string;
  identity: { seal_id: string; task_id: string };
  engine_startup: {
    wall_seconds: number;
    python_executable: string;
    method: 'fresh_python_import';
    sample_count: 1;
  };
  profiles: { sprint: CompetitionBenchmarkProfile; contest: CompetitionBenchmarkProfile };
  comparison: {
    sprint_case_count: number;
    contest_case_count: number;
    sprint_uses_fewer_cases: boolean;
    sprint_mean_turnaround_seconds: number;
    contest_mean_turnaround_seconds: number;
    observed_turnaround_ratio: number | null;
    sprint_observed_faster: boolean;
    final_promotion_profiles: ['contest', 'audit'];
    quick_profiles_final_promotion_forbidden: true;
  };
  source_packet_count: number;
  benchmark_hash: string;
  benchmark_ref: string;
  created: boolean;
  official_submission_enabled: false;
};

type BenchmarkError = { code: string; message: string; retryable: boolean; engine_code?: string };

export type CompetitionBenchmarkActionResult =
  | {
      schema: typeof COMPETITION_BENCHMARK_ACTION_SCHEMA;
      status: 'ready';
      action: CompetitionBenchmarkRequest['action'];
      official_submission_enabled: false;
      result: CompetitionBenchmarkPayload;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_BENCHMARK_ACTION_SCHEMA;
      status: 'unavailable';
      action: CompetitionBenchmarkRequest['action'];
      official_submission_enabled: false;
      error: BenchmarkError;
      diagnostics?: { stderr: string };
    };

export type CompetitionBenchmarkReaderOptions = CompetitionEngineRequestOptions & {
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestAction?: (
    launch: CompetitionEngineLaunch,
    action: CompetitionBenchmarkRequest['action'],
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

class BenchmarkValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'BenchmarkValidationError';
  }
}

export async function readCompetitionBenchmarkAction(
  request: CompetitionBenchmarkRequest,
  options: CompetitionBenchmarkReaderOptions = {}
): Promise<CompetitionBenchmarkActionResult> {
  try {
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const response = await (options.requestAction ?? defaultRequest)(
      launch,
      request.action,
      request.action === 'benchmark_run'
        ? {
            project_root: requiredInput(request.projectRoot, 'project_root'),
            seal_id: requiredSeal(request.sealId),
            task_id: requiredInput(request.taskId, 'task_id'),
            run_id: requiredRunId(request.runId),
          }
        : {
            project_root: requiredInput(request.projectRoot, 'project_root'),
            run_id: requiredRunId(request.runId),
          },
      { timeoutMs: options.timeoutMs, signal: options.signal }
    );
    const result = parseBenchmark(response.result, request);
    return {
      schema: COMPETITION_BENCHMARK_ACTION_SCHEMA,
      status: 'ready',
      action: request.action,
      official_submission_enabled: false,
      result,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailable(request.action, error);
  }
}

export function formatCompetitionBenchmarkAction(result: CompetitionBenchmarkActionResult) {
  return {
    content: [{ type: 'text' as const, text: JSON.stringify(result, null, 2) }],
    ...(result.status === 'unavailable' ? { isError: true as const } : {}),
  };
}

async function defaultRequest(
  launch: CompetitionEngineLaunch,
  action: CompetitionBenchmarkRequest['action'],
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request(action, params, options);
}

function parseBenchmark(
  result: Record<string, unknown>,
  request: CompetitionBenchmarkRequest
): CompetitionBenchmarkPayload {
  if (result.action_version !== 1 || result.official_submission_enabled !== false)
    invalid('benchmark envelope is unsafe');
  const operation = result.operation;
  const created = requiredBoolean(result, 'created');
  if (
    (request.action === 'benchmark_read' && (operation !== 'read' || created)) ||
    (request.action === 'benchmark_run' && !((operation === 'run' && created) || (operation === 'read' && !created)))
  ) {
    mismatch('benchmark operation does not match the request');
  }
  const runId = requiredRunId(result.run_id);
  if (runId !== request.runId.trim()) mismatch('benchmark run_id does not match the request');
  const identity = record(result.identity, 'identity');
  const sealId = requiredSeal(identity.seal_id);
  const taskId = requiredString(identity, 'task_id');
  if (request.action === 'benchmark_run' && (sealId !== request.sealId.trim() || taskId !== request.taskId.trim())) {
    mismatch('benchmark identity does not match the request');
  }
  const startup = record(result.engine_startup, 'engine_startup');
  if (startup.method !== 'fresh_python_import' || startup.sample_count !== 1)
    invalid('engine startup contract is invalid');
  const profiles = record(result.profiles, 'profiles');
  const sprint = parseProfile(profiles.sprint, 'sprint');
  const contest = parseProfile(profiles.contest, 'contest');
  const comparison = record(result.comparison, 'comparison');
  const ratio = optionalNonNegative(comparison.observed_turnaround_ratio, 'observed_turnaround_ratio');
  if (
    comparison.sprint_case_count !== sprint.case_count ||
    comparison.contest_case_count !== contest.case_count ||
    comparison.sprint_uses_fewer_cases !== sprint.case_count < contest.case_count ||
    comparison.sprint_mean_turnaround_seconds !== sprint.mean_end_to_end_seconds ||
    comparison.contest_mean_turnaround_seconds !== contest.mean_end_to_end_seconds ||
    comparison.sprint_observed_faster !== sprint.mean_end_to_end_seconds < contest.mean_end_to_end_seconds ||
    comparison.quick_profiles_final_promotion_forbidden !== true ||
    !Array.isArray(comparison.final_promotion_profiles) ||
    comparison.final_promotion_profiles.length !== 2 ||
    comparison.final_promotion_profiles[0] !== 'contest' ||
    comparison.final_promotion_profiles[1] !== 'audit'
  ) {
    invalid('benchmark comparison is inconsistent');
  }
  return {
    action_version: 1,
    operation: operation as 'run' | 'read',
    run_id: runId,
    identity: { seal_id: sealId, task_id: taskId },
    engine_startup: {
      wall_seconds: nonNegative(startup.wall_seconds, 'engine_startup.wall_seconds'),
      python_executable: requiredString(startup, 'python_executable'),
      method: 'fresh_python_import',
      sample_count: 1,
    },
    profiles: { sprint, contest },
    comparison: {
      sprint_case_count: sprint.case_count,
      contest_case_count: contest.case_count,
      sprint_uses_fewer_cases: sprint.case_count < contest.case_count,
      sprint_mean_turnaround_seconds: sprint.mean_end_to_end_seconds,
      contest_mean_turnaround_seconds: contest.mean_end_to_end_seconds,
      observed_turnaround_ratio: ratio,
      sprint_observed_faster: sprint.mean_end_to_end_seconds < contest.mean_end_to_end_seconds,
      final_promotion_profiles: ['contest', 'audit'],
      quick_profiles_final_promotion_forbidden: true,
    },
    source_packet_count: count(result.source_packet_count, 'source_packet_count', 1),
    benchmark_hash: hash(result.benchmark_hash, 'benchmark_hash'),
    benchmark_ref: relativeRef(result.benchmark_ref, 'benchmark_ref'),
    created,
    official_submission_enabled: false,
  };
}

function parseProfile(value: unknown, expected: 'sprint' | 'contest'): CompetitionBenchmarkProfile {
  const profile = record(value, `profiles.${expected}`);
  if (profile.profile !== expected || profile.utilization_basis !== 'verified_packet_intervals_and_declared_slots') {
    invalid(`profiles.${expected} identity is invalid`);
  }
  if (!Array.isArray(profile.observations) || profile.observations.length === 0)
    invalid(`${expected} observations missing`);
  const observations = profile.observations.map((value, index) => {
    const item = record(value, `${expected}.observations[${index}]`);
    const claimed = nonNegative(item.claimed_epoch, 'claimed_epoch');
    const finished = nonNegative(item.finished_epoch, 'finished_epoch');
    if (finished < claimed) invalid('benchmark observation timing is invalid');
    return {
      trial_id: requiredString(item, 'trial_id'),
      cache_hit: requiredBoolean(item, 'cache_hit'),
      scheduling_overhead_seconds: nonNegative(item.scheduling_overhead_seconds, 'scheduling_overhead_seconds'),
      evaluator_wall_seconds: nonNegative(item.evaluator_wall_seconds, 'evaluator_wall_seconds'),
      end_to_end_seconds: nonNegative(item.end_to_end_seconds, 'end_to_end_seconds'),
      cpu_slots: count(item.cpu_slots, 'cpu_slots'),
      gpu_slots: count(item.gpu_slots, 'gpu_slots'),
      claimed_epoch: claimed,
      finished_epoch: finished,
    };
  });
  const trialCount = count(profile.trial_count, 'trial_count', 1);
  const cacheHits = count(profile.cache_hits, 'cache_hits');
  const cacheMisses = count(profile.cache_misses, 'cache_misses');
  if (
    trialCount !== observations.length ||
    cacheHits + cacheMisses !== trialCount ||
    observations.filter((item) => item.cache_hit).length !== cacheHits
  ) {
    invalid(`${expected} benchmark counts are inconsistent`);
  }
  return {
    profile: expected,
    case_count: count(profile.case_count, 'case_count', 1),
    frontier_revision: count(profile.frontier_revision, 'frontier_revision'),
    incumbent_id: optionalString(profile.incumbent_id, 'incumbent_id'),
    trial_count: trialCount,
    cache_hits: cacheHits,
    cache_misses: cacheMisses,
    mean_scheduling_overhead_seconds: nonNegative(profile.mean_scheduling_overhead_seconds, 'mean scheduling'),
    mean_evaluator_wall_seconds: nonNegative(profile.mean_evaluator_wall_seconds, 'mean evaluator wall'),
    mean_end_to_end_seconds: nonNegative(profile.mean_end_to_end_seconds, 'mean end-to-end'),
    median_end_to_end_seconds: nonNegative(profile.median_end_to_end_seconds, 'median end-to-end'),
    declared_peak_processes: count(profile.declared_peak_processes, 'declared_peak_processes'),
    declared_peak_cpu_slots: count(profile.declared_peak_cpu_slots, 'declared_peak_cpu_slots'),
    declared_peak_gpu_slots: count(profile.declared_peak_gpu_slots, 'declared_peak_gpu_slots'),
    utilization_basis: 'verified_packet_intervals_and_declared_slots',
    observations,
  };
}

function record(value: unknown, field: string): Record<string, unknown> {
  if (!isRecord(value)) invalid(`${field} must be an object`);
  return value;
}

function requiredString(source: Record<string, unknown>, key: string): string {
  const value = source[key];
  if (typeof value !== 'string' || !value) invalid(`${key} must be a non-empty string`);
  return value;
}

function requiredInput(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim())
    throw new BenchmarkValidationError('invalid_request', `${field} is required`);
  return value.trim();
}

function requiredSeal(value: unknown): string {
  if (typeof value !== 'string' || !/^tc-[0-9a-f]{12}$/u.test(value.trim())) {
    throw new BenchmarkValidationError('invalid_request', 'seal_id must be canonical');
  }
  return value.trim();
}

function requiredRunId(value: unknown): string {
  if (typeof value !== 'string' || !/^benchmark-[A-Za-z0-9][A-Za-z0-9._-]{0,95}$/u.test(value.trim())) {
    throw new BenchmarkValidationError('invalid_request', 'run_id must be a canonical benchmark ID');
  }
  return value.trim();
}

function requiredBoolean(source: Record<string, unknown>, key: string): boolean {
  if (typeof source[key] !== 'boolean') invalid(`${key} must be boolean`);
  return source[key];
}

function nonNegative(value: unknown, field: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value) || value < 0) invalid(`${field} must be non-negative`);
  return value;
}

function optionalNonNegative(value: unknown, field: string): number | null {
  return value === null ? null : nonNegative(value, field);
}

function count(value: unknown, field: string, minimum = 0): number {
  if (!Number.isSafeInteger(value) || Number(value) < minimum) invalid(`${field} must be an integer >= ${minimum}`);
  return Number(value);
}

function optionalString(value: unknown, field: string): string | null {
  if (value === null) return null;
  if (typeof value !== 'string' || !value) invalid(`${field} must be a string or null`);
  return value;
}

function hash(value: unknown, field: string): string {
  if (typeof value !== 'string' || !/^[0-9a-f]{64}$/u.test(value)) invalid(`${field} must be a SHA-256 hash`);
  return value;
}

function relativeRef(value: unknown, field: string): string {
  if (
    typeof value !== 'string' ||
    !value ||
    value.startsWith('/') ||
    value.includes('\\') ||
    value.split('/').some((part) => !part || part === '.' || part === '..')
  ) {
    invalid(`${field} must be a normalized relative path`);
  }
  return value;
}

function mismatch(message: string): never {
  throw new BenchmarkValidationError('benchmark_identity_mismatch', message);
}

function invalid(message: string): never {
  throw new BenchmarkValidationError('invalid_benchmark_result', message);
}

function unavailable(action: CompetitionBenchmarkRequest['action'], error: unknown): CompetitionBenchmarkActionResult {
  if (error instanceof CompetitionEngineDiscoveryError)
    return buildUnavailable(action, error.code, error.message, false);
  if (error instanceof CompetitionEngineClientError) {
    return buildUnavailable(action, error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof BenchmarkValidationError) return buildUnavailable(action, error.code, error.message, false);
  return buildUnavailable(action, 'benchmark_action_failed', 'IOAI competition benchmark action failed', false);
}

function buildUnavailable(
  action: CompetitionBenchmarkRequest['action'],
  code: string,
  message: string,
  retryable: boolean,
  diagnostic = '',
  engineCode?: string
): CompetitionBenchmarkActionResult {
  return {
    schema: COMPETITION_BENCHMARK_ACTION_SCHEMA,
    status: 'unavailable',
    action,
    official_submission_enabled: false,
    error: { code, message, retryable, ...(engineCode ? { engine_code: engineCode } : {}) },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}
