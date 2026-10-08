/**
 * @license
 * Copyright 2026 DeepScientist contributors
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
  isIoaiCompetitionEvaluationProfile,
  type IoaiCompetitionEvaluationProfile,
} from "../../common/chat/ioaiCompetition";
import { parseCompetitionTaskFingerprint, type CompetitionTaskFingerprint } from "./frontierSnapshot";

export const COMPETITION_CONTEST_SNAPSHOT_SCHEMA = 'deepscientist.ioai.competition.contest-snapshot.v1' as const;

export type CompetitionContestTaskSnapshot = {
  task_order: number;
  seal_id: string;
  task_id: string;
  question: string;
  task_fingerprint: CompetitionTaskFingerprint;
  state: 'not_started' | 'ready' | 'active';
  frontier_revision: number | null;
  incumbent: Record<string, unknown> | null;
  candidate_queue: string[];
  active_trial: { trial_id: string; candidate_id: string; status: 'claimed' | 'running' } | null;
  recent_improvement: {
    previous_trial_id: string;
    current_trial_id: string;
    oriented_delta: number;
    improved: boolean;
  } | null;
  remaining_budget: {
    submissions: number;
    compute_seconds_spent: number;
    wall_time_seconds: number;
    tokens: number;
  } | null;
  blocker: string | null;
  next_action: string;
  control: {
    control_version: 1;
    route: 'bootstrap' | 'first_score' | 'recovery' | 'search';
    phase: 'preparation' | 'search';
    watchdog_active: boolean;
    recovery_key: string | null;
    first_score: {
      status: 'pending' | 'breached' | 'recorded';
      started_at_epoch: number;
      guard_seconds: number;
      elapsed_seconds: number;
      elapsed_to_score_seconds: number | null;
      fallback_required: boolean;
      source: 'baseline' | 'trial' | null;
      score: number | null;
    };
  };
};

export type CompetitionContestSnapshot =
  | {
      schema: typeof COMPETITION_CONTEST_SNAPSHOT_SCHEMA;
      status: 'ready';
      seal_id: string;
      seal_hash: string;
      profile: IoaiCompetitionEvaluationProfile;
      score_comparison_across_tasks: 'forbidden';
      scheduling_owner: 'python_coordinator';
      tasks: CompetitionContestTaskSnapshot[];
      scheduling: { next_task_id: string | null; next_action: string; reason: string };
      contest_snapshot_hash: string;
      official_submission_enabled: false;
      diagnostics?: { stderr: string };
    }
  | {
      schema: typeof COMPETITION_CONTEST_SNAPSHOT_SCHEMA;
      status: 'unavailable';
      official_submission_enabled: false;
      error: { code: string; message: string; retryable: boolean; engine_code?: string };
      diagnostics?: { stderr: string };
    };

export type CompetitionContestSnapshotOptions = CompetitionEngineRequestOptions & {
  projectRoot: string;
  sealId?: string;
  profile?: IoaiCompetitionEvaluationProfile;
  discoverLaunch?: () => Promise<CompetitionEngineLaunch>;
  requestSnapshot?: (
    launch: CompetitionEngineLaunch,
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions
  ) => Promise<CompetitionEngineCommandResult<Record<string, unknown>>>;
};

class ContestSnapshotValidationError extends Error {
  constructor(
    readonly code: string,
    message: string
  ) {
    super(message);
    this.name = 'ContestSnapshotValidationError';
  }
}

export async function readCompetitionContestSnapshot(
  options: CompetitionContestSnapshotOptions
): Promise<CompetitionContestSnapshot> {
  try {
    const projectRoot = requiredText(options.projectRoot, 'project_root');
    const profile = options.profile ?? DEFAULT_IOAI_COMPETITION_EVALUATION_PROFILE;
    if (!isIoaiCompetitionEvaluationProfile(profile)) invalid('profile is invalid');
    const sealId = options.sealId === undefined ? undefined : requiredText(options.sealId, 'seal_id');
    const launch = await (options.discoverLaunch ?? discoverCompetitionEngineLaunch)();
    const response = await (options.requestSnapshot ?? defaultRequest)(
      launch,
      { project_root: projectRoot, ...(sealId ? { seal_id: sealId } : {}), profile },
      { timeoutMs: options.timeoutMs, signal: options.signal }
    );
    const result = response.result;
    if (
      result.contest_snapshot_version !== 1 ||
      result.profile !== profile ||
      result.score_comparison_across_tasks !== 'forbidden' ||
      result.scheduling_owner !== 'python_coordinator' ||
      result.official_submission_enabled !== false
    ) {
      invalid('contest snapshot envelope is unsafe');
    }
    const returnedSealId = requiredText(result.seal_id, 'seal_id');
    if (sealId && returnedSealId !== sealId) invalid('contest snapshot seal identity differs from the request');
    const tasks = parseTasks(result.tasks, returnedSealId);
    const scheduling = record(result.scheduling, 'scheduling');
    const nextTaskId = scheduling.next_task_id === null ? null : requiredText(scheduling.next_task_id, 'next_task_id');
    const nextAction = requiredText(scheduling.next_action, 'next_action');
    const selectedTask = nextTaskId === null ? undefined : tasks.find((task) => task.task_id === nextTaskId);
    if (nextTaskId !== null && !selectedTask) {
      invalid('scheduling references an unknown task');
    }
    if ((selectedTask && nextAction !== selectedTask.next_action) || (!selectedTask && nextAction !== 'finish')) {
      invalid('scheduling action differs from the selected task');
    }
    return {
      schema: COMPETITION_CONTEST_SNAPSHOT_SCHEMA,
      status: 'ready',
      seal_id: returnedSealId,
      seal_hash: hash(result.seal_hash, 'seal_hash'),
      profile,
      score_comparison_across_tasks: 'forbidden',
      scheduling_owner: 'python_coordinator',
      tasks,
      scheduling: {
        next_task_id: nextTaskId,
        next_action: nextAction,
        reason: requiredText(scheduling.reason, 'reason'),
      },
      contest_snapshot_hash: hash(result.contest_snapshot_hash, 'contest_snapshot_hash'),
      official_submission_enabled: false,
      ...(response.diagnostics.stderr ? { diagnostics: response.diagnostics } : {}),
    };
  } catch (error) {
    return unavailable(error);
  }
}

export function formatCompetitionContestSnapshot(snapshot: CompetitionContestSnapshot) {
  return {
    content: [{ type: 'text' as const, text: JSON.stringify(snapshot, null, 2) }],
    ...(snapshot.status === 'unavailable' ? { isError: true as const } : {}),
  };
}

async function defaultRequest(
  launch: CompetitionEngineLaunch,
  params: Record<string, unknown>,
  options: CompetitionEngineRequestOptions
): Promise<CompetitionEngineCommandResult<Record<string, unknown>>> {
  return await new CompetitionEngineJsonlClient(launch).request('contest_snapshot', params, options);
}

function parseTasks(value: unknown, sealId: string): CompetitionContestTaskSnapshot[] {
  if (!Array.isArray(value) || value.length === 0) invalid('tasks must be a non-empty array');
  const tasks: CompetitionContestTaskSnapshot[] = value.map((raw, index) => {
    const task = record(raw, `tasks[${index}]`);
    if (task.task_order !== index + 1 || task.seal_id !== sealId) invalid('task order or seal identity is invalid');
    const state = task.state;
    if (state !== 'not_started' && state !== 'ready' && state !== 'active') invalid('task state is invalid');
    const candidateQueue = stringArray(task.candidate_queue, 'candidate_queue');
    const active = task.active_trial === null ? null : record(task.active_trial, 'active_trial');
    const activeStatus = active?.status;
    if (active && activeStatus !== 'claimed' && activeStatus !== 'running') invalid('active trial status is invalid');
    const recent = task.recent_improvement === null ? null : record(task.recent_improvement, 'recent_improvement');
    const budget = task.remaining_budget === null ? null : record(task.remaining_budget, 'remaining_budget');
    const control = parseControl(task.control);
    if (state === 'not_started' && (task.frontier_revision !== null || task.incumbent !== null || budget !== null)) {
      invalid('not-started task contains frontier state');
    }
    return {
      task_order: index + 1,
      seal_id: sealId,
      task_id: requiredText(task.task_id, 'task_id'),
      question: requiredText(task.question, 'question'),
      task_fingerprint: parseCompetitionTaskFingerprint(task.task_fingerprint, requiredText(task.task_id, 'task_id')),
      state: state as CompetitionContestTaskSnapshot['state'],
      frontier_revision: task.frontier_revision === null ? null : count(task.frontier_revision, 'frontier_revision'),
      incumbent: task.incumbent === null ? null : record(task.incumbent, 'incumbent'),
      candidate_queue: candidateQueue,
      active_trial: active
        ? {
            trial_id: requiredText(active.trial_id, 'trial_id'),
            candidate_id: requiredText(active.candidate_id, 'candidate_id'),
            status: activeStatus as 'claimed' | 'running',
          }
        : null,
      recent_improvement: recent
        ? {
            previous_trial_id: requiredText(recent.previous_trial_id, 'previous_trial_id'),
            current_trial_id: requiredText(recent.current_trial_id, 'current_trial_id'),
            oriented_delta: finite(recent.oriented_delta, 'oriented_delta'),
            improved: boolean(recent.improved, 'improved'),
          }
        : null,
      remaining_budget: budget
        ? {
            submissions: nonnegative(budget.submissions, 'submissions'),
            compute_seconds_spent: nonnegative(budget.compute_seconds_spent, 'compute_seconds_spent'),
            wall_time_seconds: nonnegative(budget.wall_time_seconds, 'wall_time_seconds'),
            tokens: nonnegative(budget.tokens, 'tokens'),
          }
        : null,
      blocker: task.blocker === null ? null : requiredText(task.blocker, 'blocker'),
      next_action: requiredText(task.next_action, 'next_action'),
      control,
    };
  });
  if (new Set(tasks.map((task) => task.task_id)).size !== tasks.length) invalid('tasks contain duplicate task_id');
  return tasks;
}

function parseControl(value: unknown): CompetitionContestTaskSnapshot['control'] {
  const control = record(value, 'control');
  if (control.control_version !== 1) invalid('control_version must be 1');
  const route = control.route;
  if (route !== 'bootstrap' && route !== 'first_score' && route !== 'recovery' && route !== 'search') {
    invalid('control route is invalid');
  }
  const phase = control.phase;
  if (phase !== 'preparation' && phase !== 'search') invalid('control phase is invalid');
  const watchdogActive = boolean(control.watchdog_active, 'watchdog_active');
  const recoveryKey =
    control.recovery_key === undefined || control.recovery_key === null
      ? null
      : hash(control.recovery_key, 'recovery_key');
  const firstScore = record(control.first_score, 'first_score');
  const status = firstScore.status;
  if (status !== 'pending' && status !== 'breached' && status !== 'recorded') {
    invalid('first_score status is invalid');
  }
  const elapsedToScore =
    firstScore.elapsed_to_score_seconds === null
      ? null
      : nonnegative(firstScore.elapsed_to_score_seconds, 'elapsed_to_score_seconds');
  const fallbackRequired = boolean(firstScore.fallback_required, 'fallback_required');
  const source = nullableFirstScoreSource(firstScore.source);
  const score = firstScore.score === null ? null : finite(firstScore.score, 'first_score score');
  if (
    (status === 'recorded' &&
      (route !== 'search' ||
        phase !== 'search' ||
        elapsedToScore === null ||
        fallbackRequired ||
        !source ||
        score === null)) ||
    (status === 'breached' &&
      (route !== 'recovery' ||
        phase !== 'search' ||
        !watchdogActive ||
        recoveryKey === null ||
        source !== null ||
        score !== null)) ||
    (status === 'pending' &&
      ((route !== 'bootstrap' && route !== 'first_score') || source !== null || score !== null)) ||
    (phase === 'preparation' && watchdogActive) ||
    (route === 'recovery' && recoveryKey === null)
  ) {
    invalid('competition control state is inconsistent');
  }
  return {
    control_version: 1,
    route,
    phase,
    watchdog_active: watchdogActive,
    recovery_key: recoveryKey,
    first_score: {
      status,
      started_at_epoch: nonnegative(firstScore.started_at_epoch, 'started_at_epoch'),
      guard_seconds: nonnegative(firstScore.guard_seconds, 'guard_seconds'),
      elapsed_seconds: nonnegative(firstScore.elapsed_seconds, 'elapsed_seconds'),
      elapsed_to_score_seconds: elapsedToScore,
      fallback_required: fallbackRequired,
      source,
      score,
    },
  };
}

function record(value: unknown, field: string): Record<string, unknown> {
  if (!isRecord(value)) invalid(`${field} must be an object`);
  return value;
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) invalid(`${field} must be a non-empty string`);
  return value.trim();
}

function hash(value: unknown, field: string): string {
  const text = requiredText(value, field);
  if (!/^[0-9a-f]{64}$/u.test(text)) invalid(`${field} must be a SHA-256 hash`);
  return text;
}

function count(value: unknown, field: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) invalid(`${field} must be a non-negative integer`);
  return Number(value);
}

function finite(value: unknown, field: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) invalid(`${field} must be finite`);
  return value;
}

function nonnegative(value: unknown, field: string): number {
  const number = finite(value, field);
  if (number < 0) invalid(`${field} must be non-negative`);
  return number;
}

function boolean(value: unknown, field: string): boolean {
  if (typeof value !== 'boolean') invalid(`${field} must be boolean`);
  return value;
}

function stringArray(value: unknown, field: string): string[] {
  if (!Array.isArray(value) || value.some((item) => typeof item !== 'string' || !item)) {
    invalid(`${field} must be a string array`);
  }
  const result = value as string[];
  if (new Set(result).size !== result.length) invalid(`${field} contains duplicates`);
  return [...result];
}

function nullableFirstScoreSource(value: unknown): 'baseline' | 'trial' | null {
  if (value === null) return null;
  if (value === 'baseline' || value === 'trial') return value;
  invalid('first_score source is invalid');
}

function unavailable(error: unknown): CompetitionContestSnapshot {
  if (error instanceof CompetitionEngineDiscoveryError) return buildUnavailable(error.code, error.message, false);
  if (error instanceof CompetitionEngineClientError) {
    return buildUnavailable(error.code, error.message, error.retryable, error.diagnostic, error.engineCode);
  }
  if (error instanceof ContestSnapshotValidationError) return buildUnavailable(error.code, error.message, false);
  return buildUnavailable('contest_snapshot_failed', 'IOAI contest snapshot failed', false);
}

function buildUnavailable(code: string, message: string, retryable: boolean, diagnostic = '', engineCode?: string) {
  return {
    schema: COMPETITION_CONTEST_SNAPSHOT_SCHEMA,
    status: 'unavailable' as const,
    official_submission_enabled: false as const,
    error: { code, message, retryable, ...(engineCode ? { engine_code: engineCode } : {}) },
    ...(diagnostic ? { diagnostics: { stderr: diagnostic } } : {}),
  };
}

function invalid(message: string): never {
  throw new ContestSnapshotValidationError('invalid_contest_snapshot', message);
}
