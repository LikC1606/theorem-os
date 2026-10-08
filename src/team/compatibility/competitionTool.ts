/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { formatCompetitionExecutionAction, readCompetitionExecutionAction } from "./executionActions";
import { formatCompetitionBenchmarkAction, readCompetitionBenchmarkAction } from "./benchmarkActions";
import { formatCompetitionFrontierSnapshot, readCompetitionFrontierSnapshot } from "./frontierSnapshot";
import { formatCompetitionSystemStatus, readCompetitionSystemStatus } from "./systemStatus";
import { formatCompetitionWorkflowAction, readCompetitionWorkflowAction } from "./workflowActions";
import {
  formatCompetitionOfficialSubmissionAction,
  readCompetitionOfficialSubmissionAction,
} from "./submissionActions";
import type { IoaiCompetitionEvaluationProfile } from "../../common/chat/ioaiCompetition";
import type {
  IoaiCompetitionActiveTeamTurn,
  IoaiCompetitionRuntimeAttestation,
} from "../../common/chat/ioaiCompetition";
import { formatCompetitionContestSnapshot, readCompetitionContestSnapshot } from "./contestSnapshot";
import { IOAI_COMPETITION_CAPABILITY_SCHEMA } from "../../common/config/builtinMcpConstants";
import type { IoaiCompetitionMcpAction } from "../../common/types/team/ioaiCompetitionActionPolicy";
import type {
  IoaiCompetitionStrategyLane,
  IoaiCompetitionTeamRoleId,
} from "../../common/types/team/ioaiCompetitionTeam";
import { authorizeCompetitionToolCall } from "./toolCapability";
import { COMPETITION_ENGINE_REQUEST_TIMEOUT_MS } from "../competition-runtime/jsonlClient";

export const COMPETITION_MCP_TIMEOUT_MS = COMPETITION_ENGINE_REQUEST_TIMEOUT_MS;

export type CompetitionToolInput = {
  action: IoaiCompetitionMcpAction;
  project_root?: string;
  seal_id?: string;
  task_id?: string;
  profile?: IoaiCompetitionEvaluationProfile;
  bundle_path?: string;
  preflight_path?: string;
  baseline_candidate_path?: string;
  operation?: 'arm' | 'run' | 'read' | 'confirm' | 'authorize' | 'prepare' | 'record';
  competition_id?: string;
  system_id?: string;
  authorization_prompt_sha256?: string;
  baseline_attempt_limit?: number;
  deadline_utc?: string;
  max_submissions?: number;
  protected_reserve?: number;
  trial_id?: string;
  packet_hash?: string;
  notebook_path?: string;
  notebook_ref?: string;
  notebook_version?: string;
  role_id?: string;
  attempt_key?: string;
  prompt_hash?: string;
  evaluator_version?: string;
  use_reserve?: boolean;
  attempt_id?: string;
  notebook_version_id?: string;
  submission_id?: string;
  remote_status?: string;
  remote_receipt_path?: string;
  score?: number;
  failure_kind?: string;
  candidate_path?: string;
  candidate_sha256?: string;
  batch_path?: string;
  max_workers?: number;
  expected_frontier_revision?: number;
  run_id?: string;
  idempotency_key?: string;
  study_id?: string;
  idea_id?: string;
  durable_line_id?: string;
  direction?: 'maximize' | 'minimize';
  search_space?: Record<string, unknown>;
  seed?: number;
  n_startup_trials?: number;
  parent_candidate_id?: string;
  candidate_id?: string;
  team_id?: string;
  slot_id?: string;
  team_run_id?: string;
  turn_id?: string;
  state?: 'complete' | 'pruned' | 'failed';
};

export type CompetitionToolAction = CompetitionToolInput['action'];

type CompetitionToolCapabilityBase = {
  schema: typeof IOAI_COMPETITION_CAPABILITY_SCHEMA;
  roleId: string;
  projectRoot: string;
  allowedActions: readonly CompetitionToolAction[];
};

export type CompetitionTeamRosterMember = Readonly<{
  slotId: string;
  roleId: IoaiCompetitionTeamRoleId;
  strategyLane?: IoaiCompetitionStrategyLane;
}>;

export type CompetitionToolCapability = Readonly<
  CompetitionToolCapabilityBase &
    (
      | { identityBinding: 'role'; teamId?: undefined; slotId?: undefined }
      | {
          identityBinding: 'team-slot';
          teamId: string;
          slotId: string;
          agentLimit: number;
          reasoningConcurrency: number;
          roster: readonly CompetitionTeamRosterMember[];
        }
    )
>;

export type CompetitionToolContext = {
  signal?: AbortSignal;
  capability?: CompetitionToolCapability;
  runtimeAttestation?: IoaiCompetitionRuntimeAttestation;
  resolveCapability?: () => Promise<CompetitionToolCapability | undefined>;
  resolveActiveTeamTurn?: (capability: CompetitionToolCapability) => Promise<IoaiCompetitionActiveTeamTurn>;
};

export type CompetitionToolReaders = {
  systemStatus: typeof readCompetitionSystemStatus;
  workflowAction: typeof readCompetitionWorkflowAction;
  executionAction: typeof readCompetitionExecutionAction;
  frontierSnapshot: typeof readCompetitionFrontierSnapshot;
  contestSnapshot: typeof readCompetitionContestSnapshot;
  benchmarkAction: typeof readCompetitionBenchmarkAction;
  officialSubmissionAction: typeof readCompetitionOfficialSubmissionAction;
};

const DEFAULT_READERS: CompetitionToolReaders = {
  systemStatus: readCompetitionSystemStatus,
  workflowAction: readCompetitionWorkflowAction,
  executionAction: readCompetitionExecutionAction,
  frontierSnapshot: readCompetitionFrontierSnapshot,
  contestSnapshot: readCompetitionContestSnapshot,
  benchmarkAction: readCompetitionBenchmarkAction,
  officialSubmissionAction: readCompetitionOfficialSubmissionAction,
};

export async function runCompetitionTool(
  input: CompetitionToolInput,
  context: CompetitionToolContext = {},
  readerOverrides: Partial<CompetitionToolReaders> = {}
) {
  let capability = context.capability;
  if (!capability && context.resolveCapability) {
    try {
      capability = await context.resolveCapability();
    } catch (error) {
      return authorizationError(
        `authenticated competition capability is unavailable: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }
  const effectiveInput =
    capability && input.project_root === undefined ? { ...input, project_root: capability.projectRoot } : input;
  let activeTeamTurn: IoaiCompetitionActiveTeamTurn | undefined;
  const denied = await authorizeCompetitionToolCall(effectiveInput, capability);
  if (denied) return authorizationError(denied);
  const readers = { ...DEFAULT_READERS, ...readerOverrides };
  const {
    action,
    project_root,
    seal_id,
    task_id,
    profile,
    bundle_path,
    preflight_path,
    baseline_candidate_path,
    operation,
    competition_id,
    system_id,
    authorization_prompt_sha256,
    baseline_attempt_limit,
    deadline_utc,
    max_submissions,
    protected_reserve,
    trial_id,
    packet_hash,
    notebook_path,
    notebook_ref,
    notebook_version,
    role_id,
    attempt_key,
    prompt_hash,
    evaluator_version,
    use_reserve,
    attempt_id,
    notebook_version_id,
    submission_id,
    remote_status,
    remote_receipt_path,
    score,
    failure_kind,
    candidate_path,
    candidate_sha256,
    batch_path,
    max_workers,
    expected_frontier_revision,
    run_id,
    idempotency_key,
    study_id,
    idea_id,
    durable_line_id,
    direction,
    search_space,
    seed,
    n_startup_trials,
    parent_candidate_id,
    candidate_id,
    team_id,
    slot_id,
    team_run_id,
    turn_id,
    state,
  } = effectiveInput;
  const supplied = {
    project_root,
    seal_id,
    task_id,
    profile,
    bundle_path,
    preflight_path,
    baseline_candidate_path,
    operation,
    competition_id,
    system_id,
    authorization_prompt_sha256,
    baseline_attempt_limit,
    deadline_utc,
    max_submissions,
    protected_reserve,
    trial_id,
    packet_hash,
    notebook_path,
    notebook_ref,
    notebook_version,
    role_id,
    attempt_key,
    prompt_hash,
    evaluator_version,
    use_reserve,
    attempt_id,
    notebook_version_id,
    submission_id,
    remote_status,
    remote_receipt_path,
    score,
    failure_kind,
    candidate_path,
    candidate_sha256,
    batch_path,
    max_workers,
    expected_frontier_revision,
    run_id,
    idempotency_key,
    study_id,
    idea_id,
    durable_line_id,
    direction,
    search_space,
    seed,
    n_startup_trials,
    parent_candidate_id,
    candidate_id,
    team_id,
    slot_id,
    team_run_id,
    turn_id,
    state,
  };
  const signal = context.signal;

  if (action === 'system_status') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'seal_id',
      'task_id',
      'competition_id',
      'role_id',
      'team_id',
      'slot_id',
    ]);
    if (invalid) return inputError(`system_status does not accept: ${invalid}`);
    const status = await readers.systemStatus({ signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.status });
    if (status.status === 'ready' && capability && capability.roleId !== 'ioai-lead') {
      if (!context.resolveActiveTeamTurn) {
        return authorizationError('authenticated active Team turn resolver is unavailable');
      }
      try {
        activeTeamTurn = await context.resolveActiveTeamTurn(capability);
      } catch (error) {
        return authorizationError(
          `authenticated active Team turn is unavailable: ${error instanceof Error ? error.message : String(error)}`
        );
      }
    }
    return formatCompetitionSystemStatus(
      status.status === 'ready'
        ? {
            ...status,
            ...(context.runtimeAttestation ? { runtime_attestation: context.runtimeAttestation } : {}),
            ...(activeTeamTurn ? { active_team_turn: activeTeamTurn } : {}),
          }
        : status
    );
  }
  if (action === 'environment_preflight') {
    const invalid = unexpectedFields(supplied, ['project_root', 'preflight_path']);
    if (invalid) return inputError(`environment_preflight does not accept: ${invalid}`);
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          projectRoot: project_root ?? '',
          preflightPath: preflight_path ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.workflow }
      )
    );
  }
  if (action === 'bootstrap_run') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'preflight_path',
      'bundle_path',
      'baseline_candidate_path',
      'idempotency_key',
    ]);
    if (invalid) return inputError(`bootstrap_run does not accept: ${invalid}`);
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          projectRoot: project_root ?? '',
          preflightPath: preflight_path ?? '',
          bundlePath: bundle_path ?? '',
          baselineCandidatePath: baseline_candidate_path ?? '',
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.bootstrap }
      )
    );
  }
  if (action === 'frontier_snapshot') {
    const invalid = unexpectedFields(supplied, ['project_root', 'seal_id', 'task_id', 'profile']);
    if (invalid) return inputError(`frontier_snapshot does not accept: ${invalid}`);
    return formatCompetitionFrontierSnapshot(
      await readers.frontierSnapshot({
        projectRoot: project_root ?? '',
        sealId: seal_id ?? '',
        taskId: task_id ?? '',
        ...(profile ? { profile } : {}),
        signal,
        timeoutMs: COMPETITION_MCP_TIMEOUT_MS.read,
      })
    );
  }
  if (action === 'contest_snapshot') {
    const invalid = unexpectedFields(supplied, ['project_root', 'seal_id', 'task_id', 'profile']);
    if (invalid) return inputError(`contest_snapshot does not accept: ${invalid}`);
    return formatCompetitionContestSnapshot(
      await readers.contestSnapshot({
        projectRoot: project_root ?? '',
        ...(seal_id ? { sealId: seal_id } : {}),
        ...(profile ? { profile } : {}),
        signal,
        timeoutMs: COMPETITION_MCP_TIMEOUT_MS.read,
      })
    );
  }
  if (action === 'official_submission') {
    return formatCompetitionOfficialSubmissionAction(
      await readers.officialSubmissionAction(
        {
          action,
          projectRoot: project_root ?? '',
          operation: operation as 'authorize' | 'read' | 'prepare' | 'record',
          competitionId: competition_id,
          notebookRef: notebook_ref,
          deadlineUtc: deadline_utc,
          maxSubmissions: max_submissions,
          protectedReserve: protected_reserve,
          authorizationPromptSha256: authorization_prompt_sha256,
          sealId: seal_id,
          taskId: task_id,
          trialId: trial_id,
          packetHash: packet_hash,
          notebookPath: notebook_path,
          notebookVersion: notebook_version,
          roleId: role_id,
          attemptKey: attempt_key,
          promptHash: prompt_hash,
          evaluatorVersion: evaluator_version,
          useReserve: use_reserve,
          attemptId: attempt_id,
          notebookVersionId: notebook_version_id,
          submissionId: submission_id,
          remoteStatus: remote_status,
          remoteReceiptPath: remote_receipt_path,
          score,
          failureKind: failure_kind,
          idempotencyKey: idempotency_key,
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.workflow }
      )
    );
  }
  if (action === 'competition_lock') {
    if (operation !== 'arm' && operation !== 'read') {
      return inputError('competition_lock requires operation arm or read');
    }
    const allowed =
      operation === 'arm'
        ? [
            'project_root',
            'operation',
            'competition_id',
            'system_id',
            'authorization_prompt_sha256',
            'baseline_attempt_limit',
            'idempotency_key',
          ]
        : ['project_root', 'operation'];
    const invalid = unexpectedFields(supplied, allowed);
    if (invalid) return inputError(`competition_lock operation ${operation} does not accept: ${invalid}`);
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        operation === 'arm'
          ? {
              action,
              operation,
              projectRoot: project_root ?? '',
              competitionId: competition_id ?? '',
              systemId: system_id ?? '',
              authorizationPromptSha256: authorization_prompt_sha256 ?? '',
              baselineAttemptLimit: baseline_attempt_limit ?? 0,
              idempotencyKey: idempotency_key ?? '',
            }
          : {
              action,
              operation,
              projectRoot: project_root ?? '',
            },
        {
          signal,
          timeoutMs: operation === 'read' ? COMPETITION_MCP_TIMEOUT_MS.read : COMPETITION_MCP_TIMEOUT_MS.workflow,
        }
      )
    );
  }
  if (action === 'benchmark_run') {
    const invalid = unexpectedFields(supplied, ['project_root', 'seal_id', 'task_id', 'run_id']);
    if (invalid) return inputError(`benchmark_run does not accept: ${invalid}`);
    return formatCompetitionBenchmarkAction(
      await readers.benchmarkAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          runId: run_id ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.execution }
      )
    );
  }
  if (action === 'benchmark_read') {
    const invalid = unexpectedFields(supplied, ['project_root', 'run_id']);
    if (invalid) return inputError(`benchmark_read does not accept: ${invalid}`);
    return formatCompetitionBenchmarkAction(
      await readers.benchmarkAction(
        { action, projectRoot: project_root ?? '', runId: run_id ?? '' },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.read }
      )
    );
  }
  if (action === 'task_import') {
    const invalid = unexpectedFields(supplied, ['project_root', 'bundle_path', 'idempotency_key']);
    if (invalid) return inputError(`task_import does not accept: ${invalid}`);
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          projectRoot: project_root ?? '',
          bundlePath: bundle_path ?? '',
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.workflow }
      )
    );
  }
  if (action === 'evaluator_audit') {
    const invalid = unexpectedFields(supplied, ['project_root', 'seal_id', 'idempotency_key']);
    if (invalid) return inputError(`evaluator_audit does not accept: ${invalid}`);
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.workflow }
      )
    );
  }
  if (action === 'trial_run') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'seal_id',
      'task_id',
      'profile',
      'candidate_path',
      'candidate_sha256',
      'candidate_id',
      'role_id',
      'team_id',
      'slot_id',
      'team_run_id',
      'turn_id',
      'expected_frontier_revision',
      'idempotency_key',
    ]);
    if (invalid) return inputError(`trial_run does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          ...(profile ? { profile } : {}),
          candidatePath: candidate_path ?? '',
          ...(candidate_sha256 ? { candidateSha256: candidate_sha256 } : {}),
          expectedFrontierRevision: expected_frontier_revision ?? -1,
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.execution }
      )
    );
  }
  if (action === 'tune_create') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'seal_id',
      'task_id',
      'study_id',
      'idea_id',
      'durable_line_id',
      'parent_candidate_id',
      'direction',
      'search_space',
      'seed',
      'n_startup_trials',
    ]);
    if (invalid) return inputError(`tune_create does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          studyId: study_id ?? '',
          ideaId: idea_id ?? '',
          durableLineId: durable_line_id ?? '',
          parentCandidateId: parent_candidate_id ?? '',
          direction: direction ?? 'maximize',
          searchSpace: search_space ?? {},
          ...(seed === undefined ? {} : { seed }),
          ...(n_startup_trials === undefined ? {} : { nStartupTrials: n_startup_trials }),
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.tuning }
      )
    );
  }
  if (action === 'tune_ask') {
    const invalid = unexpectedFields(supplied, ['project_root', 'seal_id', 'task_id', 'study_id']);
    if (invalid) return inputError(`tune_ask does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          studyId: study_id ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.tuning }
      )
    );
  }
  if (action === 'tune_tell') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'study_id',
      'candidate_id',
      'state',
      'trial_id',
      'packet_hash',
    ]);
    if (invalid) return inputError(`tune_tell does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          studyId: study_id ?? '',
          candidateId: candidate_id ?? '',
          state: state ?? 'failed',
          ...(trial_id === undefined ? {} : { trialId: trial_id }),
          ...(packet_hash === undefined ? {} : { packetHash: packet_hash }),
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.tuning }
      )
    );
  }
  if (action === 'tune_status') {
    const invalid = unexpectedFields(supplied, ['project_root', 'study_id']);
    if (invalid) return inputError(`tune_status does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          ...(study_id === undefined ? {} : { studyId: study_id }),
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.tuning }
      )
    );
  }
  if (action === 'trial_batch') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'seal_id',
      'task_id',
      'profile',
      'batch_path',
      'max_workers',
      'expected_frontier_revision',
      'idempotency_key',
    ]);
    if (invalid) return inputError(`trial_batch does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          ...(profile ? { profile } : {}),
          batchPath: batch_path ?? '',
          maxWorkers: max_workers ?? 0,
          expectedFrontierRevision: expected_frontier_revision ?? -1,
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.execution }
      )
    );
  }
  if (action === 'report_generate') {
    const invalid = unexpectedFields(supplied, [
      'project_root',
      'seal_id',
      'task_id',
      'profile',
      'expected_frontier_revision',
      'idempotency_key',
    ]);
    if (invalid) return inputError(`report_generate does not accept: ${invalid}`);
    return formatCompetitionExecutionAction(
      await readers.executionAction(
        {
          action,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          taskId: task_id ?? '',
          ...(profile ? { profile } : {}),
          expectedFrontierRevision: expected_frontier_revision ?? -1,
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs: COMPETITION_MCP_TIMEOUT_MS.execution }
      )
    );
  }
  if (!operation) return inputError('baseline_run requires operation');
  if (operation !== 'run' && operation !== 'read' && operation !== 'confirm') {
    return inputError('baseline_run operation must be run, read, or confirm');
  }
  const allowed =
    operation === 'run'
      ? ['project_root', 'seal_id', 'operation', 'candidate_path', 'idempotency_key']
      : operation === 'read'
        ? ['project_root', 'seal_id', 'operation', 'run_id']
        : ['project_root', 'seal_id', 'operation', 'run_id', 'idempotency_key'];
  const invalid = unexpectedFields(supplied, allowed);
  if (invalid) return inputError(`baseline_run operation ${operation} does not accept: ${invalid}`);
  const timeoutMs = operation === 'read' ? COMPETITION_MCP_TIMEOUT_MS.read : COMPETITION_MCP_TIMEOUT_MS.workflow;
  if (operation === 'run') {
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          operation,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          candidatePath: candidate_path ?? '',
          idempotencyKey: idempotency_key ?? '',
        },
        { signal, timeoutMs }
      )
    );
  }
  if (operation === 'read') {
    return formatCompetitionWorkflowAction(
      await readers.workflowAction(
        {
          action,
          operation,
          projectRoot: project_root ?? '',
          sealId: seal_id ?? '',
          runId: run_id ?? '',
        },
        { signal, timeoutMs }
      )
    );
  }
  return formatCompetitionWorkflowAction(
    await readers.workflowAction(
      {
        action,
        operation,
        projectRoot: project_root ?? '',
        sealId: seal_id ?? '',
        runId: run_id ?? '',
        idempotencyKey: idempotency_key ?? '',
      },
      { signal, timeoutMs }
    )
  );
}

function unexpectedFields(supplied: Record<string, unknown>, allowed: string[]): string {
  const allowlist = new Set(allowed);
  return Object.entries(supplied)
    .filter(([key, value]) => value !== undefined && !allowlist.has(key))
    .map(([key]) => key)
    .join(', ');
}

function inputError(message: string) {
  return {
    content: [
      {
        type: 'text' as const,
        text: JSON.stringify({
          schema: 'deepscientist.ioai.competition.request-error.v1',
          status: 'unavailable',
          official_submission_enabled: false,
          error: { code: 'invalid_request', message, retryable: false },
        }),
      },
    ],
    isError: true,
  };
}

function authorizationError(message: string) {
  return {
    content: [
      {
        type: 'text' as const,
        text: JSON.stringify({
          schema: 'deepscientist.ioai.competition.authorization-error.v1',
          status: 'unavailable',
          official_submission_enabled: false,
          error: { code: 'permission_denied', message, retryable: false },
        }),
      },
    ],
    isError: true,
  };
}
