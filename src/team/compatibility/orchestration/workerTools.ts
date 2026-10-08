/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import path from 'node:path';
import { IOAI_COMPETITION_ATOMIC_ASSIGNMENT_SCHEMA } from "../../../common/types/team/ioaiCompetitionTeam";
import { resolveTeamAgentSlotId } from "../../../common/types/team/teamAgentIds";
import {
  normalizeTeamWaitSeconds,
  teamWaitLevelForSeconds,
  type TeamWaitLevel,
} from "../../../common/types/team/teamWaitPolicy";
import type { CompetitionToolCapability } from "../competitionTool";
import type { ChallengeCoreTeamClient } from "./coreTeamClient";
import { isRecord } from "../../competition-runtime/protocol";
import {
  createResearchTeamOrchestrator,
  ResearchTeamOrchestrationError,
  type ResearchTeamOrchestrationEvent,
  type ResearchTeamRuntime,
} from "../../orchestrator";
import {
  integrateProjectGitAgentBranch,
  prepareProjectGitAgentWorktree,
  type ProjectGitIntegrateAgentBranchRequest,
  type ProjectGitIntegrateAgentBranchResult,
  type ProjectGitPrepareAgentWorktreeRequest,
  type ProjectGitPrepareAgentWorktreeResult,
} from "../../../project-git/index";

export const CHALLENGE_DELEGATE_RESULT_SCHEMA = 'deepscientist.challenge.delegate-result.v1' as const;
export const CHALLENGE_WAIT_RESULT_SCHEMA = 'deepscientist.challenge.wait-result.v1' as const;
export const CHALLENGE_INTEGRATE_RESULT_SCHEMA = 'deepscientist.challenge.integrate-result.v1' as const;

export type ChallengeDelegateInput = Readonly<{
  targetSlotId: string;
  assignment: Record<string, unknown>;
  idempotencyKey: string;
}>;

export type ChallengeWaitInput = Readonly<{
  waitSeconds?: number;
  waitLevel?: TeamWaitLevel;
  targetSlotIds?: readonly string[];
}>;

export type ChallengeIntegrateInput = Readonly<{
  targetSlotId: string;
  branch: string;
  commit?: string;
  summary?: string;
}>;

export type ChallengeProjectGitDriver = Readonly<{
  prepareAgentWorktree: (request: ProjectGitPrepareAgentWorktreeRequest) => ProjectGitPrepareAgentWorktreeResult;
  integrateAgentBranch: (request: ProjectGitIntegrateAgentBranchRequest) => ProjectGitIntegrateAgentBranchResult;
}>;

export type ChallengeOrchestrationContext = Readonly<{
  capability: CompetitionToolCapability;
  client: ChallengeCoreTeamClient;
  signal?: AbortSignal;
  sleep?: (milliseconds: number, signal?: AbortSignal) => Promise<void>;
  projectGit?: ChallengeProjectGitDriver;
}>;

type ToolResult = {
  content: { type: 'text'; text: string }[];
  isError?: boolean;
};

type ChallengeLeadCapability = Extract<CompetitionToolCapability, { identityBinding: 'team-slot' }>;
type ChallengeRosterMember = ChallengeLeadCapability['roster'][number];
type ChallengeRuntimeContext = Readonly<{
  capability: ChallengeLeadCapability;
  projectGit: ChallengeProjectGitDriver;
}>;
type ChallengeValidatedAssignment = Readonly<{
  assignment: Record<string, unknown>;
  target: ChallengeRosterMember;
}>;
type ChallengePreparedDetail = Readonly<{
  target: ChallengeRosterMember;
  branch: NonNullable<ProjectGitPrepareAgentWorktreeResult['branch']>;
  workspace: string;
}>;
type ChallengeIntegratedDetail = Readonly<{
  target: ChallengeRosterMember;
  branch: NonNullable<ProjectGitIntegrateAgentBranchResult['branch']>;
  mergedCommit: string;
  alreadyIntegrated: boolean;
}>;
type ChallengeEvent = ResearchTeamOrchestrationEvent<
  Record<string, unknown>,
  ChallengeValidatedAssignment,
  ChallengePreparedDetail,
  ChallengeIntegrateInput,
  ChallengeIntegratedDetail
>;

const challengeOrchestrator = createResearchTeamOrchestrator<
  Record<string, unknown>,
  ChallengeValidatedAssignment,
  ChallengePreparedDetail,
  ChallengeIntegrateInput,
  ChallengeIntegratedDetail,
  ChallengeRuntimeContext,
  ToolResult
>({
  validateAssignment: (request, runtime) => {
    const capability = runtime.context.capability;
    const target = capability.roster.find((member) => member.slotId === request.targetSlotId);
    if (!target || target.roleId === 'ioai-lead' || !target.strategyLane) {
      throw new ResearchTeamOrchestrationError(
        'foreign_or_lead_slot',
        'The target slot is not a Worker in this Challenge Team.'
      );
    }
    return Object.freeze({
      assignment: validateAssignment(request.assignment, capability, target),
      target,
    });
  },
  prepare: (request, validated, runtime) => {
    const capability = runtime.context.capability;
    const hypothesis =
      isRecord(validated.assignment.lead_assignment) && isRecord(validated.assignment.lead_assignment.hypothesis)
        ? stableOptionalText(validated.assignment.lead_assignment.hypothesis.statement)
        : undefined;
    const prepared = runtime.context.projectGit.prepareAgentWorktree({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: request.targetSlotId,
      roleId: validated.target.roleId,
      strategyLane: validated.target.strategyLane,
      assignmentId: request.idempotencyKey,
      objective: hypothesis,
    });
    if (!prepared.ok || !prepared.branch || !prepared.workspace) {
      throw new ResearchTeamOrchestrationError(
        'agent_worktree_unavailable',
        prepared.error || 'Unable to prepare the Worker Git worktree.',
        true
      );
    }
    const leadAssignment = validated.assignment.lead_assignment as Record<string, unknown>;
    const enrichedAssignment = {
      ...validated.assignment,
      lead_assignment: {
        ...leadAssignment,
        git_workspace: {
          schema: 'deepscientist.challenge.git-workspace.v1',
          branch: prepared.branch.name,
          worktree_path: prepared.workspace,
          base_commit: prepared.branch.baseCommit,
          owner: {
            team_id: capability.teamId,
            slot_id: request.targetSlotId,
            role_id: validated.target.roleId,
            strategy_lane: validated.target.strategyLane,
            assignment_id: request.idempotencyKey,
          },
        },
      },
    };
    return Object.freeze({
      message: JSON.stringify(enrichedAssignment),
      detail: Object.freeze({
        target: validated.target,
        branch: prepared.branch,
        workspace: prepared.workspace,
      }),
    });
  },
  integrate: (input, runtime) => {
    const capability = runtime.context.capability;
    const targetSlotId = stableId(input.targetSlotId, 'target_slot_id');
    const target = capability.roster.find((member) => member.slotId === targetSlotId);
    if (!target || target.roleId === 'ioai-lead') {
      throw new ResearchTeamOrchestrationError(
        'foreign_or_lead_slot',
        'The target slot is not a Worker in this Challenge Team.'
      );
    }
    const branch = stableBranch(input.branch);
    const commit = input.commit?.trim();
    if (commit && !/^[a-f0-9]{40}$/u.test(commit)) {
      throw new ResearchTeamOrchestrationError('integration_failed', 'commit must be a full 40-character Git SHA');
    }
    const integrated = runtime.context.projectGit.integrateAgentBranch({
      workspace: capability.projectRoot,
      teamId: capability.teamId,
      slotId: targetSlotId,
      branch,
      expectedHead: commit,
      summary: stableOptionalText(input.summary),
    });
    if (!integrated.ok || !integrated.branch || !integrated.mergedCommit) {
      throw new ResearchTeamOrchestrationError(
        'integration_failed',
        integrated.error || 'Unable to integrate the Worker branch.'
      );
    }
    return Object.freeze({
      target,
      branch: integrated.branch,
      mergedCommit: integrated.mergedCommit,
      alreadyIntegrated: integrated.alreadyIntegrated === true,
    });
  },
  present: (event, runtime) => presentChallengeEvent(event, runtime),
});

export async function runChallengeDelegate(
  input: ChallengeDelegateInput,
  context: ChallengeOrchestrationContext
): Promise<ToolResult> {
  try {
    const runtime = toChallengeRuntime(context);
    const targetSlotId = resolveChallengeWorkerSlotId(input.targetSlotId, runtime.context.capability);
    return await challengeOrchestrator.dispatch(
      {
        ...input,
        targetSlotId,
        assignment: normalizeAssignmentSlotId(input.assignment, targetSlotId, runtime.context.capability),
      },
      runtime
    );
  } catch (error) {
    if (error instanceof ResearchTeamOrchestrationError) {
      return errorResult(CHALLENGE_DELEGATE_RESULT_SCHEMA, error.code, error.message, error.retryable);
    }
    return errorResult(
      CHALLENGE_DELEGATE_RESULT_SCHEMA,
      'dispatch_failed',
      error instanceof Error ? error.message : String(error),
      true
    );
  }
}

export async function runChallengeIntegrate(
  input: ChallengeIntegrateInput,
  context: ChallengeOrchestrationContext
): Promise<ToolResult> {
  try {
    const runtime = toChallengeRuntime(context);
    return await challengeOrchestrator.integrate(
      { ...input, targetSlotId: resolveChallengeWorkerSlotId(input.targetSlotId, runtime.context.capability) },
      runtime
    );
  } catch (error) {
    if (error instanceof ResearchTeamOrchestrationError) {
      return errorResult(CHALLENGE_INTEGRATE_RESULT_SCHEMA, error.code, error.message, error.retryable);
    }
    return errorResult(
      CHALLENGE_INTEGRATE_RESULT_SCHEMA,
      'integration_failed',
      error instanceof Error ? error.message : String(error)
    );
  }
}

export async function runChallengeWait(
  input: ChallengeWaitInput,
  context: ChallengeOrchestrationContext
): Promise<ToolResult> {
  try {
    const runtime = toChallengeRuntime(context);
    const capability = runtime.context.capability;
    const targets = normalizeTargets(input.targetSlotIds, capability);
    return await challengeOrchestrator.status(
      {
        targetSlotIds: targets,
        waitSeconds: normalizeTeamWaitSeconds(input.waitSeconds, input.waitLevel),
      },
      runtime
    );
  } catch (error) {
    return errorResult(
      CHALLENGE_WAIT_RESULT_SCHEMA,
      'wait_failed',
      error instanceof Error ? error.message : String(error),
      true
    );
  }
}

function toChallengeRuntime(context: ChallengeOrchestrationContext): ResearchTeamRuntime<ChallengeRuntimeContext> {
  const capability = requireLeadCapability(context.capability);
  return Object.freeze({
    teamId: capability.teamId,
    coordinatorSlotId: capability.slotId,
    reasoningConcurrency: capability.reasoningConcurrency,
    client: context.client,
    context: Object.freeze({
      capability,
      projectGit: context.projectGit ?? DEFAULT_PROJECT_GIT_DRIVER,
    }),
    signal: context.signal,
    sleep: context.sleep,
  });
}

function resolveChallengeWorkerSlotId(value: unknown, capability: ChallengeLeadCapability): string {
  let slotId: string;
  try {
    slotId = resolveTeamAgentSlotId(value, capability.roster);
  } catch {
    throw new ResearchTeamOrchestrationError(
      'foreign_or_lead_slot',
      'The target agent_id is not a Worker in this Challenge Team.'
    );
  }
  const target = capability.roster.find((member) => member.slotId === slotId);
  if (!target || target.roleId === 'ioai-lead' || !target.strategyLane) {
    throw new ResearchTeamOrchestrationError(
      'foreign_or_lead_slot',
      'The target agent_id is not a Worker in this Challenge Team.'
    );
  }
  return slotId;
}

function presentChallengeEvent(
  event: ChallengeEvent,
  runtime: ResearchTeamRuntime<ChallengeRuntimeContext>
): ToolResult {
  const capability = runtime.context.capability;
  switch (event.kind) {
    case 'dispatch.accepted':
      return result({
        schema: CHALLENGE_DELEGATE_RESULT_SCHEMA,
        status: 'accepted',
        accepted: true,
        retryable: false,
        team_id: capability.teamId,
        target_slot_id: event.request.targetSlotId,
        target_role_id: event.prepared.detail.target.roleId,
        strategy_lane: event.prepared.detail.target.strategyLane,
        team_run_id: event.acknowledgement.team_run_id,
        enqueue_status: event.acknowledgement.enqueue_status ?? 'accepted',
        message_id: event.acknowledgement.message_id ?? null,
        reasoning_concurrency: capability.reasoningConcurrency,
        monitor_owns_completion_wake: true,
        git_branch: event.prepared.detail.branch.name,
        git_worktree: event.prepared.detail.workspace,
        git_base_commit: event.prepared.detail.branch.baseCommit,
      });
    case 'dispatch.target-busy':
      return errorResult(
        CHALLENGE_DELEGATE_RESULT_SCHEMA,
        'target_busy',
        'The selected Worker already has queued or active work.',
        true
      );
    case 'dispatch.capacity':
      return result({
        schema: CHALLENGE_DELEGATE_RESULT_SCHEMA,
        status: 'capacity',
        accepted: false,
        retryable: true,
        reasoning_concurrency: capability.reasoningConcurrency,
        active_worker_slots: event.activeWorkerSlotIds,
        target_slot_id: event.request.targetSlotId,
        instruction: 'End this Lead turn or wait for a verified completion before dispatching more work.',
      });
    case 'dispatch.error':
      return errorResult(CHALLENGE_DELEGATE_RESULT_SCHEMA, event.code, event.message, event.retryable);
    case 'status.observed': {
      const selected = event.state.slots.filter(
        (slot) => !event.selectedSlotIds.length || event.selectedSlotIds.includes(slot.slotId)
      );
      const activeWorkerSlots = event.state.activeSlotIds.filter((slotId) => slotId !== capability.slotId);
      return result({
        schema: CHALLENGE_WAIT_RESULT_SCHEMA,
        status: 'observed',
        team_id: capability.teamId,
        reasoning_concurrency: capability.reasoningConcurrency,
        active_worker_slots: activeWorkerSlots,
        slots: selected.map((slot) => ({ slot_id: slot.slotId, state: slot.state })),
        changed: event.changed,
        wait_seconds: event.request.waitSeconds ?? 0,
        wait_level: teamWaitLevelForSeconds(event.request.waitSeconds ?? 0) ?? null,
        should_end_turn: activeWorkerSlots.length > 0,
        monitor_owns_completion_wake: true,
        instruction:
          'Do not poll repeatedly. End the Lead turn when Workers are active; the Team monitor will wake this conversation with verified completion evidence or a terminal failure.',
      });
    }
    case 'status.error':
      return errorResult(CHALLENGE_WAIT_RESULT_SCHEMA, 'wait_failed', event.message, true);
    case 'integration.accepted':
      return result({
        schema: CHALLENGE_INTEGRATE_RESULT_SCHEMA,
        status: event.integration.alreadyIntegrated ? 'already_integrated' : 'integrated',
        accepted: true,
        team_id: capability.teamId,
        target_slot_id: event.request.targetSlotId,
        target_role_id: event.integration.target.roleId,
        strategy_lane: event.integration.target.strategyLane,
        branch: event.integration.branch.name,
        delivered_commit: event.integration.branch.head,
        merged_commit: event.integration.mergedCommit,
        merged_into: event.integration.branch.mergedInto,
        merged_at: event.integration.branch.mergedAt,
      });
    case 'integration.error':
      return errorResult(CHALLENGE_INTEGRATE_RESULT_SCHEMA, event.code, event.message, event.retryable);
  }
}

function validateAssignment(
  value: unknown,
  capability: Extract<CompetitionToolCapability, { identityBinding: 'team-slot' }>,
  target: (typeof capability.roster)[number]
): Record<string, unknown> {
  if (!isRecord(value) || value.schema !== IOAI_COMPETITION_ATOMIC_ASSIGNMENT_SCHEMA) {
    throw new Error(`assignment must use ${IOAI_COMPETITION_ATOMIC_ASSIGNMENT_SCHEMA}`);
  }
  if (!isRecord(value.lead_assignment) || !isRecord(value.lead_assignment.runtime_identity)) {
    throw new Error('assignment is missing lead_assignment.runtime_identity');
  }
  const leadAssignment = value.lead_assignment as Record<string, unknown>;
  const runtimeIdentity = leadAssignment.runtime_identity as Record<string, unknown>;
  const assignmentRoot = stableOptionalText(leadAssignment.project_root);
  if (
    !assignmentRoot ||
    path.resolve(assignmentRoot) !== path.resolve(capability.projectRoot) ||
    runtimeIdentity.team_id !== capability.teamId ||
    runtimeIdentity.slot_id !== target.slotId ||
    runtimeIdentity.role_id !== target.roleId ||
    runtimeIdentity.strategy_lane !== target.strategyLane
  ) {
    throw new Error('assignment identity does not match the target Worker capability');
  }
  for (const key of ['seal_id', 'task_id'] as const) {
    if (!stableOptionalText(leadAssignment[key])) throw new Error(`assignment is missing ${key}`);
  }
  return value;
}

function requireLeadCapability(
  capability: CompetitionToolCapability
): Extract<CompetitionToolCapability, { identityBinding: 'team-slot' }> {
  if (capability.roleId !== 'ioai-lead' || capability.identityBinding !== 'team-slot') {
    throw new Error('Challenge orchestration requires the Core-authenticated Lead capability');
  }
  return capability;
}

function normalizeTargets(
  values: readonly string[] | undefined,
  capability: Extract<CompetitionToolCapability, { identityBinding: 'team-slot' }>
): string[] {
  if (!values?.length) return [];
  const targets = [...new Set(values.map((value) => resolveTeamAgentSlotId(value, capability.roster)))];
  if (targets.some((slotId) => !capability.roster.some((member) => member.slotId === slotId))) {
    throw new Error('challenge_wait target contains a foreign Team slot');
  }
  return targets;
}

function normalizeAssignmentSlotId(
  value: Record<string, unknown>,
  targetSlotId: string,
  capability: ChallengeLeadCapability
): Record<string, unknown> {
  if (!isRecord(value.lead_assignment) || !isRecord(value.lead_assignment.runtime_identity)) return value;
  const leadAssignment = value.lead_assignment as Record<string, unknown>;
  const runtimeIdentity = leadAssignment.runtime_identity as Record<string, unknown>;
  const requestedSlotId = runtimeIdentity.slot_id;
  if (requestedSlotId === undefined) return value;
  const canonicalSlotId = resolveTeamAgentSlotId(requestedSlotId, capability.roster);
  if (canonicalSlotId !== targetSlotId) {
    throw new Error('assignment runtime identity does not match target agent_id');
  }
  return {
    ...value,
    lead_assignment: {
      ...leadAssignment,
      runtime_identity: { ...runtimeIdentity, slot_id: canonicalSlotId },
    },
  };
}

function result(payload: Record<string, unknown>): ToolResult {
  return { content: [{ type: 'text', text: JSON.stringify(payload, null, 2) }] };
}

function errorResult(schema: string, code: string, message: string, retryable = false): ToolResult {
  return {
    content: [
      {
        type: 'text',
        text: JSON.stringify({
          schema,
          status: 'unavailable',
          accepted: false,
          error: { code, message, retryable },
        }),
      },
    ],
    isError: true,
  };
}

function stableOptionalText(value: unknown): string | undefined {
  const normalized = typeof value === 'string' ? value.trim() : '';
  return normalized || undefined;
}

function stableId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) throw new Error(`${field} is invalid`);
  return normalized;
}

function stableBranch(value: unknown): string {
  const branch = String(value ?? '').trim();
  if (!branch || branch.length > 180 || branch.startsWith('-') || branch.includes('\0')) {
    throw new Error('branch is invalid');
  }
  return branch;
}

const DEFAULT_PROJECT_GIT_DRIVER: ChallengeProjectGitDriver = Object.freeze({
  prepareAgentWorktree: prepareProjectGitAgentWorktree,
  integrateAgentBranch: integrateProjectGitAgentBranch,
});
