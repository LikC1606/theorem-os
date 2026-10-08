/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import type {
  BackendTeammateStatus,
  ITeamRunAck,
  TeamAgent,
  TeammateRole,
  TeammateStatus,
  TTeam,
  WorkspaceMode,
  TeamCoordinationProtocol,
} from "../types/team/teamTypes";
import { LEGACY_LOCAL_RUNTIME_ID } from "../config/legacyIdentifiers";

// ── Parameter types for team API calls ─────────────────────────────────

export type ICreateTeamParams = {
  coordination_protocol?: TeamCoordinationProtocol;
  user_id: string;
  name: string;
  workspace: string;
  workspace_mode: WorkspaceMode;
  agents: Omit<TeamAgent, 'slot_id' | 'conversation_id'>[];
};

export type IAddTeamAgentParams = {
  team_id: string;
  agent: Omit<TeamAgent, 'slot_id' | 'conversation_id'>;
};

// ── Backend → Frontend ─────────────────────────────────────────────────

const VALID_ROLES = new Set<TeammateRole>(['leader', 'teammate']);
const VALID_WORKSPACE_MODES = new Set<WorkspaceMode>(['shared', 'isolated']);
const VALID_RUN_TARGET_ROLES = new Set(['lead', 'teammate']);
const VALID_RUN_STATUSES = new Set(['accepted', 'running', 'cancelling', 'completed', 'cancelled', 'failed']);
const VALID_ENQUEUE_STATUSES = new Set(['accepted', 'queued', 'blocked_runtime_starting']);

function toRole(raw: string | undefined): TeammateRole {
  if (raw === 'lead') return 'leader';
  return VALID_ROLES.has(raw as TeammateRole) ? (raw as TeammateRole) : 'teammate';
}

export function normalizeTeamStatus(raw: BackendTeammateStatus | undefined): TeammateStatus {
  const statusMap: Record<string, TeammateStatus> = {
    pending: 'pending',
    idle: 'idle',
    working: 'active',
    thinking: 'active',
    tool_use: 'active',
    completed: 'completed',
    error: 'failed',
  };
  return statusMap[raw ?? ''] ?? 'idle';
}

function toWorkspaceMode(raw: string | undefined): WorkspaceMode {
  return VALID_WORKSPACE_MODES.has(raw as WorkspaceMode) ? (raw as WorkspaceMode) : 'shared';
}

const NON_ACP_BACKENDS = new Set(['openclaw-gateway', 'nanobot', 'remote']);

function resolveConversationType(backend: string): string {
  return NON_ACP_BACKENDS.has(backend) ? backend : 'acp';
}

export function fromBackendAgent(raw: unknown): TeamAgent {
  const r = (raw ?? {}) as Record<string, unknown>;
  const rawAgentType =
    (r.agent_type as string | undefined) ??
    (r.assistant_backend as string | undefined) ??
    (r.backend as string | undefined) ??
    '';
  const rawBackend = (r.assistant_backend as string | undefined) ?? (r.backend as string | undefined) ?? rawAgentType;
  const backend = rawBackend === LEGACY_LOCAL_RUNTIME_ID ? 'codex' : rawBackend;
  const agentType = rawAgentType === LEGACY_LOCAL_RUNTIME_ID ? backend : rawAgentType;
  const conversationType = resolveConversationType(backend);
  return {
    slot_id: (r.slot_id as string | undefined) ?? '',
    conversation_id: (r.conversation_id as string | undefined) ?? '',
    role: toRole(r.role as string | undefined),
    agent_type: agentType,
    icon: r.icon as string | undefined,
    agent_name:
      (r.assistant_name as string | undefined) ??
      (r.agent_name as string | undefined) ??
      (r.name as string | undefined) ??
      '',
    conversation_type: conversationType,
    status: normalizeTeamStatus(r.status as BackendTeammateStatus | undefined),
    cli_path: r.cli_path as string | undefined,
    custom_agent_id: r.custom_agent_id as string | undefined,
    assistant_id: r.assistant_id as string | undefined,
    model: r.model as string | undefined,
    pending_confirmations: (r.pending_confirmations ?? r.pendingConfirmations ?? 0) as number,
  };
}

export function fromBackendTeam(raw: unknown): TTeam {
  const r = (raw ?? {}) as Record<string, unknown>;
  const rawAgents = Array.isArray(r.assistants)
    ? (r.assistants as unknown[])
    : Array.isArray(r.agents)
      ? (r.agents as unknown[])
      : [];
  const agents = rawAgents.map(fromBackendAgent);
  return {
    coordination_protocol: fromBackendTeamCoordinationProtocol(r.coordination_protocol),
    id: (r.id as string | undefined) ?? '',
    user_id: (r.user_id as string | undefined) ?? '',
    name: (r.name as string | undefined) ?? '',
    workspace: (r.workspace as string | undefined) ?? '',
    workspace_mode: toWorkspaceMode(r.workspace_mode as string | undefined),
    leader_agent_id: (r.leader_assistant_id as string | undefined) ?? (r.leader_agent_id as string | undefined) ?? '',
    agents,
    session_mode: r.session_mode as string | undefined,
    created_at: (r.created_at as number | undefined) ?? 0,
    updated_at: (r.updated_at as number | undefined) ?? 0,
  };
}

function fromBackendTeamCoordinationProtocol(raw: unknown): TeamCoordinationProtocol | undefined {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return undefined;
  const value = raw as Record<string, unknown>;
  if (value.kind === 'core_native' && Object.keys(value).length === 1) return { kind: 'core_native' };
  if (value.kind === 'managed_mcp' && value.logicalTool === 'research_team' && Object.keys(value).length === 2) {
    return { kind: 'managed_mcp', logicalTool: 'research_team' };
  }
  // Unrecognized responses must not satisfy the managed-protocol startup gate.
  return undefined;
}

export function fromBackendTeamList(raw: unknown): TTeam[] {
  return Array.isArray(raw) ? (raw as unknown[]).map(fromBackendTeam) : [];
}

export function fromBackendTeamOptional(raw: unknown): TTeam | null {
  return raw == null ? null : fromBackendTeam(raw);
}

export function fromBackendTeamRunAck(
  expectedTeamId: string,
  raw: unknown,
  expectedTargetSlotId?: string
): ITeamRunAck {
  const normalizedExpectedTeamId = expectedTeamId.trim();
  if (!normalizedExpectedTeamId) throw new Error('Team run acknowledgement request Team is invalid');
  const normalizedExpectedTargetSlotId = expectedTargetSlotId?.trim();
  if (expectedTargetSlotId !== undefined && !normalizedExpectedTargetSlotId) {
    throw new Error('Team run acknowledgement request Agent is invalid');
  }
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    throw new Error('Team run acknowledgement is invalid');
  }
  const envelope = raw as Record<string, unknown>;
  const nestedRun = envelope.run;
  const isRunSnapshot = Boolean(nestedRun && typeof nestedRun === 'object' && !Array.isArray(nestedRun));
  const enqueueStatus = isRunSnapshot && typeof envelope.enqueue_status === 'string' ? envelope.enqueue_status : '';
  if (isRunSnapshot && !VALID_ENQUEUE_STATUSES.has(enqueueStatus)) {
    throw new Error('Team run acknowledgement is invalid');
  }
  const record = isRunSnapshot ? (nestedRun as Record<string, unknown>) : envelope;
  const responseTeamId = typeof record.team_id === 'string' ? record.team_id.trim() : '';
  if (!responseTeamId) throw new Error('Team run acknowledgement is invalid');
  if (responseTeamId !== normalizedExpectedTeamId) {
    throw new Error('Team run acknowledgement does not match the request Team');
  }
  const requiredString = (field: string): string => {
    const value = record[field];
    if (typeof value !== 'string' || !value.trim()) throw new Error('Team run acknowledgement is invalid');
    return value.trim();
  };
  let targetRole = requiredString('target_role');
  let targetSlotId = requiredString('target_slot_id');
  if (isRunSnapshot && normalizedExpectedTargetSlotId && normalizedExpectedTargetSlotId !== targetSlotId) {
    const slotWork = Array.isArray(record.slot_work) ? record.slot_work : [];
    const requestedSlot = slotWork.find(
      (item) =>
        item !== null &&
        typeof item === 'object' &&
        !Array.isArray(item) &&
        typeof (item as Record<string, unknown>).slot_id === 'string' &&
        (item as Record<string, unknown>).slot_id === normalizedExpectedTargetSlotId
    ) as Record<string, unknown> | undefined;
    const requestedRole = requestedSlot?.role;
    if (typeof requestedRole !== 'string' || !VALID_RUN_TARGET_ROLES.has(requestedRole)) {
      throw new Error('Team run acknowledgement does not include the requested Agent');
    }
    targetSlotId = normalizedExpectedTargetSlotId;
    targetRole = requestedRole;
  }
  const acceptedRole = isRunSnapshot ? targetRole : requiredString('accepted_role');
  const acceptedSlotId = isRunSnapshot ? targetSlotId : requiredString('accepted_slot_id');
  const status = requiredString('status');
  if (
    !VALID_RUN_TARGET_ROLES.has(targetRole) ||
    !VALID_RUN_TARGET_ROLES.has(acceptedRole) ||
    !VALID_RUN_STATUSES.has(status)
  ) {
    throw new Error('Team run acknowledgement is invalid');
  }

  return {
    team_run_id: requiredString('team_run_id'),
    team_id: normalizedExpectedTeamId,
    target_slot_id: targetSlotId,
    target_role: targetRole as ITeamRunAck['target_role'],
    accepted_slot_id: acceptedSlotId,
    accepted_role: acceptedRole as ITeamRunAck['accepted_role'],
    status: status as ITeamRunAck['status'],
    ...(isRunSnapshot ? { enqueue_status: enqueueStatus as ITeamRunAck['enqueue_status'] } : {}),
    ...(typeof envelope.message_id === 'string' && envelope.message_id.trim()
      ? { message_id: envelope.message_id.trim() }
      : typeof record.message_id === 'string' && record.message_id.trim()
        ? { message_id: record.message_id.trim() }
        : {}),
    ...(isRunSnapshot && typeof envelope.replayed === 'boolean' ? { replayed: envelope.replayed } : {}),
  };
}

// ── Frontend → Backend ─────────────────────────────────────────────────

export function toBackendAgent(a: Omit<TeamAgent, 'slot_id' | 'conversation_id'>): Record<string, unknown> {
  const assistantId = a.assistant_id ?? a.custom_agent_id;
  if (!assistantId) {
    throw new Error('assistant_id is required to create a Team member');
  }
  return {
    name: a.agent_name,
    role: a.role === 'leader' ? 'lead' : a.role,
    model: a.model || 'default',
    assistant_id: assistantId,
  };
}

/** Maps the shared Team create contract to the slimmer Core HTTP payload. */
export function toBackendTeamCreate(params: ICreateTeamParams): Record<string, unknown> {
  return {
    ...(params.coordination_protocol ? { coordination_protocol: params.coordination_protocol } : {}),
    name: params.name,
    agents: params.agents.map(toBackendAgent),
    ...(params.workspace ? { workspace: params.workspace } : {}),
  };
}
