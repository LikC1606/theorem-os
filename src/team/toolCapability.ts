/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import path from 'node:path';
import {
  RESEARCH_TEAM_AGENT_LIMIT_ENV,
  RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV,
  RESEARCH_TEAM_CAPABILITY_PROFILE_ENV,
  RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV,
  RESEARCH_TEAM_CAPABILITY_SCHEMA,
  RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV,
  RESEARCH_TEAM_CAPABILITY_SLOT_ID_ENV,
  RESEARCH_TEAM_CAPABILITY_TEAM_ID_ENV,
  RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV,
  RESEARCH_TEAM_REASONING_CONCURRENCY_ENV,
  RESEARCH_TEAM_ROSTER_ENV,
} from "../common/config/builtinMcpConstants";
import {
  RESEARCH_TEAM_MCP_ACTIONS,
  type ResearchTeamMcpAction,
  type ResearchTeamRuntimeRosterMember,
} from "../common/types/team/researchTeamMcp";
import type { ResearchTeamRoleKind } from "../common/types/team/researchTeamContracts";
import {
  RESEARCH_TEAM_MAX_AGENT_LIMIT,
  RESEARCH_TEAM_MAX_REASONING_CONCURRENCY,
} from "../common/types/team/researchTeamContracts";

const CAPABILITY_ENV_KEYS = [
  RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV,
  RESEARCH_TEAM_CAPABILITY_PROFILE_ENV,
  RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV,
  RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV,
  RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV,
  RESEARCH_TEAM_CAPABILITY_TEAM_ID_ENV,
  RESEARCH_TEAM_CAPABILITY_SLOT_ID_ENV,
  RESEARCH_TEAM_AGENT_LIMIT_ENV,
  RESEARCH_TEAM_REASONING_CONCURRENCY_ENV,
  RESEARCH_TEAM_ROSTER_ENV,
] as const;

const ROLE_CAPABILITY_ENV_KEYS = [
  RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV,
  RESEARCH_TEAM_CAPABILITY_PROFILE_ENV,
  RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_ENV,
  RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV,
  RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV,
  RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV,
] as const;

const IDENTITY_CAPABILITY_ENV_KEYS = [
  RESEARCH_TEAM_CAPABILITY_TEAM_ID_ENV,
  RESEARCH_TEAM_CAPABILITY_SLOT_ID_ENV,
  RESEARCH_TEAM_AGENT_LIMIT_ENV,
  RESEARCH_TEAM_REASONING_CONCURRENCY_ENV,
  RESEARCH_TEAM_ROSTER_ENV,
] as const;

const CORE_RUNTIME_ENV_KEYS = [
  'AIONUI_BASE_URL',
  'AIONUI_USER_ID',
  'AIONUI_CONVERSATION_ID',
  'AIONUI_RUNTIME_TOKEN',
] as const;

const ROLE_ACTION_CEILINGS: Readonly<Record<ResearchTeamRoleKind, readonly ResearchTeamMcpAction[]>> = Object.freeze({
  lead: Object.freeze(['describe', 'dispatch', 'status', 'integrate', 'read_artifact'] as const),
  worker: Object.freeze(['describe', 'deliver', 'share', 'read_artifact', 'read_feedback'] as const),
});

export type ResearchTeamToolCapability = Readonly<{
  schema: typeof RESEARCH_TEAM_CAPABILITY_SCHEMA;
  profileId: string;
  workflowId: string;
  roleId: string;
  roleKind: ResearchTeamRoleKind;
  allowedActions: readonly ResearchTeamMcpAction[];
  projectRoot: string;
  teamId: string;
  slotId: string;
  agentLimit: number;
  reasoningConcurrency: number;
  roster: readonly ResearchTeamRuntimeRosterMember[];
}>;

export type ResearchTeamRoleCapability = Pick<
  ResearchTeamToolCapability,
  'schema' | 'profileId' | 'workflowId' | 'roleId' | 'roleKind' | 'allowedActions' | 'projectRoot'
>;

type CoreRuntimeResolverOptions = Readonly<{
  env?: Readonly<Record<string, string | undefined>>;
  fetchImpl?: typeof fetch;
}>;

type CoreRuntimeAccess = Readonly<{
  baseUrl: string;
  conversationId: string;
  headers: Record<string, string>;
}>;

/**
 * Reads the role half of a Research Team capability. Team and slot ids are not
 * available until Core creates the Team, so conversation snapshots may contain
 * this valid, deliberately unbound form.
 */
export function readResearchTeamRoleCapability(
  env: Readonly<Record<string, string | undefined>> = process.env
): ResearchTeamRoleCapability | undefined {
  const supplied = CAPABILITY_ENV_KEYS.filter((key) => env[key] !== undefined);
  if (!supplied.length) return undefined;
  if (ROLE_CAPABILITY_ENV_KEYS.some((key) => env[key] === undefined)) {
    throw new Error('Research Team MCP role capability environment is incomplete');
  }
  if (env[RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV] !== RESEARCH_TEAM_CAPABILITY_SCHEMA) {
    throw new Error('Research Team MCP capability schema is unsupported');
  }
  if (
    env[RESEARCH_TEAM_CAPABILITY_PROFILE_ENV] !== 'mathematics-research-team' ||
    env[RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV] !== 'science.mathematics.v1'
  ) {
    throw new Error('Research Team MCP requires a mathematics profile and workflow');
  }

  const roleKind = readRoleKind(env[RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV], 'role_kind');
  const actions = readActions(env[RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV]);
  if (actions.some((action) => !ROLE_ACTION_CEILINGS[roleKind].includes(action))) {
    throw new Error(`Research Team MCP ${roleKind} capability exceeds its hard action ceiling`);
  }

  return Object.freeze({
    schema: RESEARCH_TEAM_CAPABILITY_SCHEMA,
    profileId: stableId(env[RESEARCH_TEAM_CAPABILITY_PROFILE_ENV], 'profile_id'),
    workflowId: stableId(env[RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV], 'workflow_id'),
    roleId: stableId(env[RESEARCH_TEAM_CAPABILITY_ROLE_ENV], 'role_id'),
    roleKind,
    allowedActions: Object.freeze(actions),
    projectRoot: absoluteProjectRoot(env[RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV]),
  });
}

/** Returns a full snapshot only after Core has bound all Team identity fields. */
export function readBoundResearchTeamToolCapability(
  env: Readonly<Record<string, string | undefined>> = process.env
): ResearchTeamToolCapability | undefined {
  const role = readResearchTeamRoleCapability(env);
  if (!role) return undefined;
  const suppliedIdentity = IDENTITY_CAPABILITY_ENV_KEYS.filter((key) => env[key] !== undefined);
  if (!suppliedIdentity.length) return undefined;
  if (suppliedIdentity.length !== IDENTITY_CAPABILITY_ENV_KEYS.length) {
    throw new Error('Research Team MCP capability identity environment is incomplete');
  }
  return readResearchTeamToolCapability(env);
}

/** Reads the immutable role-scoped snapshot. Any partial snapshot fails closed. */
export function readResearchTeamToolCapability(
  env: Readonly<Record<string, string | undefined>> = process.env
): ResearchTeamToolCapability | undefined {
  const role = readResearchTeamRoleCapability(env);
  if (!role) return undefined;
  if (IDENTITY_CAPABILITY_ENV_KEYS.some((key) => env[key] === undefined)) {
    throw new Error('Research Team MCP capability environment is incomplete');
  }
  const teamId = stableId(env[RESEARCH_TEAM_CAPABILITY_TEAM_ID_ENV], 'team_id');
  const slotId = stableId(env[RESEARCH_TEAM_CAPABILITY_SLOT_ID_ENV], 'slot_id');
  const agentLimit = positiveInteger(env[RESEARCH_TEAM_AGENT_LIMIT_ENV], 'agent_limit', RESEARCH_TEAM_MAX_AGENT_LIMIT);
  const reasoningConcurrency = positiveInteger(
    env[RESEARCH_TEAM_REASONING_CONCURRENCY_ENV],
    'reasoning_concurrency',
    RESEARCH_TEAM_MAX_REASONING_CONCURRENCY
  );
  if (reasoningConcurrency > agentLimit) {
    throw new Error('Research Team MCP reasoning concurrency exceeds its Agent limit');
  }

  const roster = readRoster(env[RESEARCH_TEAM_ROSTER_ENV], agentLimit);
  const caller = roster.find((member) => member.slotId === slotId);
  if (!caller || caller.roleId !== role.roleId || caller.roleKind !== role.roleKind) {
    throw new Error('Research Team MCP roster does not contain the caller');
  }

  return Object.freeze({
    ...role,
    teamId,
    slotId,
    agentLimit,
    reasoningConcurrency,
    roster,
  });
}

/**
 * Resolves the post-create Team identity from Core. This is required because
 * Core freezes the MCP transport while creating each role conversation, before
 * Team and slot ids exist. The runtime token authenticates the lookup, and the
 * resolved server snapshot must exactly match the frozen role capability.
 */
export async function resolveResearchTeamRuntimeCapability(
  capability: ResearchTeamToolCapability | undefined,
  options: CoreRuntimeResolverOptions = {}
): Promise<ResearchTeamToolCapability | undefined> {
  if (capability) return capability;
  const env = options.env ?? process.env;
  const expectedRole = readResearchTeamRoleCapability(env);
  if (!expectedRole) return undefined;
  const access = coreRuntimeAccess(env);
  const fetchImpl = options.fetchImpl ?? fetch;
  const context = await readCoreRuntimeData(
    fetchImpl,
    `${access.baseUrl}/api/runtime/team-tools/context`,
    access.headers,
    'Team context'
  );
  if (context.in_team !== true) throw new Error('Core runtime conversation is not in a Team');
  const teamId = stableId(context.team_id, 'team_id');
  const slotId = stableId(context.slot_id, 'slot_id');
  const conversation = await readCoreRuntimeData(
    fetchImpl,
    `${access.baseUrl}/api/conversations/${encodeURIComponent(access.conversationId)}`,
    access.headers,
    'Conversation capability snapshot'
  );
  if (stableId(conversation.id, 'conversation_id') !== access.conversationId || !isRecord(conversation.extra)) {
    throw new Error('Core conversation capability snapshot is invalid');
  }
  const extra = conversation.extra;
  if (
    stableId(extra.team_id, 'team_id') !== teamId ||
    stableId(extra.team_slot_id, 'slot_id') !== slotId ||
    stableId(extra.research_team_profile_id, 'profile_id') !== expectedRole.profileId ||
    stableId(extra.research_team_workflow_id, 'workflow_id') !== expectedRole.workflowId ||
    stableId(extra.research_team_role_id, 'role_id') !== expectedRole.roleId ||
    extra.research_team_role_kind !== expectedRole.roleKind
  ) {
    throw new Error('Core conversation capability snapshot does not match the Research Team role');
  }
  const mcpServerIds = Array.isArray(extra.mcp_server_ids)
    ? extra.mcp_server_ids.map((id) => stableId(id, 'mcp_server_id'))
    : [];
  if (!mcpServerIds.length) throw new Error('Core conversation is missing its role MCP capability');

  const resolved = (
    await Promise.all(
      mcpServerIds.map(async (id) => {
        const server = await readCoreRuntimeData(
          fetchImpl,
          `${access.baseUrl}/api/mcp/servers/${encodeURIComponent(id)}`,
          access.headers,
          'Role MCP capability'
        );
        if (!isRecord(server.transport) || !isRecord(server.transport.env)) return undefined;
        const capabilityEnv = Object.fromEntries(
          Object.entries(server.transport.env).flatMap(([key, value]) =>
            typeof value === 'string' ? [[key, value] as const] : []
          )
        );
        return readBoundResearchTeamToolCapability(capabilityEnv);
      })
    )
  ).filter((item): item is ResearchTeamToolCapability => Boolean(item));
  if (resolved.length !== 1) throw new Error('Core conversation role MCP capability is ambiguous');
  const runtimeCapability = resolved[0];
  if (
    runtimeCapability.teamId !== teamId ||
    runtimeCapability.slotId !== slotId ||
    !sameRoleCapability(runtimeCapability, expectedRole)
  ) {
    throw new Error('Core conversation role MCP capability does not match the Research Team context');
  }
  return runtimeCapability;
}

export function authorizeResearchTeamToolAction(
  action: ResearchTeamMcpAction,
  capability: ResearchTeamToolCapability
): void {
  if (!capability.allowedActions.includes(action)) {
    throw new Error(`Research Team role ${capability.roleId} cannot call action ${action}`);
  }
}

function readActions(value: unknown): ResearchTeamMcpAction[] {
  let parsed: unknown;
  try {
    parsed = JSON.parse(String(value ?? ''));
  } catch {
    throw new Error('Research Team MCP capability actions are invalid JSON');
  }
  if (
    !Array.isArray(parsed) ||
    !parsed.length ||
    !parsed.every(
      (action): action is ResearchTeamMcpAction =>
        typeof action === 'string' && RESEARCH_TEAM_MCP_ACTIONS.includes(action as ResearchTeamMcpAction)
    ) ||
    new Set(parsed).size !== parsed.length
  ) {
    throw new Error('Research Team MCP capability actions are invalid');
  }
  return parsed;
}

function readRoster(value: unknown, agentLimit: number): readonly ResearchTeamRuntimeRosterMember[] {
  let parsed: unknown;
  try {
    parsed = JSON.parse(String(value ?? ''));
  } catch {
    throw new Error('Research Team MCP roster is invalid JSON');
  }
  if (!Array.isArray(parsed) || parsed.length !== agentLimit + 1) {
    throw new Error('Research Team MCP roster does not match its Agent limit');
  }

  const slots = new Set<string>();
  const roles = new Set<string>();
  const roster = parsed.map((value): ResearchTeamRuntimeRosterMember => {
    if (!isRecord(value)) throw new Error('Research Team MCP roster member is invalid');
    const slotId = stableId(value.slotId, 'roster.slot_id');
    const roleId = stableId(value.roleId, 'roster.role_id');
    const roleKind = readRoleKind(value.roleKind, 'roster.role_kind');
    const laneId = optionalStableId(value.laneId, 'roster.lane_id');
    const displayName = requiredText(value.displayName, 'roster.display_name');
    if (
      slots.has(slotId) ||
      roles.has(roleId) ||
      (roleKind === 'lead' && laneId !== undefined) ||
      (roleKind === 'worker' && laneId === undefined)
    ) {
      throw new Error('Research Team MCP roster identity is invalid');
    }
    slots.add(slotId);
    roles.add(roleId);
    return Object.freeze({ slotId, roleId, roleKind, ...(laneId ? { laneId } : {}), displayName });
  });
  if (roster.filter((member) => member.roleKind === 'lead').length !== 1) {
    throw new Error('Research Team MCP roster requires exactly one Lead');
  }
  if (roster.filter((member) => member.roleKind === 'worker').length !== agentLimit) {
    throw new Error('Research Team MCP roster Worker count is invalid');
  }
  return Object.freeze(roster);
}

function absoluteProjectRoot(value: unknown): string {
  const root = requiredText(value, 'project_root');
  if (!path.isAbsolute(root)) throw new Error('Research Team MCP project_root must be absolute');
  return path.resolve(root);
}

function readRoleKind(value: unknown, field: string): ResearchTeamRoleKind {
  if (value !== 'lead' && value !== 'worker') throw new Error(`Research Team MCP ${field} is invalid`);
  return value;
}

function positiveInteger(value: unknown, field: string, maximum: number): number {
  const number = Number(value);
  if (!Number.isSafeInteger(number) || number < 1 || number > maximum) {
    throw new Error(`Research Team MCP ${field} is invalid`);
  }
  return number;
}

function optionalStableId(value: unknown, field: string): string | undefined {
  return value === undefined ? undefined : stableId(value, field);
}

function stableId(value: unknown, field: string): string {
  const normalized = requiredText(value, field);
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new Error(`Research Team MCP ${field} is invalid`);
  }
  return normalized;
}

function requiredText(value: unknown, field: string): string {
  const normalized = typeof value === 'string' ? value.trim() : '';
  if (!normalized) throw new Error(`Research Team MCP ${field} is required`);
  return normalized;
}

function sameRoleCapability(capability: ResearchTeamToolCapability, expected: ResearchTeamRoleCapability): boolean {
  return (
    capability.profileId === expected.profileId &&
    capability.workflowId === expected.workflowId &&
    capability.roleId === expected.roleId &&
    capability.roleKind === expected.roleKind &&
    path.resolve(capability.projectRoot) === path.resolve(expected.projectRoot) &&
    capability.allowedActions.length === expected.allowedActions.length &&
    capability.allowedActions.every((action, index) => action === expected.allowedActions[index])
  );
}

function coreRuntimeAccess(env: Readonly<Record<string, string | undefined>>): CoreRuntimeAccess {
  const supplied = CORE_RUNTIME_ENV_KEYS.filter((key) => env[key] !== undefined);
  if (supplied.length !== CORE_RUNTIME_ENV_KEYS.length) {
    throw new Error('Core runtime identity environment is incomplete');
  }
  const baseUrl = localCoreBaseUrl(env.AIONUI_BASE_URL);
  const conversationId = requiredText(env.AIONUI_CONVERSATION_ID, 'AIONUI_CONVERSATION_ID');
  return {
    baseUrl,
    conversationId,
    headers: {
      'x-aionui-user-id': requiredText(env.AIONUI_USER_ID, 'AIONUI_USER_ID'),
      'x-aionui-conversation-id': conversationId,
      'x-aionui-runtime-token': requiredText(env.AIONUI_RUNTIME_TOKEN, 'AIONUI_RUNTIME_TOKEN'),
    },
  };
}

function localCoreBaseUrl(value: unknown): string {
  const raw = requiredText(value, 'AIONUI_BASE_URL');
  const url = new URL(raw);
  if (url.protocol !== 'http:' || !['127.0.0.1', 'localhost', '::1', '[::1]'].includes(url.hostname)) {
    throw new Error('Research Team runtime capability resolution must target the local Core');
  }
  return url.toString().replace(/\/$/u, '');
}

async function readCoreRuntimeData(
  fetchImpl: typeof fetch,
  url: string,
  headers: Record<string, string>,
  label: string
): Promise<Record<string, unknown>> {
  let lastError: unknown;
  for (let attempt = 0; attempt < 2; attempt += 1) {
    try {
      const response = await fetchImpl(url, {
        method: 'GET',
        headers,
        signal: AbortSignal.timeout(5_000),
      });
      let payload: unknown;
      try {
        payload = await response.json();
      } catch {
        throw new Error(`${label} returned invalid JSON`);
      }
      if (!response.ok || !isRecord(payload) || payload.success !== true || !isRecord(payload.data)) {
        throw new Error(`${label} request failed`);
      }
      return payload.data;
    } catch (error) {
      lastError = error;
      const retryable =
        error instanceof TypeError || (error instanceof Error && ['AbortError', 'TimeoutError'].includes(error.name));
      if (!retryable || attempt === 1) throw error;
      await new Promise((resolve) => setTimeout(resolve, 150));
    }
  }
  throw lastError instanceof Error ? lastError : new Error(`${label} request failed`);
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}
