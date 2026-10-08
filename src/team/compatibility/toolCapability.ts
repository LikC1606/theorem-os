/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import path from 'node:path';
import {
  normalizeIoaiCompetitionAgentPoolConfig,
  getIoaiCompetitionConversationExtra,
  IOAI_COMPETITION_ACTIVE_TEAM_TURN_SCHEMA,
  type IoaiCompetitionActiveTeamTurn,
} from "../../common/chat/ioaiCompetition";
import {
  IOAI_COMPETITION_CAPABILITY_ACTIONS_ENV,
  IOAI_COMPETITION_CAPABILITY_PROJECT_ROOT_ENV,
  IOAI_COMPETITION_CAPABILITY_ROLE_ENV,
  IOAI_COMPETITION_CAPABILITY_SCHEMA,
  IOAI_COMPETITION_CAPABILITY_SCHEMA_ENV,
  IOAI_COMPETITION_CAPABILITY_SLOT_ID_ENV,
  IOAI_COMPETITION_CAPABILITY_TEAM_ID_ENV,
  IOAI_COMPETITION_AGENT_LIMIT_ENV,
  IOAI_COMPETITION_CORE_BASE_URL_ENV,
  IOAI_COMPETITION_REASONING_CONCURRENCY_ENV,
  IOAI_COMPETITION_TEAM_ROSTER_ENV,
} from "../../common/config/builtinMcpConstants";
import {
  getIoaiCompetitionRoleActionCeiling,
  isIoaiCompetitionMcpAction,
  type IoaiCompetitionPolicyRoleId,
} from "../../common/types/team/ioaiCompetitionActionPolicy";
import type { CompetitionTeamRosterMember, CompetitionToolAction, CompetitionToolCapability } from "./competitionTool";
import type { CompetitionToolInput } from "./competitionTool";
import { isRecord } from "../competition-runtime/protocol";

const ROLE_CAPABILITY_ENV_KEYS = [
  IOAI_COMPETITION_CAPABILITY_SCHEMA_ENV,
  IOAI_COMPETITION_CAPABILITY_ROLE_ENV,
  IOAI_COMPETITION_CAPABILITY_ACTIONS_ENV,
  IOAI_COMPETITION_CAPABILITY_PROJECT_ROOT_ENV,
] as const;

const IDENTITY_CAPABILITY_ENV_KEYS = [
  IOAI_COMPETITION_CAPABILITY_TEAM_ID_ENV,
  IOAI_COMPETITION_CAPABILITY_SLOT_ID_ENV,
  IOAI_COMPETITION_AGENT_LIMIT_ENV,
  IOAI_COMPETITION_REASONING_CONCURRENCY_ENV,
  IOAI_COMPETITION_TEAM_ROSTER_ENV,
] as const;

export function readCompetitionToolCapability(
  env: Readonly<Record<string, string | undefined>> = process.env
): CompetitionToolCapability | undefined {
  const supplied = [...ROLE_CAPABILITY_ENV_KEYS, ...IDENTITY_CAPABILITY_ENV_KEYS].filter(
    (key) => env[key] !== undefined
  );
  if (!supplied.length) return undefined;
  if (ROLE_CAPABILITY_ENV_KEYS.some((key) => env[key] === undefined)) {
    throw new Error('IOAI MCP capability environment is incomplete');
  }
  const suppliedIdentity = IDENTITY_CAPABILITY_ENV_KEYS.filter((key) => env[key] !== undefined);
  if (suppliedIdentity.length > 0 && suppliedIdentity.length !== IDENTITY_CAPABILITY_ENV_KEYS.length) {
    throw new Error('IOAI MCP capability identity environment is incomplete');
  }
  if (env[IOAI_COMPETITION_CAPABILITY_SCHEMA_ENV] !== IOAI_COMPETITION_CAPABILITY_SCHEMA) {
    throw new Error('IOAI MCP capability schema is unsupported');
  }

  const roleId = String(env[IOAI_COMPETITION_CAPABILITY_ROLE_ENV] ?? '').trim();
  if (!/^ioai-(?:lead|subagent-(?:exploit|explore|debug|audit|fusion)(?:-(?:[2-9]|[1-9][0-9]+))?)$/u.test(roleId)) {
    throw new Error('IOAI MCP capability role is invalid');
  }
  const rawProjectRoot = String(env[IOAI_COMPETITION_CAPABILITY_PROJECT_ROOT_ENV] ?? '').trim();
  if (!rawProjectRoot || !path.isAbsolute(rawProjectRoot)) {
    throw new Error('IOAI MCP capability project root is invalid');
  }
  const projectRoot = path.resolve(rawProjectRoot);
  const identity =
    suppliedIdentity.length === IDENTITY_CAPABILITY_ENV_KEYS.length
      ? readTeamSlotIdentity(env, roleId)
      : { identityBinding: 'role' as const };

  let rawActions: unknown;
  try {
    rawActions = JSON.parse(String(env[IOAI_COMPETITION_CAPABILITY_ACTIONS_ENV] ?? ''));
  } catch {
    throw new Error('IOAI MCP capability actions are invalid JSON');
  }
  if (
    !Array.isArray(rawActions) ||
    !rawActions.length ||
    !rawActions.every((action): action is CompetitionToolAction => isIoaiCompetitionMcpAction(action)) ||
    new Set(rawActions).size !== rawActions.length
  ) {
    throw new Error('IOAI MCP capability actions are invalid');
  }
  const actions = rawActions as CompetitionToolAction[];
  const hardCeiling = getIoaiCompetitionRoleActionCeiling(roleId as IoaiCompetitionPolicyRoleId);
  if (actions.some((action) => !hardCeiling.includes(action))) {
    throw new Error(
      `IOAI MCP ${roleId === 'ioai-lead' ? 'Lead' : 'Subagent'} capability exceeds its hard action ceiling`
    );
  }

  return Object.freeze({
    schema: IOAI_COMPETITION_CAPABILITY_SCHEMA,
    roleId,
    ...identity,
    projectRoot,
    allowedActions: Object.freeze([...actions]),
  });
}

function readTeamSlotIdentity(
  env: Readonly<Record<string, string | undefined>>,
  callerRoleId: string
): Readonly<{
  identityBinding: 'team-slot';
  teamId: string;
  slotId: string;
  agentLimit: number;
  reasoningConcurrency: number;
  roster: readonly CompetitionTeamRosterMember[];
}> {
  const teamId = stableId(env[IOAI_COMPETITION_CAPABILITY_TEAM_ID_ENV], 'team_id');
  const slotId = stableId(env[IOAI_COMPETITION_CAPABILITY_SLOT_ID_ENV], 'slot_id');
  const rawAgentLimit = Number(env[IOAI_COMPETITION_AGENT_LIMIT_ENV]);
  const rawReasoningConcurrency = Number(env[IOAI_COMPETITION_REASONING_CONCURRENCY_ENV]);
  const pool = normalizeIoaiCompetitionAgentPoolConfig({
    agentLimit: rawAgentLimit,
    reasoningConcurrency: rawReasoningConcurrency,
  });
  if (pool.agentLimit !== rawAgentLimit || pool.reasoningConcurrency !== rawReasoningConcurrency) {
    throw new Error('IOAI MCP capability Agent pool is invalid');
  }
  let rawRoster: unknown;
  try {
    rawRoster = JSON.parse(String(env[IOAI_COMPETITION_TEAM_ROSTER_ENV] ?? ''));
  } catch {
    throw new Error('IOAI MCP capability Team roster is invalid JSON');
  }
  if (!Array.isArray(rawRoster) || rawRoster.length !== pool.agentLimit + 1) {
    throw new Error('IOAI MCP capability Team roster does not match the Agent pool');
  }
  const slots = new Set<string>();
  const roles = new Set<string>();
  const roster = rawRoster.map((value): CompetitionTeamRosterMember => {
    if (!isRecord(value)) throw new Error('IOAI MCP capability Team roster member is invalid');
    const memberSlotId = stableId(value.slotId, 'roster slot_id');
    const memberRoleId = stableId(value.roleId, 'roster role_id');
    if (
      !/^ioai-(?:lead|subagent-(?:exploit|explore|debug|audit|fusion)(?:-(?:[2-9]|[1-9][0-9]+))?)$/u.test(memberRoleId)
    ) {
      throw new Error('IOAI MCP capability Team roster role is invalid');
    }
    const strategyLane = value.strategyLane === undefined ? undefined : String(value.strategyLane);
    const laneMatch = /^ioai-subagent-(exploit|explore|debug|audit|fusion)(?:-(?:[2-9]|[1-9][0-9]+))?$/u.exec(
      memberRoleId
    );
    if (
      (memberRoleId === 'ioai-lead' && strategyLane !== undefined) ||
      (memberRoleId !== 'ioai-lead' && (!laneMatch || strategyLane !== laneMatch[1])) ||
      slots.has(memberSlotId) ||
      roles.has(memberRoleId)
    ) {
      throw new Error('IOAI MCP capability Team roster identity is invalid');
    }
    slots.add(memberSlotId);
    roles.add(memberRoleId);
    return Object.freeze({
      slotId: memberSlotId,
      roleId: memberRoleId as CompetitionTeamRosterMember['roleId'],
      ...(strategyLane ? { strategyLane: strategyLane as CompetitionTeamRosterMember['strategyLane'] } : {}),
    });
  });
  if (roster.filter((member) => member.roleId === 'ioai-lead').length !== 1) {
    throw new Error('IOAI MCP capability Team roster requires exactly one Lead');
  }
  const caller = roster.find((member) => member.slotId === slotId);
  if (!caller || caller.roleId !== callerRoleId) {
    throw new Error('IOAI MCP capability Team roster does not contain the caller');
  }
  return Object.freeze({
    identityBinding: 'team-slot',
    teamId,
    slotId,
    agentLimit: pool.agentLimit,
    reasoningConcurrency: pool.reasoningConcurrency,
    roster: Object.freeze(roster),
  });
}

function stableId(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new Error(`IOAI MCP capability ${field} is invalid`);
  }
  return normalized;
}

export async function authorizeCompetitionToolCall(
  input: CompetitionToolInput,
  capability?: CompetitionToolCapability
): Promise<string | undefined> {
  if (!capability) return undefined;
  if (capability.schema !== IOAI_COMPETITION_CAPABILITY_SCHEMA) {
    return 'caller capability schema is invalid';
  }
  if (!capability.allowedActions.includes(input.action)) {
    return `role ${capability.roleId} cannot call action ${input.action}`;
  }
  if (input.action !== 'system_status' || input.project_root !== undefined) {
    const requestedRoot = String(input.project_root ?? '').trim();
    if (!requestedRoot || path.resolve(requestedRoot) !== path.resolve(capability.projectRoot)) {
      return 'caller capability is bound to a different project_root';
    }
  }
  if (input.role_id !== undefined && input.role_id !== capability.roleId) {
    return 'role_id does not match the caller capability';
  }
  if (capability.identityBinding === 'team-slot') {
    if (input.team_id !== undefined && input.team_id !== capability.teamId) {
      return 'team_id does not match the caller capability';
    }
    if (input.slot_id !== undefined && input.slot_id !== capability.slotId) {
      return 'slot_id does not match the caller capability';
    }
  }
  return undefined;
}

type CoreRuntimeResolverOptions = Readonly<{
  env?: Readonly<Record<string, string | undefined>>;
  fetchImpl?: typeof fetch;
}>;

type CoreRuntimeAccess = Readonly<{
  baseUrl: string;
  conversationId: string;
  headers: Record<string, string>;
}>;

const CORE_RUNTIME_ENV_KEYS = [
  'AIONUI_BASE_URL',
  'AIONUI_USER_ID',
  'AIONUI_CONVERSATION_ID',
  'AIONUI_RUNTIME_TOKEN',
] as const;

export async function resolveCompetitionRuntimeCapability(
  capability: CompetitionToolCapability | undefined,
  options: CoreRuntimeResolverOptions = {}
): Promise<CompetitionToolCapability | undefined> {
  if (capability) return capability;
  const env = options.env ?? process.env;
  const access = coreRuntimeAccess(env, false);
  if (!access) return undefined;
  const fetchImpl = options.fetchImpl ?? fetch;
  const context = await readCoreRuntimeData(
    fetchImpl,
    `${access.baseUrl}/api/runtime/team-tools/context`,
    access.headers,
    'Team context'
  );
  if (context.in_team !== true) return undefined;
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
  if (stableId(extra.team_id, 'team_id') !== teamId || stableId(extra.team_slot_id, 'slot_id') !== slotId) {
    throw new Error('Core conversation capability snapshot does not match the Team context');
  }
  const roleId = stableId(extra.ioai_team_role_id, 'role_id');
  const competition = getIoaiCompetitionConversationExtra(extra);
  if (!competition) throw new Error('Core conversation is missing the IOAI competition identity');
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
        return readCompetitionToolCapability(capabilityEnv);
      })
    )
  ).filter((item): item is CompetitionToolCapability => Boolean(item));
  if (resolved.length !== 1) throw new Error('Core conversation role MCP capability is ambiguous');
  const runtimeCapability = resolved[0];
  if (
    runtimeCapability.identityBinding !== 'team-slot' ||
    runtimeCapability.teamId !== teamId ||
    runtimeCapability.slotId !== slotId ||
    runtimeCapability.roleId !== roleId ||
    path.resolve(runtimeCapability.projectRoot) !== path.resolve(competition.projectRoot)
  ) {
    throw new Error('Core conversation role MCP capability does not match the Team context');
  }
  return runtimeCapability;
}

export async function resolveCompetitionActiveTeamTurn(
  capability: CompetitionToolCapability | undefined,
  options: CoreRuntimeResolverOptions = {}
): Promise<IoaiCompetitionActiveTeamTurn> {
  if (!capability || capability.roleId === 'ioai-lead') {
    throw new Error('active Team turn resolution requires a Subagent capability');
  }
  const env = options.env ?? process.env;
  const fetchImpl = options.fetchImpl ?? fetch;
  const suppliedRuntimeIdentity = CORE_RUNTIME_ENV_KEYS.filter((key) => env[key] !== undefined);
  const directBaseUrl =
    capability.identityBinding === 'team-slot' && suppliedRuntimeIdentity.length !== CORE_RUNTIME_ENV_KEYS.length
      ? (env.AIONUI_BASE_URL ??
        (suppliedRuntimeIdentity.length === 0 ? env[IOAI_COMPETITION_CORE_BASE_URL_ENV] : undefined))
      : undefined;
  if (directBaseUrl) {
    return readActiveTeamTurnFromRunState(
      fetchImpl,
      localCoreBaseUrl(directBaseUrl),
      capability.teamId,
      capability.slotId,
      {}
    );
  }

  const access = coreRuntimeAccess(env, true)!;
  const context = await readCoreRuntimeData(
    fetchImpl,
    `${access.baseUrl}/api/runtime/team-tools/context`,
    access.headers,
    'Team context'
  );
  if (context.in_team !== true) throw new Error('Core runtime conversation is not in a Team');
  const teamId = stableId(context.team_id, 'team_id');
  const slotId = stableId(context.slot_id, 'slot_id');
  if (capability.identityBinding === 'team-slot' && (teamId !== capability.teamId || slotId !== capability.slotId)) {
    throw new Error('Core runtime Team context does not match the MCP capability');
  }

  return readActiveTeamTurnFromRunState(fetchImpl, access.baseUrl, teamId, slotId, access.headers);
}

async function readActiveTeamTurnFromRunState(
  fetchImpl: typeof fetch,
  baseUrl: string,
  teamId: string,
  slotId: string,
  headers: Record<string, string>
): Promise<IoaiCompetitionActiveTeamTurn> {
  const runState = await readCoreRuntimeData(
    fetchImpl,
    `${baseUrl}/api/teams/${encodeURIComponent(teamId)}/run-state`,
    headers,
    'Team run state'
  );
  const slotWork = Array.isArray(runState.slot_work)
    ? runState.slot_work.map((item) => (isRecord(item) ? item : {})).find((item) => item.slot_id === slotId)
    : undefined;
  if (!slotWork) throw new Error('Core Team run state does not contain the caller slot');
  if (slotWork.state !== 'running') throw new Error('Core Team caller slot is not running');
  return {
    schema: IOAI_COMPETITION_ACTIVE_TEAM_TURN_SCHEMA,
    team_id: teamId,
    slot_id: slotId,
    team_run_id: stableId(slotWork.team_run_id, 'team_run_id'),
    turn_id: stableId(slotWork.active_turn_id, 'turn_id'),
  };
}

function coreRuntimeAccess(
  env: Readonly<Record<string, string | undefined>>,
  required: boolean
): CoreRuntimeAccess | undefined {
  const supplied = CORE_RUNTIME_ENV_KEYS.filter((key) => env[key] !== undefined);
  if (!supplied.length && !required) return undefined;
  if (supplied.length !== CORE_RUNTIME_ENV_KEYS.length) {
    throw new Error('Core runtime identity environment is incomplete');
  }
  return {
    baseUrl: localCoreBaseUrl(env.AIONUI_BASE_URL),
    conversationId: requiredRuntimeEnv(env.AIONUI_CONVERSATION_ID, 'AIONUI_CONVERSATION_ID'),
    headers: {
      'x-aionui-user-id': requiredRuntimeEnv(env.AIONUI_USER_ID, 'AIONUI_USER_ID'),
      'x-aionui-conversation-id': requiredRuntimeEnv(env.AIONUI_CONVERSATION_ID, 'AIONUI_CONVERSATION_ID'),
      'x-aionui-runtime-token': requiredRuntimeEnv(env.AIONUI_RUNTIME_TOKEN, 'AIONUI_RUNTIME_TOKEN'),
    },
  };
}

function localCoreBaseUrl(value: unknown): string {
  const raw = String(value ?? '').trim();
  if (!raw) throw new Error('AIONUI_BASE_URL is required for active Team turn resolution');
  const url = new URL(raw);
  if (url.protocol !== 'http:' || !['127.0.0.1', 'localhost', '::1', '[::1]'].includes(url.hostname)) {
    throw new Error('active Team turn resolution must target the local Core');
  }
  return url.toString().replace(/\/$/u, '');
}

function requiredRuntimeEnv(value: unknown, field: string): string {
  const normalized = String(value ?? '').trim();
  if (!normalized) throw new Error(`${field} is required for active Team turn resolution`);
  return normalized;
}

async function readCoreRuntimeData(
  fetchImpl: typeof fetch,
  url: string,
  headers: Record<string, string>,
  label: string
): Promise<Record<string, unknown>> {
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
}
