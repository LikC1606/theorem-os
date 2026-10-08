/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import {
  BUILTIN_RESEARCH_TEAM_NAME,
  BUILTIN_RESEARCH_EVIDENCE_NAME,
  BUILTIN_IOAI_COMPETITION_NAME,
  BUILTIN_SCIENCE_ARTIFACT_NAME,
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
  RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA,
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV,
} from "../../config/builtinMcpConstants";
import type { ISessionMcpServer } from "../../config/storage";
import type { ResearchTeamProfile, ResearchTeamRoleContract } from "./researchTeamContracts";
import { createTeamAgentId } from "./teamAgentIds";
import { TEAM_WAIT_LEVELS, TEAM_WAIT_LEVEL_SECONDS, type TeamWaitLevel } from "./teamWaitPolicy";

export const RESEARCH_TEAM_MCP_TOOL = 'research_team' as const;
export const RESEARCH_TEAM_MCP_ACTIONS = [
  'describe',
  'dispatch',
  'status',
  'deliver',
  'share',
  'read_feedback',
  'integrate',
  'read_artifact',
] as const;
export type ResearchTeamMcpAction = (typeof RESEARCH_TEAM_MCP_ACTIONS)[number];
export { TEAM_WAIT_LEVELS, TEAM_WAIT_LEVEL_SECONDS };
export type { TeamWaitLevel };

export const createResearchTeamDeferredToolRoutingPrompt = (): string =>
  [
    'Codex deferred MCP routing:',
    '- Skill loading and MCP tool routing are independent checks. A missing or failed Skill does not prove that an MCP tool is absent, and a hidden MCP tool does not prove that its supporting Skill failed to load.',
    '- MCP tools in this Team are runtime-namespaced and may be omitted from the directly displayed tool catalog. Absence there does not mean that a logical tool is unavailable.',
    '- Before using or declaring a required MCP tool unavailable, resolve and invoke it in the same exec JavaScript cell: filter ALL_TOOLS for the unique entry whose name ends with `__<logical_tool_name>`, or, when the runtime hashes the tool name, for the unique entry whose description identifies that logical tool. Then call `await tools[match.name](arguments)`. Never assume a literal `tools.research_team`, `tools.project_workspace`, or `tools.science_artifact` handle.',
    '- Example for the startup gate: find exactly one ALL_TOOLS entry ending in `__research_team`; if the runtime name is hashed, use the unique description beginning with the Research Team tool description instead. Call `await tools[match.name]({action:"describe"})` in that same exec cell. Apply the same pattern to the other required logical tools.',
    '- If all required Team tools are absent on the first catalog snapshot, treat this as the bounded MCP startup race: wait briefly and repeat the resolution once. Do not conclude that the project is unsupported from that first empty snapshot. If the second check is still empty, record a retryable runtime fault, leave the loop goal active, and end the current turn without declaring the research complete; the next continuation will retry.',
    '- Do not use an exact-interface enumeration, the directly displayed catalog, or a Skill warning as a substitute for the ALL_TOOLS suffix resolution above. Complete this gate once, then continue instead of repeating equivalent preflights.',
    '- Do not inspect Skill folders, project files, Git state, or shell command availability to infer whether an MCP tool exists.',
    '- Report a Team runtime fault only when the ALL_TOOLS match count is not exactly one or the resolved call returns a real unavailable or handshake error. Include the logical tool name and match count or returned error; never replace it with a generic Agent or manual Git workflow.',
    '- Waiting is Lead-only: research_team(action="status") may use wait_level="1m", "5m", or "10m" for one bounded observation window. Omit wait_level for an immediate snapshot. Workers do not poll; Core wakes the Lead on delivery or terminal failure.',
  ].join('\n');

export type ResearchTeamRuntimeRosterMember = Readonly<{
  slotId: string;
  roleId: string;
  roleKind: ResearchTeamRoleContract['kind'];
  laneId?: string;
  displayName: string;
}>;

export type ResearchTeamRuntimeIdentity = Readonly<{
  teamId: string;
  slotId: string;
  roster: readonly ResearchTeamRuntimeRosterMember[];
}>;

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
  RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV,
  RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV,
  RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV,
] as const;

export const getResearchTeamRoleMcpActions = (
  role: ResearchTeamRoleContract,
  profileId?: string
): readonly ResearchTeamMcpAction[] => {
  const actions: readonly ResearchTeamMcpAction[] =
    role.kind === 'lead'
      ? Object.freeze(['describe', 'dispatch', 'status', 'integrate'] as const)
      : profileId === 'mathematics-research-team'
        ? Object.freeze(['deliver'] as const)
        : Object.freeze(['describe', 'deliver'] as const);
  const canReadMathArtifacts =
    profileId === 'mathematics-research-team' &&
    role.allowedTools.some(
      (tool) => tool.toolName === 'research_team' && tool.actions !== '*' && tool.actions.includes('read_artifact')
    );
  const canShareMathProgress =
    profileId === 'mathematics-research-team' &&
    role.kind === 'worker' &&
    role.allowedTools.some(
      (tool) => tool.toolName === 'research_team' && tool.actions !== '*' && tool.actions.includes('share')
    );
  return Object.freeze([
    ...actions,
    ...(canReadMathArtifacts ? ['read_artifact' as const] : []),
    ...(canShareMathProgress ? ['share' as const] : []),
    ...(canShareMathProgress &&
    role.allowedTools.some(
      (tool) => tool.toolName === 'research_team' && tool.actions !== '*' && tool.actions.includes('read_feedback')
    )
      ? ['read_feedback' as const]
      : []),
  ]);
};

/** Creates a fail-closed role snapshot before Core assigns Team and slot ids. */
export function prepareResearchTeamRoleMcpServers(
  servers: readonly ISessionMcpServer[],
  profile: ResearchTeamProfile,
  role: ResearchTeamRoleContract,
  projectRoot: string
): ISessionMcpServer[] {
  return projectRoleMcpServers(servers, profile, role, projectRoot);
}

/** Adds the exact Core Team identity after Team creation. */
export function scopeResearchTeamRoleMcpServers(
  servers: readonly ISessionMcpServer[],
  profile: ResearchTeamProfile,
  role: ResearchTeamRoleContract,
  projectRoot: string,
  identity: ResearchTeamRuntimeIdentity
): ISessionMcpServer[] {
  const roster = identity.roster.map((member) =>
    Object.freeze({
      slotId: stableId(member.slotId, 'roster.slotId'),
      roleId: stableId(member.roleId, 'roster.roleId'),
      roleKind: member.roleKind,
      ...(member.laneId ? { laneId: stableId(member.laneId, 'roster.laneId') } : {}),
      displayName: requiredText(member.displayName, 'roster.displayName'),
    })
  );
  if (
    roster.length !== profile.roles.length ||
    new Set(roster.map((member) => member.slotId)).size !== roster.length ||
    new Set(roster.map((member) => member.roleId)).size !== roster.length
  ) {
    throw new TypeError('Research Team runtime roster does not match its Profile');
  }
  const caller = roster.find((member) => member.slotId === identity.slotId);
  if (!caller || caller.roleId !== role.id || caller.roleKind !== role.kind) {
    throw new TypeError('Research Team runtime identity does not match the role');
  }
  return projectRoleMcpServers(servers, profile, role, projectRoot, {
    teamId: stableId(identity.teamId, 'teamId'),
    slotId: stableId(identity.slotId, 'slotId'),
    roster: Object.freeze(roster),
  });
}

function projectRoleMcpServers(
  servers: readonly ISessionMcpServer[],
  profile: ResearchTeamProfile,
  role: ResearchTeamRoleContract,
  projectRoot: string,
  identity?: ResearchTeamRuntimeIdentity
): ISessionMcpServer[] {
  if (!profile.roles.some((candidate) => candidate.id === role.id)) {
    throw new TypeError('Research Team role is not part of the selected Profile');
  }
  const actions = getResearchTeamRoleMcpActions(role, profile.id);
  let orchestrationServerCount = 0;
  const projected = servers.map((server) => {
    // Keep the historical Challenge name valid for existing sessions while
    // allowing new Teams to use the domain-neutral Research Team source.
    const isOrchestrationServer =
      server.name === BUILTIN_IOAI_COMPETITION_NAME || server.name === BUILTIN_RESEARCH_TEAM_NAME;
    const isScienceArtifactServer = server.name === BUILTIN_SCIENCE_ARTIFACT_NAME;
    const isResearchEvidenceServer = server.name === BUILTIN_RESEARCH_EVIDENCE_NAME;
    if (!isOrchestrationServer && !isScienceArtifactServer && !isResearchEvidenceServer) return server;
    if (isOrchestrationServer) orchestrationServerCount += 1;
    if (server.transport.type !== 'stdio') {
      throw new TypeError('Research Team built-in MCPs require a role-scoped stdio transport');
    }
    const env = { ...server.transport.env };
    for (const key of CAPABILITY_ENV_KEYS) delete env[key];
    const sharedIdentity = {
      [RESEARCH_TEAM_CAPABILITY_PROFILE_ENV]: profile.id,
      [RESEARCH_TEAM_CAPABILITY_WORKFLOW_ENV]: profile.workflowId,
      [RESEARCH_TEAM_CAPABILITY_ROLE_ENV]: role.id,
      [RESEARCH_TEAM_CAPABILITY_ROLE_KIND_ENV]: role.kind,
      [RESEARCH_TEAM_CAPABILITY_PROJECT_ROOT_ENV]: requiredText(projectRoot, 'projectRoot'),
    };
    if (isScienceArtifactServer || isResearchEvidenceServer) {
      // Mathematics Workers are always scoped. Adapter-specific mathematics
      // Leads can also narrow the official Lead surface by adding explicit
      // deny rules (for example, a headless evaluator that needs
      // project_workspace but forbids science_artifact publication).
      const enforceRolePolicy =
        profile.id === 'mathematics-research-team' && (role.kind === 'worker' || role.deniedTools.length > 0);
      return {
        ...server,
        transport: {
          ...server.transport,
          env: {
            ...env,
            ...(enforceRolePolicy
              ? {
                  ...sharedIdentity,
                  [RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV]: RESEARCH_TEAM_CAPABILITY_SCHEMA,
                  [RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV]: JSON.stringify(actions),
                  [RESEARCH_TEAM_TOOL_POLICY_SCHEMA_ENV]: RESEARCH_TEAM_TOOL_POLICY_SCHEMA,
                  [RESEARCH_TEAM_TOOL_POLICY_ALLOWED_ENV]: JSON.stringify(role.allowedTools),
                  [RESEARCH_TEAM_TOOL_POLICY_DENIED_ENV]: JSON.stringify(role.deniedTools),
                  ...(role.allowedTools.some((tool) => tool.toolName === 'math_research')
                    ? {
                        [RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV]: RESEARCH_TEAM_CAPABILITY_SCHEMA,
                        [RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV]: JSON.stringify(actions),
                      }
                    : {}),
                }
              : {}),
          },
        },
      } satisfies ISessionMcpServer;
    }
    return {
      ...server,
      transport: {
        ...server.transport,
        env: {
          ...env,
          [RESEARCH_TEAM_CAPABILITY_SCHEMA_ENV]: RESEARCH_TEAM_CAPABILITY_SCHEMA,
          ...sharedIdentity,
          [RESEARCH_TEAM_CAPABILITY_ACTIONS_ENV]: JSON.stringify(actions),
          ...(identity
            ? {
                [RESEARCH_TEAM_CAPABILITY_TEAM_ID_ENV]: identity.teamId,
                [RESEARCH_TEAM_CAPABILITY_SLOT_ID_ENV]: identity.slotId,
                [RESEARCH_TEAM_AGENT_LIMIT_ENV]: String(profile.pool.agentLimit),
                [RESEARCH_TEAM_REASONING_CONCURRENCY_ENV]: String(profile.pool.reasoningConcurrency),
                [RESEARCH_TEAM_ROSTER_ENV]: JSON.stringify(identity.roster),
              }
            : {}),
        },
      },
    } satisfies ISessionMcpServer;
  });
  if (orchestrationServerCount !== 1) {
    throw new TypeError('Research Team role requires exactly one orchestration MCP server');
  }
  return projected;
}

export function createResearchTeamRuntimeRosterPrompt(input: {
  profile: ResearchTeamProfile;
  teamId: string;
  members: readonly ResearchTeamRuntimeRosterMember[];
  headlessMathematics?: boolean;
}): string {
  const teamId = stableId(input.teamId, 'teamId');
  const members = input.members.map(
    (member, index) =>
      `- agent_id=${createTeamAgentId(index)} role_id=${stableId(member.roleId, 'roleId')} role_kind=${member.roleKind} display_name=${JSON.stringify(requiredText(member.displayName, 'displayName'))}${member.laneId ? ` lane_id=${stableId(member.laneId, 'laneId')}` : ''}`
  );
  if (input.headlessMathematics && input.profile.id === 'mathematics-research-team') {
    // Derived from the roster: a second proof owner shifts the Lean slots.
    const leanIds = input.members.flatMap((member, index) =>
      member.laneId === 'lean-engineering' ? [createTeamAgentId(index)] : []
    );
    const leanText =
      leanIds.length > 1
        ? `${leanIds[0]} is the primary Lean Engineer and ${leanIds.slice(1).join(', ')} the second proof owner`
        : `${leanIds[0] ?? 'A003'} is the Lean Engineer`;
    return [
      'Core-authenticated Research Team roster:',
      ...members,
      `Concurrency: ${input.profile.pool.reasoningConcurrency}. Use agent_id in target_slot_id; Core resolves and authorizes the slot.`,
      `For proof-mainline mathematics, ${leanText}. Never copy opaque status slot_id values into dispatch; use the roster agent_id alias.`,
    ].join('\n');
  }
  return [
    'Core-authenticated Research Team roster:',
    `profile_id: ${input.profile.id}`,
    `workflow_id: ${input.profile.workflowId}`,
    `team_id: ${teamId}`,
    ...members,
    '',
    '- agent_id is the real, short, session-local routing identifier accepted by the MCP tools; it is not a display placeholder. Even though the compatibility fields are named target_slot_id and target_slot_ids, pass agent_id (for example A002). The server resolves it to the canonical Core slot before authorization.',
    '- Canonical slot ids are intentionally omitted from this routing roster. They remain server-owned audit identities for Git, runtime attribution, and delivery evidence; never guess or memorize them.',
    `- The Lead dispatches one wave of at most ${input.profile.pool.reasoningConcurrency} independent assignments in one research_team call, then ends its turn while Workers run. Idle slots may receive a later wave only after a real delivery.`,
    '- Roster membership means available, not summoned. Call a Worker dispatched or summoned only when that dispatch item is accepted. Report the receipt accepted_count and the exact accepted agent_id values; when a batch is partial or deferred, state the smaller real count and never imply the requested count was started.',
    '- accepted_count=0 means no Worker started, even if the requested assignments were already named in the conversation. When blocker.code=lead_checkpoint_required, checkpoint the verified explicit Lead changes through project_workspace, rebuild every assignment from the returned full commit, and retry the wave.',
    '- Worker delivery is event-driven through research_team(action="deliver"); do not poll each Worker or reread unchanged project state. If Core sends a terminal reconciliation message, that Worker is no longer active: inspect the named turn and explicitly retry, reassign, or continue. Never wait for a delivery that was not accepted.',
    '- If a short observation is genuinely useful, the Lead may call research_team(action="status", wait_level="1m"|"5m"|"10m") once. This is bounded monitoring, not a completion loop; never make Workers wait or poll.',
    '- Never call Codex native spawn_agent, wait, wait_agent, or yield_control. DeepScientist Workers are Core-managed ACP conversations, not Codex child threads; after dispatch or one status snapshot, end the current assistant turn so Core can process deliveries.',
    '- Every Worker terminal turn produces a receipt to the Lead, including completed turns that already delivered successfully. Treat completed_with_delivery as an informational acknowledgement and completed_without_delivery/failed/cancelled as a recovery decision; never assume that a silent or waiting Worker will resume by itself.',
    '- Mathematics Workers send the compact lane result and omit assignmentBinding; the runtime reconstructs the exact binding from the durable accepted assignment. Never restate runtime-owned binding coordinates. Kernel certification completes FORMALIZE; Workers never run a separate LOCAL_GATE or OFFICIAL_GATE wave.',
  ].join('\n');
}

export { createTeamAgentId as createTeamAgentDisplayId } from "./teamAgentIds";

function stableId(value: unknown, field: string): string {
  const normalized = requiredText(value, field);
  if (!/^[A-Za-z0-9][A-Za-z0-9._:-]{0,127}$/u.test(normalized)) {
    throw new TypeError(`Research Team ${field} is invalid`);
  }
  return normalized;
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) throw new TypeError(`Research Team ${field} is required`);
  return value.trim();
}
