/**
 * @license
 * Copyright 2026 DeepScientist contributors
 * SPDX-License-Identifier: Apache-2.0
 */

import type { ICreateTeamParams } from "../../adapter/teamMapper";
import type { Assistant, CreateAssistantRequest } from "../agent/assistantTypes";
import type { IMcpServer, ISessionMcpServer, TeamInitialMessage } from "../../config/storage";
import type { ITeamRunAck, TTeam, TeamAgent } from "./teamTypes";
import type { ResearchTeamProfile, ResearchTeamRoleContract } from "./researchTeamContracts";
import { PROJECT_WORKSPACE_ENV_KEYS } from "../../chat/projectWorkspace";
import {
  createResearchTeamRuntimeRosterPrompt,
  scopeResearchTeamRoleMcpServers,
  type ResearchTeamRuntimeRosterMember,
} from "./researchTeamMcp";

type UpdateConversationParams = {
  id: string;
  updates: {
    name?: string;
    extra?: Record<string, unknown>;
  };
  merge_extra?: boolean;
};

export type ResearchTeamProvisioningDeps = {
  updateConversation: (params: UpdateConversationParams) => Promise<unknown>;
  listAssistants: () => Promise<Assistant[]>;
  createAssistant: (params: CreateAssistantRequest) => Promise<Pick<Assistant, 'id'>>;
  writeAssistantRule: (params: { assistant_id: string; content: string }) => Promise<unknown>;
  removeAssistant: (params: { id: string }) => Promise<unknown>;
  createMcpServer: (
    params: Pick<IMcpServer, 'name' | 'description' | 'transport' | 'original_json' | 'builtin'>
  ) => Promise<Pick<IMcpServer, 'id' | 'name' | 'enabled'>>;
  toggleMcpServer: (params: { id: string }) => Promise<Pick<IMcpServer, 'id' | 'name' | 'enabled'>>;
  updateMcpServer: (params: {
    id: string;
    data: Partial<Pick<IMcpServer, 'name' | 'description' | 'transport' | 'original_json' | 'builtin'>>;
  }) => Promise<unknown>;
  removeMcpServer: (params: { id: string }) => Promise<unknown>;
  createTeam: (params: ICreateTeamParams) => Promise<TTeam>;
  removeTeam: (params: { id: string }) => Promise<unknown>;
  setSessionMode: (params: { team_id: string; session_mode: string }) => Promise<unknown>;
  ensureSession: (params: { team_id: string }) => Promise<unknown>;
  /** Optional Core runtime wake-up for dormant Team slots before first Lead turn. */
  ensureAgentRuntime?: (params: { team_id: string; slot_id: string }) => Promise<unknown>;
  waitForMcpToolsReady: (params: {
    teamId: string;
    slotIds: readonly string[];
    timeoutMs: number;
    onSlotReady?: (slotId: string) => void;
    onSlotFailed?: (slotId: string, error: unknown) => void;
    /**
     * Registers a callback that the caller invokes after Core's ensure-session
     * endpoint has completed successfully. Some Core versions do not emit
     * per-slot MCP events, but that response is still the startup barrier.
     */
    registerSessionReady?: (notify: () => void) => void;
  }) => Promise<void>;
  sendMessage: (params: { team_id: string; input: string; files?: string[] }) => Promise<ITeamRunAck>;
};

const TEAM_MCP_READY_BASE_TIMEOUT_MS = 30_000;
const TEAM_MCP_READY_PER_AGENT_TIMEOUT_MS = 10_000;
const TEAM_MCP_READY_MAX_TIMEOUT_MS = 10 * 60_000;
const RESEARCH_TEAM_MCP_SERVER_NAME_PREFIX = 'ds-team';
const RESEARCH_TEAM_PREPARATION_CONCURRENCY = 4;

export type ResearchTeamRoleConversationParams = {
  name?: string;
  extra: Record<string, unknown> & {
    preset_context?: string;
    preset_rules?: string;
    selected_session_mcp_servers?: ISessionMcpServer[];
    session_mcp_servers?: ISessionMcpServer[];
    headless_proof_search?: boolean;
    headless_proof_mainline?: boolean;
  };
};

export type ProvisionResearchTeamInput = {
  profile: ResearchTeamProfile;
  projectRoot: string;
  userId: string;
  teamName: string;
  backend: string;
  model?: string;
  leadModel?: string;
  workerModel?: string;
  leadThoughtLevel?: string;
  workerThoughtLevel?: string;
  sessionMode: string;
  initialMessage: string;
  files?: string[];
  /** Durable mode metadata shared by every role conversation. */
  modeConversationExtra?: Readonly<Record<string, unknown>>;
  /** Leader-only runtime state. Keep loop control out of Worker conversations. */
  leaderConversationExtra?: Readonly<Record<string, unknown>>;
  requiredMcpServers: (role: ResearchTeamRoleContract) => readonly string[];
  requiredSkillIds: (role: ResearchTeamRoleContract) => readonly string[];
  disabledBuiltinSkillIds?: readonly string[];
  buildConversationParams: (
    role: ResearchTeamRoleContract,
    initialPromptSha256: string
  ) => ResearchTeamRoleConversationParams;
  onRuntimeReady?: (
    runtime: Readonly<{
      team: TTeam;
      agents: readonly TeamAgent[];
      roster: readonly ResearchTeamRuntimeRosterMember[];
    }>
  ) => Promise<void>;
  onLaunchProgress?: (progress: ResearchTeamLaunchProgress) => void;
};

export type ResearchTeamLaunchPhase =
  | 'preparing'
  | 'role_prepared'
  | 'team_created'
  | 'slot_ready'
  | 'ready'
  | 'degraded';

export type ResearchTeamLaunchProgress = Readonly<{
  phase: ResearchTeamLaunchPhase;
  total: number;
  roleId?: string;
  roleIndex?: number;
  roleKind?: ResearchTeamRoleContract['kind'];
  displayName?: string;
  slotId?: string;
  error?: string;
}>;

export type ResearchTeamRuntimeMcpResource = Readonly<{
  id: string;
  name: string;
  sourceName: string;
}>;

export type ResearchTeamRuntimeResources = Readonly<{
  assistantIds: readonly string[];
  mcpServersByRole: readonly (readonly ResearchTeamRuntimeMcpResource[])[];
}>;

export type ProvisionResearchTeamResult = {
  team: TTeam;
  leaderConversationId: string;
  run: ITeamRunAck;
  runtimeResources: ResearchTeamRuntimeResources;
};

type PreparedRoleRuntime = Readonly<{
  role: ResearchTeamRoleContract;
  conversationParams: ResearchTeamRoleConversationParams;
  assistantId: string;
  mcpServers: readonly ResearchTeamRuntimeMcpResource[];
  sourceMcpServers: readonly ISessionMcpServer[];
}>;

const DEFAULT_TEAM_NAME = 'Research Team';
const MAX_TEAM_NAME_LENGTH = 256;
const DEFAULT_DISABLED_BUILTIN_SKILLS = Object.freeze(['aionui-config', 'cron', 'officecli', 'skill-creator']);

export async function provisionResearchTeam(
  input: ProvisionResearchTeamInput,
  deps: ResearchTeamProvisioningDeps
): Promise<ProvisionResearchTeamResult> {
  assertProfile(input.profile);
  if (input.profile.id !== 'mathematics-research-team' || input.modeConversationExtra?.headless_proof_search !== true) {
    throw new Error('RESEARCH_TEAM_HEADLESS_MATHEMATICS_REQUIRED');
  }
  if (input.backend !== 'codex') {
    throw new Error('RESEARCH_TEAM_BACKEND_UNSUPPORTED');
  }
  if (!input.sessionMode.trim()) throw new Error('RESEARCH_TEAM_SESSION_MODE_REQUIRED');
  const initialPromptSha256 = await sha256(input.initialMessage);
  const teamInitialMessage: TeamInitialMessage = {
    schema: 'deepscientist.team_initial_message.v1',
    input: input.initialMessage.trim(),
    files: [...(input.files ?? [])],
    createdAt: Date.now(),
  };
  const roleModels = input.profile.roles.map((role) => resolveRoleRuntime(input, role).model ?? 'default');
  const assistant = resolveResearchTeamAssistant(await deps.listAssistants(), input.backend);
  const runtimeToken = createRuntimeToken();
  emitLaunchProgress(input, { phase: 'preparing', total: input.profile.roles.length });
  // Role runtimes have independent deterministic ids. Prepare a bounded
  // number concurrently, but settle every started role before rollback so a
  // late failure cannot leave an assistant or MCP row behind.
  const preparedResult = await prepareRoleRuntimesConcurrently(
    input,
    deps,
    runtimeToken,
    assistant.agent_id!,
    initialPromptSha256
  );
  const prepared = preparedResult.results
    .filter((item): item is { index: number; runtime: PreparedRoleRuntime } => item.runtime !== undefined)
    .toSorted((left, right) => left.index - right.index)
    .map((item) => item.runtime);
  if (preparedResult.error || prepared.length !== input.profile.roles.length) {
    await cleanupProvisionedResources(deps, prepared);
    if (preparedResult.error) throw preparedResult.error;
    throw new Error('RESEARCH_TEAM_ROLE_RUNTIME_PREPARATION_INVALID');
  }

  let team: TTeam;
  let provisioningActive = true;
  try {
    team = await deps.createTeam(
      createCoreTeamParams(
        input,
        roleModels,
        prepared.map((item) => item.assistantId)
      )
    );
  } catch (error) {
    await cleanupProvisionedResources(deps, prepared);
    throw error;
  }
  if (!team.id) {
    await cleanupProvisionedResources(deps, prepared);
    throw new Error('RESEARCH_TEAM_CREATE_INVALID');
  }
  if (team.coordination_protocol?.kind !== 'managed_mcp' || team.coordination_protocol.logicalTool !== 'research_team') {
    await cleanupProvisionedResources(deps, prepared, team.id);
    throw new Error('RESEARCH_TEAM_COORDINATION_PROTOCOL_NOT_OBSERVED');
  }
  const agents = findProvisionedAgents(team, input.profile, prepared);
  if (!agents) {
    await cleanupProvisionedResources(deps, prepared, team.id);
    throw new Error('RESEARCH_TEAM_ASSISTANT_PROVISIONING_INVALID');
  }
  if (agents.some((agent, index) => agent.model !== roleModels[index])) {
    await cleanupProvisionedResources(deps, prepared, team.id);
    throw new Error('RESEARCH_TEAM_ROLE_MODEL_NOT_OBSERVED');
  }
  if (agents.some((agent) => agent.agent_type.trim().toLowerCase() !== input.backend.trim().toLowerCase())) {
    await cleanupProvisionedResources(deps, prepared, team.id);
    throw new Error('RESEARCH_TEAM_ROLE_BACKEND_NOT_OBSERVED');
  }
  emitLaunchProgress(input, { phase: 'team_created', total: agents.length });

  try {
    const roster: readonly ResearchTeamRuntimeRosterMember[] = Object.freeze(
      agents.map((agent, index) => {
        const role = input.profile.roles[index];
        return Object.freeze({
          slotId: agent.slot_id,
          roleId: role.id,
          roleKind: role.kind,
          ...(role.laneId ? { laneId: role.laneId } : {}),
          displayName: role.displayName,
        });
      })
    );
    const scopedMcpServersByRole = agents.map((agent, roleIndex) => {
      const role = input.profile.roles[roleIndex];
      return bindConversationIdentity(
        scopeResearchTeamRoleMcpServers(prepared[roleIndex].sourceMcpServers, input.profile, role, input.projectRoot, {
          teamId: team.id,
          slotId: agent.slot_id,
          roster,
        }),
        agent.conversation_id
      );
    });
    const runtimeRoster = createResearchTeamRuntimeRosterPrompt({
      profile: input.profile,
      teamId: team.id,
      members: roster,
    });
    await settleProvisioningOperations(
      agents.flatMap((agent, roleIndex) => {
        return prepared[roleIndex].mcpServers.map((server, serverIndex) =>
          deps.updateMcpServer({
            id: server.id,
            data: {
              name: server.name,
              description: `ds-team ${team.id} slot ${agent.slot_id} MCP runtime for ${server.sourceName}.`,
              transport: scopedMcpServersByRole[roleIndex][serverIndex].transport,
              original_json: '{}',
              builtin: false,
            },
          })
        );
      })
    );
    const runtimeRules = agents.map((agent, index) => {
      const role = input.profile.roles[index];
      const runtimeIdentity = createDefaultRuntimeIdentityPrompt(agent.conversation_id, team.id, agent.slot_id);
      const baseRule = createRoleRule(prepared[index].conversationParams, role);
      const roleIdentity = appendRuntimeIdentity(baseRule, runtimeIdentity);
      const rule =
        role.kind === 'worker'
          ? roleIdentity
          : appendRuntimeIdentity(roleIdentity, runtimeRoster);
      return rule;
    });
    await settleProvisioningOperations(
      agents.map((_, index) =>
        deps.writeAssistantRule({
          assistant_id: prepared[index].assistantId,
          content: runtimeRules[index],
        })
      )
    );
    await settleProvisioningOperations(
      agents.map((agent, index) => {
        const role = input.profile.roles[index];
        return deps.updateConversation({
          id: agent.conversation_id,
          updates: {
            name: role.kind === 'lead' ? input.teamName.trim() || role.displayName : role.displayName,
            extra: {
              ...input.modeConversationExtra,
              ...(role.kind === 'lead' ? input.leaderConversationExtra : {}),
              team_id: team.id,
              team_slot_id: agent.slot_id,
              team_role: agent.role,
              research_team_profile_id: input.profile.id,
              research_team_workflow_id: input.profile.workflowId,
              research_team_role_id: role.id,
              research_team_role_kind: role.kind,
              ...(role.laneId ? { research_team_lane_id: role.laneId } : {}),
              research_team_initial_prompt_sha256: initialPromptSha256,
              ...(role.kind === 'lead' ? { team_initial_message: teamInitialMessage } : {}),
              ...(resolveRoleRuntime(input, role).thoughtLevel
                ? { thought_level: resolveRoleRuntime(input, role).thoughtLevel }
                : {}),
              preset_context: runtimeRules[index],
              // Clear the legacy alias explicitly because this is a merge patch.
              preset_rules: '',
            },
          },
          merge_extra: true,
        });
      })
    );
    await input.onRuntimeReady?.({ team, agents, roster });
    // Subscribe before the initial message starts the Team session. The Lead
    // must have its MCP catalog before the first model turn, while Workers may
    // continue starting in the background.
    const leaderSlotId = agents[0].slot_id;
    let leaderMcpReady = false;
    let leaderMcpFailed = false;
    let resolveLeaderMcpReady!: () => void;
    let rejectLeaderMcpReady!: (error: unknown) => void;
    const leaderMcpToolsReady = new Promise<void>((resolve, reject) => {
      resolveLeaderMcpReady = resolve;
      rejectLeaderMcpReady = reject;
    });
    const markSlotReady = (slotId: string): void => {
      if (!provisioningActive) return;
      if (slotId === leaderSlotId && !leaderMcpReady) {
        leaderMcpReady = true;
        resolveLeaderMcpReady();
      }
      const roleIndex = agents.findIndex((agent) => agent.slot_id === slotId);
      const role = input.profile.roles[roleIndex];
      emitLaunchProgress(input, {
        phase: 'slot_ready',
        total: agents.length,
        slotId,
        ...(roleIndex >= 0 ? { roleIndex } : {}),
        ...(role ? { roleId: role.id, roleKind: role.kind, displayName: role.displayName } : {}),
      });
    };
    const markSlotFailed = (slotId: string, error: unknown): void => {
      if (!provisioningActive || slotId !== leaderSlotId || leaderMcpFailed) return;
      leaderMcpFailed = true;
      rejectLeaderMcpReady(error);
    };
    let notifySessionReady: (() => void) | undefined;
    const mcpToolsReady = deps.waitForMcpToolsReady({
      teamId: team.id,
      slotIds: agents.map((agent) => agent.slot_id),
      timeoutMs: resolveTeamMcpReadyTimeoutMs(agents.length),
      onSlotReady: markSlotReady,
      onSlotFailed: markSlotFailed,
      registerSessionReady: (notify) => {
        notifySessionReady = notify;
      },
    });
    void mcpToolsReady.then(
      () => {
        if (!provisioningActive) return;
        if (!leaderMcpReady) {
          leaderMcpReady = true;
          resolveLeaderMcpReady();
        }
        emitLaunchProgress(input, { phase: 'ready', total: agents.length });
      },
      (error: unknown) => {
        const errorText = error instanceof Error ? error.message : String(error);
        const leaderFailure = errorText.includes(leaderSlotId);
        if (!leaderMcpReady || leaderFailure || leaderMcpFailed) rejectLeaderMcpReady(error);
        console.warn('[Research Team] Background MCP readiness check did not complete:', error);
        emitLaunchProgress(input, {
          phase: 'degraded',
          total: agents.length,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    );
    await deps.setSessionMode({ team_id: team.id, session_mode: input.sessionMode });
    // Team creation only registers the slots. Start the Core sessions after
    // the final role-scoped MCP transports are bound so the readiness events
    // we are already listening for can actually be emitted.
    await deps.ensureSession({ team_id: team.id });
    if (deps.ensureAgentRuntime) {
      await settleProvisioningOperations(
        agents.slice(1).map((agent) => deps.ensureAgentRuntime!({ team_id: team.id, slot_id: agent.slot_id }))
      );
    }
    // The current Core returns from ensure-session only after the Team
    // session has attached its agent runtimes. Older clients waited for a
    // per-slot MCP event that this Core does not emit, which caused a healthy
    // Team to be rolled back after the readiness timeout. Let the dependency
    // resolve its compatibility handshake now that the authoritative request
    // has completed successfully.
    // The callback is optional so older test doubles remain valid.
    notifySessionReady?.();
    // session_ready confirms that Core created the runtime session; it does
    // not prove that the Lead has received its MCP catalog. Starting the first
    // model turn before mcp_tools_ready can make a healthy mathematics workflow
    // conclude that its required tools do not exist. Keep the bounded catalog
    // observer as the authoritative first-turn barrier.
    await leaderMcpToolsReady;
    const run = await deps.sendMessage({
      team_id: team.id,
      input: input.initialMessage.trim(),
      ...(input.files?.length ? { files: input.files } : {}),
    });
    return {
      team: { ...team, session_mode: input.sessionMode },
      leaderConversationId: agents[0].conversation_id,
      run,
      runtimeResources: {
        assistantIds: prepared.map((item) => item.assistantId),
        mcpServersByRole: prepared.map((item) => item.mcpServers),
      },
    };
  } catch (error) {
    provisioningActive = false;
    await cleanupProvisionedResources(deps, prepared, team.id);
    throw error;
  }
}

function emitLaunchProgress(input: ProvisionResearchTeamInput, progress: ResearchTeamLaunchProgress): void {
  try {
    input.onLaunchProgress?.(Object.freeze(progress));
  } catch (error) {
    console.warn('[Research Team] Launch progress observer failed:', error);
  }
}

export function resolveTeamMcpReadyTimeoutMs(agentCount: number): number {
  const normalizedAgentCount = Number.isSafeInteger(agentCount) ? Math.max(1, agentCount) : 1;
  return Math.min(
    TEAM_MCP_READY_MAX_TIMEOUT_MS,
    Math.max(TEAM_MCP_READY_BASE_TIMEOUT_MS, normalizedAgentCount * TEAM_MCP_READY_PER_AGENT_TIMEOUT_MS)
  );
}

export async function removeResearchTeamRuntimeResources(
  resources: ResearchTeamRuntimeResources,
  deps: Pick<ResearchTeamProvisioningDeps, 'removeAssistant' | 'removeMcpServer'>
): Promise<readonly string[]> {
  const assistantResults = await Promise.allSettled(resources.assistantIds.map((id) => deps.removeAssistant({ id })));
  const mcpResults = await Promise.allSettled(
    resources.mcpServersByRole.flatMap((servers) => servers.map((server) => deps.removeMcpServer({ id: server.id })))
  );
  return Object.freeze(
    [...assistantResults, ...mcpResults]
      .filter((result): result is PromiseRejectedResult => result.status === 'rejected')
      .map((result) => (result.reason instanceof Error ? result.reason.message : String(result.reason)))
  );
}

export function resolveResearchTeamAssistant(catalog: readonly Assistant[], backend: string): Assistant {
  const normalizedBackend = backend.trim().toLowerCase();
  const selectable = catalog.filter(
    (assistant) =>
      assistant.enabled !== false &&
      Boolean(assistant.agent_id) &&
      // Core's generated bare ACP assistants are the canonical runtime
      // bases even when the UI marks them team_selectable=false.
      (assistant.team_selectable !== false || assistant.id.startsWith('bare:'))
  );
  // Core's nested ACP backend is authoritative. Older clients normalized an
  // absent preset_agent_type to "codex", which otherwise makes the first bare
  // Claude/OpenCode assistant look like a Codex match.
  const exactBackendMatches = selectable.filter(
    (assistant) => assistant.agent?.acp_backend?.trim().toLowerCase() === normalizedBackend
  );
  const legacyMatches = selectable.filter(
    (assistant) =>
      !assistant.agent?.acp_backend?.trim() && assistant.preset_agent_type?.trim().toLowerCase() === normalizedBackend
  );
  const matches = exactBackendMatches.length > 0 ? exactBackendMatches : legacyMatches;
  const match = matches.find((assistant) => assistant.id.startsWith('bare:')) ?? matches[0];
  if (!match?.id || !match.agent_id) throw new Error(`RESEARCH_TEAM_ASSISTANT_NOT_FOUND:${normalizedBackend}`);
  return match;
}

function createCoreTeamParams(
  input: ProvisionResearchTeamInput,
  roleModels: readonly string[],
  assistantIds: readonly string[]
): ICreateTeamParams {
  return {
    coordination_protocol: { kind: 'managed_mcp', logicalTool: 'research_team' },
    user_id: requiredText(input.userId, 'userId'),
    name: normalizeTeamName(input.teamName),
    workspace: requiredText(input.projectRoot, 'projectRoot'),
    workspace_mode: 'shared',
    agents: input.profile.roles.map((role, index) => ({
      role: role.kind === 'lead' ? 'leader' : 'teammate',
      agent_type: input.backend,
      agent_name: role.displayName,
      conversation_type: 'acp',
      status: 'pending',
      model: roleModels[index],
      assistant_id: assistantIds[index],
    })),
  };
}

async function prepareRoleRuntimesConcurrently(
  input: ProvisionResearchTeamInput,
  deps: ResearchTeamProvisioningDeps,
  runtimeToken: string,
  assistantAgentId: string,
  initialPromptSha256: string
): Promise<{
  results: Array<{ index: number; runtime?: PreparedRoleRuntime }>;
  error?: unknown;
}> {
  const results: Array<{ index: number; runtime?: PreparedRoleRuntime }> = [];
  let nextIndex = 0;
  let preparationFailed = false;
  let firstError: unknown;
  const workerCount = Math.min(RESEARCH_TEAM_PREPARATION_CONCURRENCY, input.profile.roles.length);
  // Keep the total number of in-flight Core MCP mutations bounded even when
  // several role runtimes are prepared concurrently.
  const mcpConcurrencyPerRole = Math.max(1, Math.floor(RESEARCH_TEAM_PREPARATION_CONCURRENCY / workerCount));
  const prepareNext = async (): Promise<void> => {
    if (preparationFailed) return;
    const index = nextIndex;
    nextIndex += 1;
    if (index >= input.profile.roles.length) return;
    const role = input.profile.roles[index];
    try {
      const runtime = await prepareRoleRuntime(
        input,
        deps,
        role,
        index,
        runtimeToken,
        assistantAgentId,
        initialPromptSha256,
        mcpConcurrencyPerRole
      );
      results.push({ index, runtime });
      emitLaunchProgress(input, {
        phase: 'role_prepared',
        total: input.profile.roles.length,
        roleId: role.id,
        roleIndex: index,
        roleKind: role.kind,
        displayName: role.displayName,
      });
    } catch (error) {
      if (!preparationFailed) {
        preparationFailed = true;
        firstError = error;
      }
      return;
    }
    await prepareNext();
  };
  await Promise.all(Array.from({ length: workerCount }, () => prepareNext()));
  return { results, ...(firstError !== undefined ? { error: firstError } : {}) };
}

async function prepareRoleRuntime(
  input: ProvisionResearchTeamInput,
  deps: ResearchTeamProvisioningDeps,
  role: ResearchTeamRoleContract,
  index: number,
  runtimeToken: string,
  assistantAgentId: string,
  initialPromptSha256: string,
  mcpConcurrency: number
): Promise<PreparedRoleRuntime> {
  const conversationParams = input.buildConversationParams(role, initialPromptSha256);
  const requiredMcpServers = input.requiredMcpServers(role);
  const sourceMcpServers = roleSessionMcpServers(conversationParams, role, requiredMcpServers);
  const createdMcpServers: ResearchTeamRuntimeMcpResource[] = [];
  let assistantId = '';
  try {
    // MCP resources are independent within a role. Create and enable them in
    // parallel, while Promise.allSettled guarantees every started request has
    // settled before a partial failure is rolled back.
    const preparedMcpServers = await settleMapWithConcurrency(
      sourceMcpServers,
      mcpConcurrency,
      async (source, sourceIndex) => {
        // Keep the runtime name short enough that Codex preserves the logical
        // `__research_team` tool suffix instead of hashing the complete MCP name.
        // The source name remains available in the description and resource
        // metadata; role/source indexes are sufficient for uniqueness.
        const name = `${RESEARCH_TEAM_MCP_SERVER_NAME_PREFIX}-${runtimeToken}-${index}-${sourceIndex}`;
        const created = await deps.createMcpServer({
          name,
          description: `Role-scoped ds-team MCP runtime for ${role.id} (${source.name}).`,
          transport: source.transport,
          original_json: '{}',
          builtin: false,
        });
        if (!created?.id) throw new Error(`RESEARCH_TEAM_ROLE_MCP_CREATE_INVALID:${role.id}`);
        try {
          const enabled = created.enabled ? created : await deps.toggleMcpServer({ id: created.id });
          if (!enabled.enabled) throw new Error(`RESEARCH_TEAM_ROLE_MCP_ENABLE_INVALID:${role.id}`);
          return {
            id: created.id,
            name: enabled.name || created.name || name,
            sourceName: source.name,
          } satisfies ResearchTeamRuntimeMcpResource;
        } catch (error) {
          await deps.removeMcpServer({ id: created.id }).catch((): undefined => undefined);
          throw error;
        }
      }
    );
    const failedMcpServer = preparedMcpServers.find(
      (result): result is PromiseRejectedResult => result.status === 'rejected'
    );
    if (failedMcpServer) {
      createdMcpServers.push(
        ...preparedMcpServers
          .filter(
            (result): result is PromiseFulfilledResult<ResearchTeamRuntimeMcpResource> => result.status === 'fulfilled'
          )
          .map((result) => result.value)
      );
      throw failedMcpServer.reason;
    }
    createdMcpServers.push(
      ...preparedMcpServers.map((result) => (result as PromiseFulfilledResult<ResearchTeamRuntimeMcpResource>).value)
    );
    const roleRuntime = resolveRoleRuntime(input, role);
    const requiredSkillIds = [...input.requiredSkillIds(role)];
    assistantId = `research-runtime-${runtimeToken}-${index}`;
    const createdAssistant = await deps.createAssistant({
      id: assistantId,
      name: role.displayName,
      description: `Internal Research Team runtime for ${role.id}.`,
      agent_id: assistantAgentId,
      enabled_skills: requiredSkillIds,
      disabled_builtin_skills: [...(input.disabledBuiltinSkillIds ?? DEFAULT_DISABLED_BUILTIN_SKILLS)],
      models: roleRuntime.model ? [roleRuntime.model] : [],
      defaults: {
        model: { mode: 'fixed', value: roleRuntime.model ?? 'default' },
        permission: { mode: 'fixed', value: input.sessionMode },
        skills: { mode: 'fixed', value: requiredSkillIds },
        mcps: { mode: 'fixed', value: createdMcpServers.map((server) => server.id) },
      },
    });
    if (createdAssistant.id !== assistantId) throw new Error(`RESEARCH_TEAM_ROLE_ASSISTANT_CREATE_INVALID:${role.id}`);
    // The role rule depends on the Core-issued Team and slot identity, which
    // does not exist until createTeam returns. The final identity-bound rule
    // is written once below, before ensureSession starts any agent turn.
    return { role, conversationParams, assistantId, mcpServers: createdMcpServers, sourceMcpServers };
  } catch (error) {
    const cleanupWarnings = await removeResearchTeamRuntimeResources(
      { assistantIds: assistantId ? [assistantId] : [], mcpServersByRole: [createdMcpServers] },
      deps
    );
    if (cleanupWarnings.length) {
      console.warn('[Research Team] Role provisioning rollback was incomplete:', cleanupWarnings.join('; '));
    }
    throw error;
  }
}

async function settleMapWithConcurrency<T, R>(
  values: readonly T[],
  concurrency: number,
  mapper: (value: T, index: number) => Promise<R>
): Promise<PromiseSettledResult<R>[]> {
  const results = Array.from<PromiseSettledResult<R>>({ length: values.length });
  let nextIndex = 0;
  const worker = async (): Promise<void> => {
    while (true) {
      const index = nextIndex++;
      if (index >= values.length) return;
      try {
        results[index] = { status: 'fulfilled', value: await mapper(values[index]!, index) };
      } catch (reason) {
        results[index] = { status: 'rejected', reason };
      }
    }
  };
  await Promise.all(Array.from({ length: Math.min(Math.max(1, concurrency), values.length) }, () => worker()));
  return results;
}

async function settleProvisioningOperations<T>(operations: readonly Promise<T>[]): Promise<void> {
  const settled = await Promise.allSettled(operations);
  const failures = settled.filter((result): result is PromiseRejectedResult => result.status === 'rejected');
  if (failures.length) {
    const first = failures[0].reason;
    throw first instanceof Error ? first : new Error(String(first));
  }
}

function bindConversationIdentity(servers: readonly ISessionMcpServer[], conversationId: string): ISessionMcpServer[] {
  const stableConversationId = requiredText(conversationId, 'conversationId');
  return servers.map((server) =>
    server.transport.type === 'stdio'
      ? {
          ...server,
          transport: {
            ...server.transport,
            env: {
              ...server.transport.env,
              [PROJECT_WORKSPACE_ENV_KEYS.conversationId]: stableConversationId,
              AIONUI_CONVERSATION_ID: stableConversationId,
            },
          },
        }
      : server
  );
}

function createRoleRule(
  params: ResearchTeamRoleConversationParams,
  role: ResearchTeamRoleContract
): string {
  const base = params.extra.preset_context?.trim() || params.extra.preset_rules;
  const normalized = typeof base === 'string' ? base.trim() : '';
  const roleRule = !normalized
    ? role.prompt
    : normalized.includes(role.prompt)
      ? normalized
      : `${normalized}\n\n${role.prompt}`;
  return `${roleRule.trim()}\n\n${createSharedTeamOperatingContract(role)}`;
}

function createSharedTeamOperatingContract(role: ResearchTeamRoleContract): string {
  return [
    '# Mathematics Team Operating Contract',
    '- Use the language of the latest user request for visible progress and delivery summaries.',
    '- Coordinate only through research_team. Select ALL_TOOLS names ending with __research_team and invoke the unique match. Only if absent, search its logical description for hashed names. Missing/ambiguous: report the runtime fault and end the turn.',
    '- Code mode: call tools[entry.name](args) and return its result in the same exec cell as discovery; discovery without invocation is not progress.',
    ...(role.kind === 'worker'
      ? [
          '- Current assignment and frozen original target are authoritative; use your worktree and pinned Lean; research is read-only.',
          '- Share early with research_team(action="share", result={summary}); shares are provisional. Attach private .md/.lean by worktree-relative path. Use target_slot_id only for a related research recipient; send corrections explicitly.',
          '- Use the current Lean checkpoint diagnostic and attached feedback first. Read research_team(action="read_feedback") for missing or changed findings. Do not reread unchanged findings, poll, or cancel slow turns.',
          '- Deliver via research_team(action="deliver", result={status:"completed" or "blocked",summary,files,blockers}); blockers only if blocked, and files must exist and be relative. Host freezes bytes/identity; never invent success. Do not dispatch, integrate, or poll.',
        ]
      : [
          '- Plan from the supplied task/environment. Dispatch an exact Worker target, concrete task and optional kind, research_question and consumer_assignment_ids; the host supplies identity and verification targets.',
          '- Dispatch useful independent work within the configured concurrency, then end the turn for Core delivery events. An unaccepted dispatch is not a running Worker.',
          '- A share is provisional context from an active assignment. Call status once to reconcile progress feedback and capacity. Use its frozen evidence to dispatch an independent mathematical question to an idle Researcher while the Lean Worker continues useful base lemmas. Never replace the active proof assignment or treat shared text as completion.',
          '- Review and integrate accepted deliveries. completion_deferred closes only that assignment; it is not full-problem completion. Do not redispatch closed work.',
          '- After solving the complete problem, receive solver_ready_receipt for the integrated commit and end the turn. Do not emit a completion marker or perform further validation, checkpointing, or dispatch. The outer runner owns independent evaluation.',
        ]),
  ].join('\n');
}

function appendRuntimeIdentity(base: string, runtimeIdentity: string): string {
  const identity = requiredText(runtimeIdentity, 'runtimeIdentityPrompt');
  return base.trim() ? `${base.trim()}\n\n${identity}` : identity;
}

function createDefaultRuntimeIdentityPrompt(conversationId: string, teamId: string, slotId: string): string {
  return [
    '# Research Team Runtime Identity',
    `Current conversation id: ${requiredText(conversationId, 'conversationId')}`,
    `Core Team id: ${requiredText(teamId, 'teamId')}`,
    `Core slot id: ${requiredText(slotId, 'slotId')}`,
    'These Core-issued ids are authoritative. Never substitute a planned project, run, task, or workspace id.',
  ].join('\n');
}

function roleSessionMcpServers(
  params: ResearchTeamRoleConversationParams,
  role: ResearchTeamRoleContract,
  expectedNames: readonly string[]
): ISessionMcpServer[] {
  const servers = params.extra.selected_session_mcp_servers ?? params.extra.session_mcp_servers ?? [];
  if (!Array.isArray(servers) || servers.length !== expectedNames.length) {
    throw new Error(`RESEARCH_TEAM_ROLE_MCP_SNAPSHOT_INVALID:${role.id}`);
  }
  if (
    servers.some(
      (server, index) => !server?.id || !server.name || server.name !== expectedNames[index] || !server.transport
    )
  ) {
    throw new Error(`RESEARCH_TEAM_ROLE_MCP_SNAPSHOT_INVALID:${role.id}`);
  }
  return servers;
}

function findProvisionedAgents(
  team: TTeam,
  profile: ResearchTeamProfile,
  prepared: readonly PreparedRoleRuntime[]
): TeamAgent[] | undefined {
  const agents = profile.roles.map((role, index) =>
    team.agents.find(
      (agent) =>
        agent.assistant_id === prepared[index].assistantId &&
        agent.role === (role.kind === 'lead' ? 'leader' : 'teammate') &&
        agent.agent_name === role.displayName
    )
  );
  if (agents.some((agent) => !agent?.slot_id || !agent.conversation_id)) return undefined;
  const provisioned = agents as TeamAgent[];
  if (new Set(provisioned.map((agent) => agent.conversation_id)).size !== provisioned.length) return undefined;
  if (team.leader_agent_id && team.leader_agent_id !== provisioned[0].slot_id) return undefined;
  return provisioned;
}

function resolveRoleRuntime(input: ProvisionResearchTeamInput, role: ResearchTeamRoleContract) {
  return role.kind === 'lead'
    ? {
        model: normalizeOptionalText(input.leadModel) ?? normalizeOptionalText(input.model),
        thoughtLevel: normalizeOptionalText(input.leadThoughtLevel),
      }
    : {
        model: normalizeOptionalText(input.workerModel) ?? normalizeOptionalText(input.model),
        thoughtLevel: normalizeOptionalText(input.workerThoughtLevel),
      };
}

const normalizeOptionalText = (value: string | undefined): string | undefined => value?.trim() || undefined;

async function cleanupProvisionedResources(
  deps: ResearchTeamProvisioningDeps,
  prepared: readonly PreparedRoleRuntime[],
  teamId?: string
): Promise<void> {
  const warnings: string[] = [];
  if (teamId) {
    try {
      await deps.removeTeam({ id: teamId });
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      if (!/\b(?:404|not found|does not exist)\b/iu.test(message)) {
        warnings.push(`Team ${teamId}: ${message}`);
        // Do not delete assistants/MCP resources while Team deletion is
        // ambiguous. The Team may still be active and its runtime resources
        // must remain recoverable for a later cleanup pass.
        console.warn('[Research Team] Provisioning rollback deferred:', warnings.join('; '));
        return;
      }
    }
  }
  warnings.push(...(await removeResearchTeamRuntimeResources(
    { assistantIds: prepared.map((item) => item.assistantId), mcpServersByRole: prepared.map((item) => item.mcpServers) },
    deps
  )));
  if (warnings.length) {
    console.warn('[Research Team] Provisioning rollback was incomplete:', warnings.join('; '));
  }
}

function assertProfile(profile: ResearchTeamProfile): void {
  if (
    !Object.isFrozen(profile) ||
    !Object.isFrozen(profile.roles) ||
    profile.roles.length !== profile.pool.agentLimit + 1
  ) {
    throw new TypeError('Research Team Profile must be immutable and match its Worker pool');
  }
  if (profile.roles[0]?.id !== profile.leadRoleId || profile.roles[0]?.kind !== 'lead') {
    throw new TypeError('Research Team Profile requires the Lead as its first role');
  }
  if (profile.roles.slice(1).some((role) => role.kind !== 'worker')) {
    throw new TypeError('Research Team Profile contains an invalid Worker role');
  }
}

function normalizeTeamName(value: string): string {
  const normalized = value.trim().replace(/\s+/gu, ' ');
  if (!normalized) return DEFAULT_TEAM_NAME;
  if (normalized.length <= MAX_TEAM_NAME_LENGTH) return normalized;
  return `${normalized.slice(0, MAX_TEAM_NAME_LENGTH - 3).trimEnd()}...`;
}

function createRuntimeToken(): string {
  if (!globalThis.crypto?.randomUUID) throw new Error('RESEARCH_TEAM_RUNTIME_ID_UNAVAILABLE');
  return globalThis.crypto.randomUUID().replace(/-/gu, '').slice(0, 16);
}

async function sha256(value: string): Promise<string> {
  if (!globalThis.crypto?.subtle) throw new Error('RESEARCH_TEAM_SHA256_UNAVAILABLE');
  const digest = await globalThis.crypto.subtle.digest('SHA-256', new TextEncoder().encode(value));
  return Array.from(new Uint8Array(digest), (item) => item.toString(16).padStart(2, '0')).join('');
}

function requiredText(value: unknown, field: string): string {
  if (typeof value !== 'string' || !value.trim()) throw new TypeError(`Research Team ${field} is required`);
  return value.trim();
}
