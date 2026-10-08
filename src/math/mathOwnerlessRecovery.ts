import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport, type StdioServerParameters } from '@modelcontextprotocol/sdk/client/stdio.js';
import fs from 'node:fs';
import path from 'node:path';
import { PROJECT_WORKSPACE_ENV_KEYS } from "../common/chat/projectWorkspace";
import { readBoundResearchTeamToolCapability } from "../team/toolCapability";
import type { ProjectGitResearchTeamAssignmentReceipt } from "../project-git/ProjectGitService";
import { normalizeRuntimeMathAssignment } from "./mathAssignmentJournal";
import { MATH_RUN_INPUTS_ENV, verifyMathRunInputsEnvironment } from "./mathRunInputs";

type RecordValue = Record<string, unknown>;
const record = (value: unknown): value is RecordValue =>
  typeof value === 'object' && value !== null && !Array.isArray(value);
const text = (value: unknown): value is string => typeof value === 'string' && value.trim().length > 0;

function isExecutable(file: string): boolean {
  try {
    const stat = fs.statSync(file);
    if (!stat.isFile()) return false;
    fs.accessSync(file, fs.constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

/** Resolve the registered command without relying on the sealed child PATH. */
function resolveOwnerlessRecoveryCommand(command: string, environment: NodeJS.ProcessEnv): string {
  const requested = command.trim();
  if (path.isAbsolute(requested)) {
    if (isExecutable(requested)) return requested;
    throw new Error('math_ownerless_recovery_executable_unavailable');
  }

  if (requested === 'node' && environment.DEEPSCIENTIST_MATH_ACP_ISOLATION_NODE?.trim()) {
    const configuredNode = environment.DEEPSCIENTIST_MATH_ACP_ISOLATION_NODE.trim();
    if (path.isAbsolute(configuredNode) && isExecutable(configuredNode)) return configuredNode;
    throw new Error('math_ownerless_recovery_executable_unavailable');
  }

  // If recovery is already running under the trusted Node runtime, prefer that
  // exact executable: the bound math environment intentionally has a minimal
  // PATH and may omit user-local Node installations.
  if (
    requested === 'node' &&
    /(?:^|[\\/])node(?:js)?(?:\.exe)?$/iu.test(process.execPath) &&
    isExecutable(process.execPath)
  )
    return process.execPath;

  const pathValues =
    requested === 'node' ? [environment.PATH, process.env.PATH, '/usr/local/bin:/usr/bin:/bin'] : [environment.PATH];
  const searchedDirectories = new Set<string>();
  for (const directory of pathValues.flatMap((value) => (value || '').split(path.delimiter).filter(Boolean))) {
    if (searchedDirectories.has(directory)) continue;
    searchedDirectories.add(directory);
    const candidate = path.resolve(directory, requested);
    if (isExecutable(candidate)) return candidate;
  }
  throw new Error('math_ownerless_recovery_executable_unavailable');
}

export type MathOwnerlessRecoveryCall = (
  request: Readonly<Record<string, unknown>>,
  signal: AbortSignal
) => Promise<unknown>;

export type MathOwnerlessRecoveryOutcome = Readonly<{
  status: 'dispatched' | 'waiting' | 'blocked';
  reason: string;
  targetSlotId?: string;
  assignmentId?: string;
  producerAssignmentIds: readonly string[];
}>;

/**
 * Perform only lifecycle actions already authorized by the normal status and
 * dispatch handlers. The caller invokes this after an idle Lead failed to
 * create useful work; mathematical choices remain with that Lead and Worker.
 */
export async function recoverMathOwnerlessAssignment(input: {
  call: MathOwnerlessRecoveryCall;
  assignments: readonly ProjectGitResearchTeamAssignmentReceipt[];
  targetSlotId: string;
  workerObjective: string;
  signal: AbortSignal;
}): Promise<MathOwnerlessRecoveryOutcome> {
  input.signal.throwIfAborted();
  const response = await input.call({ action: 'status' }, input.signal);
  input.signal.throwIfAborted();
  if (!record(response) || response.status !== 'observed' || !record(response.observation))
    throw new Error('math_ownerless_recovery_status_invalid');
  const observation = response.observation;
  if (['failed', 'cancelled', 'cancelling'].includes(String(observation.state)))
    return { status: 'blocked', reason: 'runtime_requires_explicit_restart', producerAssignmentIds: [] };
  if (!Array.isArray(observation.pending_assignments) || !Array.isArray(observation.continuation_actions))
    throw new Error('math_ownerless_recovery_status_invalid');
  if (Array.isArray(observation.consistency_issues) && observation.consistency_issues.length)
    return { status: 'blocked', reason: 'assignment_snapshot_inconsistent', producerAssignmentIds: [] };
  const pending = observation.pending_assignments.filter(record);
  const producers = pending
    .filter((item) => ['prepared', 'queued', 'running', 'accepted'].includes(String(item.state)))
    .map((item) => item.assignment_id)
    .filter(text);
  let request: RecordValue | undefined;
  let reason = 'legal_successor_dispatched';
  // Status has validated the seal, predecessor identity and writer release.
  // Forward its exact request, without manufacturing a new task or identity.
  for (const action of observation.continuation_actions) {
    if (!record(action) || !record(action.request) || action.request.action !== 'dispatch')
      throw new Error('math_ownerless_recovery_action_invalid');
    const requests = action.request.assignments;
    if (
      !text(action.predecessor_assignment_id) ||
      !input.assignments.some((item) => item.assignmentId === action.predecessor_assignment_id) ||
      !Array.isArray(requests) ||
      requests.length !== 1 ||
      !record(requests[0]) ||
      !text(requests[0].target_slot_id) ||
      !text(requests[0].task)
    )
      throw new Error('math_ownerless_recovery_action_invalid');
    request = action.request;
    break;
  }
  // Finished advisory research does not establish a proof owner. Any actual
  // proof lineage (or an unclassified legacy receipt) still requires its
  // normal legal successor rather than starting over from the original task.
  const hasProofHistory = input.assignments.some(
    (item) =>
      item.schema !== 'deepscientist.research_team_assignment.v2' ||
      normalizeRuntimeMathAssignment(item.assignment).request.kind === 'formalize'
  );
  const onlyAdvisoryPending = pending.every((item) => item.protocol === 'v2' && item.kind === 'research');
  if (!request && !hasProofHistory && onlyAdvisoryPending) {
    if (!text(input.targetSlotId) || !text(input.workerObjective))
      throw new Error('math_ownerless_recovery_original_target_invalid');
    if (
      !Array.isArray(observation.available_worker_slots) ||
      !observation.available_worker_slots.includes(input.targetSlotId)
    )
      return { status: 'blocked', reason: 'original_target_slot_unavailable', producerAssignmentIds: [] };
    request = {
      action: 'dispatch',
      assignments: [{ target_slot_id: input.targetSlotId, task: input.workerObjective }],
    };
    reason = 'original_target_dispatched';
  }
  if (!request && producers.length)
    return { status: 'waiting', reason: 'existing_assignment_owns_work', producerAssignmentIds: producers };
  if (!request) return { status: 'blocked', reason: 'no_authorized_lifecycle_action', producerAssignmentIds: [] };
  input.signal.throwIfAborted();
  const dispatched = await input.call(request, input.signal);
  input.signal.throwIfAborted();
  if (!record(dispatched) || dispatched.action !== 'dispatch' || !Array.isArray(dispatched.items))
    throw new Error('math_ownerless_recovery_dispatch_invalid');
  const accepted = dispatched.items.find((item) => record(item) && item.status === 'accepted');
  if (!record(accepted) || !text(accepted.assignment_id) || !text(accepted.target_slot_id))
    return { status: 'blocked', reason: 'dispatch_not_accepted', producerAssignmentIds: [] };
  const requested = (request.assignments as RecordValue[])[0]!;
  if (accepted.target_slot_id !== requested.target_slot_id)
    throw new Error('math_ownerless_recovery_dispatch_identity');
  return {
    status: 'dispatched',
    reason,
    assignmentId: accepted.assignment_id,
    targetSlotId: accepted.target_slot_id,
    producerAssignmentIds: [accepted.assignment_id],
  };
}

export type MathOwnerlessMcpInput = Readonly<{
  readCore: (pathname: string, signal: AbortSignal) => Promise<unknown>;
  conversationId: string;
  teamId: string;
  leadSlotId: string;
  projectRoot: string;
  environment: NodeJS.ProcessEnv;
  frozenEnvironment: NodeJS.ProcessEnv;
  signal: AbortSignal;
}>;

/** Resolve only the immutable, bound Lead server already registered with Core. */
export async function resolveMathOwnerlessRecoveryTransport(
  input: MathOwnerlessMcpInput
): Promise<StdioServerParameters> {
  input.signal.throwIfAborted();
  const conversation = await input.readCore(
    `/api/conversations/${encodeURIComponent(input.conversationId)}`,
    input.signal
  );
  if (
    !record(conversation) ||
    conversation.id !== input.conversationId ||
    !record(conversation.extra) ||
    conversation.extra.team_id !== input.teamId ||
    conversation.extra.team_slot_id !== input.leadSlotId ||
    conversation.extra.research_team_role_kind !== 'lead' ||
    !text(conversation.extra.research_team_profile_id) ||
    !text(conversation.extra.research_team_workflow_id) ||
    !text(conversation.extra.research_team_role_id) ||
    !Array.isArray(conversation.extra.mcp_server_ids)
  )
    throw new Error('math_ownerless_recovery_conversation_identity');
  const servers = await Promise.all(
    conversation.extra.mcp_server_ids.map(async (id: unknown) => {
      if (!text(id)) throw new Error('math_ownerless_recovery_server_identity');
      const server = await input.readCore(`/api/mcp/servers/${encodeURIComponent(id)}`, input.signal);
      if (!record(server) || server.id !== id) throw new Error('math_ownerless_recovery_server_identity');
      return server;
    })
  );
  // Provisioning renames servers to ds-team-*; the bound capability, not a
  // display name, identifies the orchestration server in the Lead snapshot.
  const candidates = servers.flatMap((server) => {
    if (!record(server.transport) || !record(server.transport.env)) return [];
    if (Object.values(server.transport.env).some((value) => typeof value !== 'string'))
      throw new Error('math_ownerless_recovery_transport_invalid');
    const capability = readBoundResearchTeamToolCapability(server.transport.env as Record<string, string>);
    return capability && capability.allowedActions.includes('status') && capability.allowedActions.includes('dispatch')
      ? [{ server, capability }]
      : [];
  });
  if (candidates.length !== 1) throw new Error('math_ownerless_recovery_server_ambiguous');
  const { server, capability } = candidates[0]!;
  const transport = server.transport;
  if (
    !record(transport) ||
    transport.type !== 'stdio' ||
    !text(transport.command) ||
    !record(transport.env) ||
    !Array.isArray(transport.args) ||
    !transport.args.every((arg) => typeof arg === 'string') ||
    Object.values(transport.env).some((value) => typeof value !== 'string')
  )
    throw new Error('math_ownerless_recovery_transport_invalid');
  const boundEnv = transport.env as Record<string, string>;
  if (
    !capability ||
    capability.teamId !== input.teamId ||
    capability.slotId !== input.leadSlotId ||
    capability.roleKind !== 'lead' ||
    capability.profileId !== conversation.extra.research_team_profile_id ||
    capability.workflowId !== conversation.extra.research_team_workflow_id ||
    capability.roleId !== conversation.extra.research_team_role_id ||
    path.resolve(capability.projectRoot) !== path.resolve(input.projectRoot) ||
    !capability.allowedActions.includes('status') ||
    !capability.allowedActions.includes('dispatch')
  )
    throw new Error('math_ownerless_recovery_capability_identity');
  if (!input.frozenEnvironment[MATH_RUN_INPUTS_ENV]) throw new Error('math_ownerless_recovery_run_inputs_missing');
  for (const [key, value] of Object.entries(input.frozenEnvironment)) {
    if (value !== undefined && boundEnv[key] !== value) throw new Error('math_ownerless_recovery_environment_mismatch');
  }
  verifyMathRunInputsEnvironment(boundEnv);
  const env: Record<string, string> = Object.fromEntries(
    Object.entries(input.environment).filter((entry): entry is [string, string] => entry[1] !== undefined)
  );
  // The caller may itself be an unrelated agent. Never borrow its runtime token.
  for (const key of ['AIONUI_USER_ID', 'AIONUI_RUNTIME_TOKEN', 'AIONUI_CONVERSATION_ID']) delete env[key];
  Object.assign(env, boundEnv);
  if (boundEnv.AIONUI_CONVERSATION_ID && boundEnv.AIONUI_CONVERSATION_ID !== input.conversationId)
    throw new Error('math_ownerless_recovery_runtime_identity');
  if (Boolean(boundEnv.AIONUI_USER_ID) !== Boolean(boundEnv.AIONUI_RUNTIME_TOKEN))
    throw new Error('math_ownerless_recovery_runtime_identity');
  env.AIONUI_CONVERSATION_ID = input.conversationId;
  env[PROJECT_WORKSPACE_ENV_KEYS.conversationId] = input.conversationId;
  // Preserve the authoritative project binding, which may be the generated
  // solver root rather than the containing Git workspace.
  if (!boundEnv[PROJECT_WORKSPACE_ENV_KEYS.projectRoot])
    throw new Error('math_ownerless_recovery_project_binding_missing');
  input.signal.throwIfAborted();
  return {
    command: resolveOwnerlessRecoveryCommand(transport.command, input.environment),
    args: [...transport.args] as string[],
    env,
    cwd: input.projectRoot,
    stderr: 'pipe',
  };
}

/** One scoped MCP process; no process-global environment or model invocation. */
export async function withMathOwnerlessRecoveryMcp<T>(
  input: MathOwnerlessMcpInput,
  use: (call: MathOwnerlessRecoveryCall) => Promise<T>
): Promise<T> {
  const parameters = await resolveMathOwnerlessRecoveryTransport(input);
  const client = new Client({ name: 'math-host-lifecycle-recovery', version: '1.0.0' });
  const transport = new StdioClientTransport(parameters);
  const close = () => {
    void client.close().catch(() => {});
  };
  input.signal.addEventListener('abort', close, { once: true });
  try {
    input.signal.throwIfAborted();
    await client.connect(transport, { signal: input.signal });
    // Drain diagnostics without exposing environment or blocking a noisy child.
    transport.stderr?.on('data', () => {});
    return await use(async (request, signal) => {
      signal.throwIfAborted();
      if (request.action !== 'status' && request.action !== 'dispatch')
        throw new Error('math_ownerless_recovery_action_forbidden');
      const response = await client.callTool({ name: 'research_team', arguments: { ...request } }, undefined, {
        signal,
      });
      signal.throwIfAborted();
      const content = response.content;
      if (
        !Array.isArray(content) ||
        content.length !== 1 ||
        !record(content[0]) ||
        content[0].type !== 'text' ||
        !text(content[0].text)
      )
        throw new Error('math_ownerless_recovery_response_invalid');
      const payload: unknown = JSON.parse(content[0].text);
      if (response.isError) {
        const code =
          record(payload) && record(payload.error) && text(payload.error.code) ? payload.error.code : 'tool_error';
        throw new Error(`math_ownerless_recovery_${code}`);
      }
      return payload;
    });
  } finally {
    input.signal.removeEventListener('abort', close);
    await client.close().catch(() => {});
    await transport.close().catch(() => {});
  }
}
