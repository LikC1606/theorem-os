// Shared Team records and run acknowledgements for the standalone runtime.

/** Role of a teammate within a team */
export type TeammateRole = 'leader' | 'teammate';

/** Backend runtime status value as delivered by Team WebSocket events */
export type BackendTeammateStatus = string;

/** Normalized lifecycle status of a teammate agent */
export type TeammateStatus = 'pending' | 'idle' | 'active' | 'completed' | 'failed';

/** Workspace sharing strategy for the team */
export type WorkspaceMode = 'shared' | 'isolated';

/** Persisted agent configuration within a team */
export type TeamAgent = {
  slot_id: string;
  conversation_id: string;
  role: TeammateRole;
  agent_type: string;
  icon?: string;
  agent_name: string;
  conversation_type: string;
  status: TeammateStatus;
  cli_path?: string;
  custom_agent_id?: string;
  /** Assistant catalog identity required by Core when creating Team members. */
  assistant_id?: string;
  model?: string;
  pending_confirmations?: number;
};

/** Immutable coordination authority acknowledged by Core at Team creation. */
export type TeamCoordinationProtocol =
  | Readonly<{ kind: 'core_native' }>
  | Readonly<{ kind: 'managed_mcp'; logicalTool: 'research_team' }>;

/** Persisted team record (stored in SQLite `teams` table). */
export type TTeam = {
  /** Absent on legacy Core responses; never an acknowledgement of managed coordination. */
  coordination_protocol?: TeamCoordinationProtocol;
  id: string;
  user_id: string;
  name: string;
  workspace: string;
  workspace_mode: WorkspaceMode;
  leader_agent_id: string;
  agents: TeamAgent[];
  /** Current session permission mode (e.g. 'plan', 'auto'). Persisted so newly spawned agents inherit it. */
  session_mode?: string;
  created_at: number;
  updated_at: number;
};

export type TeamRunTargetRole = 'lead' | 'teammate';
export type TeamRunStatus = 'accepted' | 'running' | 'cancelling' | 'completed' | 'cancelled' | 'failed';
export type TeamMessageEnqueueStatus = 'accepted' | 'queued' | 'blocked_runtime_starting';
export type TeamSlotWorkState = 'idle' | 'queued' | 'starting' | 'running' | 'paused' | 'blocked';
export type TeamSlotBlockedReason = 'runtime_starting' | 'runtime_failed' | 'removing' | 'session_stopped';

export type ITeamRunAck = {
  team_run_id: string;
  team_id: string;
  target_slot_id: string;
  target_role: TeamRunTargetRole;
  accepted_slot_id: string;
  accepted_role: TeamRunTargetRole;
  status: TeamRunStatus;
  enqueue_status?: TeamMessageEnqueueStatus;
  message_id?: string;
  replayed?: boolean;
  /** Optional provenance fields returned by newer Core delivery endpoints. */
  source_slot_id?: string;
  delivery_id?: string;
  idempotency_key?: string;
  payload_hash?: string;
  persisted?: boolean;
};

export const isTeamRunAckPersisted = (ack: ITeamRunAck): boolean =>
  ack.persisted !== undefined
    ? ack.persisted
    : ack.enqueue_status === undefined
      ? ack.status === 'accepted'
      : ['accepted', 'queued', 'blocked_runtime_starting'].includes(ack.enqueue_status);
