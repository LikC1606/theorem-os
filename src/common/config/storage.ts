/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
import type { LabSkillDepositionConversationExtra } from "../chat/labSkillDeposition";
import type { FinancialFactorConversationExtra } from "../chat/financialFactor";
import type { FinancialConversationExtra } from "../chat/finance/index";
import type { MathematicsConversationExtra } from "../chat/mathematics";
import type { LoopGoalState as CanonicalLoopGoalState, LoopGoalStatus as CanonicalLoopGoalStatus, } from "../chat/loopGoal";
import type { MedicalEvidenceConversationExtra } from "../chat/medicalEvidence";
import type { ScienceConversationExtra } from "../chat/science";
import type { TargetDiscoveryConversationExtra } from "../chat/targetDiscovery";
import type { ProjectMemoryConversationExtra } from "../chat/projectMemory/index";
import type { ComputeConfig, ComputeConversationExtra } from "../types/compute";
import type { ModeStack } from "../types/modes/types";
import type { DeepScientistTeamConfig, DeepScientistTeamConversationExtra } from "../chat/team/deepScientistTeam";
/**
 * Conversation source type - identifies where the conversation was created
 * 会话来源类型 - 标识会话创建的来源
 */
export type ConversationSource = 'app' | 'telegram' | 'lark' | 'dingtalk' | 'weixin' | 'wecom' | (string & {});
export type TChatConversationStatus = 'pending' | 'running' | 'finished';
export type TConversationRuntimeStateKind = 'idle' | 'starting' | 'running' | 'cancelling' | 'waiting_confirmation';
export type TConversationRuntimeSummary = {
    state: TConversationRuntimeStateKind;
    can_send_message: boolean;
    has_task: boolean;
    task_status?: TChatConversationStatus;
    is_processing: boolean;
    pending_confirmations: number;
    turn_id: string | null;
};
export type LoopGoalState = CanonicalLoopGoalState;
interface IChatConversation<T, Extra> {
    created_at: number;
    modified_at: number;
    name: string;
    desc?: string;
    id: string;
    type: T;
    extra: Extra;
    model: TProviderWithModel;
    status?: TChatConversationStatus | undefined;
    runtime?: TConversationRuntimeSummary;
    /** 会话来源，默认为 app / Conversation source, defaults to app */
    source?: ConversationSource;
    /** Channel chat isolation ID (e.g. user:xxx, group:xxx) */
    channel_chat_id?: string;
}
// Token 使用统计数据类型
export interface TokenUsageData {
    total_tokens: number;
}
export type ConversationForkWorkspaceMode = 'shared' | 'isolated-worktree';
export type ConversationForkKind = 'assistant-continue' | 'user-edit';
export type ConversationForkBoundary = 'through-source' | 'before-source';
export type ConversationForkMetadata = {
    schema: 'deepscientist.conversation_fork.v1';
    parentConversationId: string;
    parentConversationName: string;
    sourceMessageId: string;
    sourceMsgId?: string;
    sourceMessageCreatedAt?: number;
    sourceExcerpt: string;
    workspaceMode: ConversationForkWorkspaceMode;
    /** Why the branch was created. Missing on branches created before this field existed. */
    kind?: ConversationForkKind;
    /** Whether inherited context includes the selected source message. */
    boundary?: ConversationForkBoundary;
    baseCommit?: string;
    createdAt: number;
};
/**
 * Durable hand-off for the first message of a newly-created conversation.
 * It survives a renderer reload while the Agent runtime is still starting.
 */
export type PendingInitialMessage = {
    schema: 'deepscientist.pending_initial_message.v1';
    input: string;
    files: string[];
    createdAt: number;
};
/**
 * Durable display receipt for the task that started a Team run. Unlike
 * pending_initial_message, this must never trigger a second ACP send.
 */
export type TeamInitialMessage = {
    schema: 'deepscientist.team_initial_message.v1';
    input: string;
    files: string[];
    createdAt: number;
};
/**
 * Small durable checkpoint for the only part of a turn that Core cannot
 * recover itself: the hand-off between the renderer and the Agent runtime.
 * Accepted messages and execution nodes remain owned by Core's message DB.
 */
export type ConversationTurnRecovery = {
    schema: 'deepscientist.turn_recovery.v1';
    requestId: string;
    input: string;
    files: string[];
    phase: 'sending' | 'accepted' | 'failed' | 'interrupted';
    createdAt: number;
    updatedAt: number;
    turnId?: string;
    error?: {
        message: string;
        code?: string;
        retryable?: boolean;
    };
};
export type TChatConversation = Omit<IChatConversation<'acp', {
    workspace?: string;
    backend: string;
    cli_path?: string;
    custom_workspace?: boolean;
    agent_name?: string;
    custom_agent_id?: string; // UUID for identifying specific custom agent
    preset_context?: string; // 智能助手的预设规则/提示词 / Preset context from smart assistant
    lark_project_binding_id?: string;
    lark_project_tasklist_guid?: string;
    lark_project_tasklist_name?: string;
    lark_project_role?: 'leader' | 'agent';
    lark_project_focused_task_guid?: string;
    lark_project_focused_task_title?: string;
    lark_im_profile_name?: string;
    lark_im_chat_id?: string;
    lark_im_sender_id?: string;
    lark_im_display_group?: string;
    lark_im_kind?: 'direct_chat' | 'group_chat';
    lark_im_last_message_id?: string;
    is_temporary_workspace?: boolean;
    /** Skills snapshot for this conversation — authoritative list, written
     * once at creation. Join with `GET /api/skills` for descriptions. */
    skills?: string[];
    /** MCP server id snapshot chosen when the conversation was created. */
    mcp_server_ids?: string[];
    /** MCP server name snapshot chosen when the conversation was created. */
    mcp_servers?: string[];
    /** Conversation-scoped MCP status snapshot shown in the sendbox menu. */
    mcp_statuses?: IConversationMcpStatus[];
    /** Session-only MCP server snapshot persisted at creation time. */
    session_mcp_servers?: ISessionMcpServer[];
    /** Session-only MCP servers selected by the user before backend normalization. */
    selected_session_mcp_servers?: ISessionMcpServer[];
    /** Git workspace bound to a persistent discovery-mode conversation. */
    project_git?: import("../types/office/preview").ProjectGitWorkspaceBinding;
    /** 预设助手 ID，用于在会话面板显示助手名称和头像 / Preset assistant ID for displaying name and avatar in conversation panel */
    preset_assistant_id?: string;
    /** 是否置顶会话 / Whether this conversation is pinned */
    pinned?: boolean;
    /** 置顶时间戳（毫秒）/ Pin timestamp in milliseconds */
    pinned_at?: number;
    /** ACP 后端的 session UUID，用于会话恢复 / ACP backend session UUID for session resume */
    acp_session_id?: string;
    /** Conversation ID that owns the ACP session / 拥有该 ACP session 的会话 ID */
    acp_session_conversation_id?: string;
    /** ACP session 最后更新时间 / Last update time of ACP session */
    acp_session_updated_at?: number;
    /** Last context usage from usage_update */
    last_token_usage?: TokenUsageData;
    /** Context window capacity from usage_update */
    last_context_limit?: number;
    /** Persisted session mode for resume support / 持久化的会话模式，用于恢复 */
    session_mode?: string;
    /** Persisted model ID for resume support / 持久化的模型 ID，用于恢复 */
    current_model_id?: string;
    /** Cached config options from ACP backend / 缓存的 ACP 配置选项 */
    cached_config_options?: import("../types/platform/acpTypes").AcpSessionConfigOption[];
    /** Pending config option selections from Guid page / Guid 页面待应用的配置选项 */
    pending_config_options?: Record<string, string>;
    /** First message waiting for backend acceptance. Null means it has been consumed. */
    pending_initial_message?: PendingInitialMessage | null;
    /** Original user task shown while the Team endpoint persists the canonical message. */
    team_initial_message?: TeamInitialMessage | null;
    /** Unresolved turn hand-off retained for restart, retry, and continue actions. */
    turn_recovery?: ConversationTurnRecovery | null;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    /** Cron job ID that spawned this conversation */
    cron_job_id?: string;
    /** Persistent Loop Goal state for auto-continuation. */
    loop_goal?: LoopGoalState;
    /** Versioned primary-plus-overlays mode composition snapshot. */
    mode_stack?: ModeStack;
    /** Optional DeepScientist-managed multi-Agent orchestration snapshot. */
    deepscientist_team?: DeepScientistTeamConversationExtra;
    /** Locale captured when the conversation was created, used by mode continuations. */
    assistant_locale?: string;
    /** Medical Evidence Mode metadata and rendering contract. */
    medical_evidence?: MedicalEvidenceConversationExtra;
    /** Science Mode metadata and artifact rendering contract. */
    science?: ScienceConversationExtra;
    /** Target Discovery overlay metadata and portfolio rendering contract. */
    target_discovery?: TargetDiscoveryConversationExtra;
    /** Financial Mode routing and provider preflight snapshot. */
    financial?: FinancialConversationExtra;
    /** Mathematical Research overlay metadata and artifact contract. */
    mathematical_research?: MathematicsConversationExtra;
    /** Selected compute hosts and prompt context snapshot. */
    compute?: ComputeConversationExtra;
    /** Lab Skill deposition mode metadata and rendering contract. */
    lab_skill_deposition?: LabSkillDepositionConversationExtra;
    /** Git-backed project memory overlay metadata. */
    knowledge_deposition?: ProjectMemoryConversationExtra;
    /** Financial Factor Mode metadata and rendering contract. */
    financial_factor?: FinancialFactorConversationExtra;
    /** Immutable origin metadata for a conversation created from a completed assistant message. */
    fork?: ConversationForkMetadata;
}>, 'model'> | Omit<IChatConversation<'codex', {
    workspace?: string;
    cli_path?: string;
    custom_workspace?: boolean;
    sandboxMode?: 'read-only' | 'workspace-write' | 'danger-full-access'; // Codex sandbox permission mode
    preset_context?: string; // 智能助手的预设规则/提示词 / Preset context from smart assistant
    /** Skills snapshot for this conversation — authoritative list, written
     * once at creation. Join with `GET /api/skills` for descriptions. */
    skills?: string[];
    /** 预设助手 ID，用于在会话面板显示助手名称和头像 / Preset assistant ID for displaying name and avatar in conversation panel */
    preset_assistant_id?: string;
    /** 是否置顶会话 / Whether this conversation is pinned */
    pinned?: boolean;
    /** 置顶时间戳（毫秒）/ Pin timestamp in milliseconds */
    pinned_at?: number;
    /** Persisted session mode for resume support / 持久化的会话模式，用于恢复 */
    session_mode?: string;
    /** User-selected Codex model from Guid page / 用户在引导页选择的 Codex 模型 */
    codexModel?: string;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    /** Cron job ID that spawned this conversation */
    cron_job_id?: string;
    /** Immutable origin metadata for a conversation created from a completed assistant message. */
    fork?: ConversationForkMetadata;
}>, 'model'> | Omit<IChatConversation<'openclaw-gateway', {
    workspace?: string;
    backend?: string;
    agent_name?: string;
    custom_workspace?: boolean;
    /** Gateway configuration */
    gateway?: {
        host?: string;
        port?: number;
        token?: string;
        password?: string;
        useExternalGateway?: boolean;
        cli_path?: string;
    };
    /** Session key for resume */
    sessionKey?: string;
    /** Runtime validation snapshot used for post-switch strong checks */
    runtimeValidation?: {
        expectedWorkspace?: string;
        expectedBackend?: string;
        expectedAgentName?: string;
        expectedCliPath?: string;
        expectedModel?: string;
        expectedIdentityHash?: string | null;
        switchedAt?: number;
    };
    /** Skills snapshot for this conversation — authoritative list, written
     * once at creation. Join with `GET /api/skills` for descriptions. */
    skills?: string[];
    /** 预设助手 ID / Preset assistant ID */
    preset_assistant_id?: string;
    /** 是否置顶会话 / Whether this conversation is pinned */
    pinned?: boolean;
    /** 置顶时间戳（毫秒）/ Pin timestamp in milliseconds */
    pinned_at?: number;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    /** Cron job ID that spawned this conversation */
    cron_job_id?: string;
}>, 'model'>
// Legacy Gemini conversations. Kept solely so that the renderer can
// open historical rows with type='gemini' (message history is served
// by the shared messages table). The backend factory rejects any
// attempt to resume this conversation — see
// DeepScientist Core backend enums and factory.
// Every field is optional because legacy rows shape-varies across
// several older Gemini-runtime versions.
 | Omit<IChatConversation<'gemini', {
    workspace?: string;
    custom_workspace?: boolean;
    agent_name?: string;
    preset_assistant_id?: string;
    pinned?: boolean;
    pinned_at?: number;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    cron_job_id?: string;
}>, 'model'> | Omit<IChatConversation<'nanobot', {
    workspace?: string;
    custom_workspace?: boolean;
    /** Skills snapshot for this conversation — authoritative list, written
     * once at creation. Join with `GET /api/skills` for descriptions. */
    skills?: string[];
    /** 预设助手 ID / Preset assistant ID */
    preset_assistant_id?: string;
    /** 是否置顶会话 / Whether this conversation is pinned */
    pinned?: boolean;
    /** 置顶时间戳（毫秒）/ Pin timestamp in milliseconds */
    pinned_at?: number;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    /** Cron job ID that spawned this conversation */
    cron_job_id?: string;
}>, 'model'> | Omit<IChatConversation<'remote', {
    workspace?: string;
    custom_workspace?: boolean;
    /** Remote agent config ID (FK to remote_agents table) */
    remoteAgentId: string;
    /** Remote session key for resume */
    sessionKey?: string;
    /** Skills snapshot for this conversation — authoritative list, written
     * once at creation. Join with `GET /api/skills` for descriptions. */
    skills?: string[];
    /** Preset assistant ID */
    preset_assistant_id?: string;
    /** Whether this conversation is pinned */
    pinned?: boolean;
    /** Pin timestamp in milliseconds */
    pinned_at?: number;
    /** Legacy marker for pre-provider-probe health-check conversations */
    is_health_check?: boolean;
    /** Cron job ID that spawned this conversation */
    cron_job_id?: string;
}>, 'model'>;
export type ModelType = 'text' // 文本对话
 | 'vision' // 视觉理解
 | 'function_calling' // 工具调用
 | 'image_generation' // 图像生成
 | 'web_search' // 网络搜索
 | 'reasoning' // 推理模型
 | 'embedding' // 嵌入模型
 | 'rerank' // 重排序模型
 | 'excludeFromPrimary'; // 排除：不适合作为主力模型

export type ModelCapability = {
    type: ModelType;
    /**
     * 是否为用户手动选择，如果为true，则表示用户手动选择了该类型，否则表示用户手动禁止了该模型；如果为undefined，则表示使用默认值
     */
    isUserSelected?: boolean;
};
export interface IProvider {
    id: string;
    platform: string;
    name: string;
    base_url: string;
    api_key: string;
    models: string[];
    /**
     * 模型能力标签列表。打了标签就是支持，没打就是不支持
     */
    capabilities?: ModelCapability[];
    /**
     * 上下文token限制，可选字段，只在明确知道时填写
     */
    context_limit?: number;
    /**
     * 每个模型的协议覆盖配置。映射模型名称到协议字符串。
     * 仅在 platform 为 'new-api' 时使用。
     * Per-model protocol overrides. Maps model name to protocol string.
     * Only used when platform is 'new-api'.
     * e.g. { "gemini-2.5-pro": "gemini", "claude-sonnet-4": "anthropic", "gpt-4o": "openai" }
     */
    model_protocols?: Record<string, string>;
    /**
     * AWS Bedrock specific configuration
     * Only used when platform is 'bedrock'
     */
    bedrock_config?: {
        auth_method: 'accessKey' | 'profile';
        region: string;
        // For access key method
        access_key_id?: string;
        secret_access_key?: string;
        // For profile method
        profile?: string;
    };
    /**
     * 供应商启用状态，默认为 true
     * Provider enabled state, defaults to true
     */
    enabled?: boolean;
    /**
     * 各个模型的启用状态，默认全部为 true
     * Individual model enabled states, defaults to all true
     */
    model_enabled?: Record<string, boolean>;
    /**
     * 各个模型的健康检测结果（仅用于 UI 显示，不影响启用状态）
     * Model health check results (for UI display only, does not affect enabled state)
     */
    model_health?: Record<string, {
        status: 'unknown' | 'healthy' | 'unhealthy';
        last_check?: number; // 时间戳 / timestamp
        latency?: number; // 延迟时间（毫秒）/ latency in milliseconds
        error?: string; // 错误信息 / error message
    }>;
    is_full_url?: boolean;
}
export type TProviderWithModel = Omit<IProvider, 'models'> & {
    use_model: string;
};
export interface MedicalEvidenceConfig {
    enabled?: boolean;
    paperclipApiKey?: string;
    paperclipBaseUrl?: string;
    defaultSources?: Array<'pmc' | 'abstracts' | 'abstracts_only' | 'biorxiv' | 'medrxiv' | 'arxiv' | 'fda' | 'fda/jp' | 'fda/eu' | 'trials' | 'trials/us' | 'trials/cn' | 'trials/jp' | 'trials/eu' | 'clinicaltrials'>;
    strictAnchors?: boolean;
    timeoutMs?: number;
}
export interface ResearchEvidenceConfig {
    enabled?: boolean;
    paperclipApiKey?: string;
    paperclipBaseUrl?: string;
    defaultSources?: string[];
    timeoutMs?: number;
    literatureSearchEnabled?: boolean;
    literatureSearchDefaultSources?: string[];
    semanticScholarApiKey?: string;
    openAlexApiKey?: string;
    openAlexEmail?: string;
    crossrefEmail?: string;
    crossrefApiToken?: string;
    bioToolsEnabled?: boolean;
    bioToolsPythonPath?: string;
    bioToolsServerRoot?: string;
    bioToolsDefaultDomains?: string[];
}
export interface ScienceArtifactConfig {
    enabled?: boolean;
    strictProvenance?: boolean;
    writeProjectManifest?: boolean;
    defaultSkillIds?: string[];
    allowedDatabaseHosts?: string[];
    /** Provider reference used by the optional AlphaSchema factor-mining runtime. */
    alphaSchemaProviderId?: string;
    /** Model name inside alphaSchemaProviderId. Provider credentials remain in IProvider. */
    alphaSchemaModel?: string;
}
export interface AlphaDojoFinanceConfig {
    enabled?: boolean;
    endpoint?: string;
    defaultMarket?: 'us' | 'cn' | 'hk' | 'cross_market';
    timezone?: string;
    currency?: string;
    imagePrivacy?: 'local_only' | 'ask_each_time' | 'allow_cloud';
    allowSimulationWrites?: boolean;
    allowScheduledMonitoring?: boolean;
    timeoutMs?: number;
}
export interface IMcpServerTransportStdio {
    type: 'stdio';
    command: string;
    args?: string[];
    env?: Record<string, string>;
}
export interface IMcpServerTransportSSE {
    type: 'sse';
    url: string;
    headers?: Record<string, string>;
}
export interface IMcpServerTransportHTTP {
    type: 'http';
    url: string;
    headers?: Record<string, string>;
}
export interface IMcpServerTransportStreamableHTTP {
    type: 'streamable_http';
    url: string;
    headers?: Record<string, string>;
}
export type IMcpServerTransport = IMcpServerTransportStdio | IMcpServerTransportSSE | IMcpServerTransportHTTP | IMcpServerTransportStreamableHTTP;
export interface IMcpServer {
    id: string;
    name: string;
    description?: string;
    enabled: boolean; // 是否默认启用（新会话默认勾选）
    transport: IMcpServerTransport;
    tools?: IMcpTool[];
    last_test_status?: 'connected' | 'disconnected' | 'error' | 'testing'; // 最近一次检测结果
    last_connected?: number;
    created_at: number;
    updated_at: number;
    original_json: string; // 存储原始JSON配置，用于编辑时的准确显示
    /** Built-in MCP server managed by DeepScientist (hide edit/delete in UI) */
    builtin?: boolean;
}
export type ISessionMcpServer = Pick<IMcpServer, 'id' | 'name' | 'transport'>;
export type IConversationMcpStatusKind = 'loaded' | 'failed' | 'unsupported';
export interface IConversationMcpStatus {
    id: string;
    name: string;
    status: IConversationMcpStatusKind;
    reason?: string;
}
export interface IMcpTool {
    name: string;
    description?: string;
    input_schema?: unknown;
    _meta?: Record<string, unknown>;
}
/**
 * CSS 主题配置接口 / CSS Theme configuration interface
 * 用于存储用户自定义的 CSS 皮肤 / Used to store user-defined CSS skins
 */
export interface ICssTheme {
    id: string; // 唯一标识 / Unique identifier
    name: string; // 主题名称 / Theme name
    cover?: string; // 封面图片 base64 或 URL / Cover image base64 or URL
    css: string; // CSS 样式代码 / CSS style code
    is_preset?: boolean; // 是否为预设主题 / Whether it's a preset theme
    created_at: number; // 创建时间 / Creation time
    updated_at: number; // 更新时间 / Update time
}
