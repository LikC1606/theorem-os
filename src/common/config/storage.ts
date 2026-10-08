/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */

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
export interface IMcpTool {
    name: string;
    description?: string;
    input_schema?: unknown;
    _meta?: Record<string, unknown>;
}
