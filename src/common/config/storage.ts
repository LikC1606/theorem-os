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
