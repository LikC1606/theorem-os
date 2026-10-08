/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
import type { AcpPermissionRequest, PlanUpdate, ToolCallUpdate } from "../types/platform/acpTypes";
/**
 * @description 跟对话相关的消息类型申明 及相关处理
 */
type TMessageType = 'text' | 'tips' | 'tool_call' | 'tool_group' | 'agent_status' | 'permission' | 'acp_permission' | 'acp_tool_call' | 'plan' | 'thinking' | 'available_commands';
interface IMessage<T extends TMessageType, Content extends Record<string, any>> {
    /**
     * 唯一ID
     */
    id: string;
    /**
     * 消息来源ID，
     */
    msg_id?: string;
    //消息会话ID
    conversation_id: string;
    /** Backend turn identity used to scope live renderer state. */
    turn_id?: string;
    /**
     * 消息类型
     */
    type: T;
    /**
     * 消息内容
     */
    content: Content;
    /**
     * 消息创建时间
     */
    created_at?: number;
    /**
     * 消息位置
     */
    position?: 'left' | 'right' | 'center' | 'pop';
    /**
     * 消息状态
     */
    status?: 'finish' | 'pending' | 'error' | 'work';
    /**
     * Hidden from UI display but persisted to DB and sent to agent.
     */
    hidden?: boolean;
}
export type IMessageToolCall = IMessage<'tool_call', {
    call_id: string;
    name: string;
    args: Record<string, any>;
    error?: string;
    status?: 'running' | 'completed' | 'error';
    input?: Record<string, any>;
    output?: string;
    description?: string;
}>;
type IMessageToolGroupConfirmationDetailsBase<Type, Extra extends Record<string, any>> = {
    type: Type;
    title: string;
} & Extra;
export type IMessageToolGroup = IMessage<'tool_group', Array<{
    call_id: string;
    description: string;
    name: string;
    render_output_as_markdown: boolean;
    result_display?: string | {
        file_diff: string;
        file_name: string;
    } | {
        img_url: string;
        relative_path: string;
    } | {
        command?: string;
        cmd?: string;
        stdout?: string;
        std_out?: string;
        stderr?: string;
        std_err?: string;
        output?: string;
        result?: string;
        text?: string;
        exitCode?: number | string;
        exit_code?: number | string;
        code?: number | string;
        statusCode?: number | string;
    };
    status: 'Executing' | 'Success' | 'Error' | 'Canceled' | 'Pending' | 'Confirming';
    confirmationDetails?: IMessageToolGroupConfirmationDetailsBase<'edit', {
        file_name: string;
        file_diff: string;
        isModifying?: boolean;
    }> | IMessageToolGroupConfirmationDetailsBase<'exec', {
        rootCommand: string;
        command: string;
    }> | IMessageToolGroupConfirmationDetailsBase<'info', {
        urls?: string[];
        prompt: string;
    }> | IMessageToolGroupConfirmationDetailsBase<'mcp', {
        tool_name: string;
        tool_display_name: string;
        server_name: string;
    }>;
}>>;
export type IMessageAcpToolCall = IMessage<'acp_tool_call', ToolCallUpdate>;
