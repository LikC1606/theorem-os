/** Copyright 2026 DeepScientist contributors. SPDX-License-Identifier: Apache-2.0 */
import type { ISessionMcpServer, TProviderWithModel } from './config/storage';
import type { MathematicsConversationExtra } from './chat/mathematics';
import type { ScienceConversationExtra } from './chat/science';
import type { ProjectGitWorkspaceBinding } from './types/office/preview';
import type { ModeStack } from './types/modes/types';

/** Core HTTP request contract, independent of the Electron IPC bridge. */
export interface ICreateConversationParams {
  type: 'acp';
  id?: string;
  name?: string;
  model: TProviderWithModel;
  assistant?: {
    id: string;
    locale?: string;
    conversation_overrides?: {
      model?: string;
      permission?: string;
      skill_ids?: string[];
      disabled_builtin_skill_ids?: string[];
      mcp_ids?: string[];
    };
  };
  extra: {
    workspace?: string;
    custom_workspace?: boolean;
    backend?: string;
    cli_path?: string;
    agent_name?: string;
    agent_id?: string;
    custom_agent_id?: string;
    context?: string;
    context_file_name?: string;
    preset_rules?: string;
    mode_stack?: ModeStack;
    science?: ScienceConversationExtra;
    mathematical_research?: MathematicsConversationExtra;
    enabled_skills?: string[];
    exclude_builtin_skills?: string[];
    preset_enabled_skills?: string[];
    exclude_auto_inject_skills?: string[];
    preset_context?: string;
    preset_assistant_id?: string;
    selected_mcp_server_ids?: string[];
    selected_session_mcp_servers?: ISessionMcpServer[];
    mcp_server_ids?: string[];
    mcp_servers?: string[];
    session_mcp_servers?: ISessionMcpServer[];
    project_git?: ProjectGitWorkspaceBinding;
    session_mode?: string;
    codex_model?: string;
    current_model_id?: string;
    thought_level?: string;
    extra_skill_paths?: string[];
    team_id?: string;
  };
}
