/**
 * @license
 * Copyright 2025 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */
// Mirror of the backend assistant API type.
// Any shape change on either side requires a same-PR update on the other.
export type AssistantSource = 'builtin' | 'user';
export interface Assistant {
    id: string;
    source: AssistantSource;
    name: string;
    name_i18n: Record<string, string>;
    description?: string;
    description_i18n: Record<string, string>;
    avatar?: string;
    enabled: boolean;
    sort_order: number;
    preset_agent_type: string;
    enabled_skills: string[];
    custom_skill_names: string[];
    disabled_builtin_skills: string[];
    context?: string;
    context_i18n: Record<string, string>;
    prompts: string[];
    prompts_i18n: Record<string, string[]>;
    models: string[];
    last_used_at?: number;
    /** Core v0.1.50 runtime identity used by Team provisioning. */
    agent_id?: string;
    team_selectable?: boolean;
    agent?: {
        type?: string;
        acp_backend?: string;
    };
}
export interface AssistantDefaultScalar {
    mode: string;
    value?: string;
}
export interface AssistantDefaultList {
    mode: string;
    value: string[];
}
export interface AssistantDefaultsRequest {
    model?: AssistantDefaultScalar;
    permission?: AssistantDefaultScalar;
    skills?: AssistantDefaultList;
    mcps?: AssistantDefaultList;
}
export interface CreateAssistantRequest {
    id?: string;
    agent_id?: string;
    name: string;
    description?: string;
    avatar?: string;
    preset_agent_type?: string;
    enabled_skills?: string[];
    custom_skill_names?: string[];
    disabled_builtin_skills?: string[];
    prompts?: string[];
    models?: string[];
    name_i18n?: Record<string, string>;
    description_i18n?: Record<string, string>;
    prompts_i18n?: Record<string, string[]>;
    recommended_prompts?: string[];
    recommended_prompts_i18n?: Record<string, string[]>;
    defaults?: AssistantDefaultsRequest;
}
