import { createProviderProfile } from './providerProfile';

export const DEEPSEEK_PROVIDER = {
  id: 'deepseek', baseUrl: 'https://api.deepseek.com', wireApi: 'responses',
  apiKeyEnvironment: 'DEEPSEEK_API_KEY', defaultModel: 'deepseek-v4-pro', defaultEffort: 'high',
} as const;

export function validateDeepSeekModel(model: string, effort: string): void {
  if (!['deepseek-v4-pro', 'deepseek-flash'].includes(model))
    throw new Error('DeepSeek requires --model deepseek-v4-pro or deepseek-flash');
  if (!['low', 'high', 'max'].includes(effort))
    throw new Error('DeepSeek requires --effort low, high or max');
}

// Metadata follows DeepSeek's official Codex integration; proof instructions remain host-owned.
const baseInstructions = 'You are a mathematical research agent. Use the available tools to work on the assigned frozen problem. Follow the developer instructions and source constraints. Only the host Lean checks can accept a proof.';
export function deepSeekModelCatalog() {
  return { models: ['deepseek-v4-pro', 'deepseek-flash'].map((slug, index) => ({
    slug, display_name: slug, description: 'DeepSeek mathematical research model',
    prefer_websockets: false, support_verbosity: true, default_verbosity: 'low',
    apply_patch_tool_type: 'freeform', web_search_tool_type: 'text',
    input_modalities: slug === 'deepseek-flash' ? ['text', 'image'] : ['text'],
    supports_image_detail_original: slug === 'deepseek-flash',
    truncation_policy: { mode: 'tokens', limit: 10000 }, supports_parallel_tool_calls: true,
    tool_mode: null, multi_agent_version: 'v2', use_responses_lite: false,
    include_skills_usage_instructions: false, auto_review_model_override: null,
    context_window: 1048576, max_context_window: 1048576, effective_context_window_percent: 95,
    auto_compact_token_limit: null, comp_hash: '3000', reasoning_summary_format: 'experimental',
    default_reasoning_summary: 'none', default_reasoning_level: 'high',
    supported_reasoning_levels: ['low', 'high', 'max'].map(effort => ({ effort, description: `${effort} reasoning` })),
    shell_type: 'shell_command', visibility: 'list', minimal_client_version: '0.144.0',
    supported_in_api: true, availability_nux: null, upgrade: null, priority: index + 1,
    model_messages: null, base_instructions: baseInstructions,
    experimental_supported_tools: [], supports_search_tool: true,
    default_service_tier: null, supports_reasoning_summaries: true,
  })) };
}

export const { expectedDigest: expectedDeepSeekProfileDigest, digest: deepSeekProfileDigest,
  selected: selectedDeepSeekProfile, prepare: prepareDeepSeekProfile,
} = createProviderProfile({ ...DEEPSEEK_PROVIDER, name: 'DeepSeek',
  validate: validateDeepSeekModel, catalog: deepSeekModelCatalog });
