import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml, stringify as stringifyToml } from 'smol-toml';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';

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

function profileFiles(directory: string, model: string, effort: string) {
  validateDeepSeekModel(model, effort);
  return {
    'config.toml': stringifyToml({
      model, model_provider: DEEPSEEK_PROVIDER.id, model_reasoning_effort: effort,
      model_catalog_json: path.join(directory, 'models.json'), web_search: 'disabled',
      approval_policy: 'never', sandbox_mode: 'workspace-write',
      model_providers: { deepseek: { name: 'DeepSeek', base_url: DEEPSEEK_PROVIDER.baseUrl,
        wire_api: DEEPSEEK_PROVIDER.wireApi, env_key: DEEPSEEK_PROVIDER.apiKeyEnvironment,
        requires_openai_auth: false, request_max_retries: 0, stream_max_retries: 0,
        stream_idle_timeout_ms: 60_000 } },
      shell_environment_policy: { inherit: 'all', exclude: [DEEPSEEK_PROVIDER.apiKeyEnvironment] },
      history: { persistence: 'none' }, analytics: { enabled: false },
    }),
    'models.json': JSON.stringify(deepSeekModelCatalog(), null, 2) + '\n',
  };
}

export function expectedDeepSeekProfileDigest(directory: string, model: string, effort: string): string {
  return mathDigest(canonicalMathJson(profileFiles(directory, model, effort)));
}

export function deepSeekProfileDigest(directory: string): string {
  return mathDigest(canonicalMathJson(Object.fromEntries(['config.toml', 'models.json'].map(name =>
    [name, readMathText(path.join(directory, name))]))));
}

export function selectedDeepSeekProfile(directory: string): { profile: string; digest: string } | undefined {
  const configFile = path.join(directory, 'config.toml');
  if (!fs.existsSync(configFile) || parseToml(readMathText(configFile)).model_provider !== DEEPSEEK_PROVIDER.id) return;
  return { profile: fs.realpathSync(directory), digest: deepSeekProfileDigest(directory) };
}

/** Prepare an exclusive profile without reading credentials or starting Codex. */
export function prepareDeepSeekProfile(directory: string, model: string, effort: string): string {
  const files = profileFiles(directory, model, effort);
  fs.mkdirSync(directory, { mode: 0o700 });
  for (const [name, content] of Object.entries(files))
    fs.writeFileSync(path.join(directory, name), content, { mode: 0o400, flag: 'wx' });
  return expectedDeepSeekProfileDigest(directory, model, effort);
}
