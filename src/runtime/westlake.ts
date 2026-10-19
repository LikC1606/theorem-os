import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml, stringify as stringifyToml } from 'smol-toml';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';
import { deepSeekModelCatalog } from './deepseek';

export const WESTLAKE_PROVIDER = {
  id: 'westlake', baseUrl: 'https://hpc-api.westlake.edu.cn/v1', wireApi: 'chat-completions',
  transport: 'session-local-responses-bridge', apiKeyEnvironment: 'WESTLAKEHPC_API_KEY',
  defaultModel: 'deepseek-flash', defaultEffort: 'high',
} as const;

export function validateWestlakeModel(model: string, effort: string): void {
  if (model !== WESTLAKE_PROVIDER.defaultModel) throw new Error('Westlake requires --model deepseek-flash');
  if (!['low', 'high', 'max'].includes(effort)) throw new Error('Westlake requires --effort low, high or max');
}

export function westlakeModelCatalog() {
  return { models: deepSeekModelCatalog().models.filter(model => model.slug === 'deepseek-flash').map(model => ({
    ...model, description: 'Westlake DeepSeek via a session-local Chat Completions bridge',
    input_modalities: ['text'], supports_image_detail_original: false, supports_search_tool: false,
    multi_agent_version: null,
    // A conservative client limit; the gateway does not advertise its context limit.
    context_window: 131072, max_context_window: 131072,
  })) };
}

function profileFiles(directory: string, model: string, effort: string) {
  validateWestlakeModel(model, effort);
  return {
    'config.toml': stringifyToml({
      model, model_provider: WESTLAKE_PROVIDER.id, model_reasoning_effort: effort,
      model_catalog_json: path.join(directory, 'models.json'), web_search: 'disabled',
      approval_policy: 'never', sandbox_mode: 'workspace-write',
      model_providers: { westlake: { name: 'Westlake DeepSeek', base_url: WESTLAKE_PROVIDER.baseUrl,
        wire_api: 'responses', env_key: WESTLAKE_PROVIDER.apiKeyEnvironment,
        requires_openai_auth: false, request_max_retries: 0, stream_max_retries: 0,
        stream_idle_timeout_ms: 60_000 } },
      shell_environment_policy: { inherit: 'all', exclude: ['WESTLAKEHPC_API_KEY*'] },
      history: { persistence: 'none' }, analytics: { enabled: false },
      features: { multi_agent: false, multi_agent_v2: false, goals: false, view_image: false },
    }),
    'models.json': JSON.stringify(westlakeModelCatalog(), null, 2) + '\n',
  };
}

export function expectedWestlakeProfileDigest(directory: string, model: string, effort: string): string {
  return mathDigest(canonicalMathJson(profileFiles(directory, model, effort)));
}

export function westlakeProfileDigest(directory: string): string {
  return mathDigest(canonicalMathJson(Object.fromEntries(['config.toml', 'models.json'].map(name =>
    [name, readMathText(path.join(directory, name))]))));
}

export function selectedWestlakeProfile(directory: string): { profile: string; digest: string } | undefined {
  const configFile = path.join(directory, 'config.toml');
  if (!fs.existsSync(configFile) || parseToml(readMathText(configFile)).model_provider !== WESTLAKE_PROVIDER.id) return;
  return { profile: fs.realpathSync(directory), digest: westlakeProfileDigest(directory) };
}

/** Prepare a host-owned profile. The runtime binds its upstream to a temporary local bridge. */
export function prepareWestlakeProfile(directory: string, model: string, effort: string): string {
  const files = profileFiles(directory, model, effort);
  fs.mkdirSync(directory, { mode: 0o700 });
  for (const [name, content] of Object.entries(files))
    fs.writeFileSync(path.join(directory, name), content, { mode: 0o400, flag: 'wx' });
  return expectedWestlakeProfileDigest(directory, model, effort);
}
