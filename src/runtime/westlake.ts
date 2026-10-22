import { deepSeekModelCatalog } from './deepseek';
import { createProviderProfile } from './providerProfile';

export const WESTLAKE_PROVIDER = {
  id: 'westlake', baseUrl: 'https://hpc-api.westlake.edu.cn/v1', wireApi: 'chat-completions',
  transport: 'session-local-responses-bridge', apiKeyEnvironment: 'WESTLAKEHPC_API_KEY',
  defaultModel: 'deepseek-flash', defaultEffort: 'max',
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

export const { expectedDigest: expectedWestlakeProfileDigest, digest: westlakeProfileDigest,
  selected: selectedWestlakeProfile, prepare: prepareWestlakeProfile,
} = createProviderProfile({ ...WESTLAKE_PROVIDER, name: 'Westlake DeepSeek',
  validate: validateWestlakeModel, catalog: westlakeModelCatalog, exclude: ['WESTLAKEHPC_API_KEY*'],
  features: { multi_agent: false, multi_agent_v2: false, goals: false, view_image: false } });
