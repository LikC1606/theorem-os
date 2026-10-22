import { deepSeekModelCatalog } from './deepseek';
import { createProviderProfile } from './providerProfile';

export const SUB2API_PROVIDER = {
  id: 'sub2api', baseUrl: 'http://127.0.0.1:8080/v1', wireApi: 'responses',
  apiKeyEnvironment: 'SUB2API_WESTLAKE_API_KEY',
  defaultModel: 'deepseek-flash', defaultEffort: 'max',
} as const;

export function validateSub2apiModel(model: string, effort: string): void {
  if (model !== SUB2API_PROVIDER.defaultModel) throw new Error('Sub2API requires --model deepseek-flash');
  if (!['low', 'high', 'max'].includes(effort))
    throw new Error('Sub2API requires --effort low, high or max');
}

export function sub2apiModelCatalog() {
  return { models: deepSeekModelCatalog().models.filter(model => model.slug === 'deepseek-flash').map(model => ({
    ...model, description: 'DeepSeek Flash via the local sub2api gateway',
    input_modalities: ['text'], supports_image_detail_original: false, supports_search_tool: false,
    multi_agent_version: null,
    // The gateway pools upstream accounts and does not advertise a larger context limit.
    context_window: 131072, max_context_window: 131072,
  })) };
}

export const { expectedDigest: expectedSub2apiProfileDigest, digest: sub2apiProfileDigest,
  selected: selectedSub2apiProfile, prepare: prepareSub2apiProfile,
} = createProviderProfile({ ...SUB2API_PROVIDER, name: 'Sub2API DeepSeek',
  validate: validateSub2apiModel, catalog: sub2apiModelCatalog, exclude: ['SUB2API_WESTLAKE_API_KEY*'],
  features: { multi_agent: false, multi_agent_v2: false, goals: false, view_image: false } });
