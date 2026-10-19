import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml, stringify as stringifyToml } from 'smol-toml';
import { canonicalMathJson, mathDigest, readMathText } from '../math/mathRuntimeIo';

type ProviderProfile = {
  id: string; name: string; baseUrl: string; apiKeyEnvironment: string;
  validate: (model: string, effort: string) => void; catalog: () => unknown;
  exclude?: string[]; features?: Record<string, boolean>;
};

export function createProviderProfile(provider: ProviderProfile) {
  const files = (directory: string, model: string, effort: string) => {
    provider.validate(model, effort);
    return {
      'config.toml': stringifyToml({
        model, model_provider: provider.id, model_reasoning_effort: effort,
        model_catalog_json: path.join(directory, 'models.json'), web_search: 'disabled',
        approval_policy: 'never', sandbox_mode: 'workspace-write',
        model_providers: { [provider.id]: { name: provider.name, base_url: provider.baseUrl,
          // Codex uses Responses even when a bridge translates the upstream transport.
          wire_api: 'responses', env_key: provider.apiKeyEnvironment,
          requires_openai_auth: false, request_max_retries: 0, stream_max_retries: 0,
          stream_idle_timeout_ms: 60_000 } },
        shell_environment_policy: { inherit: 'all', exclude: provider.exclude ?? [provider.apiKeyEnvironment] },
        history: { persistence: 'none' }, analytics: { enabled: false },
        ...(provider.features ? { features: provider.features } : {}),
      }),
      'models.json': JSON.stringify(provider.catalog(), null, 2) + '\n',
    };
  };
  const expectedDigest = (directory: string, model: string, effort: string) =>
    mathDigest(canonicalMathJson(files(directory, model, effort)));
  const digest = (directory: string) => mathDigest(canonicalMathJson(Object.fromEntries(['config.toml', 'models.json'].map(name =>
    [name, readMathText(path.join(directory, name))]))));
  return { expectedDigest, digest,
    selected(directory: string): { profile: string; digest: string } | undefined {
      const configFile = path.join(directory, 'config.toml');
      if (!fs.existsSync(configFile) || parseToml(readMathText(configFile)).model_provider !== provider.id) return;
      return { profile: fs.realpathSync(directory), digest: digest(directory) };
    },
    prepare(directory: string, model: string, effort: string): string {
      const contents = files(directory, model, effort);
      fs.mkdirSync(directory, { mode: 0o700 });
      for (const [name, content] of Object.entries(contents))
        fs.writeFileSync(path.join(directory, name), content, { mode: 0o400, flag: 'wx' });
      return expectedDigest(directory, model, effort);
    },
  };
}
