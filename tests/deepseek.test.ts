import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { DEEPSEEK_PROVIDER, deepSeekProfileDigest, expectedDeepSeekProfileDigest, prepareDeepSeekProfile } from '../src/runtime/deepseek';

const roots: string[] = [];
const profile = () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-deepseek-'));
  roots.push(root); return path.join(root, 'codex');
};
afterEach(() => {
  vi.unstubAllEnvs();
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});

describe('offline DeepSeek profile preparation', () => {
  it.each([
    ['deepseek-v4-pro', 'low', '82e05a1768ca024280774aab11882db96eb279ff37ab4f33e7fe9c7c00712dcd'],
    ['deepseek-v4-pro', 'high', 'dea8b95d0a1dba4d60242cf536be78ac97e80a3760bc9fa7457e94d4cc3cb579'],
    ['deepseek-v4-pro', 'max', 'ae5f1c1c55cf582a0a2bdc3c49d08ebb6be6de6cf1f719c1518a2a53a5c37813'],
    ['deepseek-flash', 'low', '733d46ee147c6fdb3cfba5ef428631ae27c90efd3062bfb725e9e2a232ec98a5'],
    ['deepseek-flash', 'high', 'b31e6bd342f91988a710f9531c651961963b9824a4157bdba4d191252a55e9b1'],
    ['deepseek-flash', 'max', '9763ed9dd73371241657f6c315942fb22b8632d7a1b1816f294303070ae5c5e5'],
  ])('preserves frozen profile bytes for %s/%s', (model, effort, digest) => {
    expect(expectedDeepSeekProfileDigest('/fixture/codex', model, effort)).toBe(digest);
  });

  it('uses the official Responses endpoint and a credential-free isolated catalog', () => {
    vi.stubEnv('DEEPSEEK_API_KEY', 'sk-private-fixture-credential');
    const directory = profile();
    const digest = prepareDeepSeekProfile(directory, 'deepseek-v4-pro', 'high');
    const source = fs.readFileSync(path.join(directory, 'config.toml'), 'utf8');
    const config = parseToml(source);
    expect(config).toMatchObject({ model: 'deepseek-v4-pro', model_reasoning_effort: 'high', model_provider: 'deepseek',
      model_catalog_json: path.join(directory, 'models.json'), web_search: 'disabled',
      model_providers: { deepseek: { base_url: 'https://api.deepseek.com', wire_api: 'responses',
        env_key: 'DEEPSEEK_API_KEY', requires_openai_auth: false } },
      shell_environment_policy: { exclude: ['DEEPSEEK_API_KEY'] } });
    expect(source).not.toContain('sk-private-fixture-credential');
    const catalog = JSON.parse(fs.readFileSync(path.join(directory, 'models.json'), 'utf8'));
    expect(catalog.models.map(model => model.slug)).toEqual(['deepseek-v4-pro', 'deepseek-flash']);
    expect(catalog.models[0]).toMatchObject({ context_window: 1048576, default_reasoning_level: 'high',
      prefer_websockets: false, shell_type: 'shell_command' });
    expect(catalog.models[0].supported_reasoning_levels.map(level => level.effort)).toEqual(['low', 'high', 'max']);
    expect(fs.statSync(directory).mode & 0o077).toBe(0);
    for (const file of ['config.toml', 'models.json']) expect(fs.statSync(path.join(directory, file)).mode & 0o277).toBe(0);
    expect(fs.readdirSync(directory).sort()).toEqual(['config.toml', 'models.json']);
    expect(digest).toBe(expectedDeepSeekProfileDigest(directory, DEEPSEEK_PROVIDER.defaultModel, DEEPSEEK_PROVIDER.defaultEffort));
    expect(deepSeekProfileDigest(directory)).toBe(digest);
    expect(() => prepareDeepSeekProfile(directory, 'deepseek-v4-pro', 'high')).toThrow();
    expect(deepSeekProfileDigest(directory)).toBe(digest);
  });

  it.each([['gpt-6.1-sol', 'high'], ['deepseek-v4-pro', 'xhigh']])('rejects %s/%s before creating a profile', (model, effort) => {
    const directory = profile();
    expect(() => prepareDeepSeekProfile(directory, model, effort)).toThrow('DeepSeek requires');
    expect(fs.existsSync(directory)).toBe(false);
  });
});
