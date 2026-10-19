import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { prepareWestlakeProfile, expectedWestlakeProfileDigest, selectedWestlakeProfile,
  westlakeProfileDigest, WESTLAKE_PROVIDER } from '../src/runtime/westlake';

const roots: string[] = [];
afterEach(() => {
  vi.unstubAllEnvs();
  for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true });
});
function profile() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-westlake-'));
  roots.push(root); return path.join(root, 'codex');
}

describe('Westlake frozen profile', () => {
  it('prepares a credential-free gateway identity and text-only client catalog', () => {
    vi.stubEnv('WESTLAKEHPC_API_KEY', 'private-westlake-profile-fixture');
    const directory = profile();
    const digest = prepareWestlakeProfile(directory, 'deepseek-flash', 'high');
    const source = fs.readFileSync(path.join(directory, 'config.toml'), 'utf8');
    expect(source).not.toContain('private-westlake-profile-fixture');
    expect(parseToml(source)).toMatchObject({
      model: 'deepseek-flash', model_provider: 'westlake', model_reasoning_effort: 'high',
      model_providers: { westlake: { base_url: WESTLAKE_PROVIDER.baseUrl, wire_api: 'responses',
        env_key: 'WESTLAKEHPC_API_KEY', requires_openai_auth: false, request_max_retries: 0 } },
      shell_environment_policy: { exclude: ['WESTLAKEHPC_API_KEY*'] }, features: { multi_agent: false },
    });
    const catalog = JSON.parse(fs.readFileSync(path.join(directory, 'models.json'), 'utf8'));
    expect(catalog.models).toHaveLength(1);
    expect(catalog.models[0]).toMatchObject({ slug: 'deepseek-flash', input_modalities: ['text'],
      context_window: 131072, supports_search_tool: false, prefer_websockets: false });
    expect(fs.statSync(directory).mode & 0o077).toBe(0);
    for (const file of fs.readdirSync(directory)) expect(fs.statSync(path.join(directory, file)).mode & 0o277).toBe(0);
    expect(digest).toBe(expectedWestlakeProfileDigest(directory, 'deepseek-flash', 'high'));
    expect(westlakeProfileDigest(directory)).toBe(digest);
    expect(selectedWestlakeProfile(directory)).toEqual({ profile: fs.realpathSync(directory), digest });
    expect(() => prepareWestlakeProfile(directory, 'deepseek-flash', 'high')).toThrow();
  });

  it.each([['deepseek', 'high'], ['deepseek_pro', 'high'], ['deepseek-flash', 'xhigh']])
    ('rejects unsupported %s/%s before creating a profile', (model, effort) => {
      const directory = profile();
      expect(() => prepareWestlakeProfile(directory, model, effort)).toThrow('Westlake requires');
      expect(fs.existsSync(directory)).toBe(false);
    });

  it('detects catalog changes without reading credentials', () => {
    const directory = profile();
    const digest = prepareWestlakeProfile(directory, 'deepseek-flash', 'high');
    const file = path.join(directory, 'models.json');
    fs.chmodSync(file, 0o600); fs.appendFileSync(file, '\n');
    expect(selectedWestlakeProfile(directory)?.digest).not.toBe(digest);
  });
});
