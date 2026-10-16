import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parse as parseToml } from 'smol-toml';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { webProviderConfig } from '../apps/web/worker';
import { createCodexMathSession, type MathAgentSession } from '../src/runtime/codexSession';
import type { WorkerInput } from '../apps/web/shared';
import { webTemplates } from '../apps/web/config';

describe('web BYOK provider configuration and offline app-server fixture', () => {
  let root: string;
  let request: WorkerInput;
  let session: MathAgentSession | undefined;
  const fixture = path.resolve(path.dirname(fileURLToPath(import.meta.url)), 'fixtures/web-codex.mjs');
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-web-provider-'));
    request = { id: 'fixture', provider: { id: 'fixture', name: 'Fixture "service"', baseUrl: 'https://no-provider.invalid/v1' },
      input: { providerId: 'fixture', apiKey: 'sk-theoremos-smoke-local-only', model: 'offline-fixture', effort: 'xhigh',
        source: 'namespace Tutorial\n\ntheorem add_zero (n : Nat) : n + 0 = n := by sorry\n\ntheorem zero_add (n : Nat) : 0 + n = n := by sorry\n\nend Tutorial\n',
        task: 'Offline fixture', maxTurns: 1, maxRunSeconds: 30, workers: 1, coordination: 'independent' } };
    fs.copyFileSync(fixture, path.join(root, 'codex'));
    fs.chmodSync(path.join(root, 'codex'), 0o700);
    fs.mkdirSync(path.join(root, 'profile'), { mode: 0o700 });
    fs.mkdirSync(path.join(root, 'workspace/generated/problem'), { recursive: true });
    fs.writeFileSync(path.join(root, 'workspace/generated/problem/Submission.lean'), request.input.source);
    fs.writeFileSync(path.join(root, 'profile/config.toml'), webProviderConfig(request), { mode: 0o600 });
  });
  afterEach(async () => { await session?.close(); fs.rmSync(root, { recursive: true, force: true }); session = undefined; });
  const options = () => ({ executable: path.join(root, 'codex'), profile: path.join(root, 'profile'),
    workspace: path.join(root, 'workspace'), model: request.input.model, effort: request.input.effort,
    instructions: 'Offline proof fixture', onUsage: vi.fn(), environment: { ...process.env,
      THEOREMOS_PROVIDER_API_KEY: request.input.apiKey } });

  it('stores a structured Responses provider configuration without its API key', () => {
    const text = webProviderConfig(request);
    expect(text).not.toContain(request.input.apiKey);
    const config = parseToml(text);
    expect(config).toMatchObject({ model: 'offline-fixture', model_provider: 'web_provider',
      model_reasoning_effort: 'xhigh', approval_policy: 'never', sandbox_mode: 'workspace-write',
      model_providers: { web_provider: { name: 'Fixture "service"', base_url: request.provider.baseUrl,
        wire_api: 'responses', env_key: 'THEOREMOS_PROVIDER_API_KEY', requires_openai_auth: false } },
      shell_environment_policy: { exclude: ['THEOREMOS_PROVIDER_API_KEY'] }, history: { persistence: 'none' } });
  });

  it('completes a real stdio adapter turn after checking BYOK and writes a valid addition candidate', async () => {
    const activity = vi.fn();
    session = await createCodexMathSession({ ...options(), onActivity: activity });
    expect(await session.run('WEB_SMOKE_VALID_PROOF', 'valid-turn', path.join(root, 'workspace'), () => {})).toBe('completed');
    const source = fs.readFileSync(path.join(root, 'workspace/generated/problem/Submission.lean'), 'utf8');
    expect(source).toContain('by rfl');
    expect(source).toContain('by exact Nat.zero_add n');
    expect(source).not.toContain('sorry');
    const checks = JSON.parse(fs.readFileSync(path.join(root, 'profile/web-fixture-checks.json'), 'utf8'));
    expect(checks).toEqual({ apiKeyFromEnvironment: true, keyAbsentFromConfig: true, shellKeyExcluded: true,
      responsesProvider: true, privateProfile: true });
    expect(activity).toHaveBeenCalledWith({ event: 'item_started', itemType: 'commandExecution' });
    expect(JSON.stringify(checks)).not.toContain(request.input.apiKey);
  });

  it('can emit a syntactically valid but mathematically invalid Lean candidate', async () => {
    session = await createCodexMathSession(options());
    expect(await session.run('WEB_SMOKE_INVALID_PROOF', 'invalid-turn', path.join(root, 'workspace'), () => {})).toBe('completed');
    expect(fs.readFileSync(path.join(root, 'workspace/generated/problem/Submission.lean'), 'utf8')).toContain('exact True.intro');
  });

  it.each(['valid', 'invalid'] as const)('preserves the published Mathlib problem and emits a %s candidate', async kind => {
    const template = webTemplates.find(template => template.id === 'polynomial')!;
    const file = path.join(root, 'workspace/generated/problem/Submission.lean');
    fs.writeFileSync(file, template.source);
    request.input.environment = 'mathlib';
    session = await createCodexMathSession(options());
    expect(await session.run(`WEB_SMOKE_MATHLIB_${kind.toUpperCase()}`, `mathlib-${kind}`, path.join(root, 'workspace'), () => {})).toBe('completed');
    const proof = fs.readFileSync(file, 'utf8');
    expect(proof).toBe(template.source.replace(/by sorry/g, kind === 'valid' ? 'by ring' : 'by exact True.intro'));
    expect(proof).toContain('import Mathlib');
    expect(proof).not.toContain('sorry');
  });

  it.each(['standard', 'mathlib'] as const)('holds a live %s turn until interrupted for container cancellation', async environment => {
    const marker = environment === 'mathlib' ? 'WEB_SMOKE_MATHLIB_WAIT_FOR_CANCEL' : 'WEB_SMOKE_WAIT_FOR_CANCEL';
    const source = environment === 'mathlib' ? webTemplates.find(template => template.id === 'polynomial')!.source : request.input.source;
    request.input.environment = environment;
    fs.writeFileSync(path.join(root, 'workspace/generated/problem/Submission.lean'), source);
    session = await createCodexMathSession(options());
    let started = false;
    const done = session.run(marker, 'wait-turn', path.join(root, 'workspace'), () => { started = true; });
    await expect.poll(() => started).toBe(true);
    await session.interrupt();
    expect(await done).toBe('interrupted');
    expect(fs.readFileSync(path.join(root, 'workspace/generated/problem/Submission.lean'), 'utf8')).toBe(source);
  });

  it('refuses to start without an injected BYOK credential', async () => {
    await expect(createCodexMathSession({ ...options(), environment: { ...process.env,
      THEOREMOS_PROVIDER_API_KEY: '' } })).rejects.toThrow('math_codex_rpc_failed:-32000:thread/start');
    expect(fs.existsSync(path.join(root, 'profile/web-fixture-checks.json'))).toBe(false);
  });

  it('refuses a profile that persisted the API key', async () => {
    fs.appendFileSync(path.join(root, 'profile/config.toml'), `\n# ${request.input.apiKey}\n`);
    await expect(createCodexMathSession(options())).rejects.toThrow('math_codex_rpc_failed:-32000:thread/start');
  });
});
