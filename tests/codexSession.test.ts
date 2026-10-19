import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { createCodexMathSession, type MathAgentOptions, type MathAgentSession } from '../src/runtime/codexSession';
import { deepSeekProfileDigest, prepareDeepSeekProfile } from '../src/runtime/deepseek';
import { prepareWestlakeProfile, westlakeProfileDigest } from '../src/runtime/westlake';

describe('Codex app-server adapter without provider calls', () => {
  let root: string;
  let options: MathAgentOptions;
  let session: MathAgentSession | undefined;
  beforeEach(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'math-codex-'));
    const executable = path.join(root, 'fake-codex');
    fs.writeFileSync(path.join(root, 'config.toml'), '[mcp_servers.unrelated]\ncommand = "unrelated"\n');
    fs.writeFileSync(executable, `#!${process.execPath}
const fs = require('node:fs');
const readline = require('node:readline');
fs.writeFileSync(process.env.CODEX_HOME + '/provider-environment.json', JSON.stringify({
  deepseekKeyPresent: Boolean(process.env.DEEPSEEK_API_KEY), unrelatedSecretPresent: Boolean(process.env.UNRELATED_FIXTURE_SECRET),
}));
if (process.env.WESTLAKEHPC_API_KEY) fs.writeFileSync(process.env.CODEX_HOME + '/westlake-environment.json', JSON.stringify({
  receivedLocalCredential: process.env.WESTLAKEHPC_API_KEY !== 'upstream-westlake-fixture-secret',
  receivedSecondaryCredential: Boolean(process.env.WESTLAKEHPC_API_KEY_2),
}));
let settings, turn, catalogs = 0;
const send = value => process.stdout.write(JSON.stringify(value) + '\\n');
readline.createInterface({ input: process.stdin }).on('line', line => {
  const call = JSON.parse(line);
  fs.appendFileSync(process.env.CODEX_HOME + '/calls.jsonl', JSON.stringify(call) + '\\n');
  const result = value => send({ id: call.id, result: value });
  if (call.method === process.env.THEOREM_OS_FIXTURE_RPC_FAILURE) return send({ id: call.id, error: {
    code: process.env.THEOREM_OS_FIXTURE_RPC_CODE || -32600,
    message: 'private provider diagnostic', data: { detail: 'private proof text' },
  } });
  if (call.method === 'initialize') result({});
  if (call.method === 'thread/start' || call.method === 'thread/resume') {
    settings = call.params;
    if (settings.developerInstructions === 'startup-crash') return process.exit(27);
    if (settings.developerInstructions === 'mutate-profile') {
      const config = process.env.CODEX_HOME + '/config.toml';
      fs.writeFileSync(config + '.updated', fs.readFileSync(config, 'utf8') + '\\n[projects.fixture]\\ntrust_level = "trusted"\\n');
      fs.renameSync(config + '.updated', config);
    }
    result({ thread: { id: settings.developerInstructions === 'wrong-thread' ? 'wrong-thread' : settings.threadId || 'thread-fixture' },
      model: settings.developerInstructions === 'mismatch' ? 'wrong-model' : settings.model,
      modelProvider: settings.developerInstructions === 'wrong-provider' ? 'wrong-provider' : settings.config.model_provider,
      approvalPolicy: settings.approvalPolicy, reasoningEffort: settings.config.model_reasoning_effort });
  }
  if (call.method === 'mcpServerStatus/list') result({ data: Object.keys(settings.config.mcp_servers)
    .filter(name => settings.config.mcp_servers[name].enabled).map(name => ({ name,
      runtimeStatus: ++catalogs === 1 ? 'starting' : 'connected', tools: catalogs === 1 ? {} : { math: {} }, toolsError: null })), nextCursor: null });
  if (call.method === 'turn/start') {
    turn = { id: call.params.clientUserMessageId, status: 'inProgress' };
    const message = call.params.input[0].text;
    if (message === 'crash') return process.exit(9);
    if (message === 'oversized-frame') { process.stdout.write('数'.repeat(3 * 1024 * 1024)); return; }
    if (message === 'invalid-frame') { process.stdout.write('[]\\n'); return; }
    if (message === 'invalid-result') { result([]); return; }
    if (message === 'noise') for (let i = 0; i < 100; i++) send({ method: 'turn/completed', params: {
      threadId: settings.threadId || 'thread-fixture', turn: { id: 'unrelated-' + i, status: 'failed' } } });
    if (message === 'activity') {
      const notify = (method, extra, threadId = settings.threadId || 'thread-fixture') => send({ method, params: { threadId, ...extra } });
      notify('item/started', { item: { id: 'unrelated', type: 'commandExecution', command: 'secret' } }, 'other-thread');
      notify('item/started', { item: { id: 'tool', type: 'commandExecution', command: 'secret' } });
      for (let i = 0; i < 100; i++) notify('item/commandExecution/outputDelta', { itemId: 'tool', delta: 'secret output' });
      notify('item/commandExecution/outputDelta', { itemId: 'tool', delta: '{"event":"lean_lock_' });
      notify('item/commandExecution/outputDelta', { itemId: 'tool', delta: 'waiting","at":1}\\n' });
      notify('item/commandExecution/outputDelta', { itemId: 'tool', delta: '{"event":"lean_lock_acquired","at":2}\\n' });
      notify('item/completed', { item: { id: 'tool', type: 'commandExecution', aggregatedOutput: 'secret' } });
      for (let i = 0; i < 100; i++) notify('item/reasoning/textDelta', { delta: 'private reasoning' });
    }
    if (message !== 'wait') {
      send({ method: 'thread/tokenUsage/updated', params: { threadId: settings.threadId || 'thread-fixture', tokenUsage: { total: { totalTokens: 21 }, last: { inputTokens: 12345 } } } });
      const structured = {
        'structured-unauthorized': { message: 'private provider diagnostic', codexErrorInfo: 'unauthorized', additionalDetails: 'private response' },
        'structured-rate-limit': { message: 'private provider diagnostic', codexErrorInfo: { httpConnectionFailed: { httpStatusCode: 429, body: 'private response' } } },
        'structured-disconnected': { message: 'private provider diagnostic', codexErrorInfo: { responseStreamDisconnected: { httpStatusCode: 503 } } },
        'structured-invalid-status': { message: 'private provider diagnostic', codexErrorInfo: { httpConnectionFailed: { httpStatusCode: 401.5 } } },
        'structured-string-status': { message: 'private provider diagnostic', codexErrorInfo: { httpConnectionFailed: { httpStatusCode: 'private response' } } },
        'structured-unrelated-status': { message: 'private provider diagnostic', codexErrorInfo: { badRequest: { httpStatusCode: 401 } } },
        'structured-unknown': { message: 'private provider diagnostic', codexErrorInfo: 'private future error code' },
        'structured-multiple': { message: 'private provider diagnostic', codexErrorInfo: { unauthorized: {}, private: {} } },
      }[message];
      const failed = Boolean(structured) || ['rate-limit', 'late-rate-limit', 'stream-disconnected'].includes(message);
      const complete = () => send({ method: 'turn/completed', params: { threadId: settings.threadId || 'thread-fixture', turn: { ...turn,
        status: failed ? 'failed' : 'completed', ...(failed ? { error: structured || { message: message === 'stream-disconnected'
          ? 'stream disconnected before completion: error sending request' : 'Concurrency limit exceeded for account' } } : {}) } } });
      if (message === 'late-rate-limit') setImmediate(complete);
      else complete();
    }
    result({ turn });
  }
  if (call.method === 'turn/interrupt') {
    send({ method: 'turn/completed', params: { threadId: settings.threadId || 'thread-fixture', turn: { ...turn, status: 'interrupted' } } });
    result({});
  }
  if (call.method === 'turn/steer') result({ turnId: turn.id });
});
`);
    fs.chmodSync(executable, 0o700);
    options = { executable, profile: root, workspace: root, model: 'gpt-6.1-sol', effort: 'xhigh',
      instructions: 'Prove the mathematical target', onUsage: vi.fn() };
    session = undefined;
  });
  afterEach(async () => { await session?.close(); vi.unstubAllEnvs(); fs.rmSync(root, { recursive: true, force: true }); });

  it('passes only the selected provider credential after environment projection and excludes it from tools', async () => {
    const profile = path.join(root, 'deepseek');
    const nativeProfile = path.join(profile, 'runtime');
    prepareDeepSeekProfile(profile, 'deepseek-v4-pro', 'high');
    vi.stubEnv('DEEPSEEK_API_KEY', 'sk-deepseek-fixture-secret');
    vi.stubEnv('UNRELATED_FIXTURE_SECRET', 'private-unrelated-fixture');
    session = await createCodexMathSession({ ...options, profile, model: 'deepseek-v4-pro', effort: 'high',
      environment: { PATH: process.env.PATH } });
    expect(await session.run('proof', 'deepseek-turn', root, () => {})).toBe('completed');
    expect(JSON.parse(fs.readFileSync(path.join(nativeProfile, 'provider-environment.json'), 'utf8'))).toEqual({
      deepseekKeyPresent: true, unrelatedSecretPresent: false,
    });
    const traffic = fs.readFileSync(path.join(nativeProfile, 'calls.jsonl'), 'utf8');
    expect(traffic).not.toContain('sk-deepseek-fixture-secret');
    const settings = traffic.trim().split('\n').map(line => JSON.parse(line)).find(call => call.method === 'thread/start').params;
    expect(settings).toMatchObject({ model: 'deepseek-v4-pro', config: {
      model_reasoning_effort: 'high', 'shell_environment_policy.exclude': ['DEEPSEEK_API_KEY'],
      model_provider: 'deepseek', 'model_providers.deepseek.base_url': 'https://api.deepseek.com',
    } });
  });

  it('rejects an app-server bound to another provider before any model turn', async () => {
    const profile = path.join(root, 'deepseek');
    prepareDeepSeekProfile(profile, 'deepseek-v4-pro', 'high');
    await expect(createCodexMathSession({ ...options, profile, instructions: 'wrong-provider',
      environment: { PATH: process.env.PATH, DEEPSEEK_API_KEY: 'fixture-key' } }))
      .rejects.toThrow('math_codex_session_binding_mismatch');
    expect(fs.readFileSync(path.join(profile, 'runtime', 'calls.jsonl'), 'utf8')).not.toContain('turn/start');
  });

  it('binds Westlake to a disposable bridge, strips upstream credentials and closes its listener', async () => {
    const profile = path.join(root, 'westlake');
    const nativeProfile = path.join(profile, 'runtime');
    prepareWestlakeProfile(profile, 'deepseek-flash', 'high');
    session = await createCodexMathSession({ ...options, profile, model: 'deepseek-flash', effort: 'high',
      environment: { PATH: process.env.PATH, WESTLAKEHPC_API_KEY: 'upstream-westlake-fixture-secret',
        WESTLAKEHPC_API_KEY_2: 'secondary-westlake-fixture-secret' } });
    expect(JSON.parse(fs.readFileSync(path.join(nativeProfile, 'westlake-environment.json'), 'utf8'))).toEqual({
      receivedLocalCredential: true, receivedSecondaryCredential: false,
    });
    const traffic = fs.readFileSync(path.join(nativeProfile, 'calls.jsonl'), 'utf8');
    expect(traffic).not.toContain('upstream-westlake-fixture-secret');
    expect(traffic).not.toContain('secondary-westlake-fixture-secret');
    const config = traffic.trim().split('\n').map(line => JSON.parse(line)).find(call => call.method === 'thread/start').params.config;
    const base = config['model_providers.westlake.base_url'];
    expect(base).toMatch(/^http:\/\/127\.0\.0\.1:\d+\/v1$/u);
    expect(config['features.multi_agent']).toBe(false);
    expect(config['shell_environment_policy.exclude']).toContain('WESTLAKEHPC_API_KEY*');
    expect((await fetch(base + '/models')).status).toBe(401);
    await session.close();
    await expect(fetch(base + '/models')).rejects.toThrow();
  });

  it.each([
    { provider: 'deepseek', model: 'deepseek-v4-pro', apiKeyEnvironment: 'DEEPSEEK_API_KEY',
      prepare: prepareDeepSeekProfile, profileDigest: deepSeekProfileDigest },
    { provider: 'westlake', model: 'deepseek-flash', apiKeyEnvironment: 'WESTLAKEHPC_API_KEY',
      prepare: prepareWestlakeProfile, profileDigest: westlakeProfileDigest },
  ])('isolates $provider trust writes, refreshes frozen settings and preserves state for resume without copying auth', async ({
    provider, model, apiKeyEnvironment, prepare, profileDigest,
  }) => {
    const profile = path.join(root, provider), nativeProfile = path.join(profile, 'runtime');
    const digest = prepare(profile, model, 'high');
    fs.writeFileSync(path.join(profile, 'auth.json'), 'fixture-auth-must-not-be-copied');
    const config = fs.readFileSync(path.join(profile, 'config.toml'), 'utf8');
    const selected = { ...options, profile, model, effort: 'high',
      environment: { PATH: process.env.PATH, [apiKeyEnvironment]: 'fixture-only' } };
    session = await createCodexMathSession({ ...selected, instructions: 'mutate-profile' });
    expect(await session.run('proof', 'first-turn', root, () => {})).toBe('completed');
    const threadId = session.threadId;
    await session.close();
    expect(profileDigest(profile)).toBe(digest);
    expect(fs.statSync(path.join(profile, 'config.toml')).mode & 0o777).toBe(0o400);
    expect(fs.readFileSync(path.join(nativeProfile, 'config.toml'), 'utf8')).toContain('[projects.fixture]');
    expect(fs.existsSync(path.join(nativeProfile, 'auth.json'))).toBe(false);
    fs.writeFileSync(path.join(nativeProfile, 'state-marker'), 'retained');
    const runtimeConfig = path.join(nativeProfile, 'config.toml');
    fs.writeFileSync(runtimeConfig, fs.readFileSync(runtimeConfig, 'utf8')
      .replace('model_reasoning_effort = "high"', 'model_reasoning_effort = "low"'));
    expect(fs.readFileSync(runtimeConfig, 'utf8')).toContain('model_reasoning_effort = "low"');
    session = await createCodexMathSession({ ...selected, threadId });
    expect(session.threadId).toBe(threadId);
    expect(fs.readFileSync(path.join(nativeProfile, 'config.toml'), 'utf8')).toBe(config);
    expect(fs.readFileSync(path.join(nativeProfile, 'state-marker'), 'utf8')).toBe('retained');
    expect(fs.readFileSync(path.join(nativeProfile, 'calls.jsonl'), 'utf8')).toContain('thread/resume');
    expect(await session.run('proof', 'resumed-turn', root, () => {})).toBe('completed');
    expect(profileDigest(profile)).toBe(digest);
  });

  it('closes the Westlake bridge when app-server startup fails', async () => {
    const profile = path.join(root, 'westlake');
    prepareWestlakeProfile(profile, 'deepseek-flash', 'high');
    await expect(createCodexMathSession({ ...options, profile, model: 'deepseek-flash', effort: 'high',
      instructions: 'wrong-provider', environment: { PATH: process.env.PATH, WESTLAKEHPC_API_KEY: 'fixture-only' } }))
      .rejects.toThrow('math_codex_session_binding_mismatch');
    const traffic = fs.readFileSync(path.join(profile, 'runtime', 'calls.jsonl'), 'utf8');
    const config = traffic.trim().split('\n').map(line => JSON.parse(line)).find(call => call.method === 'thread/start').params.config;
    await expect(fetch(config['model_providers.westlake.base_url'] + '/models')).rejects.toThrow();
  });

  it('reports a missing Westlake credential before starting a bridge or Codex', async () => {
    const profile = path.join(root, 'westlake');
    prepareWestlakeProfile(profile, 'deepseek-flash', 'high');
    vi.stubEnv('WESTLAKEHPC_API_KEY', '');
    await expect(createCodexMathSession({ ...options, profile, environment: { PATH: process.env.PATH } }))
      .rejects.toThrow('math_model_api_key_missing:WESTLAKEHPC_API_KEY');
    expect(fs.readdirSync(profile).sort()).toEqual(['config.toml', 'models.json']);
  });

  it('rejects a missing DeepSeek key before starting any app-server process', async () => {
    const profile = path.join(root, 'deepseek');
    prepareDeepSeekProfile(profile, 'deepseek-v4-pro', 'high');
    vi.stubEnv('DEEPSEEK_API_KEY', '');
    await expect(createCodexMathSession({ ...options, profile, environment: { PATH: process.env.PATH } }))
      .rejects.toThrow('math_model_api_key_missing:DEEPSEEK_API_KEY');
    expect(fs.readdirSync(profile).sort()).toEqual(['config.toml', 'models.json']);
  });

  it('keeps canonical shell filters when excluding a custom provider credential', async () => {
    fs.writeFileSync(path.join(root, 'config.toml'), 'model_provider = "custom"\n[model_providers.custom]\nenv_key = "FIXTURE_API_KEY"\n[shell_environment_policy.filters]\nPATH = "include"\n');
    session = await createCodexMathSession({ ...options, environment: { PATH: process.env.PATH, FIXTURE_API_KEY: 'fixture-key' } });
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
    const config = calls.find(call => call.method === 'thread/start').params.config;
    expect(config['shell_environment_policy.filters']).toEqual({ PATH: 'include', FIXTURE_API_KEY: 'exclude' });
    expect(config).not.toHaveProperty('shell_environment_policy.exclude');
  });

  it('disables inherited MCP tools and handles completion before the start response', async () => {
    session = await createCodexMathSession(options);
    const started = vi.fn();
    expect(await session.run('proof', 'message-1', root, started)).toBe('completed');
    expect(started).toHaveBeenCalledWith('message-1');
    expect(options.onUsage).toHaveBeenCalledWith({ totalTokens: 21 });
    expect(session.lastInputTokens).toBe(12345);
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
    expect(calls.find(call => call.method === 'thread/start').params.config).toMatchObject({
      'features.apps': false, 'features.plugins': false,
    });
    const start = calls.find(call => call.method === 'thread/start').params;
    expect(start.config.mcp_servers.unrelated).toEqual({ enabled: false });
    expect(Object.keys(start.config.mcp_servers)).toEqual(['unrelated']);
    expect(calls.some(call => call.method === 'mcpServerStatus/list')).toBe(false);
    const turn = calls.find(call => call.method === 'turn/start').params;
    expect(turn).toMatchObject({ model: 'gpt-6.1-sol', effort: 'xhigh', approvalPolicy: 'never',
      sandboxPolicy: { type: 'workspaceWrite', writableRoots: [root] } });
  });

  it.each(['oversized-frame', 'invalid-frame', 'invalid-result'])('rejects %s before a complete valid RPC frame', async message => {
    session = await createCodexMathSession(options);
    await expect(session.run(message, 'frame-test', root, () => {})).rejects.toThrow('math_codex_transport_closed');
    expect(session.lastError).toBe('math_codex_transport_closed:' + (message === 'oversized-frame' ? 'frame_too_large' : 'invalid_frame'));
  });

  it('reports bounded activity and split lock markers without exposing content or unrelated threads', async () => {
    const activities: unknown[] = [];
    session = await createCodexMathSession({ ...options, onActivity: value => activities.push(value) });
    expect(await session.run('activity', 'activity-turn', root, () => {})).toBe('completed');
    expect(activities).toEqual([
      { event: 'item_started', itemType: 'commandExecution' },
      { event: 'lean_lock_waiting', itemType: 'commandExecution' },
      { event: 'lean_lock_acquired', itemType: 'commandExecution' },
      { event: 'item_completed', itemType: 'commandExecution' },
    ]);
    expect(JSON.stringify(activities)).not.toMatch(/secret|private reasoning/);
    expect(options.onUsage).toHaveBeenCalledOnce();
  });

  it('rejects an invalid proof environment before launching the app-server', async () => {
    await expect(createCodexMathSession({ ...options, proofProjectRoot: root,
      environment: { DEEPSCIENTIST_MATH_PROOF_ENVIRONMENT: '{}' } })).rejects.toThrow();
    expect(fs.existsSync(path.join(root, 'calls.jsonl'))).toBe(false);
  });

  it('bounds unrelated early completion messages and retains the current completion', async () => {
    session = await createCodexMathSession(options);
    expect(await session.run('noise', 'current', root, () => {})).toBe('completed');
    expect(await session.run('proof', 'unrelated-99', root, () => {})).toBe('completed');
  });

  it('resumes the existing thread and interrupts an active turn', async () => {
    session = await createCodexMathSession({ ...options, threadId: 'retained-thread' });
    expect(session.threadId).toBe('retained-thread');
    let started = false;
    const done = session.run('wait', 'message-2', root, () => { started = true; });
    await expect.poll(() => started).toBe(true);
    await expect(session.run('second', 'message-3', root, () => {})).rejects.toThrow('math_codex_turn_already_running');
    await session.interrupt();
    expect(await done).toBe('interrupted');
  });

  it('steers a live turn with its exact turn precondition and skips idle notifications', async () => {
    session = await createCodexMathSession(options);
    await session.notify!('idle');
    let started = false;
    const done = session.run('wait', 'active-turn', root, () => { started = true; });
    await expect.poll(() => started).toBe(true);
    await session.notify!('A checked dependency is available');
    await session.interrupt();
    expect(await done).toBe('interrupted');
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
    expect(calls.filter(call => call.method === 'turn/steer').map(call => call.params)).toEqual([{
      threadId: 'thread-fixture', expectedTurnId: 'active-turn',
      input: [{ type: 'text', text: 'A checked dependency is available', text_elements: [] }],
    }]);
  });

  it.each(['rate-limit', 'late-rate-limit', 'stream-disconnected'])('retains the failure reason and clears it on the next turn (%s)', async message => {
    session = await createCodexMathSession(options);
    expect(await session.run(message, 'failed-turn', root, () => {})).toBe('failed');
    expect(session.lastError).toBe(message === 'stream-disconnected'
      ? 'stream disconnected before completion: error sending request' : 'Concurrency limit exceeded for account');
    expect(await session.run('proof', 'next-turn', root, () => {})).toBe('completed');
    expect(session.lastError).toBeUndefined();
  });

  it.each([
    ['structured-unauthorized', { code: 'unauthorized' }],
    ['structured-rate-limit', { code: 'httpConnectionFailed', httpStatusCode: 429 }],
    ['structured-disconnected', { code: 'responseStreamDisconnected', httpStatusCode: 503 }],
    ['structured-invalid-status', { code: 'httpConnectionFailed' }],
    ['structured-string-status', { code: 'httpConnectionFailed' }],
    ['structured-unrelated-status', { code: 'badRequest' }],
    ['structured-unknown', undefined],
    ['structured-multiple', undefined],
  ] as const)('retains only allowlisted failure metadata and clears it after %s', async (message, expected) => {
    session = await createCodexMathSession(options);
    expect(await session.run(message, 'failed-turn', root, () => {})).toBe('failed');
    expect(session.lastFailureDiagnostic).toEqual(expected);
    expect(JSON.stringify(session.lastFailureDiagnostic) ?? '').not.toMatch(/private|body|message|additionalDetails/);
    expect(await session.run('proof', 'next-turn', root, () => {})).toBe('completed');
    expect(session.lastFailureDiagnostic).toBeUndefined();
  });

  it('interrupts a long turn for a checkpoint and keeps the session usable', async () => {
    session = await createCodexMathSession({ ...options, turnTimeoutMs: 30 });
    expect(await session.run('wait', 'long-turn', root, () => {})).toBe('checkpoint');
    expect(await session.run('proof', 'next-turn', root, () => {})).toBe('completed');
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
    expect(calls.filter(call => call.method === 'turn/interrupt')).toHaveLength(1);
  });

  it('rejects a mismatched model before any provider request and fails a disconnected turn', async () => {
    await expect(createCodexMathSession({ ...options, instructions: 'mismatch' })).rejects.toThrow('math_codex_session_binding_mismatch');
    await expect(createCodexMathSession({ ...options, threadId: 'retained-thread', instructions: 'wrong-thread' })).rejects.toThrow('math_codex_session_binding_mismatch');
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8');
    expect(calls).not.toContain('turn/start');
    session = await createCodexMathSession(options);
    await expect(session.run('crash', 'message-4', root, () => {})).rejects.toThrow('math_codex_transport_closed');
    expect(session.lastError).toBe('math_codex_transport_closed:process_exit:code=9:signal=none');
  });

  it('reports a process exit while restoring a saved thread', async () => {
    await expect(createCodexMathSession({ ...options, threadId: 'retained-thread', instructions: 'startup-crash' }))
      .rejects.toThrow('math_codex_transport_closed:process_exit:code=27:signal=none');
  });

  it.each(['thread/resume', 'turn/start'])('identifies the failed %s RPC without exposing provider diagnostics', async method => {
    const settings = { ...options, threadId: 'retained-thread',
      environment: { ...process.env, THEOREM_OS_FIXTURE_RPC_FAILURE: method } };
    const expected = `math_codex_rpc_failed:-32600:${method}`;
    if (method === 'thread/resume') await expect(createCodexMathSession(settings)).rejects.toMatchObject({ message: expected });
    else {
      session = await createCodexMathSession(settings);
      await expect(session.run('proof', 'failed-turn', root, () => {})).rejects.toMatchObject({ message: expected });
      expect(session.lastError).toBe(expected);
    }
  });

  it('keeps an invalid RPC error code out of the public failure', async () => {
    await expect(createCodexMathSession({ ...options, threadId: 'retained-thread', environment: {
      ...process.env, THEOREM_OS_FIXTURE_RPC_FAILURE: 'thread/resume', THEOREM_OS_FIXTURE_RPC_CODE: 'private provider credential',
    } })).rejects.toMatchObject({ message: 'math_codex_rpc_failed:invalid_code:thread/resume' });
  });
});
