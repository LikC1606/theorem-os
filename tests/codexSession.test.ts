import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { createCodexMathSession, type MathAgentOptions, type MathAgentSession } from '../src/runtime/codexSession';

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
let settings, turn, catalogs = 0;
const send = value => process.stdout.write(JSON.stringify(value) + '\\n');
readline.createInterface({ input: process.stdin }).on('line', line => {
  const call = JSON.parse(line);
  fs.appendFileSync(process.env.CODEX_HOME + '/calls.jsonl', JSON.stringify(call) + '\\n');
  const result = value => send({ id: call.id, result: value });
  if (call.method === 'initialize') result({});
  if (call.method === 'thread/start' || call.method === 'thread/resume') {
    settings = call.params;
    result({ thread: { id: settings.developerInstructions === 'wrong-thread' ? 'wrong-thread' : settings.threadId || 'thread-fixture' },
      model: settings.developerInstructions === 'mismatch' ? 'wrong-model' : settings.model,
      approvalPolicy: settings.approvalPolicy, reasoningEffort: settings.config.model_reasoning_effort });
  }
  if (call.method === 'mcpServerStatus/list') result({ data: Object.keys(settings.config.mcp_servers)
    .filter(name => settings.config.mcp_servers[name].enabled).map(name => ({ name,
      runtimeStatus: ++catalogs === 1 ? 'starting' : 'connected', tools: catalogs === 1 ? {} : { math: {} }, toolsError: null })), nextCursor: null });
  if (call.method === 'turn/start') {
    turn = { id: call.params.clientUserMessageId, status: 'inProgress' };
    const message = call.params.input[0].text;
    if (message === 'crash') return process.exit(9);
    if (message !== 'wait') {
      send({ method: 'thread/tokenUsage/updated', params: { threadId: 'thread-fixture', tokenUsage: { total: { totalTokens: 21 }, last: { inputTokens: 12345 } } } });
      const failed = message === 'rate-limit' || message === 'late-rate-limit';
      const complete = () => send({ method: 'turn/completed', params: { threadId: 'thread-fixture', turn: { ...turn,
        status: failed ? 'failed' : 'completed', ...(failed ? { error: { message: 'Concurrency limit exceeded for account' } } : {}) } } });
      if (message === 'late-rate-limit') setImmediate(complete);
      else complete();
    }
    result({ turn });
  }
  if (call.method === 'turn/interrupt') {
    send({ method: 'turn/completed', params: { threadId: 'thread-fixture', turn: { ...turn, status: 'interrupted' } } });
    result({});
  }
});
`);
    fs.chmodSync(executable, 0o700);
    options = { executable, profile: root, workspace: root, model: 'gpt-6.1-sol', effort: 'xhigh',
      instructions: 'Prove the mathematical target', onUsage: vi.fn() };
    session = undefined;
  });
  afterEach(async () => { await session?.close(); fs.rmSync(root, { recursive: true, force: true }); });

  it('disables inherited MCP tools and handles completion before the start response', async () => {
    session = await createCodexMathSession(options);
    const started = vi.fn();
    expect(await session.run('proof', 'message-1', root, started)).toBe('completed');
    expect(started).toHaveBeenCalledWith('message-1');
    expect(options.onUsage).toHaveBeenCalledWith({ totalTokens: 21 });
    expect(session.lastInputTokens).toBe(12345);
    const calls = fs.readFileSync(path.join(root, 'calls.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
    const start = calls.find(call => call.method === 'thread/start').params;
    expect(start.config.mcp_servers.unrelated).toEqual({ enabled: false });
    expect(Object.keys(start.config.mcp_servers)).toEqual(['unrelated']);
    expect(calls.some(call => call.method === 'mcpServerStatus/list')).toBe(false);
    const turn = calls.find(call => call.method === 'turn/start').params;
    expect(turn).toMatchObject({ model: 'gpt-6.1-sol', effort: 'xhigh', approvalPolicy: 'never',
      sandboxPolicy: { type: 'workspaceWrite', writableRoots: [root] } });
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

  it.each(['rate-limit', 'late-rate-limit'])('retains the failure reason and clears it on the next turn (%s)', async message => {
    session = await createCodexMathSession(options);
    expect(await session.run(message, 'failed-turn', root, () => {})).toBe('failed');
    expect(session.lastError).toBe('Concurrency limit exceeded for account');
    expect(await session.run('proof', 'next-turn', root, () => {})).toBe('completed');
    expect(session.lastError).toBeUndefined();
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
  });
});
