#!/usr/bin/env bun
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { parseArgs } from 'node:util';
import { createCodexMathSession, type MathAgentSession } from '../../src/runtime/codexSession';
import { startChatCompletionsBridge } from '../../src/runtime/chatCompletionsBridge';
import type { ModelRequestGate, ModelRequestReceipt } from '../../src/runtime/modelRequest';
import { prepareWestlakeProfile, westlakeProfileDigest, WESTLAKE_PROVIDER } from '../../src/runtime/westlake';
import { beginRequestUsage, buildTokenBudget, initializeRequestUsageAccounting, modelDispatchAllowed,
  type RequestUsageAccounting } from '../../src/solver/usageBudget';

type Json = Record<string, any>;
type Scenario = { name: string; usage: [boolean, boolean]; maxTotalTokens?: number };
const dummyKey = 'theoremos-offline-westlake-dummy-key';
const toolMarker = 'THEOREMOS_LOCAL_PROTOCOL_OK';
const patchMarker = 'THEOREMOS_LOCAL_PATCH_OK';
const finalMarker = 'THEOREMOS_LOCAL_PROTOCOL_COMPLETE';
const firstReasoning = 'The local fixture needs one harmless shell command.';
const upstreamUrl = `${WESTLAKE_PROVIDER.baseUrl}/chat/completions`;

function sse(chunks: Json[]): string {
  return chunks.map(chunk => `data: ${JSON.stringify(chunk)}\n\n`).join('') + 'data: [DONE]\n\n';
}

function completionChunks(index: number, delta: Json[], finishReason: string, usage: Json | undefined): Json[] {
  const common = { id: `chatcmpl-local-${index}`, object: 'chat.completion.chunk',
    created: 1, model: WESTLAKE_PROVIDER.defaultModel };
  return [...delta.map(value => ({ ...common, choices: [{ index: 0, delta: value, finish_reason: null, stop_reason: null, token_ids: null }] })),
    { ...common, choices: [{ index: 0, delta: {}, finish_reason: finishReason, stop_reason: null, token_ids: null }] },
    ...(usage ? [{ ...common, choices: [], usage }] : [])];
}

function transcriptMessages(directory: string): Json[] {
  if (!fs.existsSync(directory)) return [];
  return fs.readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const file = path.join(directory, entry.name);
    if (entry.isDirectory()) return transcriptMessages(file);
    if (!entry.isFile() || !entry.name.endsWith('.jsonl')) return [];
    return fs.readFileSync(file, 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line));
  });
}

async function closeServer(server: http.Server): Promise<void> {
  server.closeAllConnections();
  if (server.listening) await new Promise<void>((resolve, reject) =>
    server.close(error => error ? reject(error) : resolve()));
}

async function checkScenario(executable: string, scenario: Scenario): Promise<void> {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'theoremos-westlake-protocol-'));
  const profile = path.join(root, 'profile'), workspace = path.join(root, 'workspace'), home = path.join(root, 'home');
  fs.mkdirSync(workspace); fs.mkdirSync(home);
  // Deliberately avoid inheriting credentials, global profiles, proxies, or user shell startup files.
  const environment: NodeJS.ProcessEnv = { PATH: process.env.PATH, HOME: home, TMPDIR: root,
    WESTLAKEHPC_API_KEY: dummyKey, NO_PROXY: '127.0.0.1,localhost' };
  const originalFetch = globalThis.fetch;
  let session: MathAgentSession | undefined;
  let lifecycleBridge: Awaited<ReturnType<typeof startChatCompletionsBridge>> | undefined;
  let mockFailure: unknown, blockedRequests = 0, requests = 0, incompleteSignals = 0;
  let tools: string[] = [];
  const usage: Json[] = [], activities: string[] = [];
  const requestRecord: { turns: number; usage?: Record<string, unknown>; requestUsageAccounting?: RequestUsageAccounting } = { turns: 0 };
  const requestReceipts: ModelRequestReceipt[] = [], deniedReasons: string[] = [];
  const limited = scenario.maxTotalTokens !== undefined;
  if (limited) initializeRequestUsageAccounting(requestRecord);
  const requestBudget = () => buildTokenBudget(scenario.maxTotalTokens ?? 0, [requestRecord],
    'provider-observed-upstream-request-limit');
  const requestGate: ModelRequestGate | undefined = !limited ? undefined : () => {
    const budget = requestBudget();
    if (!modelDispatchAllowed(budget)) {
      const reason = budget.reason ?? 'math_model_request_stopped';
      deniedReasons.push(reason);
      return { allowed: false, reason };
    }
    const settle = beginRequestUsage(requestRecord);
    return { allowed: true, settle: receipt => {
      requestReceipts.push(receipt);
      settle(receipt);
    } };
  };
  const server = http.createServer(async (request, response) => {
    try {
      assert.equal(request.method, 'POST', 'mock_method_mismatch');
      assert.equal(request.url, '/v1/chat/completions', 'mock_path_mismatch');
      assert.equal(request.headers.authorization, `Bearer ${dummyKey}`, 'mock_credential_mismatch');
      const parts: Buffer[] = [];
      for await (const chunk of request) parts.push(Buffer.from(chunk));
      const body = JSON.parse(Buffer.concat(parts).toString('utf8'));
      assert.equal(body.model, WESTLAKE_PROVIDER.defaultModel, 'mock_model_mismatch');
      assert.equal(body.stream, true, 'mock_stream_required');
      assert.equal(body.reasoning_effort, 'high', 'mock_effort_mismatch');
      assert.ok(Array.isArray(body.messages), 'mock_messages_missing');
      assert.ok(body.messages.every((message: Json) => ['system', 'user', 'assistant', 'tool'].includes(message.role)),
        'mock_gateway_rejects_unsupported_message_role');
      assert.equal(JSON.stringify(body.messages).includes(dummyKey), false, 'mock_key_in_model_context');
      requests++;
      let chunks: Json[];
      if (requests === 1) {
        assert.ok(Array.isArray(body.tools), 'mock_tools_missing');
        tools = body.tools.map((tool: Json) => tool.function?.name);
        const command = body.tools.find((tool: Json) => tool.function?.name === 'exec_command');
        assert.ok(command, 'mock_actual_exec_command_missing');
        assert.ok(command.function.parameters.required.includes('cmd'), 'mock_command_schema_mismatch');
        const patchTool = body.tools.find((tool: Json) => tool.function?.name === 'apply_patch');
        assert.ok(patchTool?.function.parameters.required.includes('input'), 'mock_custom_patch_schema_mismatch');
        assert.ok(body.tools.every((tool: Json) => tool.type === 'function'), 'mock_non_chat_tool');
        const args = JSON.stringify({ cmd: `printf ${toolMarker}`, login: false, max_output_tokens: 100 });
        const patchArgs = JSON.stringify({ input: `*** Begin Patch\n*** Add File: protocol-check.txt\n+${patchMarker}\n*** End Patch` });
        const split = Math.floor(args.length / 2);
        chunks = completionChunks(1, [
          { role: 'assistant', reasoning_content: firstReasoning },
          { tool_calls: [{ index: 0, id: 'local_command_call', type: 'function',
            function: { name: 'exec_command', arguments: args.slice(0, split) } }] },
          { tool_calls: [{ index: 0, function: { arguments: args.slice(split) } }] },
          { tool_calls: [{ index: 1, id: 'local_patch_call', type: 'function',
            function: { name: 'apply_patch', arguments: patchArgs } }] },
        ], 'tool_calls', scenario.usage[0] ? { prompt_tokens: 25, completion_tokens: 8, total_tokens: 33,
          prompt_tokens_details: { cached_tokens: 3 }, completion_tokens_details: { reasoning_tokens: 4 } } : undefined);
      } else {
        assert.equal(requests, 2, 'mock_unexpected_extra_inference');
        const toolResult = body.messages.find((message: Json) => message.role === 'tool'
          && message.tool_call_id === 'local_command_call');
        assert.ok(toolResult, 'mock_tool_result_missing');
        assert.match(toolResult.content, /Process exited with code 0/u, 'mock_native_command_failed');
        assert.ok(toolResult.content.includes(toolMarker), 'mock_native_command_did_not_execute');
        const patchResult = body.messages.find((message: Json) => message.role === 'tool'
          && message.tool_call_id === 'local_patch_call');
        assert.ok(patchResult, 'mock_custom_patch_result_missing');
        assert.equal(fs.readFileSync(path.join(workspace, 'protocol-check.txt'), 'utf8'), `${patchMarker}\n`,
          'mock_native_patch_did_not_execute');
        const assistant = body.messages.find((message: Json) => message.role === 'assistant'
          && message.tool_calls?.some((call: Json) => call.id === 'local_command_call'));
        assert.equal(assistant?.reasoning_content, firstReasoning, 'mock_reasoning_not_preserved');
        chunks = completionChunks(2, [
          { role: 'assistant', reasoning_content: 'The local command returned its expected marker.' },
          { content: finalMarker.slice(0, 17) }, { content: finalMarker.slice(17) },
        ], 'stop', scenario.usage[1] ? { prompt_tokens: 36, completion_tokens: 6, total_tokens: 42,
          prompt_tokens_details: { cached_tokens: 4 }, completion_tokens_details: { reasoning_tokens: 2 } } : undefined);
      }
      response.writeHead(200, { 'content-type': 'text/event-stream', 'cache-control': 'no-cache' });
      response.end(sse(chunks));
    } catch (error) {
      mockFailure = error;
      response.writeHead(400, { 'content-type': 'application/json' });
      response.end(JSON.stringify({ error: { message: 'local_protocol_fixture_rejected_request' } }));
    }
  });
  const onSignal = () => { void session?.close(); };
  process.once('SIGINT', onSignal); process.once('SIGTERM', onSignal);
  let deadline: ReturnType<typeof setTimeout> | undefined;
  try {
    const version = execFileSync(executable, ['--version'], { encoding: 'utf8', env: environment,
      stdio: ['ignore', 'pipe', 'ignore'], timeout: 10_000 }).trim();
    assert.match(version, /^codex-cli [0-9][0-9.\w-]*$/u, 'codex_version_unrecognized');
    const profileDigest = prepareWestlakeProfile(profile, WESTLAKE_PROVIDER.defaultModel, 'high');
    await new Promise<void>((resolve, reject) => {
      server.once('error', reject);
      server.listen(0, '127.0.0.1', resolve);
    });
    const address = server.address();
    assert.ok(address && typeof address !== 'string', 'mock_listener_missing');
    const localUpstream = `http://127.0.0.1:${address.port}/v1/chat/completions`;
    // The only permitted host fetch is rewritten to loopback, including when a real key exists in the parent.
    globalThis.fetch = (async (input, init) => {
      const request = new Request(input, init);
      if (request.url !== upstreamUrl) { blockedRequests++; throw new Error('offline_check_blocked_non_gateway_url'); }
      assert.equal(request.headers.get('authorization'), `Bearer ${dummyKey}`, 'host_credential_mismatch');
      return originalFetch(new Request(localUpstream, request));
    }) as typeof fetch;
    session = await createCodexMathSession({ executable, profile, workspace,
      model: WESTLAKE_PROVIDER.defaultModel, effort: 'high', environment,
      instructions: 'This is an offline protocol fixture. Use the harmless local command returned by the simulated model. Do not access the network.',
      turnTimeoutMs: 30_000, onUsage: value => usage.push(value),
      onUsageIncomplete: () => { incompleteSignals++; },
      requestGate,
      onActivity: value => activities.push(`${value.event}:${value.itemType ?? ''}`) });
    assert.equal(session.usageSource, limited ? 'upstream-requests' : undefined, 'native_usage_source_mismatch');
    deadline = setTimeout(() => { void session?.close(); }, 45_000);
    const status = await session.run('Run the local protocol check and report its completion marker.',
      'westlake-offline-protocol-check', workspace, () => {});
    const incompleteAtTurnCompletion = incompleteSignals;
    if (mockFailure) throw mockFailure;
    assert.equal(status, limited ? 'failed' : 'completed', `native_turn_${status}:${session.lastError ?? 'no_diagnostic'}`);
    assert.equal(requests, limited ? 1 : 2, 'native_tool_roundtrip_upstream_request_count_mismatch');
    assert.equal(blockedRequests, 0, 'native_attempted_forbidden_host_fetch');
    if (limited) {
      assert.match(session.lastError ?? '', /\b403\b/u, 'native_budget_denial_not_http_403');
      const reason = scenario.usage[0] ? 'math_total_token_limit' : 'math_model_usage_unavailable';
      assert.ok(session.lastError?.includes(reason), 'native_budget_denial_reason_missing');
      assert.deepEqual(deniedReasons, [reason], 'native_budget_denial_retried_or_bypassed');
      assert.ok(activities.includes('item_completed:commandExecution'), 'native_budget_tool_did_not_execute');
      assert.equal(fs.readFileSync(path.join(workspace, 'protocol-check.txt'), 'utf8'), `${patchMarker}\n`,
        'native_budget_patch_did_not_execute');
      assert.equal(activities.includes('item_completed:agentMessage'), false, 'native_budget_generated_final_message');
      assert.equal(requestReceipts.length, 1, 'native_local_denial_created_request_receipt');
      assert.deepEqual(requestReceipts[0], { complete: scenario.usage[0], usage: scenario.usage[0] ? {
        inputTokens: 25, cachedInputTokens: 3, outputTokens: 8, reasoningOutputTokens: 4, totalTokens: 33,
      } : undefined }, 'native_request_receipt_mismatch');
      assert.deepEqual(requestRecord.requestUsageAccounting, { startedRequests: 1,
        reportedRequests: Number(scenario.usage[0]), pendingRequests: 0, incomplete: !scenario.usage[0] },
      'native_local_denial_changed_usage_accounting');
      assert.equal(requestBudget().status, scenario.usage[0] ? 'exhausted' : 'usage-unavailable', 'native_request_budget_status_mismatch');
      assert.equal(requestBudget().reportedTotalTokens, scenario.usage[0] ? 33 : null, 'native_thread_counter_double_counted');
      assert.equal(requestBudget().usageComplete, scenario.usage[0], 'native_request_budget_completeness_mismatch');
    } else assert.ok(activities.includes('item_completed:agentMessage'), 'native_final_message_event_missing');
    const threadId = session.threadId;
    await session.close(); session = undefined;
    assert.equal(westlakeProfileDigest(profile), profileDigest, 'native_mutated_frozen_profile');
    session = await createCodexMathSession({ executable, profile, workspace, threadId,
      model: WESTLAKE_PROVIDER.defaultModel, effort: 'high', environment,
      instructions: 'This is an offline protocol fixture. Do not access the network.',
      onUsage: () => {}, requestGate });
    assert.equal(session.threadId, threadId, 'native_resume_changed_thread');
    await session.close(); session = undefined;
    assert.equal(requests, limited ? 1 : 2, 'native_resume_made_unexpected_inference');
    assert.equal(westlakeProfileDigest(profile), profileDigest, 'native_resume_mutated_frozen_profile');
    const first = Number(scenario.usage[0]), second = limited ? 0 : Number(scenario.usage[1]);
    const expectedUsage = first + second ? { inputTokens: 25 * first + 36 * second,
      cachedInputTokens: 3 * first + 4 * second, outputTokens: 8 * first + 6 * second,
      reasoningOutputTokens: 4 * first + 2 * second, totalTokens: 33 * first + 42 * second } : null;
    if (expectedUsage) {
      for (const [name, value] of Object.entries(expectedUsage))
        assert.equal(usage.at(-1)?.[name], value, `native_usage_mismatch_${name}`);
    } else assert.equal(usage.length, 0, 'native_missing_usage_generated_event');
    assert.equal(incompleteAtTurnCompletion, (limited ? 1 : 2) - first - second, 'native_usage_incomplete_signal_missing_before_turn_completion');
    assert.equal(incompleteSignals, incompleteAtTurnCompletion, 'native_usage_incomplete_signal_arrived_after_turn_completion');
    const records = transcriptMessages(path.join(profile, 'runtime', 'sessions'));
    const finalMessage = records.find(record => record.type === 'response_item'
      && record.payload?.type === 'message' && record.payload.role === 'assistant'
      && record.payload.content?.some((part: Json) => part.type === 'output_text' && part.text === finalMarker));
    assert.equal(Boolean(finalMessage), !limited, 'native_final_transcript_mismatch');
    if (limited) {
      assert.ok(records.some(record => record.type === 'response_item' && record.payload?.type === 'function_call_output'
        && record.payload.call_id === 'local_command_call' && typeof record.payload.output === 'string'
        && record.payload.output.includes(toolMarker) && /Process exited with code 0/u.test(record.payload.output)),
      'native_budget_command_receipt_missing');
      assert.equal(requestReceipts.length, 1, 'native_resume_created_request_receipt');
    }
    assert.equal(JSON.stringify(records).includes(dummyKey), false, 'native_key_in_transcript');
    lifecycleBridge = await startChatCompletionsBridge({ baseUrl: WESTLAKE_PROVIDER.baseUrl,
      apiKey: dummyKey, model: WESTLAKE_PROVIDER.defaultModel, effort: 'high' });
    const bridgeUrl = `${lifecycleBridge.baseUrl}/responses`;
    await lifecycleBridge.close();
    await lifecycleBridge.close();
    let listenerClosed = false;
    try { await originalFetch(bridgeUrl, { signal: AbortSignal.timeout(2_000) }); }
    catch { listenerClosed = true; }
    assert.equal(listenerClosed, true, 'native_bridge_listener_remained_open');
    console.log(JSON.stringify({ status: 'passed', scenario: scenario.name, codex: version, model: WESTLAKE_PROVIDER.defaultModel,
      simulatedRequests: requests, tools, toolRoundTrip: !limited, freeformToolRoundTrip: !limited, reasoningRoundTrip: !limited,
      finalMessage: !limited, usage: expectedUsage, usageEvents: usage.length, incompleteSignals, incompleteAtTurnCompletion,
      ...(limited ? { toolsExecutedBeforeLocalDenial: true, localDeniedRequests: deniedReasons.length, localDenialStatus: 403,
        requestReceipts: requestReceipts.length, requestBudget: requestBudget(), nativeUsageIgnored: true } : {}),
      bridgeListenerClosed: true, frozenProfileUnchanged: true, resumedThread: true, remoteRequests: 0 }));
  } finally {
    clearTimeout(deadline);
    process.removeListener('SIGINT', onSignal); process.removeListener('SIGTERM', onSignal);
    try { await session?.close(); } finally {
      try { await lifecycleBridge?.close(); } finally {
        globalThis.fetch = originalFetch;
        await closeServer(server);
        fs.rmSync(root, { recursive: true, force: true });
      }
    }
  }
}

async function main(): Promise<void> {
  const { values } = parseArgs({ options: { codex: { type: 'string', default: 'codex' }, help: { type: 'boolean' } } });
  if (values.help) {
    console.log('Usage: bun scripts/mathematics/checkWestlakeProtocol.ts [--codex PATH]\nRuns installed Codex against a local simulated gateway. Covers complete, partially missing and fully missing token usage, plus request budget exhaustion and missing-usage admission stops. No model calls or real credentials are used.');
    return;
  }
  const scenarios: Scenario[] = [
    { name: 'complete-usage', usage: [true, true] },
    { name: 'missing-final-usage', usage: [true, false] },
    { name: 'missing-initial-usage', usage: [false, true] },
    { name: 'missing-all-usage', usage: [false, false] },
    { name: 'request-budget-exhausted', usage: [true, true], maxTotalTokens: 33 },
    { name: 'request-budget-missing-usage', usage: [false, true], maxTotalTokens: 100 },
  ];
  for (const scenario of scenarios) await checkScenario(values.codex, scenario);
}

void main().catch(error => {
  const message = error instanceof Error ? error.message.split('\n')[0] : 'unknown_error';
  console.error(JSON.stringify({ status: 'failed', reason: message }));
  process.exitCode = 1;
});
