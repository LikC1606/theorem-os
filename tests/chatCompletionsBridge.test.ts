import { createServer, request as httpRequest, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import type { AddressInfo } from 'node:net';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { createParser } from 'eventsource-parser';
import type { ModelRequestGate, ModelRequestReceipt } from '../src/runtime/modelRequest';
import { beginRequestUsage, buildTokenBudget, initializeRequestUsageAccounting, modelDispatchAllowed,
  type RequestUsageAccounting } from '../src/solver/usageBudget';
import { startChatCompletionsBridge } from '../src/runtime/chatCompletionsBridge';

type Bridge = Awaited<ReturnType<typeof startChatCompletionsBridge>>;
const actualFetch = globalThis.fetch;
const servers: Server[] = [], bridges: Bridge[] = [];
const upstreamKey = 'fixture-upstream-secret';
const basic = { model: 'deepseek-flash', stream: true, store: false, input: 'Prove the target.', reasoning: { effort: 'high' } };
const functions = [{ type: 'function', name: 'exec_command', parameters: { type: 'object', properties: { cmd: { type: 'string' } } } },
  { type: 'custom', name: 'apply_patch', description: 'Edit a source file', format: { type: 'grammar', syntax: 'lark', definition: 'start: /.+/' } }];
async function upstream(handler: (request: IncomingMessage, response: ServerResponse, body: any) => void) {
  const server = createServer(async (request, response) => {
    const chunks: Buffer[] = [];
    for await (const chunk of request) chunks.push(Buffer.from(chunk));
    handler(request, response, JSON.parse(Buffer.concat(chunks).toString()));
  });
  servers.push(server);
  await new Promise<void>(resolve => server.listen(0, '127.0.0.1', resolve));
  return `http://127.0.0.1:${(server.address() as AddressInfo).port}/v1`;
}
async function bridge(baseUrl: string, onUsageIncomplete?: () => void, requestGate?: ModelRequestGate) {
  const value = await startChatCompletionsBridge({ baseUrl, apiKey: upstreamKey, model: 'deepseek-flash', effort: 'high', onUsageIncomplete, requestGate });
  bridges.push(value); return value;
}
const post = (value: Bridge, body: unknown = basic, headers: Record<string, string> = {}) => actualFetch(`${value.baseUrl}/responses`, {
  method: 'POST', headers: { Authorization: `Bearer ${value.apiKey}`, 'Content-Type': 'application/json', ...headers }, body: JSON.stringify(body),
});
const chunk = (delta: unknown, finish_reason: string | null = null) => ({ choices: [{ index: 0, delta, finish_reason }] });
function sse(response: ServerResponse, values: unknown[], done = true) {
  response.writeHead(200, { 'Content-Type': 'text/event-stream' });
  for (const value of values) response.write(`data: ${JSON.stringify(value)}\r\n\r\n`);
  if (done) response.write('data: [DONE]\r\n\r\n');
  response.end();
}
async function events(response: Response): Promise<any[]> {
  const result: unknown[] = [];
  const parser = createParser({ onEvent: event => result.push(JSON.parse(event.data)), onError: error => { throw error; } });
  parser.feed(await response.text()); return result;
}
const completed = (values: any[]) => values.find(event => event.type === 'response.completed')?.response;
afterEach(async () => {
  vi.unstubAllGlobals();
  await Promise.all(bridges.splice(0).map(value => value.close()));
  await Promise.all(servers.splice(0).map(server => new Promise<void>(resolve => { server.close(() => resolve()); server.closeAllConnections(); })));
});

describe('upstream request budget across session bridges', () => {
  function budget(limit: number, workerCount = 1) {
    const records = Array.from({ length: workerCount }, () => ({ turns: 0,
      usage: undefined as Record<string, unknown> | undefined,
      requestUsageAccounting: undefined as RequestUsageAccounting | undefined }));
    for (const record of records) initializeRequestUsageAccounting(record);
    const receipts: ModelRequestReceipt[] = [];
    const status = () => buildTokenBudget(limit, records, 'provider-observed-upstream-request-limit');
    const gate = (worker: number): ModelRequestGate => () => {
      const current = status();
      if (!modelDispatchAllowed(current)) return { allowed: false, reason: current.reason! };
      const settle = beginRequestUsage(records[worker]);
      return { allowed: true, settle: receipt => { receipts.push(receipt); settle(receipt); } };
    };
    return { records, receipts, status, gate };
  }
  const usage = (total: number) => ({ choices: [], usage: { prompt_tokens: total - 2, completion_tokens: 2, total_tokens: total,
    prompt_tokens_details: { cached_tokens: 3 }, completion_tokens_details: { reasoning_tokens: 1 } } });

  it('blocks the next request and repeated client retries before fetch, retaining complete receipts', async () => {
    let calls = 0;
    const shared = budget(20), incomplete = vi.fn();
    const url = await upstream((_request, response) => { calls++; sse(response, [chunk({ content: 'ok' }), chunk({}, 'stop'), usage(25)]); });
    const value = await bridge(url, incomplete, shared.gate(0));
    expect(completed(await events(await post(value)))).toBeDefined();
    expect(shared.receipts).toEqual([{ complete: true, usage: { inputTokens: 23, outputTokens: 2, totalTokens: 25,
      cachedInputTokens: 3, reasoningOutputTokens: 1 } }]);
    for (let retry = 0; retry < 3; retry++) {
      const response = await post(value);
      expect(response.status).toBe(403);
      expect((await response.json() as any).error.code).toBe('math_total_token_limit');
    }
    expect(calls).toBe(1); expect(incomplete).not.toHaveBeenCalled();
    expect(shared.status()).toMatchObject({ status: 'exhausted', reportedTotalTokens: 25, overrunTokens: 5, usageComplete: true });
    expect(shared.records[0].requestUsageAccounting).toMatchObject({ startedRequests: 1, reportedRequests: 1, pendingRequests: 0 });
  });

  it('shares receipts across bridges while retaining usage from peers already in flight', async () => {
    const pending: ServerResponse[] = [];
    const shared = budget(50, 2);
    const url = await upstream((_request, response) => { pending.push(response); });
    const first = await bridge(url, undefined, shared.gate(0)), second = await bridge(url, undefined, shared.gate(1));
    const firstResponse = post(first), secondResponse = post(second);
    await expect.poll(() => pending.length).toBe(2);
    expect(shared.status()).toMatchObject({ status: 'available', reportedTotalTokens: null, usageComplete: false });
    expect(shared.records.map(record => record.requestUsageAccounting?.pendingRequests)).toEqual([1, 1]);
    sse(pending[0], [chunk({ content: 'first' }), chunk({}, 'stop'), usage(60)]);
    expect(completed(await events(await firstResponse))).toBeDefined();
    expect((await post(second)).status).toBe(403);
    sse(pending[1], [chunk({ content: 'second' }), chunk({}, 'stop'), usage(40)]);
    expect(completed(await events(await secondResponse))).toBeDefined();
    expect(shared.status()).toMatchObject({ status: 'exhausted', reportedTotalTokens: 100, overrunTokens: 50, usageComplete: true });
    expect(pending).toHaveLength(2);
  });

  it('blocks all subsequent requests when a completed response omits usage', async () => {
    let calls = 0;
    const shared = budget(100, 2), incomplete = vi.fn();
    const url = await upstream((_request, response) => { calls++; sse(response, [chunk({ content: 'unknown cost' }), chunk({}, 'stop')]); });
    const first = await bridge(url, incomplete, shared.gate(0)), second = await bridge(url, incomplete, shared.gate(1));
    expect(completed(await events(await post(first)))).toBeDefined();
    for (const value of [first, second]) {
      const response = await post(value);
      expect(response.status).toBe(403);
      expect((await response.json() as any).error.code).toBe('math_model_usage_unavailable');
    }
    expect(calls).toBe(1); expect(incomplete).toHaveBeenCalledOnce();
    expect(shared.status()).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: null, usageComplete: false });
    expect(shared.receipts).toEqual([{ complete: false, usage: undefined }]);
    expect(shared.records[1].requestUsageAccounting?.startedRequests).toBe(0);
  });

  it('settles transport failures once and rejects retries without upstream consumption', async () => {
    const shared = budget(100), incomplete = vi.fn();
    const value = await bridge('https://provider.invalid/v1', incomplete, shared.gate(0));
    const fetch = vi.fn(async () => { throw new Error('offline transport failure'); });
    vi.stubGlobal('fetch', fetch);
    expect((await post(value)).status).toBe(502);
    expect((await post(value)).status).toBe(403);
    expect(fetch).toHaveBeenCalledOnce(); expect(incomplete).toHaveBeenCalledOnce();
    expect(shared.receipts).toEqual([{ complete: false, usage: undefined }]);
    expect(shared.records[0].requestUsageAccounting?.pendingRequests).toBe(0);
  });

  it.each([429, 200])('blocks new requests before awaiting cleanup of an unusable HTTP %s response', async status => {
    const shared = budget(100), incomplete = vi.fn();
    let release!: () => void;
    const cleanup = new Promise<void>(resolve => { release = resolve; });
    const value = await bridge('https://provider.invalid/v1', incomplete, shared.gate(0));
    const fetch = vi.fn(async () => new Response(new ReadableStream({ cancel: () => cleanup }), { status }));
    vi.stubGlobal('fetch', fetch);
    const first = post(value);
    try {
      await expect.poll(() => shared.receipts.length).toBe(1);
      expect(shared.status()).toMatchObject({ status: 'usage-unavailable', usageComplete: false });
      expect((await post(value)).status).toBe(403);
    } finally { release(); }
    expect((await first).status).toBe(status === 429 ? 429 : 502);
    expect(fetch).toHaveBeenCalledOnce(); expect(incomplete).toHaveBeenCalledOnce();
    expect(shared.receipts).toEqual([{ complete: false, usage: undefined }]);
  });

  it('retains known usage when closing a response before its terminal marker', async () => {
    const shared = budget(100);
    const url = await upstream((_request, response) => {
      response.writeHead(200, { 'Content-Type': 'text/event-stream' });
      response.write([chunk({ content: 'partial' }), chunk({}, 'stop'), usage(12)]
        .map(value => `data: ${JSON.stringify(value)}\n\n`).join(''));
    });
    const value = await bridge(url, undefined, shared.gate(0)), response = await post(value);
    const reader = response.body!.getReader(); await reader.read();
    await value.close();
    await reader.cancel().catch(() => {});
    expect(shared.receipts).toEqual([{ complete: false, usage: { inputTokens: 10, outputTokens: 2, totalTokens: 12,
      cachedInputTokens: 3, reasoningOutputTokens: 1 } }]);
    expect(shared.status()).toMatchObject({ status: 'usage-unavailable', reportedTotalTokens: 12, usageComplete: false });
    expect(shared.records[0].requestUsageAccounting?.pendingRequests).toBe(0);
  });

  it('never acquires a budget lease for locally invalid requests', async () => {
    const gate = vi.fn<ModelRequestGate>(), incomplete = vi.fn(), fetch = vi.fn();
    const value = await bridge('https://provider.invalid/v1', incomplete, gate);
    vi.stubGlobal('fetch', fetch);
    expect((await post(value, { ...basic, surprise: true })).status).toBe(400);
    expect(gate).not.toHaveBeenCalled(); expect(fetch).not.toHaveBeenCalled(); expect(incomplete).not.toHaveBeenCalled();
  });
});

describe('session-scoped Responses to Chat Completions bridge, entirely offline', () => {
  it('streams function/custom tools and replays original reasoning and tool outputs after a fresh bridge', async () => {
    const forwarded: any[] = [];
    const patch = '*** Begin Patch\n*** Add File: Proof.lean\n+example : True := by trivial\n*** End Patch';
    const url = await upstream((request, response, body) => {
      expect(request.url).toBe('/v1/chat/completions');
      expect(request.headers.authorization).toBe(`Bearer ${upstreamKey}`);
      forwarded.push(body);
      if (forwarded.length === 1) sse(response, [
        chunk({ role: 'assistant', reasoning_content: 'Check the Lean ' }), chunk({ reasoning_content: 'goal first.' }),
        chunk({ tool_calls: [{ index: 0, id: 'call-shell', type: 'function', function: { name: 'exec_', arguments: '{"cmd":' } }] }),
        chunk({ tool_calls: [{ index: 0, function: { name: 'command', arguments: '"true"}' } }] }),
        chunk({ tool_calls: [{ index: 1, id: 'call-patch', type: 'function', function: { name: 'apply_patch', arguments: JSON.stringify({ input: patch }).slice(0, 20) } }] }),
        chunk({ tool_calls: [{ index: 1, function: { arguments: JSON.stringify({ input: patch }).slice(20) } }] }),
        chunk({}, 'tool_calls'), { choices: [], usage: { prompt_tokens: 100, completion_tokens: 30, total_tokens: 130,
          prompt_tokens_details: { cached_tokens: 40 }, completion_tokens_details: { reasoning_tokens: 20 } } },
      ]);
      else sse(response, [chunk({ content: 'Proof checked.' }), chunk({}, 'stop')]);
    });
    const first = await bridge(url);
    const initial = { ...basic, input: [{ type: 'message', role: 'developer', content: [{ type: 'input_text', text: 'Use Lean.' }] },
      { type: 'message', role: 'user', content: [{ type: 'input_text', text: 'Prove True.' }] }], tools: functions,
      tool_choice: 'auto', include: ['reasoning.encrypted_content'], text: { verbosity: 'low' },
      client_metadata: { fixture: 'offline' }, prompt_cache_key: 'fixture-cache', parallel_tool_calls: true };
    const response = await post(first, initial);
    expect(response.status).toBe(200);
    const traffic = await events(response), result = completed(traffic);
    expect(result.usage).toEqual({ input_tokens: 100, output_tokens: 30, total_tokens: 130,
      input_tokens_details: { cached_tokens: 40 }, output_tokens_details: { reasoning_tokens: 20 } });
    expect(result.output.map((item: any) => item.type)).toEqual(['reasoning', 'function_call', 'custom_tool_call']);
    expect(result.output[0].summary).toEqual([{ type: 'summary_text', text: 'Check the Lean goal first.' }]);
    expect(result.output[1]).toMatchObject({ call_id: 'call-shell', name: 'exec_command', arguments: '{"cmd":"true"}', status: 'completed' });
    expect(result.output[2]).toMatchObject({ call_id: 'call-patch', name: 'apply_patch', input: patch, status: 'completed' });
    expect(traffic.filter(event => event.type === 'response.function_call_arguments.delta').map(event => event.delta).join('')).toBe('{"cmd":"true"}');
    expect(traffic.find(event => event.type === 'response.custom_tool_call_input.delta').delta).toBe(patch);
    expect(forwarded[0]).toMatchObject({ reasoning_effort: 'high', stream: true, stream_options: { include_usage: true }, messages: [
      { role: 'system', content: 'Use Lean.' }, { role: 'user', content: 'Prove True.' }], tools: [{ type: 'function', function: { name: 'exec_command' } },
      { type: 'function', function: { name: 'apply_patch', parameters: { required: ['input'], additionalProperties: false } } }] });
    expect(JSON.stringify(traffic)).not.toContain(upstreamKey);
    expect(first.apiKey).not.toBe(upstreamKey);
    await first.close();
    const second = await bridge(url);
    expect(second.apiKey).not.toBe(first.apiKey);
    const savedOutput = result.output.map((item: any) => item.type === 'reasoning' ? { ...item, content: null, encrypted_content: null } : item);
    const replay = await events(await post(second, { ...initial, input: [...initial.input, ...savedOutput,
      { type: 'function_call_output', call_id: 'call-shell', output: 'exit 0' },
      { type: 'custom_tool_call_output', call_id: 'call-patch', output: [{ type: 'input_text', text: 'patch applied' }] }] }));
    expect(completed(replay).output[0].content[0].text).toBe('Proof checked.');
    expect(forwarded[1].messages.slice(2)).toEqual([
      { role: 'assistant', content: null, reasoning_content: 'Check the Lean goal first.', tool_calls: [
        { id: 'call-shell', type: 'function', function: { name: 'exec_command', arguments: '{"cmd":"true"}' } },
        { id: 'call-patch', type: 'function', function: { name: 'apply_patch', arguments: JSON.stringify({ input: patch }) } }] },
      { role: 'tool', tool_call_id: 'call-shell', content: 'exit 0' }, { role: 'tool', tool_call_id: 'call-patch', content: 'patch applied' },
    ]);
  });

  it('preserves instruction order through a gateway that rejects developer messages', async () => {
    const forwarded: any[] = [];
    const url = await upstream((_request, response, body) => {
      forwarded.push(body.messages);
      if (body.messages.some((message: any) => message.role === 'developer')) {
        response.writeHead(422); response.end('{"error":{"message":"openai_error"}}'); return;
      }
      sse(response, [chunk({ content: 'checked' }), chunk({}, 'stop')]);
    });
    const response = await post(await bridge(url), { ...basic, instructions: 'Frozen target.', input: [
      { role: 'system', content: 'Use Lean.' }, { role: 'developer', content: 'Preserve the statement.' },
      { role: 'user', content: 'Prove the target.' },
    ] });
    expect(response.status).toBe(200);
    expect(completed(await events(response)).output[0].content[0].text).toBe('checked');
    expect(forwarded).toEqual([[
      { role: 'system', content: 'Frozen target.' }, { role: 'system', content: 'Use Lean.' },
      { role: 'system', content: 'Preserve the statement.' }, { role: 'user', content: 'Prove the target.' },
    ]]);
  });

  it('preserves text across UTF-8 fragments, CRLF and multiline SSE without estimating absent usage', async () => {
    const url = await upstream((_request, response) => {
      response.writeHead(200, { 'Content-Type': 'text/event-stream' });
      const data = Buffer.from(`: keepalive\r\ndata: ${JSON.stringify(chunk({ content: '证明 ✓' }))}\r\n\r\ndata: {"choices":\r\ndata: [{"index":0,"delta":{},"finish_reason":"stop"}]}\r\n\r\ndata: [DONE]\r\n\r\n`);
      for (let offset = 0; offset < data.length; offset += 3) response.write(data.subarray(offset, offset + 3));
      response.end();
    });
    const traffic = await events(await post(await bridge(url)));
    expect(completed(traffic).usage).toBeNull();
    expect(completed(traffic).output[0].content[0].text).toBe('证明 ✓');
    expect(traffic.map(event => event.sequence_number)).toEqual(traffic.map((_event, index) => index));
  });

  it('maps DeepSeek cache details without inventing absent reasoning details', async () => {
    const url = await upstream((_request, response) => sse(response, [chunk({ content: 'ok' }), chunk({}, 'stop'),
      { choices: [], usage: { prompt_tokens: 12, completion_tokens: 4, total_tokens: 16, prompt_cache_hit_tokens: 9, prompt_cache_miss_tokens: 3 } }]));
    expect(completed(await events(await post(await bridge(url)))).usage).toEqual({ input_tokens: 12, output_tokens: 4, total_tokens: 16,
      input_tokens_details: { cached_tokens: 9 } });
  });

  it.each([null, 151645, 'end'])('accepts vLLM choice metadata with stop_reason %s', async stopReason => {
    const url = await upstream((_request, response) => sse(response, [
      { choices: [{ index: 0, delta: { role: 'assistant', content: '' }, finish_reason: null, logprobs: null }],
        prompt_token_ids: null, prompt_text: null },
      { choices: [{ index: 0, delta: { reasoning: 'Check the target.' }, finish_reason: null,
        stop_reason: null, token_ids: [42] }] },
      { choices: [{ index: 0, delta: { content: 'checked' }, finish_reason: 'stop',
        stop_reason: stopReason, token_ids: null }] },
      { choices: [], usage: { prompt_tokens: 35, completion_tokens: 3, total_tokens: 38 }, system_fingerprint: 'vllm-fixture' },
    ]));
    const result = completed(await events(await post(await bridge(url))));
    expect(result.output[0].summary).toEqual([{ type: 'summary_text', text: 'Check the target.' }]);
    expect(result.output[1].content[0].text).toBe('checked');
    expect(result.usage).toEqual({ input_tokens: 35, output_tokens: 3, total_tokens: 38 });
  });

  it.each([[true, false], [false, true]])('reports each missing receipt independently in mixed request order %j', async (first, second) => {
    let calls = 0;
    const reports = [first, second], incomplete = vi.fn();
    const url = await upstream((_request, response) => {
      const values: unknown[] = [chunk({ content: 'ok' }), chunk({}, 'stop')];
      if (reports[calls++]) values.push({ choices: [], usage: { prompt_tokens: 10, completion_tokens: 2, total_tokens: 12 } });
      sse(response, values);
    });
    const value = await bridge(url, incomplete);
    for (let index = 0; index < reports.length; index++) {
      const traffic = await events(await post(value));
      expect(completed(traffic)).toBeDefined();
      expect(incomplete).toHaveBeenCalledTimes(reports.slice(0, index + 1).filter(reported => !reported).length);
    }
    expect(incomplete).toHaveBeenCalledOnce();
    expect(incomplete.mock.calls[0]).toEqual([]);
  });

  it('does not report incomplete usage for rejected requests that never try the upstream', async () => {
    const incomplete = vi.fn();
    const value = await bridge('https://provider.invalid/v1', incomplete), fetch = vi.fn();
    vi.stubGlobal('fetch', fetch);
    expect((await post(value, { ...basic, surprise: true })).status).toBe(400);
    expect((await post(value, basic, { Authorization: 'Bearer wrong' })).status).toBe(401);
    expect(fetch).not.toHaveBeenCalled(); expect(incomplete).not.toHaveBeenCalled();
  });

  it('reports an attempted transport failure once before asynchronous cleanup', async () => {
    const incomplete = vi.fn();
    const value = await bridge('https://provider.invalid/v1', incomplete);
    vi.stubGlobal('fetch', vi.fn(async () => { throw new Error('fixture transport failure'); }));
    expect((await post(value)).status).toBe(502);
    expect(incomplete).toHaveBeenCalledOnce();
    expect(incomplete.mock.calls[0]).toEqual([]);
  });

  it('reports truncated streams even if they supplied usage', async () => {
    const incomplete = vi.fn();
    const url = await upstream((_request, response) => sse(response, [chunk({ content: 'partial' }), chunk({}, 'length'),
      { choices: [], usage: { prompt_tokens: 10, completion_tokens: 2, total_tokens: 12 } }]));
    const traffic = await events(await post(await bridge(url, incomplete)));
    expect(traffic.some(event => event.type === 'response.incomplete')).toBe(true);
    expect(incomplete).toHaveBeenCalledOnce();
  });

  it.each([401, 429])('preserves upstream HTTP %s and makes only one request', async status => {
    let calls = 0;
    const url = await upstream((_request, response) => { calls++; response.writeHead(status, { 'Retry-After': '7' }); response.end(`private diagnostic ${upstreamKey}`); });
    const response = await post(await bridge(url));
    expect(response.status).toBe(status); expect(response.headers.get('retry-after')).toBe('7');
    const body = await response.text(); expect(body).toContain(`upstream_http_${status}`); expect(body).not.toContain(upstreamKey);
    expect(calls).toBe(1);
  });

  it.each(['length', 'content_filter'])('reports %s as incomplete rather than completed', async reason => {
    const url = await upstream((_request, response) => sse(response, [chunk({ content: 'partial' }), chunk({}, reason)]));
    const traffic = await events(await post(await bridge(url)));
    expect(completed(traffic)).toBeUndefined();
    expect(traffic.find(event => event.type === 'response.incomplete').response).toMatchObject({ status: 'incomplete',
      incomplete_details: { reason: reason === 'length' ? 'max_output_tokens' : 'content_filter' } });
  });

  it('does not finish an executable tool item when its arguments were truncated', async () => {
    const url = await upstream((_request, response) => sse(response, [chunk({ tool_calls: [{ index: 0, id: 'partial',
      function: { name: 'exec_command', arguments: '{"cmd":"unfinished' } }] }), chunk({}, 'length')]));
    const traffic = await events(await post(await bridge(url), { ...basic, tools: functions }));
    expect(traffic.some(event => event.type === 'response.incomplete')).toBe(true);
    expect(traffic.some(event => event.type === 'response.output_item.done')).toBe(false);
    expect(completed(traffic)).toBeUndefined();
  });

  it('preserves HTTP failure status even when cancelling the upstream error body fails', async () => {
    const value = await bridge('https://provider.invalid/v1');
    vi.stubGlobal('fetch', vi.fn(async () => new Response(new ReadableStream({ cancel() { throw new Error('fixture cancellation failure'); } }), { status: 429 })));
    const response = await post(value);
    expect(response.status).toBe(429);
    expect((await response.json() as any).error.code).toBe('upstream_http_429');
  });

  it.each([
    { values: [chunk({ content: 'partial' })], code: 'upstream_stream_disconnected', done: false },
    { values: [chunk({ content: 'partial' }), chunk({}, 'stop')], code: 'upstream_stream_disconnected', done: false },
    { values: [chunk({ content: 'partial' }), { error: { message: `private ${upstreamKey}` } }], code: 'upstream_stream_error' },
    { values: [chunk({ content: 'ok' }), chunk({}, 'stop'), { choices: [], usage: { prompt_tokens: 1 } }], code: 'invalid_upstream_usage' },
    { values: [chunk({ content: 'ok' }), chunk({}, 'stop'), { choices: [], usage: { prompt_tokens: 1, completion_tokens: 1, total_tokens: 3 } }], code: 'invalid_upstream_usage' },
    { values: [chunk({ audio: { data: 'unsupported' } })], code: 'unsupported_upstream_chunk' },
    { values: [chunk({ tool_calls: [{ index: 0, id: 'bad', function: { name: 'apply_patch', arguments: '{"wrong":"value"}' } }] }), chunk({}, 'tool_calls')], code: 'invalid_custom_tool_arguments' },
    { values: [chunk({ tool_calls: [{ index: 0, id: 'bad', function: { name: 'exec_command', arguments: '{"cmd":"true"}' } }] }), chunk({}, 'stop')], code: 'inconsistent_upstream_finish_reason' },
  ])('fails without a completed receipt on $code', async ({ values, code, done }) => {
    const url = await upstream((_request, response) => sse(response, values, done ?? true));
    const traffic = await events(await post(await bridge(url), { ...basic, tools: functions }));
    expect(completed(traffic)).toBeUndefined();
    expect(traffic.find(event => event.type === 'response.failed').response.error.code).toBe(code);
    expect(traffic.some(event => event.type === 'response.output_item.done')).toBe(false);
    expect(JSON.stringify(traffic)).not.toContain(upstreamKey);
  });

  it('aborts the upstream when the downstream cancels', async () => {
    let disconnected = false;
    const url = await upstream((_request, response) => {
      response.on('close', () => { disconnected = true; });
      response.writeHead(200, { 'Content-Type': 'text/event-stream' }); response.write(`data: ${JSON.stringify(chunk({ content: 'working' }))}\n\n`);
    });
    const value = await bridge(url), response = await post(value);
    await response.body!.cancel();
    await expect.poll(() => disconnected).toBe(true);
  });

  it('aborts active work and releases its listener on close, including repeated close', async () => {
    let disconnected = false;
    const url = await upstream((_request, response) => {
      response.on('close', () => { disconnected = true; });
      response.writeHead(200, { 'Content-Type': 'text/event-stream' }); response.write(`data: ${JSON.stringify(chunk({ content: 'working' }))}\n\n`);
    });
    const value = await bridge(url), response = await post(value);
    await value.close(); await value.close();
    await expect.poll(() => disconnected).toBe(true);
    await response.body?.cancel().catch(() => {});
    await expect(post(value)).rejects.toThrow();
  });

  it('uses the current global fetch so offline callers can intercept the upstream only', async () => {
    const value = await bridge('https://provider.invalid/v1');
    const fetch = vi.fn(async (url: any, options: any) => {
      expect(url).toBe('https://provider.invalid/v1/chat/completions');
      expect(options.redirect).toBe('error');
      return new Response(`data: ${JSON.stringify(chunk({ content: 'offline' }))}\n\ndata: ${JSON.stringify(chunk({}, 'stop'))}\n\ndata: [DONE]\n\n`,
        { headers: { 'Content-Type': 'text/event-stream' } });
    });
    vi.stubGlobal('fetch', fetch);
    expect(completed(await events(await post(value))).output[0].content[0].text).toBe('offline');
    expect(fetch).toHaveBeenCalledOnce();
  });

  it('rejects unauthorized, browser, wrong-host and unrelated requests before contacting any upstream', async () => {
    let calls = 0;
    const value = await bridge(await upstream((_request, response) => { calls++; sse(response, [chunk({}, 'stop')]); }));
    expect((await post(value, basic, { Authorization: 'Bearer wrong' })).status).toBe(401);
    expect((await post(value, basic, { Origin: 'https://outside.invalid' })).status).toBe(403);
    expect((await post(value, basic, { 'Sec-Fetch-Site': 'cross-site' })).status).toBe(403);
    const wrongHost = await new Promise<number>(resolve => {
      const request = httpRequest(`${value.baseUrl}/responses`, { method: 'POST', headers: {
        Host: 'outside.invalid', Authorization: `Bearer ${value.apiKey}`, 'Content-Type': 'application/json',
      } }, response => { response.resume(); resolve(response.statusCode!); });
      request.end(JSON.stringify(basic));
    });
    expect(wrongHost).toBe(403);
    const headers = { Authorization: `Bearer ${value.apiKey}` };
    expect((await actualFetch(`${value.baseUrl}/models`, { headers })).status).toBe(404);
    expect((await actualFetch(`${value.baseUrl}/responses`, { headers })).status).toBe(405);
    expect(calls).toBe(0);
  });

  it.each([
    { ...basic, surprise: true }, { ...basic, stream: false }, { ...basic, model: 'Qwen' },
    { ...basic, input: [{ role: 'user', content: [{ type: 'input_image', image_url: 'https://outside.invalid/image' }] }] },
    { ...basic, input: [{ type: 'reasoning', summary: [], encrypted_content: 'unknown-opaque-content' }] },
    { ...basic, tools: [{ type: 'web_search' }] }, { ...basic, tools: [{ type: 'namespace', name: 'collaboration', tools: [] }] },
    { ...basic, tools: functions, tool_choice: { type: 'function', name: 'missing' } },
    { ...basic, input: [{ type: 'function_call_output', call_id: 'unknown', output: 'untrusted' }] },
  ])('rejects unsupported input explicitly without a model request %#', async body => {
    let calls = 0;
    const value = await bridge(await upstream((_request, response) => { calls++; sse(response, [chunk({}, 'stop')]); }));
    const response = await post(value, body);
    expect(response.status).toBe(400); expect((await response.json() as any).error.code).toBeTruthy(); expect(calls).toBe(0);
  });

  it('bounds request bodies and unfinished SSE events', async () => {
    let calls = 0;
    const url = await upstream((_request, response) => {
      calls++; response.writeHead(200, { 'Content-Type': 'text/event-stream' }); response.end(`data: ${'x'.repeat(2 * 1024 * 1024 + 1)}`);
    });
    const value = await bridge(url);
    expect((await post(value, { ...basic, input: 'x'.repeat(8 * 1024 * 1024) })).status).toBe(413);
    expect(calls).toBe(0);
    const traffic = await events(await post(value));
    expect(completed(traffic)).toBeUndefined();
    expect(traffic.find(event => event.type === 'response.failed').response.error.code).toBe('upstream_event_too_large');
  });
});
