import { randomBytes, timingSafeEqual } from 'node:crypto';
import { once } from 'node:events';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import type { AddressInfo } from 'node:net';
import { createParser } from 'eventsource-parser';
import { ChatBridgeError, ChatBridgeStream, translateChatBridgeRequest } from './chatCompletionsProtocol';
import type { ModelRequestAdmission, ModelRequestGate } from './modelRequest';

const MAX_REQUEST_BYTES = 8 * 1024 * 1024;
const MAX_STREAM_BYTES = 32 * 1024 * 1024;
const MAX_EVENT_BYTES = 2 * 1024 * 1024;
const IDLE_TIMEOUT_MS = 60_000;
const MAX_ERROR_BYTES = 16 * 1024;

type UpstreamDiagnostic = { category?: string; code?: string; type?: string; param?: string };

async function readUpstreamDiagnostic(response: Response, secret: string): Promise<UpstreamDiagnostic | undefined> {
  if (!response.headers.get('content-type')?.toLowerCase().startsWith('application/json') || !response.body) return;
  const reader = response.body.getReader();
  let timer: ReturnType<typeof setTimeout> | undefined;
  const read = async () => {
    const chunks: Uint8Array[] = []; let bytes = 0;
    while (true) {
      const chunk = await reader.read();
      if (chunk.done) break;
      bytes += chunk.value.byteLength;
      if (bytes > MAX_ERROR_BYTES) return;
      chunks.push(chunk.value);
    }
    const value: unknown = JSON.parse(Buffer.concat(chunks).toString('utf8'));
    if (!value || typeof value !== 'object' || !('error' in value) || !value.error || typeof value.error !== 'object') return;
    const error = value.error as Record<string, unknown>;
    const result: UpstreamDiagnostic = {};
    // Retain machine fields and fixed categories, never the provider's raw message or echoed input.
    for (const key of ['code', 'type', 'param'] as const) {
      const field = error[key];
      if (typeof field === 'string' && /^[A-Za-z0-9_.\[\]-]{1,128}$/u.test(field) && !field.includes(secret)) result[key] = field;
    }
    const message = [error.code, error.type, error.message].filter(item => typeof item === 'string').join(' ');
    if (/context[ _-]?(?:window|length).{0,80}(?:exceed|limit)|maximum context length/iu.test(message))
      result.category = 'context_window_exceeded';
    else if (/reasoning_content.{0,80}(?:missing|required)|(?:missing|required).{0,80}reasoning_content/iu.test(message))
      result.category = 'missing_reasoning_content';
    else if (/(?:tool_call|tool call|tool message).{0,80}(?:invalid|missing|match|respond)|(?:missing|invalid).{0,80}tool_call/iu.test(message))
      result.category = 'tool_call_history_invalid';
    else if (/(?:max_tokens|max_completion_tokens|max_output_tokens).{0,80}(?:exceed|range|limit|maximum|too large)/iu.test(message))
      result.category = 'output_token_limit';
    else if (/unsupported.{0,40}(?:parameter|argument)|(?:parameter|argument).{0,40}not supported/iu.test(message))
      result.category = 'unsupported_parameter';
    return Object.keys(result).length ? result : undefined;
  };
  try {
    return await Promise.race([read(), new Promise<undefined>(resolve => { timer = setTimeout(() => resolve(undefined), 1000); timer.unref(); })]);
  } catch { return; }
  finally {
    clearTimeout(timer);
    void reader.cancel().catch(() => {});
    reader.releaseLock();
  }
}

function jsonError(response: ServerResponse, status: number, code: string, upstream?: UpstreamDiagnostic) {
  if (response.destroyed) return;
  response.writeHead(status, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store', Connection: 'close' });
  const message = upstream?.category === 'context_window_exceeded' ? `${code}: maximum context length exceeded` : code;
  response.end(JSON.stringify({ error: { type: 'chat_bridge_error', code, message, ...(upstream ? { upstream } : {}) } }));
}
function upstreamUrl(baseUrl: string): string {
  let url: URL;
  try { url = new URL(baseUrl); } catch { throw new ChatBridgeError('invalid_chat_base_url'); }
  if (url.username || url.password || url.search || url.hash || url.protocol !== 'https:' &&
    !(url.protocol === 'http:' && ['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname)))
    throw new ChatBridgeError('invalid_chat_base_url');
  url.pathname = url.pathname.replace(/\/+$/u, '') + '/chat/completions';
  return url.href;
}
async function readRequest(request: IncomingMessage): Promise<unknown> {
  if (request.headers['content-encoding'] && request.headers['content-encoding'] !== 'identity') throw new ChatBridgeError('unsupported_content_encoding', 415);
  if (request.headers['content-type']?.split(';')[0].trim().toLowerCase() !== 'application/json') throw new ChatBridgeError('expected_json_request', 415);
  const length = request.headers['content-length'];
  if (length && (!/^\d+$/u.test(length) || Number(length) > MAX_REQUEST_BYTES)) throw new ChatBridgeError('request_too_large', 413);
  const chunks: Buffer[] = []; let bytes = 0;
  for await (const chunk of request) {
    const data = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
    bytes += data.length;
    if (bytes > MAX_REQUEST_BYTES) throw new ChatBridgeError('request_too_large', 413);
    chunks.push(data);
  }
  try { return JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(chunks))); }
  catch { throw new ChatBridgeError('invalid_request_json'); }
}

/** A session-scoped stdio provider compatibility bridge; no application state or credentials are persisted. */
export async function startChatCompletionsBridge(input: {
  baseUrl: string; apiKey: string; model: string; effort: string;
  onUsageIncomplete?: () => void;
  requestGate?: ModelRequestGate;
}): Promise<{ baseUrl: string; apiKey: string; close: () => Promise<void> }> {
  const upstream = upstreamUrl(input.baseUrl);
  if (!input.apiKey.trim() || /[\r\n]/u.test(input.apiKey)) throw new ChatBridgeError('invalid_chat_api_key');
  const apiKey = randomBytes(32).toString('hex'), expectedAuth = Buffer.from(`Bearer ${apiKey}`);
  const active = new Set<AbortController>(), tasks = new Set<Promise<void>>();
  let closed = false, closing: Promise<void> | undefined, host = '';
  const handle = async (request: IncomingMessage, response: ServerResponse) => {
    response.setHeader('X-Content-Type-Options', 'nosniff');
    const auth = Buffer.from(request.headers.authorization ?? '');
    if (request.headers.origin || request.headers['sec-fetch-site'] && request.headers['sec-fetch-site'] !== 'none' || request.headers.host !== host)
      return jsonError(response, 403, 'cross_site_request_rejected');
    if (auth.length !== expectedAuth.length || !timingSafeEqual(auth, expectedAuth)) return jsonError(response, 401, 'invalid_bridge_authorization');
    if (request.url !== '/v1/responses') return jsonError(response, 404, 'unknown_bridge_route');
    if (request.method !== 'POST') return jsonError(response, 405, 'unsupported_bridge_method');
    if (closed || active.size >= 8) return jsonError(response, 429, 'bridge_unavailable');
    const controller = new AbortController(); active.add(controller);
    let stream: ChatBridgeStream | undefined, reader: ReadableStreamDefaultReader<Uint8Array> | undefined;
    let upstreamAttempted = false;
    let upstreamDiagnostic: UpstreamDiagnostic | undefined;
    let admission: ModelRequestAdmission | undefined, settled = false;
    const settle = (complete: boolean) => {
      if (!upstreamAttempted || settled) return;
      settled = true;
      if (admission?.allowed) admission.settle({ usage: stream?.reportedUsage, complete });
      if (!complete) input.onUsageIncomplete?.();
    };
    let timer: ReturnType<typeof setTimeout> | undefined;
    const timeout = () => { clearTimeout(timer); timer = setTimeout(() => controller.abort(), IDLE_TIMEOUT_MS); timer.unref(); };
    const abort = () => { if (!response.writableEnded) controller.abort(); };
    request.once('aborted', abort); response.once('close', abort); timeout();
    try {
      const translated = translateChatBridgeRequest(await readRequest(request), input.model, input.effort);
      const body = JSON.stringify(translated.body);
      controller.signal.throwIfAborted();
      admission = input.requestGate?.();
      if (admission?.allowed === false) throw new ChatBridgeError(admission.reason, 403);
      upstreamAttempted = true;
      const upstreamResponse = await globalThis.fetch(upstream, { method: 'POST', redirect: 'error', signal: controller.signal,
        headers: { Authorization: `Bearer ${input.apiKey}`, 'Content-Type': 'application/json', Accept: 'text/event-stream' },
        body });
      if (!upstreamResponse.ok) {
        settle(false);
        upstreamDiagnostic = await readUpstreamDiagnostic(upstreamResponse, input.apiKey);
        void upstreamResponse.body?.cancel().catch(() => {});
        const status = upstreamResponse.status >= 400 && upstreamResponse.status <= 599 ? upstreamResponse.status : 502;
        const retry = upstreamResponse.headers.get('retry-after');
        if (retry && /^\d{1,8}$/u.test(retry)) response.setHeader('Retry-After', retry);
        throw new ChatBridgeError(`upstream_http_${upstreamResponse.status}`, status);
      }
      if (!upstreamResponse.headers.get('content-type')?.toLowerCase().startsWith('text/event-stream') || !upstreamResponse.body) {
        settle(false);
        await upstreamResponse.body?.cancel(); throw new ChatBridgeError('expected_upstream_sse', 502);
      }
      response.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-store', Connection: 'keep-alive' });
      stream = new ChatBridgeStream(input.model, translated.tools, event => {
        if (response.destroyed || controller.signal.aborted) throw new ChatBridgeError('bridge_request_aborted', 499);
        if (event.type === 'response.completed' || event.type === 'response.incomplete')
          settle(event.type === 'response.completed' && stream?.reportedUsage !== undefined);
        response.write(`event: ${event.type}\ndata: ${JSON.stringify(event)}\n\n`);
      });
      stream.start();
      let pendingBytes = 0;
      const parser = createParser({ onEvent: event => {
        if (Buffer.byteLength(event.data) > MAX_EVENT_BYTES) throw new ChatBridgeError('upstream_event_too_large', 502);
        pendingBytes = 0;
        if (event.event === 'error') throw new ChatBridgeError('upstream_stream_error', 502);
        if (event.event && !['message', 'completion.chunk', 'chat.completion.chunk'].includes(event.event))
          throw new ChatBridgeError('unsupported_upstream_event', 502);
        stream!.accept(event.data);
      }, onError: () => { throw new ChatBridgeError('invalid_upstream_sse', 502); } });
      const decoder = new TextDecoder('utf-8', { fatal: true }); let bytes = 0;
      reader = upstreamResponse.body.getReader();
      while (!stream.ended) {
        const chunk = await reader.read(); timeout();
        if (chunk.done) { parser.feed(decoder.decode()); stream.end(); break; }
        bytes += chunk.value.byteLength;
        if (bytes > MAX_STREAM_BYTES) throw new ChatBridgeError('upstream_stream_too_large', 502);
        // Bound parser buffering without interpreting or splitting SSE lines ourselves.
        for (let offset = 0; offset < chunk.value.byteLength; offset += 32 * 1024) {
          const slice = chunk.value.subarray(offset, offset + 32 * 1024); pendingBytes += slice.byteLength;
          if (pendingBytes > MAX_EVENT_BYTES) throw new ChatBridgeError('upstream_event_too_large', 502);
          parser.feed(decoder.decode(slice, { stream: true }));
        }
        if (response.writableNeedDrain) await once(response, 'drain', { signal: controller.signal });
      }
      response.end();
    } catch (error) {
      settle(false);
      const code = controller.signal.aborted ? 'bridge_request_aborted' : error instanceof ChatBridgeError ? error.code : 'upstream_transport_error';
      if (response.headersSent) {
        try { stream?.fail(code); response.end(); } catch { response.destroy(); }
      } else jsonError(response, error instanceof ChatBridgeError ? error.status : 502, code, upstreamDiagnostic);
    } finally {
      try {
        settle(Boolean(stream?.ended && stream.usageReported));
      } finally {
        clearTimeout(timer); controller.abort(); await reader?.cancel().catch(() => {});
        active.delete(controller); request.off('aborted', abort); response.off('close', abort);
      }
    }
  };
  const server = createServer((request, response) => {
    const task = handle(request, response); tasks.add(task);
    void task.finally(() => tasks.delete(task)).catch(() => { response.destroy(); });
  });
  server.requestTimeout = 30_000; server.headersTimeout = 10_000; server.maxHeadersCount = 64; server.maxConnections = 16;
  await new Promise<void>((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', () => { server.off('error', reject); resolve(); }); });
  host = `127.0.0.1:${(server.address() as AddressInfo).port}`;
  return { baseUrl: `http://${host}/v1`, apiKey, close: () => closing ??= (async () => {
    closed = true; for (const controller of active) controller.abort();
    const stopped = new Promise<void>((resolve, reject) => server.close(error => error ? reject(error) : resolve()));
    server.closeAllConnections(); await stopped; await Promise.allSettled([...tasks]);
  })() };
}
