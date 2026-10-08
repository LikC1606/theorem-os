import { createServer, request as httpRequest, type IncomingMessage } from 'node:http';
import { request as httpsRequest } from 'node:https';
import { randomUUID } from 'node:crypto';
import fs from 'node:fs';

export type MathIsolatedProviderEvent = Readonly<{
  requestId: string;
  startedAt: string;
  finishedAt: string;
  durationMs: number;
  outcome: 'completed' | 'http_error' | 'transport_error' | 'cancelled' | 'rejected';
  rejectionCode?: string;
  transportErrorCode?: string;
  httpStatus: number | null;
  usage: {
    inputTokens: number;
    outputTokens: number;
    totalTokens: number;
    cachedInputTokens: number;
    reasoningOutputTokens: number;
  } | null;
}>;

function rejectRemoteInput(entry: unknown, depth: number): void {
  if (depth > 64) throw new Error('math_isolation_request_invalid');
  if (!entry || typeof entry !== 'object') return;
  for (const [key, item] of Object.entries(entry)) {
    if (['image_url', 'file_url', 'file_id', 'vector_store_ids'].includes(key))
      throw new Error('math_isolation_remote_input_denied');
    rejectRemoteInput(item, depth + 1);
  }
}

function validateLocalTools(tools: unknown, depth = 0): void {
  if (!Array.isArray(tools) || depth > 16) throw new Error('math_isolation_remote_tool_denied');
  for (const tool of tools) {
    if (!tool || typeof tool !== 'object' || Array.isArray(tool)) throw new Error('math_isolation_remote_tool_denied');
    // Codex groups locally executed MCP functions into namespaces. A namespace
    // is only a container; every child must still satisfy the local-tool policy.
    if (tool.type === 'namespace' && typeof tool.name === 'string' && tool.name.trim()) {
      validateLocalTools(tool.tools, depth + 1);
    } else if (!['function', 'custom'].includes(tool.type)) {
      throw new Error('math_isolation_remote_tool_denied');
    }
  }
}

export function validateMathIsolatedProviderRequest(value: unknown, model = 'deepseek'): Record<string, unknown> {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_isolation_request_invalid');
  const body = value as Record<string, unknown>;
  if (body.model !== model) throw new Error('math_isolation_model_denied');
  if (
    body.stream !== true ||
    body.store !== false ||
    !Array.isArray(body.input) ||
    ['previous_response_id', 'conversation'].some((key) => key in body) ||
    (body.background !== undefined && body.background !== false) ||
    (body.include !== undefined &&
      (!Array.isArray(body.include) || body.include.some((entry) => entry !== 'reasoning.encrypted_content')))
  )
    throw new Error('math_isolation_request_denied');
  if (body.tools !== undefined) validateLocalTools(body.tools);
  rejectRemoteInput(body.input, 0);
  return body;
}

function readBody(request: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    let bytes = 0;
    const chunks: Buffer[] = [];
    request.on('data', (chunk: Buffer) => {
      bytes += chunk.length;
      if (bytes > 16 * 1024 * 1024) {
        reject(new Error('math_isolation_request_too_large'));
        request.destroy();
      } else chunks.push(chunk);
    });
    request.once('end', () => resolve(Buffer.concat(chunks)));
    request.once('error', () => reject(new Error('math_isolation_request_incomplete')));
  });
}

/** The only network outlet in a model namespace; credentials and routing remain on the host. */
export async function startMathIsolatedProvider(options: {
  socketPath: string;
  baseUrl: string;
  apiKey: string;
  model?: string;
  record: (event: MathIsolatedProviderEvent) => void;
  /** Bound on waiting for upstream response headers (default 15 min). */
  headerTimeoutMs?: number;
}) {
  // Reasoning providers may buffer headers until their first event. Keep a
  // bounded wait long enough for high-effort proof turns to finish.
  const headerTimeoutMs = options.headerTimeoutMs ?? 900_000;
  const upstream = new URL(options.baseUrl);
  if (
    (upstream.protocol !== 'https:' &&
      !(upstream.protocol === 'http:' && ['127.0.0.1', '[::1]'].includes(upstream.hostname))) ||
    upstream.username ||
    upstream.password ||
    upstream.search ||
    upstream.hash ||
    !options.apiKey
  )
    throw new Error('math_isolation_provider_invalid');
  upstream.pathname = `${upstream.pathname.replace(/\/$/u, '')}/responses`;
  const active = new Set<() => void>();
  let failed = false;
  const server = createServer(async (req, res) => {
    const requestId = randomUUID();
    const startedAt = new Date().toISOString();
    const started = performance.now();
    const reject = (httpStatus: number, rejectionCode: string) => {
      try {
        options.record({
          requestId,
          startedAt,
          finishedAt: new Date().toISOString(),
          durationMs: performance.now() - started,
          outcome: 'rejected',
          rejectionCode,
          httpStatus,
          usage: null,
        });
      } catch {
        failed = true;
        for (const cancel of active) cancel();
      }
      if (!res.destroyed)
        res
          .writeHead(httpStatus, { 'content-type': 'application/json' })
          .end(
            JSON.stringify({ error: { type: 'invalid_request_error', code: rejectionCode, message: rejectionCode } })
          );
    };
    if (failed || active.size >= 4) {
      reject(503, 'math_isolation_provider_unavailable');
      return;
    }
    if (req.method !== 'POST' || req.url !== '/v1/responses') {
      reject(403, 'math_isolation_route_denied');
      return;
    }
    let payload: Buffer;
    try {
      payload = await readBody(req);
      validateMathIsolatedProviderRequest(JSON.parse(payload.toString('utf8')), options.model);
    } catch (error) {
      reject(
        400,
        error instanceof Error && /^math_isolation_[a-z_]+$/u.test(error.message)
          ? error.message
          : 'math_isolation_request_invalid'
      );
      return;
    }
    // Reading bodies yields to other requests; recheck capacity before opening an upstream connection.
    if (failed || active.size >= 4) {
      reject(503, 'math_isolation_provider_unavailable');
      return;
    }
    let status: number | null = null;
    let usage: MathIsolatedProviderEvent['usage'] = null;
    let finished = false;
    let headerTimer: ReturnType<typeof setTimeout> | undefined;
    const finish = (outcome: MathIsolatedProviderEvent['outcome'], transportErrorCode?: string) => {
      if (finished) return;
      finished = true;
      clearTimeout(headerTimer);
      active.delete(abort);
      try {
        options.record({
          requestId,
          startedAt,
          finishedAt: new Date().toISOString(),
          durationMs: performance.now() - started,
          outcome,
          httpStatus: status,
          usage,
          ...(transportErrorCode ? { transportErrorCode } : {}),
        });
      } catch {
        failed = true;
        for (const cancel of active) cancel();
      }
    };
    const outgoing = (upstream.protocol === 'https:' ? httpsRequest : httpRequest)(
      upstream,
      {
        method: 'POST',
        headers: {
          authorization: `Bearer ${options.apiKey}`,
          'content-type': 'application/json',
          accept: 'text/event-stream',
          'content-length': payload.length,
        },
      },
      (response) => {
        if (finished) {
          response.destroy();
          return;
        }
        clearTimeout(headerTimer);
        status = response.statusCode ?? 502;
        response.once('error', () => {
          if (finished) return;
          finish('transport_error', 'upstream_response_error');
          res.destroy();
        });
        // Never forward redirects, cookies, proxy headers, or upstream diagnostics.
        if (status < 200 || status >= 300) {
          finish('http_error');
          response.destroy();
          res.writeHead(502).end();
          return;
        }
        res.writeHead(200, { 'content-type': 'text/event-stream' });
        res.flushHeaders();
        let pending = '';
        let completed = false;
        let responseErrorCode: string | undefined;
        response.setEncoding('utf8');
        response.on('data', (chunk: string) => {
          pending += chunk;
          if (pending.length > 2 * 1024 * 1024) {
            pending = '';
            return;
          }
          let end: number;
          while ((end = pending.indexOf('\n')) >= 0) {
            const line = pending.slice(0, end).trimEnd();
            pending = pending.slice(end + 1);
            if (!line.startsWith('data:')) continue;
            try {
              const event = JSON.parse(line.slice(5).trimStart());
              if (event.type === 'response.completed') completed = true;
              else if (event.type === 'response.failed') responseErrorCode = 'upstream_response_failed';
              else if (event.type === 'response.incomplete') responseErrorCode = 'upstream_response_incomplete';
              else if (event.type === 'error') responseErrorCode = 'upstream_stream_error';
              const counts = event.type === 'response.completed' ? event.response?.usage : undefined;
              if (counts) {
                const values = [
                  counts.input_tokens,
                  counts.output_tokens,
                  counts.total_tokens,
                  counts.input_tokens_details?.cached_tokens ?? 0,
                  counts.output_tokens_details?.reasoning_tokens ?? 0,
                ];
                if (values.every((n) => Number.isSafeInteger(n) && n >= 0) && values[0] + values[1] === values[2])
                  usage = {
                    inputTokens: values[0],
                    outputTokens: values[1],
                    totalTokens: values[2],
                    cachedInputTokens: values[3],
                    reasoningOutputTokens: values[4],
                  };
              }
            } catch {
              /* Most stream lines contain content, not accounting. */
            }
          }
        });
        response.once('end', () => {
          // EOF alone is not a successful Responses turn, even for HTTP 200.
          if (completed && !responseErrorCode) finish('completed');
          else finish('transport_error', responseErrorCode ?? 'upstream_response_missing_completed');
        });
        response.pipe(res);
      }
    );
    const abort = () => {
      outgoing.destroy();
      finish('cancelled');
      res.destroy();
    };
    active.add(abort);
    outgoing.setTimeout(900_000, () => outgoing.destroy(new Error('math_isolation_response_timeout')));
    // Ends as transport_error with 502 to the client, so Codex retries sooner.
    headerTimer = setTimeout(() => outgoing.destroy(new Error('math_isolation_header_timeout')), headerTimeoutMs);
    outgoing.once('error', (error: NodeJS.ErrnoException) => {
      if (finished) return;
      const code =
        /^math_isolation_(header|response)_timeout$/u.test(error.message)
          ? error.message
          : /^[A-Z][A-Z0-9_]{0,63}$/u.test(error.code ?? '')
            ? error.code
            : 'upstream_request_error';
      finish('transport_error', code);
      if (!res.headersSent) res.writeHead(502).end();
      else res.destroy();
    });
    res.once('close', () => {
      if (!res.writableFinished) abort();
    });
    outgoing.end(payload);
  });
  server.on('connect', (_req, socket) => socket.destroy());
  server.on('upgrade', (_req, socket) => socket.destroy());
  server.maxConnections = 8;
  server.requestTimeout = 30000;
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(options.socketPath, resolve);
  });
  fs.chmodSync(options.socketPath, 0o600);
  return {
    close: async () => {
      failed = true;
      for (const abort of active) abort();
      await new Promise<void>((resolve) => {
        server.close(() => resolve());
        server.closeAllConnections();
      });
    },
  };
}
