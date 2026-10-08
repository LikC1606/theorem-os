import { randomUUID, timingSafeEqual } from 'node:crypto';
import fs from 'node:fs';
import net from 'node:net';
import path from 'node:path';
import { z } from 'zod';
import type { DurableMathBudgetLedger } from "./mathBudgetLedger";
import { MATH_RUN_TOKEN_LIMIT } from "./mathBudgetLedger";
import { assertMathCanonicalPath } from "./mathRunBinding";
import { canonicalMathJson, mathDigest } from "./mathRuntimeIo";

const count = z.number().int().nonnegative().safe();
const id = z.string().regex(/^[a-f0-9]{64}$/u);
const envelope = z.discriminatedUnion('kind', [
  z
    .object({
      version: z.literal(1),
      secret: id,
      kind: z.literal('reserve'),
      url: z.string(),
      body: z.record(z.string(), z.unknown()),
    })
    .strict(),
  z
    .object({
      version: z.literal(1),
      secret: id,
      kind: z.literal('settle'),
      requestId: id,
      responseId: z.string().min(1).max(256),
      usage: z
        .object({
          inputTokens: count,
          outputTokens: count,
          totalTokens: count,
          cachedInputTokens: count,
          reasoningOutputTokens: count,
        })
        .strict(),
    })
    .strict(),
]);

export type MathBudgetBrokerBinding = Readonly<{
  runId: string;
  inputDigest: string;
  actorId: string;
  provider: 'WestlakeHPC';
  model: 'deepseek';
  endpoint: string;
  outputTokens: number;
  itemId?: string;
}>;

export type MathBudgetBrokerHandle = Readonly<{
  getLaunchEnvironment: () => Readonly<Record<string, string>>;
  close: () => Promise<void>;
}>;

/** Private transport RPC. Only the host may supply identity and a complete-input counter. */
export async function startMathBudgetBroker(
  options: Readonly<{
    socketPath: string;
    secret: string;
    binding: MathBudgetBrokerBinding;
    ledger: DurableMathBudgetLedger;
    countInput: (
      request: Readonly<{ url: string; body: Readonly<Record<string, unknown>>; signal: AbortSignal }>
    ) => Promise<number>;
    onReject?: (code: string) => void;
  }>
): Promise<MathBudgetBrokerHandle> {
  const secret = Buffer.from(id.parse(options.secret), 'hex');
  const socketPath = options.socketPath;
  const binding = Object.freeze({ ...options.binding });
  count.positive().max(MATH_RUN_TOKEN_LIMIT).parse(binding.outputTokens);
  if (!path.isAbsolute(socketPath) || Buffer.byteLength(socketPath) > 103 || socketPath.includes('\0'))
    throw new Error('math_budget_socket_path_invalid');
  z.string()
    .regex(/^[A-Za-z0-9_-]{1,128}$/u)
    .parse(binding.actorId);
  if (binding.provider !== 'WestlakeHPC' || binding.model !== 'deepseek')
    throw new Error('math_budget_provider_mismatch');
  const endpoint = new URL(binding.endpoint);
  if (
    endpoint.username ||
    endpoint.password ||
    endpoint.hash ||
    endpoint.search ||
    endpoint.pathname !== '/v1/responses'
  )
    throw new Error('math_budget_endpoint_invalid');
  if (
    endpoint.protocol !== 'https:' &&
    !(endpoint.protocol === 'http:' && ['127.0.0.1', '[::1]'].includes(endpoint.hostname))
  )
    throw new Error('math_budget_endpoint_invalid');
  const state = await options.ledger.transact();
  if (state.policy.runId !== binding.runId || state.policy.inputDigest !== binding.inputDigest)
    throw new Error('math_budget_binding_mismatch');
  const directory = path.dirname(socketPath);
  assertMathCanonicalPath(directory);
  if ((fs.lstatSync(directory).mode & 0o777) !== 0o700) throw new Error('math_budget_socket_not_private');
  const shutdown = new AbortController();

  const handle = async (value: unknown) => {
    shutdown.signal.throwIfAborted();
    const message = envelope.parse(value);
    if (!timingSafeEqual(secret, Buffer.from(message.secret, 'hex'))) throw new Error('math_budget_unauthorized');
    if (message.kind === 'reserve') {
      const body = message.body;
      if (
        message.url !== binding.endpoint ||
        body.model !== binding.model ||
        body.max_output_tokens !== binding.outputTokens ||
        body.stream !== true ||
        body.store !== false ||
        !Array.isArray(body.input) ||
        'previous_response_id' in body ||
        'conversation' in body ||
        ('truncation' in body && body.truncation !== 'disabled')
      )
        throw new Error('math_budget_request_mismatch');
      // The counter must inspect all effective input, including tools and opaque context.
      // Persist a unique attempt even when a reply is lost; no transport RPC is retried.
      const requestId = mathDigest(canonicalMathJson({ binding, url: message.url, body, nonce: randomUUID() }));
      const counter = new AbortController();
      const abort = () => counter.abort();
      shutdown.signal.addEventListener('abort', abort, { once: true });
      const timer = setTimeout(abort, 10_000);
      let inputTokens: number;
      try {
        inputTokens = count.parse(
          await Promise.race([
            new Promise<never>((_, reject) => {
              counter.signal.addEventListener('abort', () => reject(new Error('math_budget_count_cancelled')), {
                once: true,
              });
            }),
            options.countInput({ url: message.url, body: structuredClone(body), signal: counter.signal }),
          ])
        );
        counter.signal.throwIfAborted();
      } finally {
        clearTimeout(timer);
        shutdown.signal.removeEventListener('abort', abort);
      }
      const receipt = await options.ledger.transact({
        kind: 'reserve',
        requestId,
        attempt: 1,
        actorId: binding.actorId,
        inputTokens,
        outputTokens: binding.outputTokens,
        itemId: binding.itemId,
      });
      if (!receipt.admitted) throw new Error('math_budget_replayed_admission');
      return { version: 1, ok: true, requestId };
    }
    const snapshot = await options.ledger.transact();
    const entry = snapshot.entries.find((item) => item.request.requestId === message.requestId);
    if (!entry || entry.request.actorId !== binding.actorId || entry.request.itemId !== binding.itemId)
      throw new Error('math_budget_unknown_request');
    const receipt = await options.ledger.transact({
      kind: 'settle',
      requestId: message.requestId,
      attempt: 1,
      usage: message.usage,
    });
    if (receipt.controlViolation) throw new Error('math_budget_admission_closed');
    return { version: 1, ok: true };
  };

  const sockets = new Set<net.Socket>();
  const pending = new Set<Promise<void>>();
  const server = net.createServer((socket) => {
    if (pending.size >= 32) {
      socket.destroy();
      return;
    }
    sockets.add(socket);
    socket.on('error', () => socket.destroy());
    socket.on('close', () => sockets.delete(socket));
    socket.setTimeout(10_000, () => socket.destroy());
    let buffer = Buffer.alloc(0);
    socket.on('data', function receive(chunk: Buffer) {
      if (buffer.length + chunk.length > 2 * 1024 * 1024) {
        socket.destroy();
        return;
      }
      buffer = Buffer.concat([buffer, chunk]);
      const end = buffer.indexOf(10);
      if (end < 0) return;
      socket.removeListener('data', receive);
      socket.pause();
      const task = (async () => {
        try {
          if (end !== buffer.length - 1) throw new Error('math_budget_invalid_frame');
          const response = await handle(JSON.parse(buffer.subarray(0, end).toString('utf8')));
          socket.end(`${JSON.stringify(response)}\n`);
        } catch (error) {
          // Do not send request content, credentials, or filesystem errors to clients.
          const message = error instanceof Error ? error.message : '';
          options.onReject?.(
            /^(?:math_budget|deepseek_tokenizer)_[a-z0-9_]+$/u.test(message)
              ? message
              : error instanceof z.ZodError
                ? 'math_budget_invalid_envelope'
                : 'math_budget_internal_error'
          );
          socket.end('{"version":1,"ok":false}\n');
        }
      })();
      pending.add(task);
      void task.finally(() => pending.delete(task));
    });
  });
  server.maxConnections = 32;
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(socketPath, () => {
      server.removeListener('error', reject);
      resolve();
    });
  });
  try {
    fs.chmodSync(socketPath, 0o600);
  } catch (error) {
    await new Promise<void>((resolve) => server.close(() => resolve()));
    throw error;
  }
  let closing: Promise<void> | undefined;
  return {
    // Supply only to the bound native child. Never persist or attach to Core's global environment.
    getLaunchEnvironment(): Readonly<Record<string, string>> {
      if (shutdown.signal.aborted) throw new Error('math_budget_broker_closed');
      return Object.freeze({
        DEEPSCIENTIST_MATH_BUDGET_SOCKET: socketPath,
        DEEPSCIENTIST_MATH_BUDGET_SECRET: secret.toString('hex'),
        DEEPSCIENTIST_MATH_BUDGET_MAX_OUTPUT_TOKENS: String(binding.outputTokens),
      });
    },
    close() {
      closing ??= (async () => {
        shutdown.abort();
        const closed = new Promise<void>((resolve, reject) =>
          server.close((error) => (error ? reject(error) : resolve()))
        );
        for (const socket of sockets) socket.destroy();
        await Promise.all([...pending, closed]);
      })();
      return closing;
    },
  };
}
