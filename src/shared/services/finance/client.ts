import { z } from 'zod';
import { ALPHA_DOJO_SIDECAR_PROTOCOL } from "../../../common/config/alphaDojoFinanceMcpEnv";
import {
  FINANCE_TOOL_NAMES,
  financeToolResultSchemas,
  type FinanceResultEnvelope,
  type FinanceToolName,
} from "../../../common/chat/finance/index";

export { ALPHA_DOJO_SIDECAR_PROTOCOL };
const MAX_RESPONSE_BYTES = 2 * 1024 * 1024;
const RETRYABLE_STATUS = new Set([429, 500, 502, 503, 504]);
const CIRCUIT_COOLDOWN_MS = 30_000;

const healthSchema = z
  .object({
    schema: z.literal(ALPHA_DOJO_SIDECAR_PROTOCOL),
    apiVersion: z.string().trim().min(1).max(40),
    status: z.enum(['healthy', 'degraded']),
    capabilities: z.array(z.string().trim().min(1).max(160)).max(100),
    markets: z.array(z.enum(['us', 'cn', 'hk', 'cross_market'])).max(4),
    tools: z.array(z.enum(FINANCE_TOOL_NAMES)).max(FINANCE_TOOL_NAMES.length),
    dataAsOf: z.string().datetime({ offset: true }).optional(),
    warnings: z.array(z.string().trim().min(1).max(500)).max(100),
  })
  .strict();

export type AlphaDojoSidecarHealth = {
  schema: typeof ALPHA_DOJO_SIDECAR_PROTOCOL;
  apiVersion: string;
  status: 'healthy' | 'degraded';
  capabilities: string[];
  markets: Array<'us' | 'cn' | 'hk' | 'cross_market'>;
  tools: FinanceToolName[];
  dataAsOf?: string;
  warnings: string[];
};

export class FinanceRuntimeError extends Error {
  constructor(
    readonly code:
      | 'disabled'
      | 'endpoint_missing'
      | 'endpoint_rejected'
      | 'timeout'
      | 'provider_error'
      | 'response_too_large'
      | 'invalid_response'
      | 'incompatible_version'
      | 'permission_denied',
    message: string,
    readonly retryable = false
  ) {
    super(message);
    this.name = 'FinanceRuntimeError';
  }
}

export const resolveLoopbackFinanceEndpoint = (value: string): URL => {
  let endpoint: URL;
  try {
    endpoint = new URL(value);
  } catch {
    throw new FinanceRuntimeError('endpoint_rejected', 'The finance sidecar endpoint is not a valid URL.');
  }
  if (
    endpoint.protocol !== 'http:' ||
    !['127.0.0.1', 'localhost', '[::1]'].includes(endpoint.hostname) ||
    endpoint.username ||
    endpoint.password ||
    endpoint.search ||
    endpoint.hash
  ) {
    throw new FinanceRuntimeError(
      'endpoint_rejected',
      'The finance sidecar endpoint must be an unauthenticated loopback HTTP URL.'
    );
  }
  endpoint.pathname = endpoint.pathname.replace(/\/+$/u, '');
  return endpoint;
};

type FinanceSidecarClientOptions = {
  endpoint: string;
  timeoutMs: number;
  fetcher?: typeof fetch;
  sleep?: (milliseconds: number) => Promise<void>;
};

export class FinanceSidecarClient {
  private readonly endpoint: URL;
  private readonly timeoutMs: number;
  private readonly fetcher: typeof fetch;
  private readonly sleep: (milliseconds: number) => Promise<void>;
  private circuitOpenUntil = 0;

  constructor(options: FinanceSidecarClientOptions) {
    this.endpoint = resolveLoopbackFinanceEndpoint(options.endpoint);
    this.timeoutMs = options.timeoutMs;
    this.fetcher = options.fetcher || fetch;
    this.sleep = options.sleep || ((milliseconds) => new Promise((resolve) => setTimeout(resolve, milliseconds)));
  }

  async health(signal?: AbortSignal): Promise<AlphaDojoSidecarHealth> {
    const value = await this.request('/v1/health', { method: 'GET' }, signal, false);
    const parsed = healthSchema.safeParse(value);
    if (!parsed.success)
      throw new FinanceRuntimeError('invalid_response', 'The finance sidecar health response is invalid.');
    if (!parsed.data.apiVersion.startsWith('1.')) {
      throw new FinanceRuntimeError('incompatible_version', 'The finance sidecar API version is not supported.');
    }
    return parsed.data as AlphaDojoSidecarHealth;
  }

  async execute<TName extends FinanceToolName>(
    toolName: TName,
    input: unknown,
    options: { signal?: AbortSignal; retryable: boolean }
  ): Promise<FinanceResultEnvelope<unknown>> {
    const value = await this.request(
      `/v1/tools/${toolName}`,
      {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', Accept: 'application/json' },
        body: JSON.stringify(input),
      },
      options.signal,
      options.retryable
    );
    const parsed = financeToolResultSchemas[toolName].safeParse(value);
    if (!parsed.success) {
      throw new FinanceRuntimeError('invalid_response', `The normalized response for ${toolName} is invalid.`);
    }
    return parsed.data as FinanceResultEnvelope<unknown>;
  }

  private async request(
    pathname: string,
    init: RequestInit,
    externalSignal: AbortSignal | undefined,
    retryable: boolean
  ): Promise<unknown> {
    const isHealthRequest = pathname === '/v1/health';
    if (!isHealthRequest && this.circuitOpenUntil > Date.now()) {
      throw new FinanceRuntimeError(
        'provider_error',
        'The finance provider is temporarily unavailable; the adapter circuit is open.',
        true
      );
    }
    const attempts = retryable ? 3 : 1;
    const attemptRequest = async (attempt: number): Promise<unknown> => {
      try {
        const result = await this.requestOnce(pathname, init, externalSignal);
        this.circuitOpenUntil = 0;
        return result;
      } catch (error) {
        const runtimeError =
          error instanceof FinanceRuntimeError
            ? error
            : new FinanceRuntimeError('provider_error', 'The finance sidecar request failed.', true);
        if (!retryable || !runtimeError.retryable || attempt >= attempts - 1 || externalSignal?.aborted) {
          if (!isHealthRequest && runtimeError.retryable) {
            this.circuitOpenUntil = Date.now() + CIRCUIT_COOLDOWN_MS;
          }
          throw runtimeError;
        }
        await this.sleep(150 * 2 ** attempt);
        return attemptRequest(attempt + 1);
      }
    };
    return attemptRequest(0);
  }

  private async requestOnce(pathname: string, init: RequestInit, externalSignal?: AbortSignal): Promise<unknown> {
    const controller = new AbortController();
    const onAbort = () => controller.abort(externalSignal?.reason);
    externalSignal?.addEventListener('abort', onAbort, { once: true });
    const timer = setTimeout(() => controller.abort('timeout'), this.timeoutMs);
    try {
      const endpointPath = this.endpoint.pathname === '/' ? '' : this.endpoint.pathname.replace(/\/+$/u, '');
      const requestPath = pathname.startsWith('/') ? pathname : `/${pathname}`;
      const url = new URL(`${endpointPath}${requestPath}`, this.endpoint.origin);
      const response = await this.fetcher(url, { ...init, signal: controller.signal });
      const contentLength = Number(response.headers.get('content-length') || 0);
      if (contentLength > MAX_RESPONSE_BYTES) {
        throw new FinanceRuntimeError('response_too_large', 'The finance sidecar response exceeds 2 MB.');
      }
      if (!response.ok) {
        throw new FinanceRuntimeError(
          'provider_error',
          `The finance sidecar returned HTTP ${response.status}.`,
          RETRYABLE_STATUS.has(response.status)
        );
      }
      const bytes = await this.readBoundedResponse(response);
      try {
        return JSON.parse(new TextDecoder().decode(bytes));
      } catch {
        throw new FinanceRuntimeError('invalid_response', 'The finance sidecar returned invalid JSON.');
      }
    } catch (error) {
      if (error instanceof FinanceRuntimeError) throw error;
      if (controller.signal.aborted)
        throw new FinanceRuntimeError('timeout', 'The finance sidecar request timed out.', true);
      throw new FinanceRuntimeError('provider_error', 'The finance sidecar request failed.', true);
    } finally {
      clearTimeout(timer);
      externalSignal?.removeEventListener('abort', onAbort);
    }
  }

  private async readBoundedResponse(response: Response): Promise<Uint8Array> {
    if (!response.body) return new Uint8Array(await response.arrayBuffer());
    const reader = response.body.getReader();
    const chunks: Uint8Array[] = [];
    let total = 0;
    while (true) {
      // Stream reads must remain sequential so the byte limit is enforced before buffering the next chunk.
      // eslint-disable-next-line no-await-in-loop
      const { done, value } = await reader.read();
      if (done) break;
      total += value.byteLength;
      if (total > MAX_RESPONSE_BYTES) {
        // eslint-disable-next-line no-await-in-loop
        await reader.cancel();
        throw new FinanceRuntimeError('response_too_large', 'The finance sidecar response exceeds 2 MB.');
      }
      chunks.push(value);
    }
    const output = new Uint8Array(total);
    let offset = 0;
    chunks.forEach((chunk) => {
      output.set(chunk, offset);
      offset += chunk.byteLength;
    });
    return output;
  }
}
