import { isAbsolute } from 'node:path';

export type MathBudgetHostBinding = Readonly<{
  run_id: string;
  input_digest: string;
  actor_id: string;
  socket_path: string;
  secret: string;
  output_tokens: number;
  provider: 'WestlakeHPC';
  model: 'deepseek';
}>;

export type MathBudgetHostClientOptions = Readonly<{
  baseUrl: string;
  hostSecret: string;
  timeoutMs?: number;
}>;

const SECRET = /^[a-f0-9]{64}$/;

function validateBinding(binding: MathBudgetHostBinding): void {
  if (
    !binding.run_id ||
    !binding.actor_id ||
    !SECRET.test(binding.input_digest) ||
    !SECRET.test(binding.secret) ||
    !isAbsolute(binding.socket_path) ||
    binding.socket_path.includes('\0') ||
    Buffer.byteLength(binding.socket_path) > 103 ||
    !Number.isSafeInteger(binding.output_tokens) ||
    binding.output_tokens < 1 ||
    binding.output_tokens > 64000 ||
    binding.provider !== 'WestlakeHPC' ||
    binding.model !== 'deepseek'
  ) {
    throw new Error('math_budget_host_binding_invalid');
  }
}

/** Private Core registration only; callers own broker lifetime and uncertain-write cleanup. */
export function createMathBudgetHostClient(options: MathBudgetHostClientOptions) {
  let baseUrl: URL;
  try {
    baseUrl = new URL(options.baseUrl);
  } catch {
    throw new Error('math_budget_host_url_invalid');
  }
  if (
    !['http:', 'https:'].includes(baseUrl.protocol) ||
    !['127.0.0.1', '[::1]', 'localhost'].includes(baseUrl.hostname) ||
    baseUrl.username ||
    baseUrl.password ||
    baseUrl.search ||
    baseUrl.hash ||
    baseUrl.pathname !== '/'
  ) {
    throw new Error('math_budget_host_url_invalid');
  }
  const hostSecret = options.hostSecret;
  if (!SECRET.test(hostSecret)) throw new Error('math_budget_host_secret_invalid');
  const timeoutMs = options.timeoutMs ?? 10_000;
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs < 1 || timeoutMs > 2_147_483_647) {
    throw new Error('math_budget_host_timeout_invalid');
  }
  const origin = baseUrl.origin;

  async function request(method: 'POST' | 'DELETE', conversationId: string, binding?: MathBudgetHostBinding) {
    if (!conversationId || conversationId === '.' || conversationId === '..') {
      throw new Error('math_budget_host_conversation_invalid');
    }
    if (binding) validateBinding(binding);
    try {
      const response = await fetch(
        `${origin}/api/conversations/${encodeURIComponent(conversationId)}/math-budget-binding`,
        {
          method,
          headers: { 'Content-Type': 'application/json', 'X-DeepScientist-Math-Host-Secret': hostSecret },
          body: binding ? JSON.stringify(binding) : undefined,
          redirect: 'error',
          signal: AbortSignal.timeout(timeoutMs),
        }
      );
      await response.body?.cancel();
      if (!response.ok && !(method === 'DELETE' && response.status === 404)) throw new Error('request_failed');
    } catch {
      // Transport errors and server bodies can contain launch credentials.
      throw new Error(method === 'POST' ? 'math_budget_host_register_failed' : 'math_budget_host_revoke_failed');
    }
  }

  return Object.freeze({
    register: (conversationId: string, binding: MathBudgetHostBinding): Promise<void> =>
      request('POST', conversationId, binding),
    revoke: (conversationId: string): Promise<void> => request('DELETE', conversationId),
  });
}
