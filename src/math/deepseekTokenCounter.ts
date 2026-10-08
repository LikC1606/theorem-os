import { execFile } from 'node:child_process';
import path from 'node:path';
import { z } from 'zod';

const tokens = z.number().int().nonnegative().safe();
const estimateSchema = z
  .object({
    kind: z.literal('local_estimate'),
    basis: z.literal('deepseek_chat_template_plus_tool_json'),
    promptTokens: tokens,
    toolDefinitionTokens: tokens,
    estimatedInputTokens: tokens,
  })
  .strict()
  .refine((value) => value.estimatedInputTokens === value.promptTokens + value.toolDefinitionTokens);

export type DeepseekTokenEstimate = Readonly<z.infer<typeof estimateSchema>>;

/** Local estimate only; deliberately incompatible with the broker's trusted number counter. */
export function createDeepseekTokenCounter(
  options: Readonly<{
    python: string;
    script: string;
    tokenizer: string;
    timeoutMs?: number;
  }>
) {
  const { python, script, tokenizer, timeoutMs = 10_000 } = options;
  if (![python, script, tokenizer].every(path.isAbsolute) || !Number.isSafeInteger(timeoutMs) || timeoutMs < 1) {
    throw new Error('deepseek_tokenizer_invalid_options');
  }
  return async (
    request: Readonly<{ body: Readonly<Record<string, unknown>>; signal: AbortSignal }>
  ): Promise<DeepseekTokenEstimate> => {
    request.signal.throwIfAborted();
    const input = JSON.stringify(request.body);
    if (Buffer.byteLength(input) > 4 * 1024 * 1024) throw new Error('deepseek_tokenizer_request_too_large');
    return await new Promise<DeepseekTokenEstimate>((resolve, reject) => {
      const child = execFile(
        python,
        [script],
        {
          env: {
            LANG: 'C.UTF-8',
            PYTHONUTF8: '1',
            PYTHONNOUSERSITE: '1',
            DEEPSCIENTIST_DEEPSEEK_TOKENIZER: tokenizer,
          },
          encoding: 'utf8',
          timeout: timeoutMs,
          killSignal: 'SIGKILL',
          maxBuffer: 4096,
        },
        (error, stdout) => {
          request.signal.removeEventListener('abort', abort);
          if (request.signal.aborted) return reject(new Error('deepseek_tokenizer_cancelled'));
          // Native errors may contain stderr, request data, or local paths.
          if (error) return reject(new Error('deepseek_tokenizer_failed'));
          try {
            resolve(Object.freeze(estimateSchema.parse(JSON.parse(stdout))));
          } catch {
            reject(new Error('deepseek_tokenizer_invalid_estimate'));
          }
        }
      );
      const abort = () => {
        child.kill('SIGKILL');
      };
      request.signal.addEventListener('abort', abort, { once: true });
      if (request.signal.aborted) abort();
      // An early child exit can close stdin before this write completes.
      child.stdin!.on('error', () => {});
      child.stdin!.end(input);
    });
  };
}

/** Adapter for callers that explicitly accept the local estimate as a number. */
export function createDeepseekEstimatedInputCounter(
  options: Readonly<{ python: string; script: string; tokenizer: string; timeoutMs?: number }>
) {
  const estimate = createDeepseekTokenCounter(options);
  return async (request: Readonly<{ body: Readonly<Record<string, unknown>>; signal: AbortSignal }>): Promise<number> =>
    (await estimate(request)).estimatedInputTokens;
}
