import { randomUUID } from 'node:crypto';
import { z } from 'zod';

export class ChatBridgeError extends Error {
  constructor(readonly code: string, readonly status = 400) { super(code); }
}

const text = z.string().max(8 * 1024 * 1024);
const name = z.string().regex(/^[A-Za-z0-9_.-]{1,128}$/u);
const id = z.string().min(1).max(256);
const count = z.number().int().nonnegative().max(Number.MAX_SAFE_INTEGER);
const empty = z.array(z.never());
const status = z.enum(['in_progress', 'completed', 'incomplete']).optional();
const textPart = z.union([
  z.object({ type: z.literal('input_text'), text }).strict(),
  z.object({ type: z.literal('output_text'), text, annotations: empty.optional(), logprobs: empty.optional() }).strict(),
]);
const content = z.union([text, z.array(textPart).max(4096)]);
const inputItem = z.union([
  z.object({ type: z.literal('message').optional(), id: id.optional(),
    role: z.enum(['system', 'developer', 'user', 'assistant']), content, status,
    phase: z.enum(['commentary', 'final_answer']).nullable().optional() }).strict(),
  z.object({ type: z.literal('reasoning'), id: id.optional(), status,
    summary: z.array(z.object({ type: z.literal('summary_text'), text }).strict()).max(4096),
    content: z.array(z.object({ type: z.literal('reasoning_text'), text }).strict()).nullable().optional(),
    encrypted_content: z.null().optional() }).strict(),
  z.object({ type: z.literal('function_call'), id: id.optional(), status, call_id: id, name,
    arguments: text }).strict(),
  z.object({ type: z.literal('custom_tool_call'), id: id.optional(), status, call_id: id, name, input: text }).strict(),
  z.object({ type: z.literal('function_call_output'), id: id.optional(), status, call_id: id, output: content }).strict(),
  z.object({ type: z.literal('custom_tool_call_output'), id: id.optional(), status, call_id: id, output: content }).strict(),
]);
const tool = z.union([
  z.object({ type: z.literal('function'), name, description: text.optional(),
    parameters: z.record(z.unknown()), strict: z.boolean().nullable().optional() }).strict(),
  z.object({ type: z.literal('custom'), name, description: text.optional(),
    format: z.union([z.object({ type: z.literal('text') }).strict(),
      z.object({ type: z.literal('grammar'), syntax: z.literal('lark'), definition: text }).strict()]).optional() }).strict(),
]);
const toolChoice = z.union([z.enum(['auto', 'none', 'required']),
  z.object({ type: z.enum(['function', 'custom']), name }).strict()]);
const requestSchema = z.object({
  model: name, input: z.union([text, z.array(inputItem).max(8192)]), instructions: text.nullable().optional(),
  stream: z.literal(true), store: z.literal(false).optional(),
  tools: z.array(tool).max(256).optional(), tool_choice: toolChoice.optional(), parallel_tool_calls: z.boolean().optional(),
  reasoning: z.object({ effort: z.enum(['none', 'minimal', 'low', 'medium', 'high', 'xhigh', 'max']).optional(),
    summary: z.enum(['auto', 'concise', 'detailed', 'none']).nullable().optional() }).strict().optional(),
  text: z.object({ verbosity: z.enum(['low', 'medium', 'high']).optional(),
    format: z.object({ type: z.literal('text') }).strict().optional() }).strict().optional(),
  max_output_tokens: count.positive().optional(), temperature: z.number().min(0).max(2).optional(),
  top_p: z.number().min(0).max(1).optional(),
  include: z.array(z.literal('reasoning.encrypted_content')).max(1).optional(),
  prompt_cache_key: z.string().max(512).optional(), service_tier: z.enum(['auto', 'default', 'flex', 'priority']).optional(),
  truncation: z.literal('disabled').optional(), previous_response_id: z.null().optional(),
  metadata: z.record(z.string().max(512)).optional(),
  client_metadata: z.record(z.string().max(4096)).optional(),
}).strict();

type RecordValue = Record<string, unknown>;
export type BridgeRequest = { body: RecordValue; tools: Map<string, 'function' | 'custom'> };
const flatten = (value: z.infer<typeof content>): string => typeof value === 'string' ? value : value.map(part => part.text).join('');
function validate<T>(schema: z.ZodType<T>, value: unknown, code: string, httpStatus = 400): T {
  const result = schema.safeParse(value);
  if (!result.success) throw new ChatBridgeError(code, httpStatus);
  return result.data;
}

/** Summary text carries the original Chat reasoning so a saved transcript can be replayed. */
export function translateChatBridgeRequest(value: unknown, model: string, effort: string): BridgeRequest {
  const request = validate(requestSchema, value, 'unsupported_responses_request');
  if (request.model !== model || request.reasoning?.effort && request.reasoning.effort !== effort)
    throw new ChatBridgeError('model_binding_mismatch');
  const messages: RecordValue[] = [];
  if (request.instructions) messages.push({ role: 'system', content: request.instructions });
  let reasoning = '', assistant: RecordValue | undefined;
  const pending = new Map<string, string>();
  const seen = new Set<string>();
  const items = typeof request.input === 'string' ? [{ role: 'user' as const, content: request.input }] : request.input;
  for (const item of items) {
    if (item.type === 'reasoning') {
      if (reasoning) throw new ChatBridgeError('ambiguous_reasoning_history');
      const summary = item.summary.map(part => part.text).join('');
      const original = item.content?.map(part => part.text).join('');
      if (original && summary && original !== summary) throw new ChatBridgeError('ambiguous_reasoning_history');
      reasoning = original ?? summary;
      assistant = undefined;
    } else if (item.type === 'function_call' || item.type === 'custom_tool_call') {
      if (seen.has(item.call_id)) throw new ChatBridgeError('duplicate_tool_call');
      if (!assistant) { assistant = { role: 'assistant', content: null, reasoning_content: reasoning }; messages.push(assistant); reasoning = ''; }
      const calls = (assistant.tool_calls ??= []) as RecordValue[];
      calls.push({ id: item.call_id, type: 'function', function: { name: item.name,
        arguments: item.type === 'custom_tool_call' ? JSON.stringify({ input: item.input }) : item.arguments } });
      seen.add(item.call_id); pending.set(item.call_id, item.type === 'custom_tool_call' ? 'custom_tool_call_output' : 'function_call_output');
    } else if (item.type === 'function_call_output' || item.type === 'custom_tool_call_output') {
      if (pending.get(item.call_id) !== item.type) throw new ChatBridgeError('orphan_tool_output');
      pending.delete(item.call_id);
      messages.push({ role: 'tool', tool_call_id: item.call_id, content: flatten(item.output) }); assistant = undefined;
    } else if ('role' in item) {
      if (pending.size) throw new ChatBridgeError('missing_tool_output');
      // Westlake's Chat endpoint accepts system instructions but rejects developer roles.
      const message: RecordValue = { role: item.role === 'developer' ? 'system' : item.role, content: flatten(item.content) };
      if (item.role === 'assistant') { message.reasoning_content = reasoning; reasoning = ''; assistant = message; }
      else { if (reasoning) throw new ChatBridgeError('orphan_reasoning_history'); assistant = undefined; }
      messages.push(message);
    }
  }
  if (pending.size || reasoning || !messages.length) throw new ChatBridgeError('incomplete_input_history');
  const tools = new Map<string, 'function' | 'custom'>();
  const chatTools = (request.tools ?? []).map(entry => {
    if (tools.has(entry.name)) throw new ChatBridgeError('duplicate_tool_name');
    tools.set(entry.name, entry.type);
    return { type: 'function', function: entry.type === 'function'
      ? { name: entry.name, ...(entry.description === undefined ? {} : { description: entry.description }), parameters: entry.parameters,
        ...(entry.strict == null ? {} : { strict: entry.strict }) }
      : { name: entry.name, description: [entry.description, 'Return the exact freeform tool input as the input string in a JSON object.',
        entry.format?.type === 'grammar' ? `The input must follow this ${entry.format.syntax} grammar:\n${entry.format.definition}` : undefined]
        .filter(Boolean).join('\n\n'), parameters: { type: 'object', properties: { input: { type: 'string' } }, required: ['input'], additionalProperties: false } } };
  });
  let choice: unknown = request.tool_choice;
  if (choice && typeof choice === 'object') {
    if (tools.get(request.tool_choice['name']) !== request.tool_choice['type']) throw new ChatBridgeError('unknown_tool_choice');
    choice = { type: 'function', function: { name: request.tool_choice['name'] } };
  }
  if (choice === 'required' && !chatTools.length) throw new ChatBridgeError('unknown_tool_choice');
  return { tools, body: {
    model, messages, stream: true, stream_options: { include_usage: true }, reasoning_effort: request.reasoning?.effort ?? effort,
    ...(chatTools.length ? { tools: chatTools } : {}), ...(choice === undefined ? {} : { tool_choice: choice }),
    ...(request.parallel_tool_calls === undefined ? {} : { parallel_tool_calls: request.parallel_tool_calls }),
    ...(request.max_output_tokens === undefined ? {} : { max_tokens: request.max_output_tokens }),
    ...(request.temperature === undefined ? {} : { temperature: request.temperature }),
    ...(request.top_p === undefined ? {} : { top_p: request.top_p }),
    ...(request.prompt_cache_key === undefined ? {} : { prompt_cache_key: request.prompt_cache_key }),
    ...(request.service_tier === undefined ? {} : { service_tier: request.service_tier }),
    // Responses storage/include/verbosity are client preferences; no remote state is created.
  } };
}

const usageSchema = z.object({ prompt_tokens: count, completion_tokens: count, total_tokens: count,
  prompt_tokens_details: z.object({ cached_tokens: count.optional() }).passthrough().nullable().optional(),
  completion_tokens_details: z.object({ reasoning_tokens: count.optional() }).passthrough().nullable().optional(),
  prompt_cache_hit_tokens: count.optional(), prompt_cache_miss_tokens: count.optional(),
}).passthrough();
function translateUsage(value: unknown): RecordValue {
  const usage = validate(usageSchema, value, 'invalid_upstream_usage', 502);
  const cached = usage.prompt_tokens_details?.cached_tokens ?? usage.prompt_cache_hit_tokens;
  const reasoning = usage.completion_tokens_details?.reasoning_tokens;
  if (usage.total_tokens !== usage.prompt_tokens + usage.completion_tokens || cached !== undefined && cached > usage.prompt_tokens ||
    reasoning !== undefined && reasoning > usage.completion_tokens || usage.prompt_tokens_details?.cached_tokens !== undefined &&
    usage.prompt_cache_hit_tokens !== undefined && usage.prompt_tokens_details.cached_tokens !== usage.prompt_cache_hit_tokens ||
    cached !== undefined && usage.prompt_cache_miss_tokens !== undefined && cached + usage.prompt_cache_miss_tokens !== usage.prompt_tokens)
    throw new ChatBridgeError('invalid_upstream_usage', 502);
  return { input_tokens: usage.prompt_tokens, output_tokens: usage.completion_tokens, total_tokens: usage.total_tokens,
    ...(cached === undefined ? {} : { input_tokens_details: { cached_tokens: cached } }),
    ...(reasoning === undefined ? {} : { output_tokens_details: { reasoning_tokens: reasoning } }) };
}

const deltaSchema = z.object({ role: z.literal('assistant').optional(), content: text.nullable().optional(),
  reasoning_content: text.nullable().optional(), reasoning: text.nullable().optional(),
  tool_calls: z.array(z.object({ index: count.max(63), id: id.optional(), type: z.literal('function').optional(),
    function: z.object({ name: name.optional(), arguments: text.optional() }).strict().optional(),
  }).strict()).max(64).optional(), refusal: z.null().optional() }).strict();
const chunkSchema = z.object({
  id: z.string().optional(), object: z.string().optional(), created: count.optional(), model: z.string().optional(),
  choices: z.array(z.object({ index: z.literal(0), delta: deltaSchema,
    finish_reason: z.enum(['stop', 'tool_calls', 'length', 'content_filter']).nullable().optional(),
    logprobs: z.null().optional(), stop_reason: z.union([text, count]).nullable().optional(),
    token_ids: z.array(count).max(8192).nullable().optional() }).strict()).max(1), usage: z.unknown().optional(),
}).passthrough();

type OutputItem = RecordValue & { id: string; type: string };
type ToolState = { callId?: string; name: string; args: string; emitted: number; item?: OutputItem; index?: number };

export class ChatBridgeStream {
  private sequence = 0;
  private readonly responseId = `resp_${randomUUID().replaceAll('-', '')}`;
  private readonly createdAt = Math.floor(Date.now() / 1000);
  private readonly output: OutputItem[] = [];
  private readonly calls = new Map<number, ToolState>();
  private reasoningItem?: OutputItem;
  private messageItem?: OutputItem;
  private reasoning = '';
  private message = '';
  private usage: RecordValue | null = null;
  private finishReason?: string;
  private done = false;
  private failed = false;
  constructor(private readonly model: string, private readonly tools: Map<string, 'function' | 'custom'>,
    private readonly emit: (event: RecordValue) => void) {}

  private send(type: string, data: RecordValue) { this.emit({ type, sequence_number: this.sequence++, ...data }); }
  private snapshot(state: string, error?: string): RecordValue {
    return { id: this.responseId, object: 'response', created_at: this.createdAt, status: state, model: this.model,
      output: this.output, usage: this.usage,
      error: error ? { code: error, message: error } : null,
      incomplete_details: state === 'incomplete' ? { reason: this.finishReason === 'length' ? 'max_output_tokens' : 'content_filter' } : null };
  }
  start() { this.send('response.created', { response: this.snapshot('in_progress') }); }
  get ended() { return this.done; }
  get usageReported() {
    return this.done && !this.failed && this.usage !== null && ['stop', 'tool_calls'].includes(this.finishReason ?? '');
  }
  get reportedUsage() {
    if (!this.usage) return undefined;
    return { inputTokens: this.usage.input_tokens as number, outputTokens: this.usage.output_tokens as number,
      totalTokens: this.usage.total_tokens as number,
      ...(this.usage.input_tokens_details ? { cachedInputTokens: (this.usage.input_tokens_details as RecordValue).cached_tokens as number } : {}),
      ...(this.usage.output_tokens_details ? { reasoningOutputTokens: (this.usage.output_tokens_details as RecordValue).reasoning_tokens as number } : {}) };
  }
  private add(item: OutputItem): number {
    const index = this.output.push(item) - 1;
    this.send('response.output_item.added', { output_index: index, item: { ...item } }); return index;
  }
  private append(kind: 'reasoning' | 'message', delta: string) {
    if (!delta) return;
    if (kind === 'reasoning') {
      if (!this.reasoningItem) {
        this.reasoningItem = { id: `rs_${randomUUID()}`, type: 'reasoning', summary: [] };
        const index = this.add(this.reasoningItem);
        this.send('response.reasoning_summary_part.added', { item_id: this.reasoningItem.id, output_index: index, summary_index: 0,
          part: { type: 'summary_text', text: '' } });
      }
      this.reasoning += delta;
      this.send('response.reasoning_summary_text.delta', { item_id: this.reasoningItem.id,
        output_index: this.output.indexOf(this.reasoningItem), summary_index: 0, delta });
    } else {
      if (!this.messageItem) {
        this.messageItem = { id: `msg_${randomUUID()}`, type: 'message', role: 'assistant', status: 'in_progress', content: [] };
        const index = this.add(this.messageItem);
        this.send('response.content_part.added', { item_id: this.messageItem.id, output_index: index, content_index: 0,
          part: { type: 'output_text', text: '', annotations: [], logprobs: [] } });
      }
      this.message += delta;
      this.send('response.output_text.delta', { item_id: this.messageItem.id,
        output_index: this.output.indexOf(this.messageItem), content_index: 0, delta, logprobs: [] });
    }
  }
  private toolEvent(state: ToolState, final = false) {
    const matches = [...this.tools.keys()].filter(name => name.startsWith(state.name));
    if (state.name && !matches.length) throw new ChatBridgeError('unknown_upstream_tool', 502);
    const type = this.tools.get(state.name);
    if (!state.item && type && state.callId && (final || matches.length === 1)) {
      state.item = { id: `${type === 'custom' ? 'ctc' : 'fc'}_${randomUUID()}`, type: type === 'custom' ? 'custom_tool_call' : 'function_call',
        status: 'in_progress', call_id: state.callId, name: state.name, ...(type === 'custom' ? { input: '' } : { arguments: '' }) };
      state.index = this.add(state.item);
    }
    if (!state.item) { if (final) throw new ChatBridgeError('incomplete_upstream_tool', 502); return; }
    if (state.item.name !== state.name || state.item.call_id !== state.callId) throw new ChatBridgeError('changed_upstream_tool', 502);
    if (type === 'function' && state.args.length > state.emitted) {
      this.send('response.function_call_arguments.delta', { item_id: state.item.id, output_index: state.index, delta: state.args.slice(state.emitted) });
      state.emitted = state.args.length;
    }
    if (!final) return;
    if (type === 'custom') {
      let raw: unknown;
      try { raw = JSON.parse(state.args); } catch { throw new ChatBridgeError('invalid_custom_tool_arguments', 502); }
      const input = validate(z.object({ input: text }).strict(), raw, 'invalid_custom_tool_arguments', 502).input;
      state.item.input = input;
      if (input) this.send('response.custom_tool_call_input.delta', { item_id: state.item.id, output_index: state.index, delta: input });
      this.send('response.custom_tool_call_input.done', { item_id: state.item.id, output_index: state.index, input });
    } else {
      try { JSON.parse(state.args); } catch { throw new ChatBridgeError('invalid_function_tool_arguments', 502); }
      state.item.arguments = state.args;
      this.send('response.function_call_arguments.done', { item_id: state.item.id, output_index: state.index, arguments: state.args });
    }
  }
  accept(data: string) {
    if (this.done || this.failed) throw new ChatBridgeError('data_after_stream_end', 502);
    if (data === '[DONE]') { this.complete(); this.done = true; return; }
    let value: unknown;
    try { value = JSON.parse(data); } catch { throw new ChatBridgeError('invalid_upstream_json', 502); }
    if (value && typeof value === 'object' && 'error' in value) throw new ChatBridgeError('upstream_stream_error', 502);
    const chunk = validate(chunkSchema, value, 'unsupported_upstream_chunk', 502);
    if (chunk.usage != null) {
      const usage = translateUsage(chunk.usage);
      if (this.usage && JSON.stringify(this.usage) !== JSON.stringify(usage)) throw new ChatBridgeError('conflicting_upstream_usage', 502);
      this.usage = usage;
    }
    const choice = chunk.choices[0];
    if (!choice) return;
    if (this.finishReason) throw new ChatBridgeError('data_after_finish_reason', 502);
    const delta = choice.delta;
    if (delta.reasoning && delta.reasoning_content && delta.reasoning !== delta.reasoning_content)
      throw new ChatBridgeError('ambiguous_upstream_reasoning', 502);
    this.append('reasoning', delta.reasoning_content ?? delta.reasoning ?? '');
    this.append('message', delta.content ?? '');
    for (const part of delta.tool_calls ?? []) {
      const state = this.calls.get(part.index) ?? { name: '', args: '', emitted: 0 };
      if (part.id) {
        if (state.callId && state.callId !== part.id) throw new ChatBridgeError('changed_upstream_tool', 502);
        state.callId = part.id;
      }
      state.name += part.function?.name ?? ''; state.args += part.function?.arguments ?? '';
      this.calls.set(part.index, state); this.toolEvent(state);
    }
    if (choice.finish_reason) this.finishReason = choice.finish_reason;
  }
  private complete() {
    if (!this.finishReason) throw new ChatBridgeError('missing_upstream_finish_reason', 502);
    if (this.finishReason === 'stop' && this.calls.size) throw new ChatBridgeError('inconsistent_upstream_finish_reason', 502);
    const completed = this.finishReason === 'stop' || this.finishReason === 'tool_calls';
    if (completed) {
      if (this.finishReason === 'tool_calls' && !this.calls.size) throw new ChatBridgeError('missing_upstream_tool_calls', 502);
      const callIds = new Set<string>();
      for (const state of this.calls.values()) {
        this.toolEvent(state, true);
        if (callIds.has(state.callId!)) throw new ChatBridgeError('duplicate_upstream_tool_call', 502);
        callIds.add(state.callId!);
      }
    }
    if (this.reasoningItem) {
      const index = this.output.indexOf(this.reasoningItem), part = { type: 'summary_text', text: this.reasoning };
      this.reasoningItem.summary = [part];
      this.send('response.reasoning_summary_text.done', { item_id: this.reasoningItem.id, output_index: index, summary_index: 0, text: this.reasoning });
      this.send('response.reasoning_summary_part.done', { item_id: this.reasoningItem.id, output_index: index, summary_index: 0, part });
    }
    if (this.messageItem) {
      const index = this.output.indexOf(this.messageItem), part = { type: 'output_text', text: this.message, annotations: [], logprobs: [] };
      this.messageItem.content = [part];
      this.send('response.output_text.done', { item_id: this.messageItem.id, output_index: index, content_index: 0, text: this.message, logprobs: [] });
      this.send('response.content_part.done', { item_id: this.messageItem.id, output_index: index, content_index: 0, part });
    }
    for (const item of this.output) {
      item.status = completed ? 'completed' : 'incomplete';
      if (!completed && ['function_call', 'custom_tool_call'].includes(item.type)) continue;
      this.send('response.output_item.done', { output_index: this.output.indexOf(item), item: { ...item } });
    }
    this.send(completed ? 'response.completed' : 'response.incomplete', { response: this.snapshot(completed ? 'completed' : 'incomplete') });
  }
  end() { if (!this.done) throw new ChatBridgeError('upstream_stream_disconnected', 502); }
  fail(code: string) {
    if (this.done || this.failed) return;
    this.failed = true; this.send('response.failed', { response: this.snapshot('failed', code) });
  }
}
