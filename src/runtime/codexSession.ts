import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { closeMathProcess } from '../math/mathProcess';
import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';
import { mathProofEnvironmentWorkerEnvironment } from '../math/mathProofEnvironment';

type Json = Record<string, unknown>;
const object = (value: unknown): Json => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_codex_invalid_message');
  return value as Json;
};
export type MathAgentActivity = {
  event: 'item_started' | 'item_completed' | 'reasoning' | 'message' | 'command_output' | 'lean_lock_waiting' | 'lean_lock_acquired';
  itemType?: string;
};
export type MathAgentOptions = {
  executable: string;
  profile: string;
  workspace: string;
  model: string;
  effort: string;
  instructions: string;
  environment?: NodeJS.ProcessEnv;
  proofProjectRoot?: string;
  threadId?: string;
  turnTimeoutMs?: number;
  onUsage: (usage: Json) => void;
  onActivity?: (activity: MathAgentActivity) => void;
};
export type MathAgentSession = {
  threadId: string;
  readonly lastError?: string;
  readonly lastInputTokens?: number;
  run: (message: string, messageId: string, workspace: string, onStarted: (turnId: string) => void) => Promise<string>;
  notify?: (message: string) => Promise<void>;
  interrupt: () => Promise<void>;
  close: () => Promise<void>;
};

/** One persistent Codex app-server; all protocol traffic stays on stdio. */
class CodexRpc {
  private child: ChildProcessWithoutNullStreams;
  private nextId = 0;
  private pending = new Map<number, { resolve: (result: Json) => void; reject: (error: Error) => void; timer: NodeJS.Timeout }>();
  private failure?: Error;
  private closing?: Promise<void>;
  onNotification: (method: string, params: Json) => void = () => {};
  onFailure: (error: Error) => void = () => {};

  constructor(executable: string, profile: string, environment: NodeJS.ProcessEnv = process.env) {
    this.child = spawn(executable, ['app-server', '--listen', 'stdio://'], {
      env: { ...environment, CODEX_HOME: profile }, stdio: 'pipe', detached: process.platform !== 'win32',
    });
    // Do not forward provider diagnostics, which can contain credentials or task text.
    this.child.stderr.resume();
    const fail = (reason: string) => {
      if (this.failure) return;
      this.failure = new Error(`math_codex_transport_closed:${reason}`);
      for (const call of this.pending.values()) { clearTimeout(call.timer); call.reject(this.failure); }
      this.pending.clear();
      this.onFailure(this.failure);
    };
    const errorCode = (error: NodeJS.ErrnoException) => /^[A-Z0-9_]{1,32}$/u.test(error.code ?? '') ? error.code : 'unknown';
    this.child.once('error', error => fail(`spawn_error:code=${errorCode(error)}`));
    this.child.once('close', (code, signal) => fail(`process_exit:code=${code ?? 'none'}:signal=${signal ?? 'none'}`));
    this.child.stdin.on('error', error => fail(`stdin_error:code=${errorCode(error)}`));
    const receive = (line: Buffer) => {
      try {
        const message = object(JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(line)));
        if (message.method !== undefined && typeof message.method !== 'string') throw new Error();
        if (message.method && message.id !== undefined) {
          // Headless math never grants an interactive permission request.
          this.write({ id: message.id, error: { code: -32601, message: 'Interactive requests are unavailable in headless mathematics' } });
        } else if (message.method) {
          this.onNotification(message.method as string, object(message.params ?? {}));
        } else {
          if (typeof message.id !== 'number') return;
          const call = this.pending.get(message.id);
          if (!call) return;
          const error = message.error ? object(message.error) : undefined;
          const result = error ? undefined : object(message.result ?? {});
          this.pending.delete(message.id);
          clearTimeout(call.timer);
          if (error) call.reject(new Error(`math_codex_rpc_failed:${error.code}`));
          else call.resolve(result!);
        }
      } catch { fail('invalid_frame'); void this.close(); }
    };
    let parts: Buffer[] = [], bytes = 0;
    this.child.stdout.on('data', (chunk: Buffer) => {
      if (this.failure) return;
      let start = 0;
      while (start < chunk.length) {
        const newline = chunk.indexOf(10, start), end = newline < 0 ? chunk.length : newline;
        bytes += end - start;
        if (bytes > 8 * 1024 * 1024) { parts = []; fail('frame_too_large'); void this.close(); return; }
        parts.push(chunk.subarray(start, end));
        if (newline < 0) break;
        const line = Buffer.concat(parts, bytes); parts = []; bytes = 0;
        receive(line);
        if (this.failure) return;
        start = newline + 1;
      }
    });
  }

  private write(message: Json): void {
    if (this.failure) throw this.failure;
    this.child.stdin.write(`${JSON.stringify(message)}\n`);
  }

  request(method: string, params: Json): Promise<Json> {
    if (this.failure) return Promise.reject(this.failure);
    const id = ++this.nextId;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`math_codex_rpc_timeout:${method}`));
      }, 120_000);
      this.pending.set(id, { resolve, reject, timer });
      try { this.write({ id, method, params }); }
      catch (error) { clearTimeout(timer); this.pending.delete(id); reject(error); }
    });
  }

  async initialize(): Promise<void> {
    await this.request('initialize', { clientInfo: { name: 'deepscientist-math', version: '0.1.0' }, capabilities: null });
    this.write({ method: 'initialized' });
  }

  close(): Promise<void> { return this.closing ??= closeMathProcess(this.child); }
}

export async function createCodexMathSession(options: MathAgentOptions): Promise<MathAgentSession> {
  const environment = options.proofProjectRoot
    ? mathProofEnvironmentWorkerEnvironment(options.proofProjectRoot, options.environment ?? process.env)
    : options.environment;
  const rpc = new CodexRpc(options.executable, options.profile, environment);
  let activeTurn: string | undefined;
  let completion: { resolve: (turn: Json) => void; reject: (error: Error) => void } | undefined;
  const earlyCompletions = new Map<string, Json>();
  let lastError: string | undefined;
  let lastInputTokens = 0;
  let transportFailure: Error | undefined;
  let threadId = options.threadId;
  let lastStreamActivityAt = 0;
  const outputTails = new Map<string, string>();
  const activity = (event: MathAgentActivity['event'], itemType?: string, streaming = false) => {
    if (!options.onActivity || !completion) return;
    const now = Date.now();
    if (streaming && now - lastStreamActivityAt < 30_000) return;
    lastStreamActivityAt = now;
    options.onActivity({ event, ...(itemType && /^[A-Za-z][A-Za-z0-9]{0,63}$/u.test(itemType) ? { itemType } : {}) });
  };
  rpc.onFailure = error => { transportFailure = error; lastError = error.message; completion?.reject(error); };
  rpc.onNotification = (method, params) => {
    if (threadId !== undefined && params.threadId !== undefined && params.threadId !== threadId) return;
    if (method === 'item/started' || method === 'item/completed') {
      const item = object(params.item);
      activity(method === 'item/started' ? 'item_started' : 'item_completed', typeof item.type === 'string' ? item.type : undefined);
      if (method === 'item/completed' && typeof item.id === 'string') outputTails.delete(item.id);
    } else if (method === 'item/reasoning/textDelta' || method === 'item/reasoning/summaryTextDelta') {
      activity('reasoning', undefined, true);
    } else if (method === 'item/agentMessage/delta') {
      activity('message', undefined, true);
    } else if (method === 'item/commandExecution/outputDelta') {
      const key = typeof params.itemId === 'string' ? params.itemId : '';
      const delta = typeof params.delta === 'string' ? params.delta : '';
      let tail = (outputTails.get(key) ?? '') + delta;
      let reported = false;
      for (const event of ['lean_lock_waiting', 'lean_lock_acquired'] as const) {
        const marker = `"event":"${event}"`, index = tail.indexOf(marker);
        if (index < 0) continue;
        activity(event, 'commandExecution'); reported = true;
        tail = tail.slice(index + marker.length);
      }
      if (!outputTails.has(key) && outputTails.size >= 32) outputTails.delete(outputTails.keys().next().value!);
      outputTails.set(key, tail.slice(-128));
      if (!reported) activity('command_output', 'commandExecution', true);
    }
    if (method === 'thread/tokenUsage/updated') {
      const usage = object(params.tokenUsage ?? {}), last = object(usage.last ?? {});
      lastInputTokens = typeof last.inputTokens === 'number' && Number.isSafeInteger(last.inputTokens) && last.inputTokens >= 0 ? last.inputTokens : 0;
      options.onUsage(object(usage.total ?? {}));
    }
    if (method === 'turn/completed') {
      const turn = object(params.turn);
      if (typeof turn.id !== 'string') return;
      if (turn.id === activeTurn && completion) completion.resolve(turn);
      else if (completion && !activeTurn) {
        if (earlyCompletions.size >= 32) earlyCompletions.delete(earlyCompletions.keys().next().value!);
        earlyCompletions.set(turn.id, turn);
      }
    }
  };
  try {
    await rpc.initialize();
    const profileConfig = path.join(options.profile, 'config.toml');
    const inherited = fs.existsSync(profileConfig) ? parseToml(fs.readFileSync(profileConfig, 'utf8')).mcp_servers : {};
    const disabled = Object.fromEntries(Object.keys(inherited ?? {}).map(name => [name, { enabled: false }]));
    const settings = {
      model: options.model, cwd: options.workspace,
      approvalPolicy: 'never', sandbox: 'workspace-write',
      developerInstructions: options.instructions,
      config: {
        mcp_servers: disabled,
        'features.apps': false,
        'features.plugins': false,
        model_reasoning_effort: options.effort,
        'sandbox_workspace_write.network_access': true,
      },
    };
    const result = await rpc.request(options.threadId ? 'thread/resume' : 'thread/start', {
      ...settings, ...(options.threadId ? { threadId: options.threadId } : {}),
    });
    const startedThreadId = object(result.thread).id;
    if (typeof startedThreadId !== 'string' || !startedThreadId) throw new Error('math_codex_thread_missing');
    threadId = startedThreadId;
    if (options.threadId && threadId !== options.threadId) throw new Error('math_codex_session_binding_mismatch');
    if (result.model !== options.model || result.reasoningEffort !== options.effort || result.approvalPolicy !== 'never')
      throw new Error('math_codex_session_binding_mismatch');
    return {
      threadId,
      get lastError() { return lastError; },
      get lastInputTokens() { return lastInputTokens; },
      run: async (message, messageId, workspace, onStarted) => {
        if (transportFailure) throw transportFailure;
        if (completion) throw new Error('math_codex_turn_already_running');
        lastError = undefined;
        let resolve!: (turn: Json) => void;
        let reject!: (error: Error) => void;
        const done = new Promise<Json>((yes, no) => { resolve = yes; reject = no; });
        // Attach immediately so a transport failure during turn/start is handled.
        void done.catch(() => {});
        completion = { resolve, reject };
        lastStreamActivityAt = 0; outputTails.clear();
        let checkpoint = false;
        let timer: NodeJS.Timeout | undefined;
        let interruptDeadline: NodeJS.Timeout | undefined;
        try {
          const started = await rpc.request('turn/start', {
            threadId, clientUserMessageId: messageId, cwd: workspace,
            model: options.model, effort: options.effort, approvalPolicy: 'never',
            sandboxPolicy: { type: 'workspaceWrite', writableRoots: [workspace], networkAccess: true, excludeTmpdirEnvVar: true, excludeSlashTmp: true },
            input: [{ type: 'text', text: message, text_elements: [] }],
          });
          const turnId = object(started.turn).id;
          if (typeof turnId !== 'string' || !turnId) throw new Error('math_codex_turn_missing');
          activeTurn = turnId;
          onStarted(activeTurn);
          if (options.turnTimeoutMs) timer = setTimeout(() => {
            checkpoint = true;
            // Only check sources after turn/completed confirms the writer stopped.
            interruptDeadline = setTimeout(() => { void rpc.close(); }, 10_000);
            void rpc.request('turn/interrupt', { threadId, turnId: activeTurn }).catch(() => { void rpc.close(); });
          }, options.turnTimeoutMs);
          const early = earlyCompletions.get(activeTurn);
          earlyCompletions.delete(activeTurn);
          if (early) resolve(early);
          const finished = await done;
          if (typeof finished.status !== 'string') throw new Error('math_codex_turn_status_missing');
          if (finished.status === 'failed' && finished.error) {
            const error = object(finished.error);
            if (typeof error.message === 'string') lastError = error.message;
          }
          return checkpoint && finished.status === 'interrupted' ? 'checkpoint' : finished.status;
        } catch (error) {
          lastError = error instanceof Error ? error.message : 'math_codex_turn_failed';
          throw error;
        } finally {
          clearTimeout(timer); clearTimeout(interruptDeadline);
          activeTurn = undefined; completion = undefined;
          earlyCompletions.clear();
          outputTails.clear();
        }
      },
      interrupt: async () => {
        if (activeTurn) await rpc.request('turn/interrupt', { threadId, turnId: activeTurn });
      },
      notify: async message => {
        if (activeTurn) await rpc.request('turn/steer', { threadId, expectedTurnId: activeTurn,
          input: [{ type: 'text', text: message, text_elements: [] }] });
      },
      close: () => rpc.close(),
    };
  } catch (error) { await rpc.close(); throw error; }
}
