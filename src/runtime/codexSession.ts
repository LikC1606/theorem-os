import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { closeMathProcess } from '../math/mathProcess';
import fs from 'node:fs';
import path from 'node:path';
import { randomUUID } from 'node:crypto';
import { parse as parseToml } from 'smol-toml';
import { mathProofEnvironmentWorkerEnvironment } from '../math/mathProofEnvironment';
import { startChatCompletionsBridge } from './chatCompletionsBridge';
import { DEEPSEEK_PROVIDER } from './deepseek';
import { WESTLAKE_PROVIDER, validateWestlakeModel } from './westlake';
import type { ModelRequestGate } from './modelRequest';

type Json = Record<string, unknown>;
const object = (value: unknown): Json => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_codex_invalid_message');
  return value as Json;
};
const CODEX_FAILURE_CODES = [
  'contextWindowExceeded', 'sessionBudgetExceeded', 'usageLimitExceeded', 'rateLimitExceeded', 'flexUnavailable',
  'serverOverloaded', 'cyberPolicy', 'misalignmentPolicyViolation', 'tooManyDenials', 'httpConnectionFailed',
  'responseStreamConnectionFailed', 'internalServerError', 'unauthorized', 'badRequest', 'threadRollbackFailed',
  'sandboxError', 'responseStreamDisconnected', 'responseTooManyFailedAttempts', 'activeTurnNotSteerable', 'other',
] as const;
export type MathAgentFailureDiagnostic = Readonly<{
  code: typeof CODEX_FAILURE_CODES[number];
  httpStatusCode?: number;
}>;
const HTTP_FAILURE_CODES = new Set(['httpConnectionFailed', 'responseStreamConnectionFailed',
  'responseStreamDisconnected', 'responseTooManyFailedAttempts']);
const failureDiagnostic = (error: Json): MathAgentFailureDiagnostic | undefined => {
  const info = error.codexErrorInfo;
  const structured = info && typeof info === 'object' && !Array.isArray(info) ? info as Json : undefined;
  const keys = structured ? Object.keys(structured) : [];
  const candidate = typeof info === 'string' ? info : keys.length === 1 ? keys[0] : undefined;
  const code = CODEX_FAILURE_CODES.find(value => value === candidate);
  if (!code) return undefined;
  const payload = structured?.[code];
  const status = payload && typeof payload === 'object' && !Array.isArray(payload)
    ? (payload as Json).httpStatusCode : undefined;
  return { code,
    ...(HTTP_FAILURE_CODES.has(code) && typeof status === 'number' && Number.isInteger(status) && status >= 100 && status <= 599
      ? { httpStatusCode: status } : {}) };
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
  onUsageIncomplete?: () => void;
  /** Used by host-controlled upstream bridges; native thread usage remains observational. */
  requestGate?: ModelRequestGate;
  onActivity?: (activity: MathAgentActivity) => void;
};
export type MathAgentSession = {
  threadId: string;
  readonly lastError?: string;
  readonly lastFailureDiagnostic?: MathAgentFailureDiagnostic;
  readonly lastInputTokens?: number;
  readonly usageSource?: 'upstream-requests';
  run: (message: string, messageId: string, workspace: string, onStarted: (turnId: string) => void) => Promise<string>;
  notify?: (message: string) => Promise<void>;
  interrupt: () => Promise<void>;
  close: () => Promise<void>;
};

/** One persistent Codex app-server; all protocol traffic stays on stdio. */
class CodexRpc {
  private child: ChildProcessWithoutNullStreams;
  private nextId = 0;
  private pending = new Map<number, { method: string; resolve: (result: Json) => void; reject: (error: Error) => void; timer: NodeJS.Timeout }>();
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
          const code = typeof error?.code === 'number' && Number.isSafeInteger(error.code) ? error.code : 'invalid_code';
          if (error) call.reject(new Error(`math_codex_rpc_failed:${code}:${call.method}`));
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
      this.pending.set(id, { method, resolve, reject, timer });
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
  const configFile = path.join(options.profile, 'config.toml');
  const profileConfig = fs.existsSync(configFile) ? parseToml(fs.readFileSync(configFile, 'utf8')) : {};
  const providerId = typeof profileConfig.model_provider === 'string' ? profileConfig.model_provider : undefined;
  const provider = typeof profileConfig.model_provider === 'string' && profileConfig.model_providers
    ? profileConfig.model_providers[profileConfig.model_provider] : undefined;
  const envKey = provider && typeof provider === 'object' && typeof provider.env_key === 'string'
    ? provider.env_key : undefined;
  if (envKey && !/^[A-Za-z_][A-Za-z0-9_]{0,127}$/u.test(envKey)) throw new Error('math_model_api_key_environment_invalid');
  const apiKey = envKey ? options.environment?.[envKey] ?? process.env[envKey] : undefined;
  if (envKey && !apiKey?.trim()) throw new Error(`math_model_api_key_missing:${envKey}`);
  const workerEnvironment = options.proofProjectRoot
    ? mathProofEnvironmentWorkerEnvironment(options.proofProjectRoot, options.environment ?? process.env)
    : options.environment;
  const policy = profileConfig.shell_environment_policy ? object(profileConfig.shell_environment_policy) : {};
  const filters = policy.filters;
  const exclude = Array.isArray(policy.exclude) ? policy.exclude.filter((value): value is string => typeof value === 'string') : [];
  const shellCredentialPolicy = !envKey ? {} : filters && typeof filters === 'object'
    ? { 'shell_environment_policy.filters': { ...filters, [envKey]: 'exclude' } }
    : { 'shell_environment_policy.exclude': [...new Set([...exclude, envKey])] };
  // Credentials enter only the provider process, after preparing solver-visible environments.
  let environment = envKey ? { ...(workerEnvironment ?? process.env), [envKey]: apiKey } : workerEnvironment;
  let bridge: Awaited<ReturnType<typeof startChatCompletionsBridge>> | undefined;
  let nativeProfile = options.profile;
  if (providerId === WESTLAKE_PROVIDER.id) {
    if (envKey !== WESTLAKE_PROVIDER.apiKeyEnvironment || provider.base_url !== WESTLAKE_PROVIDER.baseUrl)
      throw new Error('math_westlake_profile_invalid');
    validateWestlakeModel(options.model, options.effort);
  }
  if (providerId === DEEPSEEK_PROVIDER.id || providerId === WESTLAKE_PROVIDER.id) {
    // Codex persists project trust in config.toml; keep those writes outside the frozen profile.
    nativeProfile = path.join(options.profile, 'runtime');
    fs.mkdirSync(nativeProfile, { recursive: true, mode: 0o700 });
    const snapshot = path.join(nativeProfile, `.config-${randomUUID()}.toml`);
    try {
      fs.writeFileSync(snapshot, fs.readFileSync(configFile), { flag: 'wx', mode: 0o600 });
      fs.renameSync(snapshot, path.join(nativeProfile, 'config.toml'));
    } finally { fs.rmSync(snapshot, { force: true }); }
  }
  if (providerId === WESTLAKE_PROVIDER.id) {
    bridge = await startChatCompletionsBridge({ baseUrl: WESTLAKE_PROVIDER.baseUrl, apiKey: apiKey!,
      model: options.model, effort: options.effort, onUsageIncomplete: options.onUsageIncomplete, requestGate: options.requestGate });
    // Codex receives only a disposable loopback credential, including outside proof projections.
    environment = Object.fromEntries(Object.entries(environment ?? process.env)
      .filter(([name]) => !name.startsWith('WESTLAKEHPC_API_KEY')));
    environment[envKey] = bridge.apiKey;
  }
  const providerSettings = providerId ? {
    model_provider: providerId,
    ...(provider && typeof provider.base_url === 'string'
      ? { [`model_providers.${providerId}.base_url`]: bridge?.baseUrl ?? provider.base_url } : {}),
    ...(typeof profileConfig.model_catalog_json === 'string' ? { model_catalog_json: profileConfig.model_catalog_json } : {}),
  } : {};
  let rpc: CodexRpc;
  try { rpc = new CodexRpc(options.executable, nativeProfile, environment); }
  catch (error) { await bridge?.close(); throw error; }
  let closing: Promise<void> | undefined;
  const closeSession = () => closing ??= (async () => {
    try { await rpc.close(); } finally { await bridge?.close(); }
  })();
  let activeTurn: string | undefined;
  let completion: { resolve: (turn: Json) => void; reject: (error: Error) => void } | undefined;
  const earlyCompletions = new Map<string, Json>();
  let lastError: string | undefined;
  let lastFailureDiagnostic: MathAgentFailureDiagnostic | undefined;
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
  rpc.onFailure = error => {
    transportFailure = error; lastError = error.message; lastFailureDiagnostic = undefined; completion?.reject(error);
    void bridge?.close().catch(() => {});
  };
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
    const inherited = profileConfig.mcp_servers;
    const disabled = Object.fromEntries(Object.keys(inherited ?? {}).map(name => [name, { enabled: false }]));
    const settings = {
      model: options.model, cwd: options.workspace,
      approvalPolicy: 'never', sandbox: 'workspace-write',
      developerInstructions: options.instructions,
      config: {
        mcp_servers: disabled,
        'features.apps': false,
        'features.plugins': false,
        // Preserve the projected proof environment; user profiles and shell snapshots
        // can select tools that execute outside the isolated mathematical worktree.
        allow_login_shell: false,
        'features.shell_snapshot': false,
        'shell_environment_policy.experimental_use_profile': false,
        ...(bridge ? { 'features.multi_agent': false, 'features.multi_agent_v2': false,
          'features.goals': false, 'features.view_image': false } : {}),
        model_reasoning_effort: options.effort,
        'sandbox_workspace_write.network_access': true,
        ...shellCredentialPolicy,
        ...providerSettings,
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
    if (providerId && result.modelProvider !== providerId) throw new Error('math_codex_session_binding_mismatch');
    return {
      threadId,
      ...(bridge && options.requestGate ? { usageSource: 'upstream-requests' as const } : {}),
      get lastError() { return lastError; },
      get lastFailureDiagnostic() { return lastFailureDiagnostic; },
      get lastInputTokens() { return lastInputTokens; },
      run: async (message, messageId, workspace, onStarted) => {
        if (transportFailure) throw transportFailure;
        if (completion) throw new Error('math_codex_turn_already_running');
        lastError = undefined;
        lastFailureDiagnostic = undefined;
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
            interruptDeadline = setTimeout(() => { void closeSession(); }, 10_000);
            void rpc.request('turn/interrupt', { threadId, turnId: activeTurn }).catch(() => { void closeSession(); });
          }, options.turnTimeoutMs);
          const early = earlyCompletions.get(activeTurn);
          earlyCompletions.delete(activeTurn);
          if (early) resolve(early);
          const finished = await done;
          if (typeof finished.status !== 'string') throw new Error('math_codex_turn_status_missing');
          if (finished.status === 'failed' && finished.error) {
            const error = object(finished.error);
            lastFailureDiagnostic = failureDiagnostic(error);
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
      close: closeSession,
    };
  } catch (error) { await closeSession(); throw error; }
}
