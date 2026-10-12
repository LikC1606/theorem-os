import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { createInterface } from 'node:readline';
import fs from 'node:fs';
import path from 'node:path';
import { parse as parseToml } from 'smol-toml';

type Json = Record<string, any>;
export type MathAgentOptions = {
  executable: string;
  profile: string;
  workspace: string;
  model: string;
  effort: string;
  instructions: string;
  environment?: NodeJS.ProcessEnv;
  threadId?: string;
  turnTimeoutMs?: number;
  onUsage: (usage: Json) => void;
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
  private exit: Promise<void>;
  onNotification: (method: string, params: Json) => void = () => {};
  onFailure: (error: Error) => void = () => {};

  constructor(executable: string, profile: string, environment: NodeJS.ProcessEnv = process.env) {
    this.child = spawn(executable, ['app-server', '--listen', 'stdio://'], {
      env: { ...environment, CODEX_HOME: profile }, stdio: 'pipe',
    });
    // Do not forward provider diagnostics, which can contain credentials or task text.
    this.child.stderr.resume();
    this.exit = new Promise(resolve => this.child.once('close', () => resolve()));
    const fail = () => {
      if (this.failure) return;
      this.failure = new Error('math_codex_transport_closed');
      for (const call of this.pending.values()) { clearTimeout(call.timer); call.reject(this.failure); }
      this.pending.clear();
      this.onFailure(this.failure);
    };
    this.child.once('error', fail);
    this.child.once('close', fail);
    this.child.stdin.on('error', fail);
    createInterface({ input: this.child.stdout }).on('line', line => {
      try {
        if (line.length > 8 * 1024 * 1024) throw new Error();
        const message: Json = JSON.parse(line);
        if (message.method && message.id !== undefined) {
          // Headless math never grants an interactive permission request.
          this.write({ id: message.id, error: { code: -32601, message: 'Interactive requests are unavailable in headless mathematics' } });
        } else if (message.method) {
          this.onNotification(message.method, message.params ?? {});
        } else {
          const call = this.pending.get(message.id);
          if (!call) return;
          this.pending.delete(message.id);
          clearTimeout(call.timer);
          if (message.error) call.reject(new Error(`math_codex_rpc_failed:${message.error.code}`));
          else call.resolve(message.result ?? {});
        }
      } catch { fail(); this.child.kill('SIGTERM'); }
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
      this.write({ id, method, params });
    });
  }

  async initialize(): Promise<void> {
    await this.request('initialize', { clientInfo: { name: 'deepscientist-math', version: '0.1.0' }, capabilities: null });
    this.write({ method: 'initialized' });
  }

  async close(): Promise<void> {
    this.child.kill('SIGTERM');
    const timer = setTimeout(() => this.child.kill('SIGKILL'), 3000);
    try { await this.exit; } finally { clearTimeout(timer); }
  }
}

export async function createCodexMathSession(options: MathAgentOptions): Promise<MathAgentSession> {
  const rpc = new CodexRpc(options.executable, options.profile, options.environment);
  let activeTurn: string | undefined;
  let completion: { resolve: (turn: Json) => void; reject: (error: Error) => void } | undefined;
  const earlyCompletions = new Map<string, Json>();
  let lastError: string | undefined;
  let lastInputTokens = 0;
  let transportFailure: Error | undefined;
  rpc.onFailure = error => { transportFailure = error; completion?.reject(error); };
  rpc.onNotification = (method, params) => {
    if (method === 'thread/tokenUsage/updated') {
      lastInputTokens = params.tokenUsage?.last?.inputTokens ?? 0;
      options.onUsage(params.tokenUsage?.total ?? {});
    }
    if (method === 'turn/completed') {
      const turn = params.turn;
      if (!turn || typeof turn.id !== 'string') return;
      if (turn.id === activeTurn && completion) completion.resolve(turn);
      else earlyCompletions.set(turn.id, turn);
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
        model_reasoning_effort: options.effort,
        'sandbox_workspace_write.network_access': true,
      },
    };
    const result = await rpc.request(options.threadId ? 'thread/resume' : 'thread/start', {
      ...settings, ...(options.threadId ? { threadId: options.threadId } : {}),
    });
    const threadId = result.thread?.id;
    if (typeof threadId !== 'string' || !threadId) throw new Error('math_codex_thread_missing');
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
          activeTurn = started.turn?.id;
          if (!activeTurn) throw new Error('math_codex_turn_missing');
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
          if (finished.status === 'failed' && typeof finished.error?.message === 'string') lastError = finished.error.message;
          return checkpoint && finished.status === 'interrupted' ? 'checkpoint' : finished.status;
        } finally {
          clearTimeout(timer); clearTimeout(interruptDeadline);
          activeTurn = undefined; completion = undefined;
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
