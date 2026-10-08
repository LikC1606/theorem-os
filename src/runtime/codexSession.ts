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
  mcpServers: Json;
  threadId?: string;
  onUsage: (usage: Json) => void;
};
export type MathAgentSession = {
  threadId: string;
  run: (message: string, messageId: string, workspace: string, onStarted: (turnId: string) => void) => Promise<string>;
  interrupt: () => Promise<void>;
  close: () => Promise<void>;
};

/** One persistent Codex app-server per role; all protocol traffic stays on stdio. */
class CodexRpc {
  private child: ChildProcessWithoutNullStreams;
  private nextId = 0;
  private pending = new Map<number, { resolve: (result: Json) => void; reject: (error: Error) => void; timer: NodeJS.Timeout }>();
  private failure?: Error;
  private exit: Promise<void>;
  onNotification: (method: string, params: Json) => void = () => {};
  onFailure: (error: Error) => void = () => {};

  constructor(executable: string, profile: string) {
    this.child = spawn(executable, ['app-server', '--listen', 'stdio://'], {
      env: { ...process.env, CODEX_HOME: profile }, stdio: 'pipe',
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
  const rpc = new CodexRpc(options.executable, options.profile);
  let activeTurn: string | undefined;
  let completion: { resolve: (status: string) => void; reject: (error: Error) => void } | undefined;
  const earlyCompletions = new Map<string, string>();
  let transportFailure: Error | undefined;
  rpc.onFailure = error => { transportFailure = error; completion?.reject(error); };
  rpc.onNotification = (method, params) => {
    if (method === 'thread/tokenUsage/updated') options.onUsage(params.tokenUsage?.total ?? {});
    if (method === 'turn/completed') {
      const turn = params.turn;
      if (!turn || typeof turn.id !== 'string') return;
      if (turn.id === activeTurn && completion) completion.resolve(turn.status);
      else earlyCompletions.set(turn.id, turn.status);
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
        mcp_servers: { ...disabled, ...options.mcpServers },
        model_reasoning_effort: options.effort,
        'sandbox_workspace_write.network_access': true,
      },
    };
    const result = await rpc.request(options.threadId ? 'thread/resume' : 'thread/start', {
      ...settings, ...(options.threadId ? { threadId: options.threadId } : {}),
    });
    const threadId = result.thread?.id;
    if (typeof threadId !== 'string' || !threadId) throw new Error('math_codex_thread_missing');
    if (result.model !== options.model || result.reasoningEffort !== options.effort || result.approvalPolicy !== 'never')
      throw new Error('math_codex_session_binding_mismatch');
    // Check the actual role catalog before allowing its first model turn.
    const deadline = Date.now() + 60_000;
    for (;;) {
      let cursor: string | null = null;
      const catalogs: Json[] = [];
      do {
        const page = await rpc.request('mcpServerStatus/list', { threadId, cursor, limit: 100 });
        if (!Array.isArray(page.data)) throw new Error('math_codex_mcp_catalog_invalid');
        catalogs.push(...page.data);
        cursor = page.nextCursor ?? null;
      } while (cursor);
      if (Object.keys(options.mcpServers).every(name => {
        const catalog = catalogs.find(item => item.name === name);
        return catalog && !catalog.toolsError && Object.keys(catalog.tools ?? {}).length && catalog.runtimeStatus === 'connected';
      })) break;
      if (Date.now() >= deadline) throw new Error('math_codex_mcp_not_ready');
      await new Promise(resolve => setTimeout(resolve, 100));
    }
    return {
      threadId,
      run: async (message, messageId, workspace, onStarted) => {
        if (transportFailure) throw transportFailure;
        if (completion) throw new Error('math_codex_turn_already_running');
        let resolve!: (status: string) => void;
        let reject!: (error: Error) => void;
        const done = new Promise<string>((yes, no) => { resolve = yes; reject = no; });
        // Attach immediately so a transport failure during turn/start is handled.
        void done.catch(() => {});
        completion = { resolve, reject };
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
          const early = earlyCompletions.get(activeTurn);
          earlyCompletions.delete(activeTurn);
          if (early) resolve(early);
          return await done;
        } finally { activeTurn = undefined; completion = undefined; }
      },
      interrupt: async () => {
        if (activeTurn) await rpc.request('turn/interrupt', { threadId, turnId: activeTurn });
      },
      close: () => rpc.close(),
    };
  } catch (error) { await rpc.close(); throw error; }
}
