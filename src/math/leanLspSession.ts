import { resolveMathProofEnvironment } from "./mathProofEnvironment";
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import {
  startMathematicsSandboxedSession,
  type MathematicsSandboxDuplex,
  type MathematicsSandboxCommandResult,
} from "./verifier";

type Message = {
  id?: number | string;
  method?: string;
  params?: Record<string, unknown>;
  result?: unknown;
  error?: unknown;
};
type Diagnostic = {
  severity?: number;
  message?: string;
  range?: { start?: { line: number; character: number } };
  fullRange?: { start: { line: number; character: number }; end: { line: number; character: number } };
};
type Pending = { resolve: (value: unknown) => void; reject: (reason: Error) => void };
const liveSessions = new Set<MathematicsLeanLspSession>();

export type LeanLspFallbackDisposition = 'timed_out' | 'aborted' | 'unavailable';

class LeanLspExecutionError extends Error {
  constructor(
    message: string,
    readonly disposition: LeanLspFallbackDisposition
  ) {
    super(message);
    this.name = 'LeanLspExecutionError';
  }
}

export async function closeAllMathematicsLeanLspSessions(): Promise<void> {
  await Promise.allSettled([...liveSessions].map((session) => session.close()));
}

export type LeanLspSessionOptions = Readonly<{
  workspaceRoot: string;
  projectRelative?: string;
  sourceFile: string;
  env?: NodeJS.ProcessEnv;
  lakePackagesPath?: string;
}>;

/** Imports are cached by Lean. Restart when an editable dependency or project configuration changes. */
const dependencyIdentity = (
  options: LeanLspSessionOptions
): Readonly<{ fingerprint: string; structuralFingerprint: string; manifestPresent: boolean }> => {
  const root = path.resolve(options.workspaceRoot, options.projectRelative ?? '');
  const hash = crypto.createHash('sha256');
  const structuralHash = crypto.createHash('sha256');
  let manifestPresent = false;
  const excludedDirectories = new Set([
    '.git',
    '.lake',
    '.deepscientist',
    'reference',
    'references',
    'solution',
    'solutions',
    'benchmark',
    'benchmarks',
    'test',
    'tests',
  ]);
  const visit = (directory: string): void => {
    for (const entry of fs
      .readdirSync(directory, { withFileTypes: true })
      .toSorted((a, b) => a.name.localeCompare(b.name))) {
      if (excludedDirectories.has(entry.name.toLowerCase()) || /^(?:solution|workspacetest)\.lean$/iu.test(entry.name))
        continue;
      const file = path.join(directory, entry.name);
      const relative = path.relative(root, file).replaceAll(path.sep, '/');
      if (relative === options.sourceFile) continue;
      if (entry.isSymbolicLink()) throw new Error('Lean LSP dependency tree contains a symlink');
      if (entry.isDirectory()) visit(file);
      else if (
        entry.name.endsWith('.lean') ||
        ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml'].includes(entry.name)
      ) {
        const content = fs.readFileSync(file);
        hash.update(relative).update('\0').update(content).update('\0');
        if (entry.name === 'lake-manifest.json') manifestPresent = true;
        else structuralHash.update(relative).update('\0').update(content).update('\0');
      }
    }
  };
  visit(root);
  // The mounted dependencies are immutable for a pinned manifest. Include the
  // cache identity and package revisions without opening any proof sources.
  const sealed = resolveMathProofEnvironment(root, options.env ?? process.env);
  if (sealed) {
    if (options.lakePackagesPath && options.lakePackagesPath !== sealed.packagesRoot)
      throw new Error('Lean LSP sealed package identity mismatch');
    hash.update(sealed.identity);
    structuralHash.update(sealed.identity);
  } else if (options.lakePackagesPath) {
    const packagesRoot = fs.realpathSync(options.lakePackagesPath);
    hash.update(packagesRoot);
    structuralHash.update(packagesRoot);
    for (const entry of fs
      .readdirSync(options.lakePackagesPath, { withFileTypes: true })
      .toSorted((a, b) => a.name.localeCompare(b.name))) {
      if (!entry.isDirectory() || entry.isSymbolicLink()) continue;
      const head = path.join(options.lakePackagesPath, entry.name, '.git', 'HEAD');
      if (fs.existsSync(head)) {
        const value = fs.readFileSync(head, 'utf8').trim();
        hash.update(entry.name).update(value);
        structuralHash.update(entry.name).update(value);
        if (/^ref: refs\/[A-Za-z0-9_./-]+$/u.test(value) && !value.includes('..')) {
          const ref = path.join(options.lakePackagesPath, entry.name, '.git', value.slice(5));
          if (fs.existsSync(ref)) {
            const revision = fs.readFileSync(ref);
            hash.update(revision);
            structuralHash.update(revision);
          }
        }
      }
    }
  }
  return Object.freeze({
    fingerprint: hash.digest('hex'),
    structuralFingerprint: structuralHash.digest('hex'),
    manifestPresent,
  });
};

export type LeanDependencyIdentity =
  | Readonly<{
      status: 'known';
      fingerprint: string;
      structuralFingerprint: string;
      manifestPresent: boolean;
    }>
  | Readonly<{ status: 'unavailable'; reason: string }>;

/** Lake may materialize a previously absent manifest before the first check. */
export const isLeanDependencyBootstrapTransition = (
  before: LeanDependencyIdentity,
  after: LeanDependencyIdentity
): boolean =>
  before.status === 'known' &&
  after.status === 'known' &&
  !before.manifestPresent &&
  after.manifestPresent &&
  before.structuralFingerprint === after.structuralFingerprint;

/** Read the dependency identity without treating an unreadable tree as a valid identity. */
export const readLeanDependencyIdentity = (options: LeanLspSessionOptions): LeanDependencyIdentity => {
  try {
    return Object.freeze({ status: 'known', ...dependencyIdentity(options) });
  } catch (error) {
    return Object.freeze({
      status: 'unavailable',
      reason: error instanceof Error ? error.message : String(error),
    });
  }
};

/** A versioned Lean language-server connection; final acceptance still uses the independent verifier. */
export class MathematicsLeanLspSession {
  private transport?: MathematicsSandboxDuplex;
  private buffer = Buffer.alloc(0);
  private nextId = 0;
  private version = 0;
  private readonly pending = new Map<number, Pending>();
  private diagnostics: Diagnostic[] = [];
  private diagnosticVersion?: number;
  private identity?: string;
  private queue: Promise<unknown> = Promise.resolve();
  private disabled = false;
  private closed = false;
  private lastCheckedIdentity?: string;
  private readonly uri: string;
  private readonly rootUri: string;
  fallbackReason?: string;
  fallbackDisposition?: LeanLspFallbackDisposition;

  get dependencyFingerprint(): string | undefined {
    const identity = readLeanDependencyIdentity(this.options);
    return identity.status === 'known' ? identity.fingerprint : undefined;
  }

  /** Identity captured before and after the most recent successful check. */
  get checkedDependencyFingerprint(): string | undefined {
    return this.lastCheckedIdentity;
  }

  constructor(private readonly options: LeanLspSessionOptions) {
    liveSessions.add(this);
    this.rootUri = `file:///workspace${options.projectRelative ? `/${options.projectRelative.split('/').map(encodeURIComponent).join('/')}` : ''}`;
    this.uri = `${this.rootUri}/${options.sourceFile.split('/').map(encodeURIComponent).join('/')}`;
  }

  private fail(error: Error): void {
    for (const request of this.pending.values()) request.reject(error);
    this.pending.clear();
  }

  private readonly receive = (chunk: Buffer | string): void => {
    try {
      this.buffer = Buffer.concat([this.buffer, Buffer.from(chunk)]);
      while (true) {
        const boundary = this.buffer.indexOf('\r\n\r\n');
        if (boundary < 0) {
          if (this.buffer.length > 8_192) throw new Error('Lean LSP frame header is invalid');
          return;
        }
        const length = Number(
          /(?:^|\r\n)Content-Length:\s*(\d+)/iu.exec(this.buffer.subarray(0, boundary).toString())?.[1]
        );
        if (!Number.isSafeInteger(length) || length < 0 || length > 32 * 1024 * 1024)
          throw new Error('Lean LSP frame length is invalid');
        if (this.buffer.length < boundary + 4 + length) return;
        const message = JSON.parse(this.buffer.subarray(boundary + 4, boundary + 4 + length).toString()) as Message;
        this.buffer = this.buffer.subarray(boundary + 4 + length);
        if (message.method && message.id !== undefined) {
          if (message.method === 'client/registerCapability' || message.method === 'client/unregisterCapability')
            this.send({ id: message.id, result: null });
          else if (message.method === 'workspace/configuration')
            this.send({
              id: message.id,
              result: Array.isArray(message.params?.items) ? message.params.items.map(() => ({})) : [],
            });
          else this.send({ id: message.id, error: { code: -32601, message: 'Client request is not supported' } });
        } else if (typeof message.id === 'number') {
          const request = this.pending.get(message.id);
          if (request) {
            this.pending.delete(message.id);
            if (message.error) request.reject(new Error(`Lean LSP request failed: ${JSON.stringify(message.error)}`));
            else request.resolve(message.result);
          }
        } else if (
          message.method === 'textDocument/publishDiagnostics' &&
          message.params?.uri === this.uri &&
          message.params.version === this.version
        ) {
          this.diagnostics = Array.isArray(message.params.diagnostics)
            ? (message.params.diagnostics as Diagnostic[])
            : [];
          this.diagnosticVersion = this.version;
        }
      }
    } catch (error) {
      this.fail(error instanceof Error ? error : new Error(String(error)));
      void this.stopTransport();
    }
  };

  private send(message: Message): void {
    if (!this.transport) throw new Error('Lean LSP transport is closed');
    const body = JSON.stringify({ jsonrpc: '2.0', ...message });
    this.transport.input.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  }

  private request(
    method: string,
    params: Record<string, unknown>,
    timeoutMs: number,
    signal?: AbortSignal
  ): Promise<unknown> {
    return new Promise((resolve, reject) => {
      const id = ++this.nextId;
      let timer: NodeJS.Timeout;
      const cleanup = () => {
        clearTimeout(timer);
        signal?.removeEventListener('abort', abort);
        this.pending.delete(id);
      };
      const abort = () => {
        cleanup();
        reject(new LeanLspExecutionError('Lean LSP request aborted', 'aborted'));
      };
      timer = setTimeout(() => {
        cleanup();
        reject(new LeanLspExecutionError(`Lean LSP ${method} timed out`, 'timed_out'));
      }, timeoutMs);
      this.pending.set(id, {
        resolve: (value) => {
          cleanup();
          resolve(value);
        },
        reject: (error) => {
          cleanup();
          reject(error);
        },
      });
      signal?.addEventListener('abort', abort, { once: true });
      if (signal?.aborted) {
        abort();
        return;
      }
      try {
        this.send({ id, method, params });
      } catch (error) {
        cleanup();
        reject(error);
      }
    });
  }

  private async start(deadline: number, signal?: AbortSignal): Promise<void> {
    const startupSignal = new AbortController();
    let deadlineExpired = false;
    const forwardAbort = () => startupSignal.abort();
    signal?.addEventListener('abort', forwardAbort, { once: true });
    const startupTimer = setTimeout(
      () => {
        deadlineExpired = true;
        startupSignal.abort();
      },
      Math.max(1, Math.ceil(deadline - performance.now()))
    );
    try {
      const transport = await startMathematicsSandboxedSession({
        checkoutRoot: this.options.workspaceRoot,
        projectRelative: this.options.projectRelative,
        command: 'lake',
        args: ['env', 'lean', '--server'],
        env: this.options.env,
        lakePackagesPath: this.options.lakePackagesPath,
        signal: startupSignal.signal,
      });
      if (deadlineExpired || performance.now() >= deadline) {
        await transport.close();
        throw new LeanLspExecutionError('Lean LSP startup timed out', 'timed_out');
      }
      if (this.closed) {
        await transport.close();
        throw new LeanLspExecutionError('Lean LSP session was closed during startup', 'unavailable');
      }
      this.transport = transport;
      this.buffer = Buffer.alloc(0);
      this.version = 0;
      transport.output.on('data', this.receive);
      void transport.done.then(
        (result) => {
          if (this.transport === transport) {
            this.fail(
              new Error(
                `Lean LSP process exited (${result.sandboxBackend ?? 'unknown'}): ${result.errorMessage || result.stderr.slice(-2_000) || result.exitCode}`
              )
            );
            void this.stopTransport();
          }
        },
        (error) => {
          if (this.transport === transport) {
            this.fail(error instanceof Error ? error : new Error(String(error)));
            void this.stopTransport();
          }
        }
      );
      const initializeTimeoutMs = deadline - performance.now();
      if (initializeTimeoutMs <= 0) throw new LeanLspExecutionError('Lean LSP initialize timed out', 'timed_out');
      await this.request(
        'initialize',
        {
          processId: null,
          rootUri: this.rootUri,
          capabilities: { textDocument: { publishDiagnostics: { versionSupport: true } } },
          initializationOptions: { hasWidgets: false },
        },
        initializeTimeoutMs,
        startupSignal.signal
      );
      this.send({ method: 'initialized', params: {} });
    } catch (error) {
      if (deadlineExpired) throw new LeanLspExecutionError('Lean LSP startup timed out', 'timed_out');
      if (signal?.aborted) throw new LeanLspExecutionError('Lean LSP startup aborted', 'aborted');
      throw error;
    } finally {
      clearTimeout(startupTimer);
      signal?.removeEventListener('abort', forwardAbort);
    }
  }

  compile(
    source: string,
    timeoutMs: number,
    signal?: AbortSignal
  ): Promise<MathematicsSandboxCommandResult | undefined> {
    const effectiveTimeoutMs = Number.isFinite(timeoutMs) ? Math.max(1, Math.floor(timeoutMs)) : 30_000;
    const deadline = performance.now() + effectiveTimeoutMs;
    const operation = this.queue.then(async () => {
      if (this.closed) {
        this.fallbackReason = 'Lean LSP session is closed';
        this.fallbackDisposition = 'unavailable';
        return undefined;
      }
      if (this.disabled) {
        this.fallbackDisposition = 'unavailable';
        return undefined;
      }
      this.fallbackReason = undefined;
      this.fallbackDisposition = undefined;
      const started = performance.now();
      try {
        if (signal?.aborted) throw new LeanLspExecutionError('Lean LSP request aborted while queued', 'aborted');
        if (deadline <= started)
          throw new LeanLspExecutionError('Lean LSP request timed out while queued', 'timed_out');
        const identityBefore = readLeanDependencyIdentity(this.options);
        if (identityBefore.status === 'unavailable')
          throw new LeanLspExecutionError(
            `Lean LSP dependency environment is unavailable: ${identityBefore.reason}`,
            'unavailable'
          );
        const reusedTransport = Boolean(this.transport && identityBefore.fingerprint === this.identity);
        if (this.transport && !reusedTransport) await this.stopTransport();
        if (!this.transport) await this.start(deadline, signal);
        const identityAtStart = reusedTransport ? identityBefore : readLeanDependencyIdentity(this.options);
        if (identityAtStart.status === 'unavailable')
          throw new LeanLspExecutionError(
            `Lean LSP dependency environment is unavailable: ${identityAtStart.reason}`,
            'unavailable'
          );
        if (
          identityAtStart.fingerprint !== identityBefore.fingerprint &&
          !isLeanDependencyBootstrapTransition(identityBefore, identityAtStart)
        ) {
          throw new LeanLspExecutionError('Lean LSP dependency environment changed before checking', 'unavailable');
        }
        this.identity = identityAtStart.fingerprint;
        this.lastCheckedIdentity = undefined;
        this.version += 1;
        this.diagnostics = [];
        this.diagnosticVersion = undefined;
        this.send(
          this.version === 1
            ? {
                method: 'textDocument/didOpen',
                params: { textDocument: { uri: this.uri, languageId: 'lean4', version: this.version, text: source } },
              }
            : {
                method: 'textDocument/didChange',
                params: { textDocument: { uri: this.uri, version: this.version }, contentChanges: [{ text: source }] },
              }
        );
        // Lean's own barrier waits for both elaboration and diagnostic publication.
        const diagnosticTimeoutMs = deadline - performance.now();
        if (diagnosticTimeoutMs <= 0) throw new LeanLspExecutionError('Lean LSP diagnostics timed out', 'timed_out');
        await this.request(
          'textDocument/waitForDiagnostics',
          { uri: this.uri, version: this.version },
          diagnosticTimeoutMs,
          signal
        );
        if (this.diagnosticVersion !== this.version)
          throw new Error('Lean LSP did not publish diagnostics for the requested document version');
        const identityAfter = readLeanDependencyIdentity(this.options);
        if (identityAfter.status === 'unavailable')
          throw new LeanLspExecutionError(
            `Lean LSP dependency environment is unavailable after checking: ${identityAfter.reason}`,
            'unavailable'
          );
        if (
          identityAfter.fingerprint !== identityAtStart.fingerprint &&
          !isLeanDependencyBootstrapTransition(identityAtStart, identityAfter)
        ) {
          throw new LeanLspExecutionError('Lean LSP dependency environment changed during checking', 'unavailable');
        }
        const errors = this.diagnostics.filter((diagnostic) => diagnostic.severity === 1);
        const stdout = this.diagnostics
          .map((diagnostic) =>
            JSON.stringify({
              severity: diagnostic.severity === 1 ? 'error' : 'warning',
              data: diagnostic.message ?? '',
              pos: { line: (diagnostic.range?.start?.line ?? 0) + 1, column: diagnostic.range?.start?.character ?? 0 },
              ...(diagnostic.fullRange
                ? {
                    pos: { line: diagnostic.fullRange.start.line + 1, column: diagnostic.fullRange.start.character },
                    endPos: { line: diagnostic.fullRange.end.line + 1, column: diagnostic.fullRange.end.character },
                  }
                : {}),
            })
          )
          .join('\n');
        const result: MathematicsSandboxCommandResult = {
          started: true,
          exitCode: errors.length ? 1 : 0,
          signal: null,
          timedOut: false,
          aborted: false,
          stdout,
          stderr: '',
          durationMs: performance.now() - started,
        };
        this.lastCheckedIdentity = identityAfter.fingerprint;
        return result;
      } catch (error) {
        this.fallbackReason = error instanceof Error ? error.message : String(error);
        this.fallbackDisposition =
          error instanceof LeanLspExecutionError ? error.disposition : signal?.aborted ? 'aborted' : 'unavailable';
        // Cancellation belongs to the current request. Close the transport so
        // queued work cannot observe a half-finished document, but allow a
        // later request to create a fresh session once its own signal is live.
        // Typed request/environment failures are recoverable.  Keep the
        // permanent disabled fallback only for untyped transport/protocol
        // failures; a timeout or an unreadable environment must be allowed to
        // recover on a later request.
        this.disabled = !(error instanceof LeanLspExecutionError) && this.fallbackDisposition === 'unavailable';
        await this.stopTransport();
        return undefined;
      }
    });
    this.queue = operation;
    return operation;
  }

  private async stopTransport(): Promise<void> {
    const transport = this.transport;
    this.transport = undefined;
    if (!transport) return;
    transport.output.removeListener('data', this.receive);
    this.fail(new Error('Lean LSP transport closed'));
    await transport.close();
  }

  async close(): Promise<void> {
    this.closed = true;
    liveSessions.delete(this);
    await this.stopTransport();
  }
}
