import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { z } from 'zod';
import { captureLeanProbePackages, type ImmutableLeanProbePackages } from "./leanProbeSnapshot";
import { LEAN_SHARED_ENVIRONMENT_NATIVE } from "./leanSharedEnvironmentNative";

const nativeResult = z.object({
  started: z.boolean(),
  exitCode: z.number().int().nullable(),
  signal: z
    .custom<NodeJS.Signals>((value) => typeof value === 'string' && Object.hasOwn(os.constants.signals, value))
    .nullable(),
  stdout: z.string().max(6 * 1024 * 1024),
  stderr: z.string().max(6 * 1024 * 1024),
  stdoutSha256: z.string().regex(/^[a-f0-9]{64}$/u),
  stderrSha256: z.string().regex(/^[a-f0-9]{64}$/u),
  timedOut: z.boolean(),
  aborted: z.boolean(),
  durationMs: z.number().finite().nonnegative(),
  errorCode: z.string().optional(),
  errorMessage: z.string().optional(),
});
type NativeResult = {
  started: boolean;
  exitCode: number | null;
  signal: NodeJS.Signals | null;
  stdout: string;
  stderr: string;
  stdoutSha256: string;
  stderrSha256: string;
  timedOut: boolean;
  aborted: boolean;
  durationMs: number;
  errorCode?: string;
  errorMessage?: string;
};
type RunOptions = Readonly<{
  cwd: string;
  timeoutMs: number;
  signal?: AbortSignal;
  stdin?: string;
  outputCapture?: 'head' | 'tail';
}>;
type Pending = { resolve: (value: NativeResult) => void; reject: (error: Error) => void };
const leases = new WeakSet<object>();
const brokers = new Set<PackageBroker>();
const cache = new Map<string, PackageBroker>();
const MAX_CACHED_BASES = 2;
const IDLE_MS = 60_000;
const cleanEnvironment = { PATH: '/usr/bin:/bin', LANG: 'C.UTF-8', PYTHONNOUSERSITE: '1' };

export class SharedLeanEnvironmentUnavailableError extends Error {}

class PackageBroker {
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly pending = new Map<string, Pending>();
  private buffer = '';
  private readyResolve!: () => void;
  private readyReject!: (error: Error) => void;
  readonly ready: Promise<void>;
  private failure?: Error;
  private idleTimer?: NodeJS.Timeout;
  private references = 0;
  readonly createdAt = performance.now();
  preparationMs = 0;

  constructor(
    readonly digest: string,
    input: ReturnType<typeof captureLeanProbePackages>,
    timeoutMs: number
  ) {
    this.ready = new Promise<void>((resolve, reject) => {
      this.readyResolve = resolve;
      this.readyReject = reject;
    });
    this.child = spawn('/usr/bin/python3', ['-I', '-c', LEAN_SHARED_ENVIRONMENT_NATIVE], {
      env: cleanEnvironment,
      detached: true,
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    brokers.add(this);
    this.child.stdin.on('error', (error: NodeJS.ErrnoException) => {
      if (error.code !== 'EPIPE') this.fail(new Error('Shared Lean dependency broker input closed.'));
    });
    this.child.stderr.resume();
    this.child.on('error', (error) => this.fail(error));
    this.child.on('close', () => this.fail(new Error('Shared Lean dependency broker exited.')));
    this.child.stdout.setEncoding('utf8');
    this.child.stdout.on('data', (chunk: string) => {
      this.buffer += chunk;
      if (this.buffer.length > 16 * 1024 * 1024) {
        this.fail(new Error('Shared Lean broker response exceeds its limit.'));
        return;
      }
      let boundary: number;
      while ((boundary = this.buffer.indexOf('\n')) >= 0) {
        const line = this.buffer.slice(0, boundary);
        this.buffer = this.buffer.slice(boundary + 1);
        try {
          const message: unknown = JSON.parse(line);
          if (!message || typeof message !== 'object' || Array.isArray(message))
            throw new Error('Invalid shared Lean broker response.');
          const frame = message as Record<string, unknown>;
          if (frame.ready === true) {
            this.preparationMs = performance.now() - this.createdAt;
            this.readyResolve();
          } else if (frame.ready === false) {
            const detail = `Shared Lean environment unavailable: ${String(frame.errorCode ?? 'prepare_failed')}`;
            throw frame.failureKind === 'capability'
              ? new SharedLeanEnvironmentUnavailableError(detail)
              : new Error(detail);
          } else if (typeof frame.id === 'string' && frame.result) {
            const request = this.pending.get(frame.id);
            if (!request) throw new Error('Unexpected shared Lean broker response.');
            const parsed = nativeResult.parse(frame.result) as NativeResult;
            this.pending.delete(frame.id);
            request.resolve(parsed);
          } else if (frame.closed !== true) throw new Error('Invalid shared Lean broker response.');
        } catch (error) {
          this.fail(error instanceof Error ? error : new Error(String(error)));
        }
      }
    });
    this.send({
      op: 'prepare',
      files: input.files.map(({ path, sha256, ...entry }) => ({ ...entry, relative: path, digest: sha256 })),
      maxBytes: Math.max(1, input.bytes),
      timeoutMs,
    });
  }

  private send(message: unknown) {
    if (this.failure) throw this.failure;
    this.child.stdin.write(`${JSON.stringify(message)}\n`);
  }

  private fail(error: Error) {
    if (this.failure) return;
    this.failure = error;
    this.readyReject(error);
    for (const pending of this.pending.values()) pending.reject(error);
    this.pending.clear();
    if (cache.get(this.digest) === this) cache.delete(this.digest);
    brokers.delete(this);
    clearTimeout(this.idleTimer);
    if (this.child.pid) {
      try {
        process.kill(-this.child.pid, 'SIGKILL');
      } catch {
        /* Already reaped. */
      }
    }
    this.child.stdin.destroy();
    this.child.stdout.destroy();
    this.child.stderr.destroy();
  }

  assertLive() {
    if (this.failure) throw this.failure;
  }

  retain() {
    this.assertLive();
    clearTimeout(this.idleTimer);
    this.references++;
  }

  release() {
    this.references--;
    if (this.references === 0) {
      if (cache.get(this.digest) !== this) this.close();
      else {
        this.idleTimer = setTimeout(() => this.close(), IDLE_MS);
        this.idleTimer.unref();
      }
    }
  }

  close() {
    this.fail(new Error('Shared Lean dependency broker disposed.'));
  }

  async run(args: readonly string[], options: RunOptions): Promise<NativeResult> {
    this.assertLive();
    if (options.signal?.aborted) throw new Error('Source probe deadline exceeded or cancelled.');
    const id = crypto.randomUUID();
    const response = new Promise<NativeResult>((resolve, reject) => this.pending.set(id, { resolve, reject }));
    const abort = () => {
      try {
        this.send({ op: 'cancel', id });
      } catch {
        /* Exit already rejects the request. */
      }
    };
    const timer = setTimeout(
      () => this.fail(new Error('Shared Lean broker failed to finish bounded cleanup.')),
      options.timeoutMs + 5_000
    );
    options.signal?.addEventListener('abort', abort, { once: true });
    try {
      this.send({
        op: 'run',
        id,
        argv: ['/usr/bin/bwrap', ...args],
        cwd: options.cwd,
        env: cleanEnvironment,
        timeoutMs: options.timeoutMs,
        stdin: options.stdin ?? '',
        outputCapture: options.outputCapture ?? 'tail',
      });
      if (options.signal?.aborted) abort();
      return await response;
    } finally {
      clearTimeout(timer);
      options.signal?.removeEventListener('abort', abort);
    }
  }
}

export type SharedLeanPackagesLease = ImmutableLeanProbePackages &
  Readonly<{
    run: (args: readonly string[], options: RunOptions) => Promise<NativeResult>;
    release: () => void;
    metrics: Readonly<{ cacheHit: boolean; inputScanMs: number; sealMs: number; sealedBytes: number }>;
  }>;

/** Only runtime-created leases may select the protected transport. Never deserialize a lease. */
export function assertSharedLeanPackagesLease(value: SharedLeanPackagesLease): void {
  if (!leases.has(value)) throw new Error('Invalid shared Lean dependency lease.');
}

export function sharedLeanPackagesUnavailableReason(): string | undefined {
  if (process.platform !== 'linux' || !['x64', 'arm64'].includes(process.arch)) return 'unsupported_platform';
  for (const executable of ['/usr/bin/python3', '/usr/bin/bwrap']) {
    try {
      const stat = fs.statSync(executable);
      if (!stat.isFile() || stat.uid !== 0 || stat.mode & 0o022 || !(stat.mode & 0o111)) return 'untrusted_helper';
    } catch {
      return 'missing_helper';
    }
  }
  for (const directory of ['/', '/mnt', '/run']) {
    try {
      const stat = fs.lstatSync(directory);
      if (!stat.isDirectory() || stat.uid !== 0 || stat.mode & 0o022) return 'unprotected_mount_root';
    } catch {
      return 'missing_mount_root';
    }
  }
  try {
    fs.accessSync('/dev/fuse', fs.constants.R_OK | fs.constants.W_OK);
  } catch {
    return 'fuse_unavailable';
  }
  return undefined;
}

export async function acquireSharedLeanPackages(
  sourceRoot: string,
  options: Readonly<{ signal?: AbortSignal; deadlineAt: number }>
): Promise<SharedLeanPackagesLease> {
  const unavailable = sharedLeanPackagesUnavailableReason();
  if (unavailable)
    throw new SharedLeanEnvironmentUnavailableError(`Shared Lean environment unavailable: ${unavailable}`);
  const started = performance.now();
  const capture = captureLeanProbePackages(sourceRoot, options);
  if (!capture.files.length)
    throw new SharedLeanEnvironmentUnavailableError('Shared Lean environment unavailable: empty_packages');
  const inputScanMs = performance.now() - started;
  let broker = cache.get(capture.digest);
  const cacheHit = Boolean(broker);
  if (!broker) {
    if (brokers.size >= MAX_CACHED_BASES)
      throw new SharedLeanEnvironmentUnavailableError('Shared Lean environment unavailable: capacity');
    broker = new PackageBroker(capture.digest, capture, Math.max(1, options.deadlineAt - Date.now()));
    if (cache.size < MAX_CACHED_BASES) cache.set(capture.digest, broker);
  }
  broker.retain();
  const selected = broker;
  let rejectWait!: (error: Error) => void;
  const interrupted = new Promise<never>((_resolve, reject) => {
    rejectWait = reject;
  });
  const abort = () => {
    rejectWait(new Error('Source probe deadline exceeded or cancelled.'));
    if (!cacheHit) selected.close();
  };
  const remainingMs = options.deadlineAt - Date.now();
  const timer = setTimeout(abort, Math.max(1, remainingMs));
  options.signal?.addEventListener('abort', abort, { once: true });
  try {
    if (remainingMs <= 0 || options.signal?.aborted) throw new Error('Source probe deadline exceeded or cancelled.');
    await Promise.race([selected.ready, interrupted]);
    if (Date.now() >= options.deadlineAt || options.signal?.aborted)
      throw new Error('Source probe deadline exceeded or cancelled.');
    let released = false;
    const assertActive = () => {
      if (released) throw new Error('Shared Lean dependency lease disposed.');
      selected.assertLive();
    };
    const lease: SharedLeanPackagesLease = Object.freeze({
      sourceRoot,
      digest: capture.digest,
      fileCount: capture.fileCount,
      bytes: capture.bytes,
      packageNames: capture.packageNames,
      verify: () => {
        assertActive();
        capture.verify();
      },
      run: (args, runOptions) => {
        assertActive();
        return selected.run(args, runOptions);
      },
      release: () => {
        if (!released) {
          released = true;
          selected.release();
        }
      },
      metrics: Object.freeze({
        cacheHit,
        inputScanMs,
        sealMs: cacheHit ? 0 : selected.preparationMs,
        sealedBytes: cacheHit ? 0 : capture.bytes,
      }),
    });
    leases.add(lease);
    return lease;
  } catch (error) {
    selected.release();
    throw error;
  } finally {
    clearTimeout(timer);
    options.signal?.removeEventListener('abort', abort);
  }
}

export function closeAllSharedLeanPackages(): void {
  for (const broker of brokers) broker.close();
}

process.once('exit', closeAllSharedLeanPackages);
