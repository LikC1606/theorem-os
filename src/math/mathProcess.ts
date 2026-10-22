import crypto from 'node:crypto';
import { spawn, type ChildProcess } from 'node:child_process';
import path from 'node:path';
import { StringDecoder } from 'node:string_decoder';
import type { Readable } from 'node:stream';
import { setTimeout as delay } from 'node:timers/promises';

export const MATH_PROCESS_OUTPUT_LIMIT = 12_000;

export type MathProcessResult = {
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

const PROCESS_STOP_GRACE_MS = 1_000;

/** Share a compile slot across solver processes; waiting uses the normal cancellation and deadline. */
export function runLeanProcess(command: string, args: string[], options: Parameters<typeof runMathProcess>[2] & {
  onLockProgress?: (event: 'lean_lock_waiting' | 'lean_lock_acquired') => void;
}) {
  const lock = (options.env ?? process.env).DEEPSCIENTIST_MATH_LEAN_LOCK;
  if (!lock) return runMathProcess(command, args, options);
  if (process.platform !== 'linux' || !path.isAbsolute(lock)) throw new Error('math_lean_lock_requires_absolute_linux_path');
  const progress = options.onLockProgress ?? (event => console.error(JSON.stringify({ event, at: Date.now() })));
  if (!options.signal?.aborted) progress('lean_lock_waiting');
  // A separate pipe reports acquisition without changing Lean output or inherited input descriptors.
  const descriptor = 3 + (options.inheritedFds?.length ?? 0);
  return runMathProcess('/usr/bin/flock', ['--exclusive', lock, '/bin/sh', '-c',
    `printf 1 >&${descriptor}; exec "$@"`, 'math-lean-lock', command, ...args], {
    ...options, onExtraPipe: stream => stream.once('data', () => progress('lean_lock_acquired')),
  });
}

/** Bound UTF-8 bytes without introducing a partial character at either edge. */
export function limitMathOutput(value: string, limit = MATH_PROCESS_OUTPUT_LIMIT, capture: 'head' | 'tail' = 'tail'): string {
  if (Buffer.byteLength(value) <= limit) return value;
  const bytes = Buffer.from(value);
  if (capture === 'head') return new StringDecoder('utf8').write(bytes.subarray(0, limit));
  let start = bytes.length - limit;
  while (start < bytes.length && (bytes[start] & 0xc0) === 0x80) start++;
  return bytes.subarray(start).toString('utf8');
}

export const stopMathProcess = (child: ChildProcess, signal: NodeJS.Signals): void => {
  if (process.platform !== 'win32' && child.pid) {
    try {
      process.kill(-child.pid, signal);
      return;
    } catch {
      // Fall through when the process group has already exited or could not be created.
    }
  }
  if (child.exitCode !== null || child.signalCode !== null) return;
  try {
    child.kill(signal);
  } catch {
    // The process may have exited between the state check and kill.
  }
};

export type MathProcessStopReceipt = Readonly<{ status: 'stopped' } | { status: 'unconfirmed';
  reason: 'process-exit-unconfirmed' | 'process-identity-unavailable' | 'unsupported-platform' |
    'process-group-active' | 'process-group-unavailable' }>;

/** A bounded close is cleanup, not proof that the owned writer process group has exited. */
export async function confirmMathProcessStopped(child: ChildProcess, timeoutMs = 1000): Promise<MathProcessStopReceipt> {
  if (process.platform === 'win32') return { status: 'unconfirmed', reason: 'unsupported-platform' };
  if (!Number.isSafeInteger(child.pid) || child.pid! <= 0)
    return { status: 'unconfirmed', reason: 'process-identity-unavailable' };
  const deadline = Date.now() + Math.max(0, timeoutMs);
  for (;;) {
    const exited = typeof child.exitCode === 'number' || typeof child.signalCode === 'string';
    let group: 'absent' | 'active';
    try { process.kill(-child.pid!, 0); group = 'active'; }
    catch (error) {
      if ((error as NodeJS.ErrnoException).code !== 'ESRCH')
        return { status: 'unconfirmed', reason: 'process-group-unavailable' };
      group = 'absent';
    }
    if (exited && group === 'absent') return { status: 'stopped' };
    const remaining = deadline - Date.now();
    if (remaining <= 0) return { status: 'unconfirmed',
      reason: !exited ? 'process-exit-unconfirmed' : 'process-group-active' };
    await delay(Math.min(25, remaining));
  }
}

/** Cleanup has a finite deadline even when solving has none. Launch owned children detached on POSIX. */
export function closeMathProcess(child: ChildProcess, gracefulInput = false, graceMs = 3_000): Promise<void> {
  return new Promise(resolve => {
    let force: NodeJS.Timeout | undefined, fallback: NodeJS.Timeout | undefined;
    const finish = () => {
      clearTimeout(force); clearTimeout(fallback);
      child.off('close', finish);
      stopMathProcess(child, 'SIGKILL');
      resolve();
    };
    if ((child.exitCode !== null || child.signalCode !== null) && child.stdout?.closed && child.stderr?.closed) return finish();
    child.once('close', finish);
    if (gracefulInput) child.stdin?.end();
    else stopMathProcess(child, 'SIGTERM');
    force = setTimeout(() => {
      stopMathProcess(child, 'SIGKILL');
      fallback = setTimeout(() => {
        child.stdin?.destroy(); child.stdout?.destroy(); child.stderr?.destroy();
        finish();
      }, PROCESS_STOP_GRACE_MS);
    }, graceMs);
  });
}

export const runMathProcess = (
  command: string,
  args: string[],
  options: {
    cwd: string;
    timeoutMs: number;
    signal?: AbortSignal;
    env?: NodeJS.ProcessEnv;
    stdin?: string;
    outputCapture?: 'head' | 'tail';
    outputLimit?: number;
    stopGraceMs?: number;
    onDuplexSpawn?: (child: ChildProcess) => void;
    inheritedFds?: readonly number[];
    onExtraPipe?: (stream: Readable) => void;
  }
): Promise<MathProcessResult> =>
  new Promise((resolve) => {
    const startedAt = Date.now();
    let child: ChildProcess;
    let extraPipe: Readable | undefined;
    let stdout: Buffer = Buffer.alloc(0), stderr: Buffer = Buffer.alloc(0);
    const capture = (current: Buffer, chunk: Buffer | string): Buffer => {
      const bytes = typeof chunk === 'string' ? Buffer.from(chunk) : chunk;
      const limit = options.outputLimit ?? MATH_PROCESS_OUTPUT_LIMIT;
      if (options.outputCapture === 'head') return current.length >= limit ? current :
        Buffer.concat([current, bytes.subarray(0, limit - current.length)]);
      return Buffer.from(Buffer.concat([current, bytes]).subarray(-limit));
    };
    const decode = (bytes: Buffer): string => {
      let start = 0;
      if (options.outputCapture !== 'head') while (start < bytes.length && (bytes[start] & 0xc0) === 0x80) start++;
      return limitMathOutput(new StringDecoder('utf8').write(bytes.subarray(start)), options.outputLimit ?? MATH_PROCESS_OUTPUT_LIMIT, options.outputCapture);
    };
    const stdoutHash = crypto.createHash('sha256');
    const stderrHash = crypto.createHash('sha256');
    let timedOut = false;
    let aborted = options.signal?.aborted || false;
    let processError: NodeJS.ErrnoException | undefined;
    let timeout: NodeJS.Timeout | undefined;
    let forceStopTimeout: NodeJS.Timeout | undefined;
    let fallbackTimeout: NodeJS.Timeout | undefined;
    let settled = false;
    let started = false;
    let stopping = false;

    const finish = (exitCode: number | null, signal: NodeJS.Signals | null): void => {
      if (settled) return;
      settled = true;
      if (stopping) stopMathProcess(child, 'SIGKILL');
      if (timeout) clearTimeout(timeout);
      if (forceStopTimeout) clearTimeout(forceStopTimeout);
      if (fallbackTimeout) clearTimeout(fallbackTimeout);
      options.signal?.removeEventListener('abort', abort);
      resolve({
        started,
        exitCode,
        signal,
        stdout: decode(stdout),
        stderr: decode(stderr),
        stdoutSha256: stdoutHash.digest('hex'),
        stderrSha256: stderrHash.digest('hex'),
        timedOut,
        aborted,
        durationMs: Date.now() - startedAt,
        ...(processError?.code ? { errorCode: processError.code } : {}),
        ...(processError?.message ? { errorMessage: processError.message } : {}),
      });
    };

    const requestStop = (): void => {
      if (stopping || settled) return;
      stopping = true;
      stopMathProcess(child, options.stopGraceMs === 0 ? 'SIGKILL' : 'SIGTERM');
      forceStopTimeout = setTimeout(() => {
        stopMathProcess(child, 'SIGKILL');
        fallbackTimeout = setTimeout(() => {
          child.stdin?.destroy(); child.stdout?.destroy(); child.stderr?.destroy();
          extraPipe?.destroy();
          finish(child.exitCode, child.signalCode);
        }, PROCESS_STOP_GRACE_MS);
      }, options.stopGraceMs ?? PROCESS_STOP_GRACE_MS);
    };

    const abort = (): void => {
      aborted = true;
      requestStop();
    };

    try {
      child = spawn(command, args, {
        cwd: options.cwd,
        env: options.env || process.env,
        detached: process.platform !== 'win32',
        stdio: [
          options.stdin === undefined && !options.onDuplexSpawn ? 'ignore' : 'pipe',
          'pipe',
          'pipe',
          ...(options.inheritedFds ?? []),
          ...(options.onExtraPipe ? ['pipe' as const] : []),
        ],
      });
    } catch (error) {
      processError = error as NodeJS.ErrnoException;
      finish(null, null);
      return;
    }

    child.stdout?.on('data', (chunk: Buffer | string) => {
      if (settled) return;
      stdoutHash.update(chunk);
      stdout = capture(stdout, chunk);
    });
    child.stderr?.on('data', (chunk: Buffer | string) => {
      if (settled) return;
      stderrHash.update(chunk);
      stderr = capture(stderr, chunk);
    });
    child.once('spawn', () => { started = true; });
    child.once('error', (error: NodeJS.ErrnoException) => {
      processError = error;
    });
    // A short-lived wrapper may close stdin before consuming the request
    // (for example after rejecting its arguments). Treat that expected
    // write-side failure as a normal process outcome instead of leaking an
    // unhandled EPIPE from the Writable stream.
    child.stdin?.on('error', (error: NodeJS.ErrnoException) => {
      if (error.code !== 'EPIPE') processError = error;
    });
    child.once('close', (exitCode, signal) => finish(exitCode, signal));

    if (options.onExtraPipe) {
      extraPipe = child.stdio.at(-1) as Readable;
      options.onExtraPipe(extraPipe);
    }

    if (options.stdin !== undefined) child.stdin?.end(options.stdin);

    options.signal?.addEventListener('abort', abort, { once: true });
    if (aborted) {
      requestStop();
      return;
    }
    if (options.onDuplexSpawn) {
      options.onDuplexSpawn(child);
      return;
    }
    if (Number.isFinite(options.timeoutMs)) timeout = setTimeout(() => {
      timedOut = true;
      requestStop();
    }, options.timeoutMs);
  });
