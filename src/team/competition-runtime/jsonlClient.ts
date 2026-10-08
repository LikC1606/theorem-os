/**
 * @license
 * Copyright 2026 DeepScientist (deepscientist.cc)
 * SPDX-License-Identifier: Apache-2.0
 */

import { randomUUID } from 'node:crypto';
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import {
  IOAI_ENGINE_PROTOCOL_VERSION,
  parseCompetitionEngineResponse,
  type CompetitionEngineRequest,
} from "./protocol";

export const COMPETITION_ENGINE_REQUEST_TIMEOUT_MS = Object.freeze({
  status: 10_000,
  read: 30_000,
  workflow: 120_000,
  bootstrap: 900_000,
  tuning: 60_000,
  execution: 1_800_000,
});

const DEFAULT_TIMEOUT_MS = COMPETITION_ENGINE_REQUEST_TIMEOUT_MS.status;
const MAX_TIMEOUT_MS = Math.max(...Object.values(COMPETITION_ENGINE_REQUEST_TIMEOUT_MS));
const DEFAULT_MAX_STDOUT_BYTES = 1024 * 1024;
const DEFAULT_MAX_STDERR_BYTES = 64 * 1024;

export type CompetitionEngineLaunch = {
  command: string;
  args: string[];
  cwd?: string;
  env: Record<string, string>;
};

export type CompetitionEngineRequestOptions = {
  timeoutMs?: number;
  signal?: AbortSignal;
};

export type CompetitionEngineCommandResult<T extends Record<string, unknown>> = {
  requestId: string;
  action: string;
  result: T;
  diagnostics: {
    stderr: string;
  };
};

export type CompetitionEngineClientLimits = {
  maxStdoutBytes?: number;
  maxStderrBytes?: number;
};

export class CompetitionEngineClientError extends Error {
  readonly code: string;
  readonly retryable: boolean;
  readonly diagnostic: string;
  readonly engineCode?: string;

  constructor(
    code: string,
    message: string,
    options: {
      retryable?: boolean;
      diagnostic?: string;
      engineCode?: string;
    } = {}
  ) {
    super(message);
    this.name = 'CompetitionEngineClientError';
    this.code = code;
    this.retryable = options.retryable ?? false;
    this.diagnostic = options.diagnostic ?? '';
    this.engineCode = options.engineCode;
  }
}

export class CompetitionEngineJsonlClient {
  private readonly maxStdoutBytes: number;
  private readonly maxStderrBytes: number;

  constructor(
    private readonly launch: CompetitionEngineLaunch,
    limits: CompetitionEngineClientLimits = {}
  ) {
    this.maxStdoutBytes = limits.maxStdoutBytes ?? DEFAULT_MAX_STDOUT_BYTES;
    this.maxStderrBytes = limits.maxStderrBytes ?? DEFAULT_MAX_STDERR_BYTES;
  }

  async request<T extends Record<string, unknown>>(
    action: string,
    params: Record<string, unknown>,
    options: CompetitionEngineRequestOptions = {}
  ): Promise<CompetitionEngineCommandResult<T>> {
    if (options.signal?.aborted) {
      throw new CompetitionEngineClientError('cancelled', 'engine request was cancelled');
    }
    const request: CompetitionEngineRequest = {
      protocol_version: IOAI_ENGINE_PROTOCOL_VERSION,
      request_id: randomUUID(),
      action,
      params,
    };
    const timeoutMs = normalizeTimeout(options.timeoutMs);
    return await this.runChild<T>(request, timeoutMs, options.signal);
  }

  private async runChild<T extends Record<string, unknown>>(
    request: CompetitionEngineRequest,
    timeoutMs: number,
    signal?: AbortSignal
  ): Promise<CompetitionEngineCommandResult<T>> {
    return await new Promise((resolve, reject) => {
      let child: ChildProcessWithoutNullStreams;
      try {
        child = spawn(this.launch.command, this.launch.args, {
          cwd: this.launch.cwd,
          env: this.launch.env,
          shell: false,
          windowsHide: true,
          stdio: ['pipe', 'pipe', 'pipe'],
          detached: process.platform !== 'win32',
        });
      } catch (error) {
        reject(
          new CompetitionEngineClientError('launch_failed', toErrorMessage(error), {
            retryable: false,
          })
        );
        return;
      }

      let settled = false;
      let stdout = Buffer.alloc(0);
      let stderr = Buffer.alloc(0);

      const cleanup = () => {
        clearTimeout(timer);
        signal?.removeEventListener('abort', onAbort);
      };
      const fail = (error: CompetitionEngineClientError, terminate = false) => {
        if (settled) return;
        settled = true;
        cleanup();
        if (!terminate) {
          reject(error);
          return;
        }
        void terminateChild(child).finally(() => reject(error));
      };
      const onAbort = () => {
        fail(
          new CompetitionEngineClientError('cancelled', 'engine request was cancelled', {
            diagnostic: boundedDiagnostic(stderr),
          }),
          true
        );
      };
      const timer = setTimeout(() => {
        fail(
          new CompetitionEngineClientError('timeout', `engine request exceeded ${timeoutMs} ms`, {
            retryable: true,
            diagnostic: boundedDiagnostic(stderr),
          }),
          true
        );
      }, timeoutMs);
      timer.unref?.();
      signal?.addEventListener('abort', onAbort, { once: true });

      child.once('error', (error) => {
        fail(
          new CompetitionEngineClientError('launch_failed', toErrorMessage(error), {
            diagnostic: boundedDiagnostic(stderr),
          })
        );
      });
      child.stdout.on('data', (chunk: Buffer) => {
        stdout = Buffer.concat([stdout, chunk]);
        if (stdout.length > this.maxStdoutBytes) {
          fail(new CompetitionEngineClientError('output_limit', 'engine stdout exceeded its limit'), true);
        }
      });
      child.stderr.on('data', (chunk: Buffer) => {
        stderr = Buffer.concat([stderr, chunk]);
        if (stderr.length > this.maxStderrBytes) {
          fail(new CompetitionEngineClientError('output_limit', 'engine stderr exceeded its limit'), true);
        }
      });
      child.once('close', (code, closeSignal) => {
        if (settled) return;
        const diagnostic = boundedDiagnostic(stderr);
        if (code !== 0) {
          fail(
            new CompetitionEngineClientError(
              'process_exit',
              `engine process exited abnormally (${code ?? closeSignal ?? 'unknown'})`,
              { retryable: false, diagnostic }
            )
          );
          return;
        }
        const lines = stdout
          .toString('utf8')
          .split(/\r?\n/u)
          .filter((line) => line.trim().length > 0);
        if (lines.length !== 1) {
          fail(
            new CompetitionEngineClientError('invalid_stdout', 'engine must emit exactly one JSONL response', {
              diagnostic,
            })
          );
          return;
        }
        try {
          const response = parseCompetitionEngineResponse(lines[0], request);
          if (response.ok === false) {
            fail(
              new CompetitionEngineClientError('engine_error', response.error.message, {
                retryable: response.error.retryable,
                diagnostic,
                engineCode: response.error.code,
              })
            );
            return;
          }
          settled = true;
          cleanup();
          resolve({
            requestId: request.request_id,
            action: request.action,
            result: response.result as T,
            diagnostics: { stderr: diagnostic },
          });
        } catch (error) {
          fail(
            new CompetitionEngineClientError('invalid_stdout', toErrorMessage(error), {
              diagnostic,
            })
          );
        }
      });

      child.stdin.once('error', (error) => {
        fail(
          new CompetitionEngineClientError('process_exit', `failed to write engine request: ${toErrorMessage(error)}`, {
            diagnostic: boundedDiagnostic(stderr),
          }),
          true
        );
      });
      if (signal?.aborted) {
        onAbort();
        return;
      }
      child.stdin.end(`${JSON.stringify(request)}\n`, 'utf8');
    });
  }
}

function normalizeTimeout(value: number | undefined): number {
  if (value === undefined) return DEFAULT_TIMEOUT_MS;
  if (!Number.isFinite(value) || value <= 0 || value > MAX_TIMEOUT_MS) {
    throw new CompetitionEngineClientError('invalid_request', `timeoutMs must be within (0, ${MAX_TIMEOUT_MS}]`);
  }
  return Math.floor(value);
}

function boundedDiagnostic(value: Buffer): string {
  let sanitized = '';
  for (const character of value.toString('utf8')) {
    const codePoint = character.codePointAt(0) ?? 0;
    if (codePoint === 9 || codePoint === 10 || codePoint === 13 || codePoint >= 32) sanitized += character;
  }
  return sanitized.trim().slice(0, 4000);
}

async function terminateChild(child: ChildProcessWithoutNullStreams): Promise<void> {
  if (!child.pid || hasExited(child)) return;
  if (process.platform === 'win32') {
    await runTaskkill(child.pid);
    if (!(await waitForChildExit(child, 1000))) {
      child.kill('SIGKILL');
      await waitForChildExit(child, 500);
    }
    return;
  }
  try {
    process.kill(-child.pid, 'SIGTERM');
  } catch {
    child.kill('SIGTERM');
  }
  if (await waitForChildExit(child, 750)) return;
  try {
    process.kill(-child.pid, 'SIGKILL');
  } catch {
    child.kill('SIGKILL');
  }
  await waitForChildExit(child, 500);
}

function runTaskkill(pid: number): Promise<void> {
  return new Promise((resolve) => {
    const killer = spawn('taskkill', ['/pid', String(pid), '/t', '/f'], {
      shell: false,
      windowsHide: true,
      stdio: 'ignore',
    });
    const timer = setTimeout(resolve, 1500);
    timer.unref?.();
    const finish = () => {
      clearTimeout(timer);
      resolve();
    };
    killer.once('error', finish);
    killer.once('close', finish);
  });
}

function waitForChildExit(child: ChildProcessWithoutNullStreams, timeoutMs: number): Promise<boolean> {
  if (hasExited(child)) return Promise.resolve(true);
  return new Promise((resolve) => {
    const timer = setTimeout(() => {
      child.removeListener('close', onClose);
      resolve(hasExited(child));
    }, timeoutMs);
    timer.unref?.();
    const onClose = () => {
      clearTimeout(timer);
      resolve(true);
    };
    child.once('close', onClose);
  });
}

function hasExited(child: ChildProcessWithoutNullStreams): boolean {
  return child.exitCode !== null || child.signalCode !== null;
}

function toErrorMessage(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}
