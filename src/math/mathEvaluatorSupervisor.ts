import fs from 'node:fs';
import path from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import {
  assertMathEvaluationCommit,
  readMathEvaluationConfig,
  readMathEvaluationJournal,
  type MathEvaluationConfig,
} from "./mathEvaluator";
import { assertMathEvaluatorContainer, emptyMathEvaluatorContainer } from "./mathEvaluatorContainer";
import { readMathJson, writeMathJsonDurable } from "./mathRuntimeIo";
import { verifyMathRunInputs } from "./mathRunInputs";

const childResultPath = (config: MathEvaluationConfig): string =>
  path.join(path.dirname(config.workspace), 'child-result.json');
const appendDiagnostic = (previous: Buffer, chunk: Buffer): Buffer =>
  Buffer.concat([previous, chunk]).subarray(-1024 * 1024);

export type MathEvaluatorCommandVerdict = Readonly<{
  schema: 'deepscientist.math.evaluator-command.v1';
  status: 'passed' | 'failed' | 'error' | 'interrupted';
}>;

export function parseMathEvaluatorCommandVerdict(value: unknown): MathEvaluatorCommandVerdict {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('math_evaluator_verdict_invalid');
  const record = value as Record<string, unknown>;
  if (
    Object.keys(record).length !== 2 ||
    record.schema !== 'deepscientist.math.evaluator-command.v1' ||
    !['passed', 'failed', 'error', 'interrupted'].includes(String(record.status))
  )
    throw new Error('math_evaluator_verdict_invalid');
  return record as MathEvaluatorCommandVerdict;
}

async function child(config: MathEvaluationConfig): Promise<void> {
  const verdictFile = path.join(path.dirname(config.workspace), 'command-verdict.json');
  assertMathEvaluatorContainer(config.container);
  // No evaluator-controlled code runs before this process enters its container.
  try {
    fs.writeFileSync(path.join(config.container.directory, 'cgroup.procs'), String(process.pid));
  } catch (error) {
    throw new Error(`math_evaluator_container_entry_denied: ${(error as NodeJS.ErrnoException).code || 'unknown'}`, {
      cause: error,
    });
  }
  await new Promise<void>((resolve, reject) => {
    const disconnected = (): void => reject(new Error('math_evaluator_supervisor_lost'));
    process.once('disconnect', disconnected);
    process.once('message', (message) => {
      process.removeListener('disconnect', disconnected);
      if (!message || typeof message !== 'object' || !('execute' in message) || message.execute !== true)
        reject(new Error('math_evaluator_start_rejected'));
      else resolve();
    });
    if (!process.send) reject(new Error('math_evaluator_supervisor_lost'));
    else
      process.send({ ready: true }, (error) => {
        if (error) reject(new Error('math_evaluator_supervisor_lost'));
      });
  });
  const exitCode = await new Promise<number | null>((resolve, reject) => {
    const process = spawn('/bin/bash', ['--noprofile', '--norc', '-c', config.command], {
      cwd: config.workspace,
      env: {
        ...config.environment,
        CI: '1',
        DEEPSCIENTIST_MATH_EVALUATOR_VERDICT_PATH: verdictFile,
        ...(config.candidate
          ? {
              DEEPSCIENTIST_MATH_CANDIDATE_PATH: path.join(config.workspace, config.candidate.pathRelative),
              DEEPSCIENTIST_MATH_CANDIDATE_SHA256: config.candidate.sha256,
            }
          : {}),
      },
      stdio: ['ignore', 'inherit', 'inherit'],
    });
    process.once('error', () => reject(new Error('math_evaluator_command_unavailable')));
    process.once('close', (code) => resolve(code));
  });
  let verdict: MathEvaluatorCommandVerdict | undefined;
  if (fs.existsSync(verdictFile)) {
    const stat = fs.lstatSync(verdictFile);
    if (!stat.isFile() || stat.isSymbolicLink() || stat.size > 4096) throw new Error('math_evaluator_verdict_invalid');
    verdict = parseMathEvaluatorCommandVerdict(readMathJson(verdictFile));
    if ((verdict.status === 'passed') !== (exitCode === 0)) throw new Error('math_evaluator_verdict_exit_mismatch');
  }
  writeMathJsonDurable(childResultPath(config), { exitCode, ...(verdict ? { verdict } : {}) });
}

export type MathEvaluationSupervisorPorts = Readonly<{
  execute: (onStdout: (chunk: Buffer) => void, onStderr: (chunk: Buffer) => void, signal: AbortSignal) => Promise<void>;
  emptyContainer: () => Promise<void>;
  now?: () => number;
  signal?: AbortSignal;
  assertCommit?: () => void;
}>;

/** Lease FD 3 belongs to this supervisor, even if the runner is killed. */
export async function superviseMathEvaluation(
  config: MathEvaluationConfig,
  ports: MathEvaluationSupervisorPorts
): Promise<void> {
  const initial = readMathEvaluationJournal(config.journal);
  if (
    initial.state !== 'starting' ||
    initial.evaluationId !== config.evaluationId ||
    initial.attemptId !== config.attemptId ||
    initial.commit !== config.commit
  )
    throw new Error('math_evaluator_journal_integrity');
  verifyMathRunInputs(config.runInputs);
  ports.assertCommit?.();
  writeMathJsonDurable(config.journal, { ...initial, state: 'running' });
  const started = ports.now?.() ?? Date.now();
  let stdout: Buffer = Buffer.alloc(0);
  let stderr: Buffer = Buffer.alloc(0);
  let timeout = false;
  let interrupted = ports.signal?.aborted ?? false;
  let cleanupFailure: unknown;
  let rejectContainment!: (error: Error) => void;
  const containmentFailure = new Promise<never>((_resolve, reject) => {
    rejectContainment = reject;
  });
  let stopTask: Promise<void> | undefined;
  let signalStop!: () => void;
  const stopRequested = new Promise<void>((resolve) => {
    signalStop = resolve;
  });
  const execution = new AbortController();
  const stop = (): Promise<void> => {
    signalStop();
    execution.abort();
    stopTask ??= Promise.resolve()
      .then(() => ports.emptyContainer())
      .catch((error) => {
        cleanupFailure = error;
        rejectContainment(new Error('math_evaluator_container_not_empty'));
      });
    return stopTask;
  };
  const abort = (): void => {
    interrupted = true;
    void stop();
  };
  ports.signal?.addEventListener('abort', abort, { once: true });
  const timer = setTimeout(() => {
    timeout = true;
    void stop();
  }, config.timeoutMs);
  let executionFailed = false;
  try {
    try {
      await Promise.race([
        interrupted
          ? Promise.resolve()
          : Promise.resolve().then(() =>
              execution.signal.aborted
                ? undefined
                : ports.execute(
                    (chunk) => {
                      stdout = appendDiagnostic(stdout, chunk);
                    },
                    (chunk) => {
                      stderr = appendDiagnostic(stderr, chunk);
                    },
                    execution.signal
                  )
            ),
        containmentFailure,
        // A non-cooperative evaluator adapter may never resolve after its
        // AbortSignal is set. Container containment is authoritative, so the
        // supervisor can continue once the stop path has been requested.
        stopRequested,
      ]);
    } catch (error) {
      executionFailed = true;
      stderr = appendDiagnostic(stderr, Buffer.from(`\n${error instanceof Error ? error.message : String(error)}\n`));
    } finally {
      clearTimeout(timer);
    }
    await stop();
    // Do not publish any verdict when containment or process-tree termination is uncertain.
    if (cleanupFailure) throw new Error('math_evaluator_container_not_empty');
    verifyMathRunInputs(config.runInputs);
    ports.assertCommit?.();
    let exitCode: number | null = null;
    let verdict: MathEvaluatorCommandVerdict | undefined;
    if (!timeout && !interrupted && !executionFailed) {
      const result = readMathJson(childResultPath(config));
      if (
        !result ||
        typeof result !== 'object' ||
        Array.isArray(result) ||
        Object.keys(result).some((key) => !['exitCode', 'verdict'].includes(key)) ||
        !('exitCode' in result) ||
        !(result.exitCode === null || Number.isSafeInteger(result.exitCode))
      )
        throw new Error('math_evaluator_child_result_invalid');
      exitCode = result.exitCode as number | null;
      if ('verdict' in result) {
        verdict = parseMathEvaluatorCommandVerdict(result.verdict);
        if ((verdict.status === 'passed') !== (exitCode === 0)) throw new Error('math_evaluator_verdict_exit_mismatch');
      }
    }
    try {
      fs.writeFileSync(path.join(path.dirname(config.workspace), 'stdout.log'), stdout, { mode: 0o600, flag: 'wx' });
      fs.writeFileSync(path.join(path.dirname(config.workspace), 'stderr.log'), stderr, { mode: 0o600, flag: 'wx' });
    } catch {
      /* Disposable diagnostics cannot prevent a durable evaluation result. */
    }
    const current = readMathEvaluationJournal(config.journal);
    if (
      current.state !== 'running' ||
      current.evaluationId !== config.evaluationId ||
      current.attemptId !== config.attemptId
    )
      throw new Error('math_evaluator_journal_integrity');
    if (interrupted) {
      writeMathJsonDurable(config.journal, { ...current, state: 'interrupted' });
      return;
    }
    writeMathJsonDurable(config.journal, {
      ...current,
      state: 'terminal',
      result: {
        status: timeout
          ? 'timeout'
          : executionFailed
            ? 'error'
            : (verdict?.status ?? (exitCode === 70 ? 'error' : exitCode === 0 ? 'passed' : 'failed')),
        exitCode,
        durationMs: Math.max(0, (ports.now?.() ?? Date.now()) - started),
      },
    });
  } finally {
    clearTimeout(timer);
    ports.signal?.removeEventListener('abort', abort);
  }
}

async function main(): Promise<void> {
  const config = readMathEvaluationConfig(process.argv[3]);
  if (process.argv[2] === '--math-evaluator-child') {
    await child(config);
    return;
  }
  const lock = fs.fstatSync(3);
  if (!lock.isFile() || lock.nlink !== 1 || (lock.mode & 0o777) !== 0o600)
    throw new Error('math_evaluator_lease_missing');
  const named = fs.lstatSync(path.join(path.dirname(config.journal), 'evaluation.lock'));
  if (named.dev !== lock.dev || named.ino !== lock.ino) throw new Error('math_evaluator_lease_missing');
  const lease = spawnSync('/usr/bin/flock', ['--exclusive', '--nonblock', '3'], {
    stdio: ['ignore', 'ignore', 'ignore', 3],
    timeout: 10_000,
  });
  if (lease.status !== 0 || lease.error) throw new Error('math_evaluator_lease_missing');
  const controller = new AbortController();
  const abort = (): void => controller.abort();
  const stopMessage = (message: unknown): void => {
    if (message && typeof message === 'object' && 'stop' in message && message.stop === true) abort();
  };
  process.on('message', stopMessage);
  process.once('SIGINT', abort);
  process.once('SIGTERM', abort);
  try {
    await superviseMathEvaluation(config, {
      signal: controller.signal,
      assertCommit: () => assertMathEvaluationCommit(config.workspace, config.commit),
      emptyContainer: () => emptyMathEvaluatorContainer(config.container),
      execute: (onStdout, onStderr, signal) =>
        new Promise<void>((resolve, reject) => {
          if (signal.aborted) {
            reject(new Error('math_evaluator_interrupted'));
            return;
          }
          const worker = spawn(process.execPath, [process.argv[1], '--math-evaluator-child', process.argv[3]], {
            cwd: config.workspace,
            stdio: ['ignore', 'pipe', 'pipe', 'ipc'],
            env: { PATH: process.env.PATH, CI: '1' },
          });
          const cancel = (): void => {
            worker.kill('SIGKILL');
          };
          signal.addEventListener('abort', cancel, { once: true });
          worker.once('message', (message) => {
            if (
              !signal.aborted &&
              message &&
              typeof message === 'object' &&
              'ready' in message &&
              message.ready === true
            )
              worker.send({ execute: true }, (error) => {
                if (error) cancel();
              });
            else cancel();
          });
          worker.stdout.on('data', onStdout);
          worker.stderr.on('data', onStderr);
          worker.once('error', () => reject(new Error('math_evaluator_child_unavailable')));
          worker.once('close', (code) => {
            signal.removeEventListener('abort', cancel);
            if (code === 0) resolve();
            else reject(new Error('math_evaluator_child_failed'));
          });
        }),
    });
  } finally {
    process.removeListener('message', stopMessage);
    process.removeListener('SIGINT', abort);
    process.removeListener('SIGTERM', abort);
  }
}

if (['--math-evaluator-supervisor', '--math-evaluator-child'].includes(process.argv[2])) {
  main()
    .then(() => process.exit(0))
    .catch((error: unknown) => {
      console.error(error instanceof Error ? error.message : String(error));
      process.exit(1);
    });
}
