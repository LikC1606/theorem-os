import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { z } from 'zod';
import {
  canonicalMathJson,
  mathDigest,
  readMathJson,
  withMathRuntimeLease,
  writeMathJsonDurable,
} from "./mathRuntimeIo";
import { assertMathCanonicalPath, isMathPathWithin } from "./mathRunBinding";
import { verifyMathRunInputs, type MathRunInputs } from "./mathRunInputs";
import { projectMathematicsRuntimeEnvironment } from "./mathRuntimeEnvironment";
import { mathEvaluatorPolicyDigest } from "./mathEvaluatorPolicy";
export { mathEvaluatorPolicyDigest } from "./mathEvaluatorPolicy";
import {
  createMathEvaluatorContainer,
  emptyMathEvaluatorContainer,
  mathEvaluatorBootIdentity,
  recoverPreparedMathEvaluatorContainer,
  recoverMathEvaluatorContainer,
  type MathEvaluatorContainer,
} from "./mathEvaluatorContainer";

const resultSchema = z
  .object({
    status: z.enum(['passed', 'failed', 'timeout', 'interrupted', 'error']),
    exitCode: z.number().int().nullable(),
    durationMs: z.number().int().nonnegative().safe(),
  })
  .strict();
export type MathEvaluationResult = Readonly<z.infer<typeof resultSchema> & { evaluationId: string; attemptId: string }>;
const candidateTargetSchema = z
  .object({
    targetId: z.string().min(1).max(160),
    theoremName: z.string().min(1).max(1000),
    statementHash: z.string().regex(/^[a-f0-9]{64}$/u),
    leanStatementHash: z
      .string()
      .regex(/^[a-f0-9]{64}$/u)
      .optional(),
    sourceDeclarationHash: z.string().regex(/^[a-f0-9]{64}$/u),
  })
  .strict();
const candidateSchema = z
  .object({
    pathRelative: z.string().min(1).max(2000),
    sha256: z.string().regex(/^[a-f0-9]{64}$/u),
    targets: z.array(candidateTargetSchema).min(1).max(64),
  })
  .strict();
export type MathEvaluationCandidate = Readonly<{
  pathRelative: string;
  sha256: string;
  targets: readonly Readonly<{
    targetId: string;
    theoremName: string;
    statementHash: string;
    leanStatementHash?: string;
    sourceDeclarationHash: string;
  }>[];
}>;
export type MathEvaluationConfig = Readonly<{
  schema: 'deepscientist.math.evaluation-config.v1';
  evaluationId: string;
  attemptId: string;
  journal: string;
  workspace: string;
  commit: string;
  command: string;
  timeoutMs: number;
  environment: Readonly<Record<string, string>>;
  runInputs: MathRunInputs;
  container: MathEvaluatorContainer;
  candidate?: MathEvaluationCandidate;
}>;
export type MathEvaluationJournal = Readonly<{
  schema: 'deepscientist.math.evaluation.v1';
  evaluationId: string;
  attemptId: string;
  policyDigest: string;
  commit: string;
  state: 'prepared' | 'starting' | 'running' | 'terminal' | 'interrupted';
  config: string;
  configDigest?: string;
  containerRoot: string;
  bootId: string;
  container?: MathEvaluatorContainer;
  candidate?: MathEvaluationCandidate;
  result?: z.infer<typeof resultSchema>;
}>;

const containerSchema = z
  .object({
    root: z.string(),
    directory: z.string(),
    device: z.string().regex(/^\d+$/u),
    inode: z.string().regex(/^\d+$/u),
    bootId: z.string(),
  })
  .strict();
const journalSchema = z
  .object({
    schema: z.literal('deepscientist.math.evaluation.v1'),
    evaluationId: z.string().regex(/^[a-f0-9]{64}$/u),
    attemptId: z.string().uuid(),
    policyDigest: z.string().regex(/^[a-f0-9]{64}$/u),
    commit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    state: z.enum(['prepared', 'starting', 'running', 'terminal', 'interrupted']),
    config: z.string(),
    configDigest: z
      .string()
      .regex(/^[a-f0-9]{64}$/u)
      .optional(),
    containerRoot: z.string(),
    bootId: z.string().min(1),
    container: containerSchema.optional(),
    result: resultSchema.optional(),
  })
  .strict();

export function readMathEvaluationJournal(file: string): MathEvaluationJournal {
  const parsed = journalSchema.safeParse(readMathJson(file));
  if (
    !parsed.success ||
    (parsed.data.state === 'terminal' && !parsed.data.result) ||
    (['starting', 'running', 'terminal'].includes(parsed.data.state) &&
      (!parsed.data.configDigest || !parsed.data.container)) ||
    (parsed.data.state !== 'terminal' && parsed.data.result)
  )
    throw new Error('math_evaluator_journal_integrity');
  return parsed.data as MathEvaluationJournal;
}

function normalizeMathEvaluationCandidate(value: unknown): MathEvaluationCandidate {
  const parsed = candidateSchema.safeParse(value);
  if (!parsed.success) throw new Error('math_evaluator_candidate_integrity');
  const relative = parsed.data.pathRelative.replaceAll(path.sep, '/');
  if (
    path.isAbsolute(relative) ||
    path.posix.normalize(relative) !== relative ||
    relative.split('/').some((part) => part === '' || part === '.' || part === '..' || part === '.git')
  )
    throw new Error('math_evaluator_candidate_integrity');
  const identities = new Set<string>();
  for (const target of parsed.data.targets) {
    const identity = `${target.targetId}\u0000${target.theoremName}\u0000${target.statementHash}`;
    if (identities.has(identity)) throw new Error('math_evaluator_candidate_integrity');
    identities.add(identity);
  }
  return Object.freeze({
    ...parsed.data,
    pathRelative: relative,
    targets: Object.freeze(parsed.data.targets.map((target) => Object.freeze({ ...target }))),
  }) as MathEvaluationCandidate;
}

function assertMathEvaluationCandidate(workspace: string, candidate: MathEvaluationCandidate): void {
  const target = path.resolve(workspace, candidate.pathRelative);
  if (!isMathPathWithin(workspace, target)) throw new Error('math_evaluator_candidate_integrity');
  assertMathCanonicalPath(target);
  const stat = fs.lstatSync(target);
  if (stat.isSymbolicLink() || !stat.isFile() || mathDigest(fs.readFileSync(target)) !== candidate.sha256)
    throw new Error('math_evaluator_candidate_integrity');
}

export function readMathEvaluationConfig(file: string): MathEvaluationConfig {
  const configSchema = z
    .object({
      schema: z.literal('deepscientist.math.evaluation-config.v1'),
      evaluationId: z.string().regex(/^[a-f0-9]{64}$/u),
      attemptId: z.string().uuid(),
      journal: z.string(),
      workspace: z.string(),
      commit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
      command: z.string().min(1),
      timeoutMs: z.number().int().positive().safe(),
      environment: z.record(z.string(), z.string()),
      runInputs: z.unknown(),
      container: containerSchema,
      candidate: candidateSchema.optional(),
    })
    .strict();
  const parsed = configSchema.safeParse(readMathJson(file));
  if (!parsed.success || (fs.lstatSync(file).mode & 0o222) !== 0) throw new Error('math_evaluator_config_integrity');
  const config = parsed.data;
  for (const target of [file, config.journal, config.workspace]) assertMathCanonicalPath(target);
  const runInputs = verifyMathRunInputs(config.runInputs);
  const candidate = config.candidate ? normalizeMathEvaluationCandidate(config.candidate) : undefined;
  if (
    path.basename(file) !== 'config.json' ||
    path.basename(path.dirname(file)) !== config.attemptId ||
    config.workspace !== path.join(path.dirname(file), 'workspace') ||
    path.dirname(config.journal) !== path.dirname(path.dirname(path.dirname(file)))
  )
    throw new Error('math_evaluator_config_integrity');
  const journal = readMathEvaluationJournal(config.journal);
  if (
    journal.config !== file ||
    journal.configDigest !== mathDigest(canonicalMathJson(config)) ||
    journal.evaluationId !== config.evaluationId ||
    journal.attemptId !== config.attemptId ||
    journal.commit !== config.commit ||
    journal.containerRoot !== config.container.root ||
    journal.bootId !== config.container.bootId ||
    !journal.container ||
    canonicalMathJson(journal.container) !== canonicalMathJson(config.container)
  )
    throw new Error('math_evaluator_config_integrity');
  return { ...config, runInputs, ...(candidate ? { candidate } : {}) } as MathEvaluationConfig;
}

export function mathEvaluationId(runId: string, receiptId: string, policyDigest: string): string {
  if (!runId || !receiptId || !/^[a-f0-9]{64}$/u.test(policyDigest)) throw new Error('math_evaluator_identity');
  return mathDigest(canonicalMathJson({ runId, receiptId, policyDigest }));
}

/** Wait between durable evaluator journal reads without retaining old abort listeners. */
export function waitForMathEvaluatorRecoveryPoll(signal?: AbortSignal, delayMs = 100): Promise<void> {
  return new Promise<void>((resolve, reject) => {
    let settled = false;
    let timer: NodeJS.Timeout | undefined;
    const cleanup = (): void => {
      if (timer) clearTimeout(timer);
      signal?.removeEventListener('abort', abort);
    };
    const finish = (error?: Error): void => {
      if (settled) return;
      settled = true;
      cleanup();
      if (error) reject(error);
      else resolve();
    };
    const abort = (): void => finish(new Error('math_evaluator_interrupted'));
    if (signal?.aborted) {
      abort();
      return;
    }
    timer = setTimeout(finish, delayMs);
    signal?.addEventListener('abort', abort, { once: true });
    if (signal?.aborted) abort();
  });
}

const git = (workspace: string, args: string[]): string => {
  const result = spawnSync('git', args, {
    cwd: workspace,
    encoding: 'utf8',
    timeout: 120_000,
    maxBuffer: 1024 * 1024,
    env: {
      ...process.env,
      GIT_TERMINAL_PROMPT: '0',
      GIT_CONFIG_COUNT: '1',
      GIT_CONFIG_KEY_0: 'core.hooksPath',
      GIT_CONFIG_VALUE_0: '/dev/null',
    },
  });
  if (result.status !== 0 || result.error) throw new Error('math_evaluator_git_failed');
  return result.stdout.trim();
};

export function assertMathEvaluationCommit(workspace: string, commit: string): void {
  assertMathCanonicalPath(workspace);
  if (
    git(workspace, ['rev-parse', '--show-toplevel']) !== workspace ||
    git(workspace, ['rev-parse', 'HEAD']) !== commit
  )
    throw new Error('math_evaluator_head_mismatch');
}

/** Remove only a disposable evaluator worktree after its supervisor is known
 * to be gone. Journals and configs remain as the durable recovery evidence. */
function cleanupInterruptedEvaluatorWorktree(repository: string, workspace: string): void {
  if (!path.isAbsolute(workspace) || !path.isAbsolute(repository)) return;
  const attemptRoot = path.dirname(workspace);
  if (path.basename(workspace) !== 'workspace' || path.basename(attemptRoot) === '') return;
  try {
    assertMathCanonicalPath(attemptRoot);
    const stat = fs.lstatSync(workspace);
    if (stat.isSymbolicLink() || !stat.isDirectory()) return;
    git(repository, ['worktree', 'remove', '--force', '--', workspace]);
    git(repository, ['worktree', 'prune']);
  } catch {
    // A missing or already-pruned worktree is an idempotent cleanup result.
    try {
      if (fs.existsSync(workspace)) fs.rmSync(workspace, { recursive: true, force: true });
    } catch {
      /* Preserve the journal; a later recovery pass can retry cleanup. */
    }
  }
}

const recoverySchema = z
  .object({
    schema: z.literal('deepscientist.math.evaluation-request.v1'),
    runId: z.string().min(1),
    receiptId: z.string().min(1),
    workspace: z.string(),
    commit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    baseCommit: z.string().regex(/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u),
    runInputs: z.unknown(),
    cgroupRoot: z.string(),
    command: z.string().min(1),
    timeoutMs: z.number().int().positive().safe(),
    environment: z.record(z.string(), z.string()),
    protectedPaths: z.array(z.string()),
    supervisorDigest: z.string().regex(/^[a-f0-9]{64}$/u),
    candidate: candidateSchema.optional(),
  })
  .strict();

/** Explicit operator recovery uses frozen inputs; it never asks the solver to resubmit. */
export async function resumeMathEvaluation(
  input: Readonly<{
    requestFile: string;
    supervisor: string;
    flockExecutable: string;
    signal?: AbortSignal;
  }>
): Promise<MathEvaluationResult> {
  assertMathCanonicalPath(input.requestFile);
  assertMathCanonicalPath(input.supervisor);
  if ((fs.lstatSync(input.requestFile).mode & 0o222) !== 0) throw new Error('math_evaluator_request_not_frozen');
  const parsed = recoverySchema.safeParse(readMathJson(input.requestFile));
  if (!parsed.success) throw new Error('math_evaluator_request_integrity');
  const parsedRequest = parsed.data as Required<z.infer<typeof recoverySchema>>;
  const { candidate: rawCandidate, ...request } = parsedRequest;
  const candidate = rawCandidate ? normalizeMathEvaluationCandidate(rawCandidate) : undefined;
  const policyDigest = mathEvaluatorPolicyDigest(request);
  const evaluationId = mathEvaluationId(request.runId, request.receiptId, policyDigest);
  if (
    path.basename(input.requestFile) !== 'request.json' ||
    path.basename(path.dirname(input.requestFile)) !== evaluationId ||
    mathDigest(fs.readFileSync(input.supervisor)) !== request.supervisorDigest
  )
    throw new Error('math_evaluator_request_integrity');
  const run = (): Promise<MathEvaluationResult> =>
    runMathEvaluation({
      ...request,
      runInputs: verifyMathRunInputs(request.runInputs),
      root: path.dirname(path.dirname(input.requestFile)),
      supervisor: input.supervisor,
      flockExecutable: input.flockExecutable,
      signal: input.signal,
      ...(candidate ? { candidate } : {}),
    });
  try {
    return await run();
  } catch (error) {
    // An active supervisor owns the evaluation lease. Recovery attaches to
    // its durable journal instead of starting a second attempt. This wait is
    // intentionally limited to evaluator state and never polls Core or the
    // mathematical Team.
    if (!(error instanceof Error) || error.message !== 'math_runtime_lease_busy') throw error;
    const directory = path.dirname(input.requestFile);
    const journalFile = path.join(directory, 'journal.json');
    for (;;) {
      if (input.signal?.aborted) throw new Error('math_evaluator_interrupted');
      let journal: MathEvaluationJournal;
      try {
        journal = readMathEvaluationJournal(journalFile);
      } catch (error) {
        // The request is durable before the first journal write. A short
        // prepared window is therefore recoverable; malformed journals still
        // fail closed and are never treated as a stale owner.
        if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
        await waitForMathEvaluatorRecoveryPoll(input.signal);
        continue;
      }
      if (journal.state === 'terminal' && journal.result)
        return { ...journal.result, evaluationId: journal.evaluationId, attemptId: journal.attemptId };
      if (journal.state === 'interrupted') return await run();
      await waitForMathEvaluatorRecoveryPoll(input.signal);
      try {
        // Re-enter the same production runner after every wait. If the owner
        // has exited while its journal still says running, the OS lease is the
        // authoritative hand-off and this call creates the recovery attempt.
        return await run();
      } catch (retryError) {
        if (!(retryError instanceof Error) || retryError.message !== 'math_runtime_lease_busy') throw retryError;
      }
    }
  }
}

export async function runMathEvaluation(
  input: Readonly<{
    runId: string;
    receiptId: string;
    workspace: string;
    commit: string;
    runInputs: MathRunInputs;
    root: string;
    cgroupRoot: string;
    supervisor: string;
    command: string;
    timeoutMs: number;
    environment: NodeJS.ProcessEnv;
    protectedPaths: readonly string[];
    baseCommit: string;
    flockExecutable: string;
    candidate?: MathEvaluationCandidate;
    /**
     * Trusted Lake package cache for the solver project. The detached evaluator
     * worktree has no .lake, so `lake env lean` tried to clone Mathlib and
     * failed offline (found in the run 23d rehearsal).
     */
    lakePackages?: Readonly<{ projectRelative: string; path: string }>;
    signal?: AbortSignal;
  }>
): Promise<MathEvaluationResult> {
  if (input.signal?.aborted) throw new Error('math_evaluator_interrupted');
  verifyMathRunInputs(input.runInputs);
  const candidate = input.candidate ? normalizeMathEvaluationCandidate(input.candidate) : undefined;
  for (const target of [input.root, input.workspace, input.supervisor]) assertMathCanonicalPath(target);
  if (
    isMathPathWithin(input.workspace, input.root) ||
    isMathPathWithin(input.root, input.workspace) ||
    !/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u.test(input.commit) ||
    !/^[a-f0-9]{40}(?:[a-f0-9]{24})?$/u.test(input.baseCommit)
  )
    throw new Error('math_evaluator_identity');
  // The active solver tree is not the evaluator input. The request commit is
  // checked out into a private evaluator worktree below; requiring the caller's
  // HEAD or dirtiness to match here makes terminal replay and crash recovery
  // depend on unrelated later research edits.
  try {
    git(input.workspace, ['cat-file', '-e', `${input.commit}^{commit}`]);
  } catch {
    throw new Error('math_evaluator_commit_missing');
  }
  for (const relative of input.protectedPaths) {
    if (
      !relative ||
      path.isAbsolute(relative) ||
      relative.split('/').some((part) => ['..', '.', '.git', ''].includes(part))
    )
      throw new Error('math_evaluator_protected_path_invalid');
  }
  if (
    input.protectedPaths.length &&
    git(input.workspace, ['diff', '--name-only', input.baseCommit, input.commit, '--', ...input.protectedPaths])
  )
    throw new Error('math_evaluator_protected_files_changed');
  const environment = projectMathematicsRuntimeEnvironment(input.environment);
  const recoveryRequest = {
    schema: 'deepscientist.math.evaluation-request.v1' as const,
    runId: input.runId,
    receiptId: input.receiptId,
    workspace: input.workspace,
    commit: input.commit,
    baseCommit: input.baseCommit,
    runInputs: input.runInputs,
    cgroupRoot: input.cgroupRoot,
    command: input.command,
    timeoutMs: input.timeoutMs,
    environment,
    protectedPaths: [...input.protectedPaths].toSorted(),
    supervisorDigest: mathDigest(fs.readFileSync(input.supervisor)),
    ...(candidate ? { candidate } : {}),
  };
  if (!recoverySchema.safeParse(recoveryRequest).success) throw new Error('math_evaluator_request_integrity');
  const policyDigest = mathEvaluatorPolicyDigest(recoveryRequest);
  const evaluationId = mathEvaluationId(input.runId, input.receiptId, policyDigest);
  const directory = path.join(input.root, evaluationId);
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(directory);
  const journalFile = path.join(directory, 'journal.json');
  return withMathRuntimeLease(
    { lockPath: path.join(directory, 'evaluation.lock'), flockExecutable: input.flockExecutable },
    async (lease) => {
      if (input.signal?.aborted) throw new Error('math_evaluator_interrupted');
      const requestFile = path.join(directory, 'request.json');
      try {
        const stat = fs.lstatSync(requestFile);
        if (
          (stat.mode & 0o222) !== 0 ||
          canonicalMathJson(readMathJson(requestFile)) !== canonicalMathJson(recoveryRequest)
        )
          throw new Error('math_evaluator_request_integrity');
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
        // This request precedes every attempt, including the prepared-to-config crash window.
        writeMathJsonDurable(requestFile, recoveryRequest, 0o400);
      }
      let exists = false;
      try {
        fs.lstatSync(journalFile);
        exists = true;
      } catch (error) {
        if ((error as NodeJS.ErrnoException).code !== 'ENOENT') throw error;
      }
      const previous = exists ? readMathEvaluationJournal(journalFile) : undefined;
      if (previous) {
        if (
          previous.evaluationId !== evaluationId ||
          previous.commit !== input.commit ||
          previous.policyDigest !== policyDigest
        )
          throw new Error('math_evaluator_journal_integrity');
        if (previous.state === 'terminal') return { ...previous.result!, evaluationId, attemptId: previous.attemptId };
        let previousConfig: MathEvaluationConfig | undefined;
        if (previous.configDigest) previousConfig = readMathEvaluationConfig(previous.config);
        if (previous.container) await recoverMathEvaluatorContainer(previous.container);
        else await recoverPreparedMathEvaluatorContainer(previous.containerRoot, previous.attemptId, previous.bootId);
        if (previousConfig) cleanupInterruptedEvaluatorWorktree(input.workspace, previousConfig.workspace);
        writeMathJsonDurable(journalFile, { ...previous, state: 'interrupted' });
      }
      const attemptId = crypto.randomUUID();
      const attempt = path.join(directory, 'attempts', attemptId);
      const workspace = path.join(attempt, 'workspace');
      const configFile = path.join(attempt, 'config.json');
      fs.mkdirSync(attempt, { recursive: true, mode: 0o700 });
      let journal: MathEvaluationJournal = {
        schema: 'deepscientist.math.evaluation.v1',
        evaluationId,
        attemptId,
        policyDigest,
        commit: input.commit,
        state: 'prepared',
        config: configFile,
        containerRoot: input.cgroupRoot,
        bootId: mathEvaluatorBootIdentity(),
      };
      writeMathJsonDurable(journalFile, journal);
      const container = createMathEvaluatorContainer(input.cgroupRoot, attemptId);
      journal = { ...journal, container };
      writeMathJsonDurable(journalFile, journal);
      git(input.workspace, ['worktree', 'add', '--detach', '--', workspace, input.commit]);
      if (
        git(workspace, ['rev-parse', 'HEAD']) !== input.commit ||
        git(workspace, ['status', '--porcelain', '--untracked-files=all'])
      )
        throw new Error('math_evaluator_detached_workspace_invalid');
      if (candidate) assertMathEvaluationCandidate(workspace, candidate);
      if (input.lakePackages) {
        const projectRoot = path.resolve(workspace, input.lakePackages.projectRelative);
        if (!isMathPathWithin(workspace, projectRoot) || !fs.statSync(input.lakePackages.path).isDirectory())
          throw new Error('math_evaluator_lake_packages_invalid');
        // .lake/ is excluded from Git, so the checked commit stays clean.
        fs.mkdirSync(path.join(projectRoot, '.lake'), { recursive: true });
        fs.symlinkSync(fs.realpathSync(input.lakePackages.path), path.join(projectRoot, '.lake', 'packages'));
      }
      const config: MathEvaluationConfig = {
        schema: 'deepscientist.math.evaluation-config.v1',
        evaluationId,
        attemptId,
        journal: journalFile,
        workspace,
        commit: input.commit,
        command: input.command,
        timeoutMs: input.timeoutMs,
        environment,
        runInputs: input.runInputs,
        container,
        ...(candidate ? { candidate } : {}),
      };
      writeMathJsonDurable(configFile, config, 0o400);
      journal = { ...journal, state: 'starting', configDigest: mathDigest(canonicalMathJson(config)) };
      writeMathJsonDurable(journalFile, journal);
      lease.assertHeld();
      if (input.signal?.aborted) {
        await emptyMathEvaluatorContainer(container);
        writeMathJsonDurable(journalFile, { ...journal, state: 'interrupted' });
        throw new Error('math_evaluator_interrupted');
      }
      await new Promise<void>((resolve, reject) => {
        const supervisor = spawn(process.execPath, [input.supervisor, '--math-evaluator-supervisor', configFile], {
          stdio: ['ignore', 'ignore', 'ignore', lease.inheritedDescriptor, 'ipc'],
          detached: true,
          env: { PATH: input.environment.PATH, CI: '1' },
        });
        let communicationFailed = false;
        let stopDeadline: NodeJS.Timeout | undefined;
        const cancel = (): void => {
          if (stopDeadline) return;
          stopDeadline = setTimeout(() => {
            communicationFailed = true;
            supervisor.kill('SIGKILL');
          }, 15_000);
          // IPC queues safely during startup, unlike SIGTERM before handlers are installed.
          supervisor.send({ stop: true }, (error) => {
            if (!error) return;
            communicationFailed = true;
            supervisor.kill('SIGKILL');
          });
        };
        input.signal?.addEventListener('abort', cancel, { once: true });
        if (input.signal?.aborted) cancel();
        supervisor.once('error', () => {
          communicationFailed = true;
        });
        supervisor.once('close', (code) => {
          if (stopDeadline) clearTimeout(stopDeadline);
          input.signal?.removeEventListener('abort', cancel);
          if (code === 0 && !communicationFailed) resolve();
          else reject(new Error('math_evaluator_supervisor_failed'));
        });
      }).catch(async (error: unknown) => {
        await emptyMathEvaluatorContainer(container);
        throw error;
      });
      const finished = readMathEvaluationJournal(journalFile);
      if (
        finished.evaluationId === evaluationId &&
        finished.attemptId === attemptId &&
        finished.state === 'interrupted'
      ) {
        await emptyMathEvaluatorContainer(container);
        throw new Error('math_evaluator_interrupted');
      }
      if (
        finished.evaluationId !== evaluationId ||
        finished.attemptId !== attemptId ||
        finished.state !== 'terminal' ||
        !finished.result
      )
        throw new Error('math_evaluator_terminal_result_missing');
      await emptyMathEvaluatorContainer(container);
      return { ...finished.result, evaluationId, attemptId };
    }
  );
}
