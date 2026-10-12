import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { parseArgs } from 'node:util';
import { setTimeout as delay } from 'node:timers/promises';
import type { MathAgentSession } from '../runtime/codexSession';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { canonicalMathJson, mathDigest, readMathJson, withMathRuntimeLease, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { checkResolvedLeanToolchainReadiness } from '../math/leanToolchainReadiness';
import { prepareMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV } from '../math/mathProofEnvironment';
import { resolveMathematicsLakePackagesCache } from '../math/verifier';
import { prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../math/leanDiagnostics';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { git, readSolverProblem, assertSolverSources } from './problem';
import { rememberSolverFailure, solverSourceFeedback } from './feedback';
import { assertMathRetrievalCorpus, createMathRetrievalCorpus, type MathRetrievalCorpus } from '../math/mathRetrievalCorpus';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from './archive';
import { directSolverModules, lemmaSolverModules, type SolverModules } from './modules';
import type { ProofCheck } from './modules/evidence';
import type { ResearchWorker } from './modules/organization';
import type { ResearchBudget } from './modules/search';
import type { ResearchOperation } from './modules/value';
import { evaluateSolverProof } from './evaluation';

export async function runSolver(args: string[], root: string, customModules?: SolverModules): Promise<number> {
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, 'receipt-file': { type: 'string' }, 'task-file': { type: 'string' },
    output: { type: 'string' }, 'build-manifest': { type: 'string' }, model: { type: 'string', default: 'gpt-6.1-sol' },
    effort: { type: 'string', default: 'xhigh' }, codex: { type: 'string' }, resume: { type: 'boolean' },
    'max-run-seconds': { type: 'string', default: '1800' }, 'max-turns': { type: 'string', default: '20' },
    'prepare-timeout-seconds': { type: 'string', default: '1800' }, 'max-turn-seconds': { type: 'string', default: '180' },
    'evaluator-command': { type: 'string' }, 'evaluator-timeout-seconds': { type: 'string', default: '1800' },
    'proof-environment-cache-dir': { type: 'string' }, 'startup-only': { type: 'boolean' }, help: { type: 'boolean' },
    method: { type: 'string', default: 'direct' },
  } });
  if (values.help) {
    console.log('Usage: deepscientist-math run --workspace DIR --task-file FILE --output FILE --build-manifest FILE [--receipt-file FILE] [--resume] [--method direct|lemma] [--model MODEL --effort LEVEL] [--max-run-seconds N --max-turns N --max-turn-seconds N] [--prepare-timeout-seconds N] [--evaluator-command CMD --evaluator-timeout-seconds N] [--proof-environment-cache-dir DIR] [--startup-only]\nUse 0 for --max-run-seconds, --max-turns, --max-turn-seconds or --evaluator-timeout-seconds to disable that limit. Unlimited total solving time also disables proof verification deadlines.');
    return 0;
  }
  if (!['direct', 'lemma'].includes(values.method!)) throw new Error('invalid --method');
  const modules: SolverModules = customModules ?? (values.method === 'lemma' ? lemmaSolverModules : directSolverModules);
  const required = (key: string): string => {
    const value = values[key];
    if (typeof value !== 'string' || !value.trim()) throw new Error(`--${key} is required`);
    return value;
  };
  const limit = (key: string, unlimited = false): number => {
    const value = Number(required(key));
    if (!Number.isSafeInteger(value) || value < (unlimited ? 0 : 1)) throw new Error(`invalid --${key}`);
    return unlimited && value === 0 ? Infinity : value;
  };
  const maxRunMs = limit('max-run-seconds', true) * 1000;
  const preparationMs = limit('prepare-timeout-seconds') * 1000;
  const maxTurnMs = limit('max-turn-seconds', true) * 1000;
  const maxTurns = limit('max-turns', true);
  const evaluatorMs = limit('evaluator-timeout-seconds', true) * 1000;
  const workspace = fs.realpathSync(required('workspace'));
  const output = path.resolve(required('output'));
  assertMathCanonicalPath(output);
  if (isMathPathWithin(workspace, output)) throw new Error('math_output_must_be_outside_solver_workspace');
  fs.mkdirSync(path.dirname(output), { recursive: true, mode: 0o700 });
  const directory = `${output}.runtime`;
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  assertMathCanonicalPath(directory);
  const stat = fs.statSync(directory);
  if ((stat.mode & 0o077) || (process.getuid && stat.uid !== process.getuid())) throw new Error('math_state_directory_not_private');
  const stateFile = path.join(directory, 'state.json');
  const controller = new AbortController();
  const abort = () => controller.abort();
  process.once('SIGINT', abort);
  process.once('SIGTERM', abort);
  const preparationStarted = Date.now();
  let preparing = true;
  let deadline = Infinity;
  let timer: ReturnType<typeof setTimeout> | undefined = setTimeout(abort, preparationMs);
  let ownedState: SolverRunState | undefined;
  let session: MathAgentSession | undefined;
  let proofEnvironment: Awaited<ReturnType<typeof prepareMathProofEnvironment>> | undefined;
  let ownsRun = false;
  const emit = (event: string, details = {}) => console.log(JSON.stringify({ event, at: Date.now(), ...details }));
  try {
    return await withMathRuntimeLease({ lockPath: path.join(directory, 'run.lock'), flockExecutable: '/usr/bin/flock', signal: controller.signal }, async lease => {
      const signal = lease.signal;
      const buildFile = fs.realpathSync(required('build-manifest'));
      const bundleRoot = path.join(root, 'out', 'main');
      readMathBuildManifest(buildFile, root, bundleRoot);
      const task = fs.readFileSync(required('task-file'), 'utf8');
      const problem = readSolverProblem(workspace, values['receipt-file'] || path.join(workspace, 'active-problem.json'));
      let env = resolveMathematicsRuntimeEnvironment();
      let corpusFile = env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS;
      const corpusBytes = corpusFile ? fs.readFileSync(corpusFile) : undefined;
      let corpus = corpusBytes ? JSON.parse(corpusBytes.toString('utf8')) as MathRetrievalCorpus : undefined;
      if (corpusFile) {
        const digest = mathDigest(corpusBytes!);
        if (env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 && env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 !== digest)
          throw new Error('math_corpus_identity_changed');
        env = { ...env, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256: digest };
      }
      const identity = { taskDigest: mathDigest(task), buildDigest: mathDigest(fs.readFileSync(buildFile)),
        environmentDigest: mathDigest(canonicalMathJson(projectMathematicsRuntimeEnvironment(env))),
        evaluatorDigest: mathDigest(values['evaluator-command'] || 'host-default'), model: values.model!, effort: values.effort!,
        methodDigest: mathDigest(canonicalMathJson({ id: modules.id, versions: Object.entries(modules)
          .filter(([key]) => key !== 'id').map(([key, module]) => [key, (module as { version: string }).version]) })) };
      let state: SolverRunState;
      let sourceFeedback: string | undefined;
      if (values.resume) {
        state = readSolverRunState(stateFile);
        if (!state.methodDigest && modules === directSolverModules) state.methodDigest = identity.methodDigest;
        if (state.schema !== 'deepscientist.math.solver.v1' || state.problem.workspace !== workspace ||
          state.problem.receiptDigest !== problem.receiptDigest ||
          Object.entries(identity).some(([key, value]) => state[key] !== value) ||
          state.worktree !== path.join(directory, 'worktree')) throw new Error('math_resume_identity_changed');
        sourceFeedback = solverSourceFeedback(state.problem, state.worktree);
        assertSolverSources(state.problem, workspace);
        if (state.phase === 'finished' && fs.existsSync(output)) {
          const result = readMathJson(output) as { status: string };
          if (result.status === 'evaluated_passed' || result.status === 'evaluated_failed') {
            assertSolverSources(state.problem, state.worktree);
            return result.status === 'evaluated_passed' ? 0 : 2;
          }
        }
      } else {
        if (fs.existsSync(stateFile) || fs.existsSync(output)) throw new Error('math_run_exists_use_resume');
        if (git(workspace, ['status', '--porcelain', '--untracked-files=no'])) throw new Error('math_workspace_has_uncommitted_sources');
        ownsRun = true;
        state = { schema: 'deepscientist.math.solver.v1', runId: crypto.randomUUID(), problem, ...identity,
          worktree: path.join(directory, 'worktree'), phase: 'prepared', turns: 0 };
        git(workspace, ['worktree', 'add', '--detach', state.worktree, problem.baseCommit]);
        writeSolverRunState(stateFile, state);
      }
      ownsRun = true;
      ownedState = state;
      const save = () => writeSolverRunState(stateFile, state);
      const project = path.join(state.worktree, state.problem.projectRelative);
      if (!values.resume) sourceFeedback = solverSourceFeedback(state.problem, state.worktree);
      fs.mkdirSync(path.join(project, '.lake'), { recursive: true });
      writeMathJsonDurable(path.join(project, '.lake/source-constraints.json'), {
        trustedFiles: state.problem.trustedFiles, declarations: state.problem.declarations,
        sourceStructure: state.problem.sourceStructure,
      }, 0o400);
      if (sourceFeedback) { state.check = undefined; save(); }
      const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env, timeoutMs: 180_000 });
      if (readiness.status !== 'ready') throw new Error('math_lean_toolchain_unavailable');
      const sourcePackages = resolveMathematicsLakePackagesCache(path.join(workspace, problem.projectRelative), env);
      if (sourcePackages) {
        const packages = path.join(project, '.lake', 'packages');
        fs.mkdirSync(path.dirname(packages), { recursive: true });
        if (!fs.existsSync(packages)) fs.symlinkSync(sourcePackages, packages, 'dir');
        // Model-side path overrides are regenerated after binding the frozen packages.
        // Their worktree-specific paths must not invalidate the preparation cache on resume.
        const overrides = path.join(project, '.lake', 'package-overrides.json');
        assertMathCanonicalPath(overrides);
        fs.rmSync(overrides, { force: true });
        proofEnvironment = await prepareMathProofEnvironment(project, sourcePackages, { env, signal,
          cacheRoot: values['proof-environment-cache-dir'], onProgress: phase => emit('proof_environment', { phase }) });
        env = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: proofEnvironment.environmentValue };
        prepareLeanDiagnosticOverrides(project);
      }
      const diagnostics = await runLeanDiagnostics({ projectRoot: project, files: [...new Set(problem.targets.map(target => target.proofPath))],
        dependenciesOnly: true, excludedFiles: problem.ownedFiles, env, signal,
        timeoutMs: preparationMs - (Date.now() - preparationStarted),
        onProgress: file => emit('dependency_check', { file }) });
      writeMathJsonDurable(path.join(directory, 'preparation-diagnostics.json'), diagnostics);
      if (diagnostics.exitCode !== 0 || diagnostics.timedOut) throw new Error('math_lean_dependencies_failed');
      let corpusCreated = false;
      if (!corpusFile && sourcePackages && fs.existsSync(path.join(sourcePackages, 'mathlib', 'Mathlib'))) {
        corpusFile = path.join(project, '.lake', 'retrieval-corpus.json');
        if (!fs.existsSync(corpusFile)) {
          if (state.retrievalDigest) throw new Error('math_corpus_identity_changed');
          emit('library_index', { phase: 'creating', package: 'mathlib' });
          corpus = await createMathRetrievalCorpus(project, ['mathlib']);
          corpusCreated = true;
          signal.throwIfAborted();
          writeMathJsonDurable(corpusFile, corpus);
        } else corpus = readMathJson(corpusFile) as MathRetrievalCorpus;
        const digest = mathDigest(fs.readFileSync(corpusFile));
        if (state.retrievalDigest && state.retrievalDigest !== digest) throw new Error('math_corpus_identity_changed');
        state.retrievalDigest = digest; save();
        env = { ...env, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: corpusFile, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256: digest };
      }
      const retrievalRoot = corpus?.projectSubdirectory ? state.worktree : project;
      if (corpusFile) {
        if (corpus?.projectSubdirectory && corpus.projectSubdirectory !== state.problem.projectRelative.replaceAll(path.sep, '/'))
          throw new Error('math_corpus_project_mismatch');
        // Creation already verifies every frozen source; persisted inputs need a fresh check.
        if (!corpusCreated) assertMathRetrievalCorpus(retrievalRoot, corpus);
        emit('library_index', { phase: 'ready', sourceFiles: corpus!.sources.length });
      }
      emit('ready', { runId: state.runId, worktree: state.worktree });
      emit('preparation_finished', { durationMs: Date.now() - preparationStarted, dependencies: diagnostics.phases });
      if (values['startup-only']) {
        writeMathJsonDurable(output, { schema: 'deepscientist.math.run.v2', runId: state.runId,
          problemId: state.problem.contract.problemId, status: 'prepared', startup_only: true,
          evaluator: { status: 'skipped' }, stateFile });
        return 0;
      }
      signal.throwIfAborted();
      clearTimeout(timer);
      preparing = false;
      deadline = Date.now() + maxRunMs;
      timer = Number.isFinite(maxRunMs) ? setTimeout(abort, maxRunMs) : undefined;
      emit('solve_started', { budgetMs: maxRunMs, maxTurnMs });
      const resumeEvaluation = state.check?.passed === true && ['checking', 'evaluating', 'finished'].includes(state.phase) &&
        git(state.worktree, ['rev-parse', 'HEAD']) === state.check.commit &&
        !git(state.worktree, ['status', '--porcelain', '--', ...state.problem.ownedFiles.map(file => path.join(state.problem.projectRelative, file))]);
      if (state.check?.passed && !resumeEvaluation) { state.check = undefined; save(); }
      // Restored auxiliary receipts are advisory until checked again in this pinned environment.
      if (values.resume && state.lemmaResearch) {
        state.lemmaResearch = { plan: state.lemmaResearch.plan, error: state.lemmaResearch.error }; save();
      }
      const budget = (): ResearchBudget => ({ maxTurns, remainingMs: Math.max(0, deadline - Date.now()), aborted: signal.aborted });
      const buildContext = (feedback?: string, previousCheck?: ProofCheck, previousFailures = state.failures, operation?: ResearchOperation) =>
        modules.M5.build(state.problem, state, { root, worktree: state.worktree, environment: env, taskText: task,
          corpusFile, retrievalRoot, sourceFeedback: feedback, previousCheck, previousFailures, operation });
      let context = buildContext(sourceFeedback);
      const startSession = () => modules.M1.open({ executable: values.codex || process.env.DEEPSCIENTIST_MATH_CODEX_EXECUTABLE || 'codex',
        profile: process.env.CODEX_HOME || path.join(os.homedir(), '.config/deepscientist/math-sol-codex'),
        workspace: state.worktree, environment: env, model: state.model, effort: state.effort,
        turnTimeoutMs: Number.isFinite(maxTurnMs) ? maxTurnMs : undefined,
        threadId: state.threadId, instructions: context.instructions,
        onUsage: usage => {
          state.lastInputTokens = session?.lastInputTokens ?? state.lastInputTokens;
          state.usage = { ...state.usageBeforeThread, ...usage };
          for (const [key, value] of Object.entries(usage)) {
            const previous = state.usageBeforeThread?.[key];
            if (typeof value === 'number' && typeof previous === 'number') state.usage[key] = previous + value;
          }
          save();
        } });
      const workers: ResearchWorker[] = [{ id: 'solver', worktree: state.worktree, ownedFiles: state.problem.ownedFiles }];
      const cancelSession = () => { void session?.close(); };
      signal.addEventListener('abort', cancelSession, { once: true });
      if (signal.aborted) cancelSession();
      save();
      let evaluation: Record<string, unknown> = { status: 'skipped', reason: 'proof_incomplete' };
      let lastCheck: ProofCheck | undefined;
      let retries = 0;
      const retryFailedTurn = async (error?: string): Promise<boolean> => {
        const retry = modules.M4.retry(error, retries, state, budget());
        if (!retry) return false;
        retries = retry.attempt;
        emit('turn_retry', { reason: 'model_concurrency_limit', attempt: retries, delayMs: retry.delayMs });
        await delay(retry.delayMs, undefined, { signal });
        signal.throwIfAborted();
        session = await startSession();
        state.threadId = session.threadId; save();
        return true;
      };
      try {
        while ((resumeEvaluation || state.turns < maxTurns) && !signal.aborted) {
          if (!resumeEvaluation) {
            if (state.threadId && Math.max(session?.lastInputTokens ?? 0, state.lastInputTokens ?? 0) >= 96_000) {
              const previous = state.threadId;
              await session?.close(); session = undefined;
              state.previousThreadIds = [...(state.previousThreadIds ?? []), previous];
              state.threadId = undefined; state.lastInputTokens = undefined; state.usageBeforeThread = state.usage; save();
              context = buildContext(solverSourceFeedback(state.problem, state.worktree));
              emit('context_restarted', { previousThreadId: previous, turns: state.turns });
            }
            const options: readonly ResearchOperation[] = modules.M2.checkLemma
              ? ['direct', 'decompose', 'bridge', 'prove-lemma', 'integrate-lemma'] : ['direct'];
            const estimates = modules.M3.estimate(state, options);
            const action = modules.M4.select(state, options, estimates, budget());
            if (action.operation === 'stop') break;
            if (!options.includes(action.operation)) throw new Error('math_research_operation_unavailable');
            emit('research_action', { operation: action.operation, reason: action.reason, estimates });
            const team = modules.M6.organize(action, workers, budget());
            if (!workers.includes(team.worker)) throw new Error('math_solver_worker_outside_ownership');
            readMathBuildManifest(buildFile, root, bundleRoot);
            const repair = solverSourceFeedback(state.problem, state.worktree);
            if (repair) { state.check = undefined; context = buildContext(repair); }
            else if (action.operation !== 'direct') context = buildContext(undefined, undefined, state.failures, action.operation);
            if (!session) {
              session = await startSession();
              state.threadId = session.threadId;
            }
            state.phase = 'running'; state.turns++; save();
            const candidate = await modules.M1.execute(state.problem, context, action.operation, team.worker, session, signal,
              turnId => emit('turn_started', { turnId, turn: state.turns }));
            if (candidate.worktree !== state.worktree || candidate.problemReceiptDigest !== state.problem.receiptDigest || candidate.operation !== action.operation)
              throw new Error('math_candidate_identity_changed');
            state.lastInputTokens = session?.lastInputTokens ?? state.lastInputTokens;
            state.candidate = candidate;
            const turn = candidate.status;
            if (turn !== 'completed' && turn !== 'failed' && turn !== 'checkpoint') break;
            if (turn === 'checkpoint') emit('turn_checkpoint', { turn: state.turns });
            const turnError = session?.lastError;
            if (turn === 'failed') {
              await session?.close(); session = undefined;
              emit('turn_failed');
            }
            const sourceError = solverSourceFeedback(state.problem, state.worktree);
            if (sourceError) {
              state.check = undefined; state.lemmaResearch = undefined; context = buildContext(sourceError); save();
              emit('source_rejected');
              if (turn === 'failed' && !await retryFailedTurn(turnError)) break;
              continue;
            }
            state.phase = 'checking'; save();
            const previousCheck = state.check;
            const previousFailures = state.failures;
            const checkStarted = Date.now();
            emit('proof_check_started', { turn: state.turns });
            state.check = await modules.M2.check(state.problem, candidate.worktree, env, signal, lastCheck,
              maxRunMs === Infinity ? Infinity : undefined);
            const reused = state.check === lastCheck;
            state.failures = rememberSolverFailure(state.check, previousFailures);
            lastCheck = state.check; save();
            emit('proof_checked', { passed: state.check.passed, commit: state.check.commit, reused,
              durationMs: Date.now() - checkStarted });
            if (!state.check.passed) {
              if (['unavailable', 'blocked'].includes(state.check.verification.status)) throw new Error('math_verifier_unavailable');
              if (modules.M2.checkLemma && action.operation !== 'direct') {
                state.lemmaResearch = candidate.lemmaPlan
                  ? await modules.M2.checkLemma(state.problem, candidate.worktree, env, signal, state.check, candidate.lemmaPlan, state.lemmaResearch)
                  : { error: candidate.lemmaPlanError || 'math_lemma_plan_missing' };
                save();
                emit('lemma_checked', { bridge: state.lemmaResearch.bridge?.passed ?? false,
                  lemma: state.lemmaResearch.lemma?.passed ?? false, error: state.lemmaResearch.error,
                  bridgeReused: state.lemmaResearch.bridge?.reused ?? false, lemmaReused: state.lemmaResearch.lemma?.reused ?? false });
                if ([state.lemmaResearch.bridge, state.lemmaResearch.lemma].some(receipt => receipt &&
                    ['unavailable', 'blocked'].includes(receipt.verification.status))) throw new Error('math_verifier_unavailable');
              }
              context = buildContext(undefined, previousCheck, previousFailures);
              if (turn === 'failed' && !await retryFailedTurn(turnError)) break;
              continue;
            }
          }
          await session?.close(); session = undefined;
          state.phase = 'evaluating'; save();
          readMathBuildManifest(buildFile, root, bundleRoot);
          const integration = await modules.M7.integrate(state.problem,
            [{ commit: state.check.commit, sourceDigest: state.check.sourceDigest }], [state.check]);
          if (!integration.candidate || !integration.dependenciesClosed) break;
          const evaluationStarted = Date.now();
          emit('evaluation_started');
          evaluation = await evaluateSolverProof(state.problem, state.worktree, state.check, env, signal,
            { command: values['evaluator-command'], timeoutMs: evaluatorMs });
          emit('evaluation_finished', { status: evaluation.status, durationMs: Date.now() - evaluationStarted });
          break;
        }
      } finally { signal.removeEventListener('abort', cancelSession); }
      state.phase = 'finished'; save();
      const status = signal.aborted ? 'limit_reached' : evaluation.status === 'passed' ? 'evaluated_passed' : evaluation.status === 'failed' ? 'evaluated_failed' : evaluation.status === 'error' ? 'runtime_error' : 'incomplete';
      const result = { schema: 'deepscientist.math.run.v2', runId: state.runId, problemId: state.problem.contract.problemId,
        status, run_outcome: status, solution_commit: state.check?.passed ? state.check.commit : null,
        solver_ready_receipt_valid: state.check?.passed === true, completion_signal_valid: evaluation.status === 'passed',
        evaluator: evaluation, turns: state.turns, usage: state.usage, stateFile };
      writeMathJsonDurable(output, result);
      emit('finished', { status, output });
      return status === 'evaluated_passed' ? 0 : status === 'evaluated_failed' ? 2 : status === 'runtime_error' ? 1 : 4;
    });
  } catch (error) {
    if (!ownsRun) { emit('rejected', { reason: error instanceof Error ? error.message : 'math_runtime_error' }); return 1; }
    const status = controller.signal.aborted ? 'limit_reached' : 'runtime_error';
    if (ownedState) { ownedState.phase = 'finished'; writeSolverRunState(stateFile, ownedState); }
    writeMathJsonDurable(output, { schema: 'deepscientist.math.run.v2', status, run_outcome: status,
      reason: controller.signal.aborted ? preparing ? 'math_preparation_stopped' : 'math_run_stopped' : error instanceof Error ? error.message : 'math_runtime_error',
      runId: ownedState?.runId, problemId: ownedState?.problem.contract.problemId, turns: ownedState?.turns, usage: ownedState?.usage,
      evaluator: { status: 'skipped' }, stateFile });
    emit('finished', { status, output });
    return controller.signal.aborted ? 4 : 1;
  } finally {
    clearTimeout(timer);
    process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort);
    await session?.close();
    await proofEnvironment?.dispose();
  }
}

