import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { parseArgs } from 'node:util';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { canonicalMathJson, mathDigest, readMathJson, withMathRuntimeLease, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { checkResolvedLeanToolchainReadiness } from '../math/leanToolchainReadiness';
import { prepareMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV } from '../math/mathProofEnvironment';
import { resolveMathematicsLakePackagesCache } from '../math/verifier';
import { prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../math/leanDiagnostics';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { git, readSolverProblem, assertSolverSources } from './problem';
import { solverSourceFeedback } from './feedback';
import { assertMathRetrievalCorpus, createMathRetrievalCorpus, type MathRetrievalCorpus } from '../math/mathRetrievalCorpus';
import { integrateResearch } from './modules/integration';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from './archive';
import { directSolverModules, lemmaSolverModules, type SolverModules } from './modules';
import { researchWorkers } from './modules/organization';
import { runResearchWorkers, type WorkerAccess } from './research';
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
    method: { type: 'string', default: 'direct' }, workers: { type: 'string', default: '4' },
  } });
  if (values.help) {
    console.log('Usage: deepscientist-math run --workspace DIR --task-file FILE --output FILE --build-manifest FILE [--receipt-file FILE] [--resume] [--method direct|lemma] [--workers 1|2|3|4] [--model MODEL --effort LEVEL] [--max-run-seconds N --max-turns N --max-turn-seconds N] [--prepare-timeout-seconds N] [--evaluator-command CMD --evaluator-timeout-seconds N] [--proof-environment-cache-dir DIR] [--startup-only]\nUse 0 for --max-run-seconds, --max-turns, --max-turn-seconds or --evaluator-timeout-seconds to disable that limit. Unlimited total solving time also disables proof verification deadlines.');
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
  const workerCount = limit('workers');
  if (workerCount > 4) throw new Error('invalid --workers');
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
        if ((state.workerCount ?? 1) !== workerCount) throw new Error('math_resume_worker_count_changed');
        const expectedWorkers = researchWorkers(path.join(directory, 'worktree'), problem.ownedFiles, workerCount);
        if (workerCount > 1 && (!state.workers || state.workers.length !== workerCount ||
            state.workers.some((worker, index) => worker.id !== expectedWorkers[index].id ||
              worker.role !== expectedWorkers[index].role || worker.worktree !== expectedWorkers[index].worktree)))
          throw new Error('math_resume_worker_identity_changed');
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
          worktree: path.join(directory, 'worktree'), phase: 'prepared', turns: 0, workerCount };
        if (workerCount > 1) state.workers = researchWorkers(state.worktree, problem.ownedFiles, workerCount)
          .map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'prepared', turns: 0 }));
        git(workspace, ['worktree', 'add', '--detach', state.worktree, problem.baseCommit]);
        writeSolverRunState(stateFile, state);
      }
      ownsRun = true;
      ownedState = state;
      const save = () => writeSolverRunState(stateFile, state);
      const workers = researchWorkers(state.worktree, problem.ownedFiles, workerCount);
      for (const worker of workers.slice(1)) {
        signal.throwIfAborted();
        if (!fs.existsSync(worker.worktree)) git(workspace, ['worktree', 'add', '--detach', worker.worktree, problem.baseCommit]);
      }
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
      const workerAccess = new Map<string, WorkerAccess>();
      workerAccess.set('solver', { environment: env, corpusFile, retrievalRoot });
      for (const worker of workers.slice(1)) {
        signal.throwIfAborted();
        const workerProject = path.join(worker.worktree, problem.projectRelative);
        const lake = path.join(workerProject, '.lake');
        fs.mkdirSync(lake, { recursive: true });
        writeMathJsonDurable(path.join(lake, 'source-constraints.json'), {
          trustedFiles: state.problem.trustedFiles, declarations: state.problem.declarations,
          sourceStructure: state.problem.sourceStructure,
        }, 0o400);
        if (sourcePackages) {
          const packages = path.join(lake, 'packages');
          if (!fs.existsSync(packages)) fs.symlinkSync(sourcePackages, packages, 'dir');
          prepareLeanDiagnosticOverrides(workerProject);
        }
        const prepared = await runLeanDiagnostics({ projectRoot: workerProject,
          files: [...new Set(problem.targets.map(target => target.proofPath))], dependenciesOnly: true,
          excludedFiles: problem.ownedFiles, env, signal, timeoutMs: preparationMs - (Date.now() - preparationStarted),
          onProgress: file => emit('dependency_check', { workerId: worker.id, file }) });
        writeMathJsonDurable(path.join(directory, `preparation-${worker.id}.json`), prepared);
        if (prepared.exitCode !== 0 || prepared.timedOut) throw new Error('math_lean_dependencies_failed');
        let workerCorpusFile: string | undefined;
        if (corpusFile) {
          workerCorpusFile = path.join(lake, 'retrieval-corpus.json');
          const bytes = fs.readFileSync(corpusFile);
          assertMathCanonicalPath(workerCorpusFile);
          if (fs.existsSync(workerCorpusFile) && mathDigest(fs.readFileSync(workerCorpusFile)) !== mathDigest(bytes))
            throw new Error('math_corpus_identity_changed');
          fs.writeFileSync(workerCorpusFile, bytes, { mode: 0o400 });
        }
        workerAccess.set(worker.id, { environment: { ...env, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: workerCorpusFile },
          corpusFile: workerCorpusFile, retrievalRoot: corpus?.projectSubdirectory ? worker.worktree : workerProject });
      }
      emit('ready', { runId: state.runId, worktree: state.worktree, workers });
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
      if (values.resume) {
        // Persisted auxiliary receipts cannot authorize reuse after a process restart.
        for (const research of state.workers ?? [state]) if (research.lemmaResearch)
          research.lemmaResearch = { plan: research.lemmaResearch.plan, error: research.lemmaResearch.error };
        save();
      }
      const winner = await runResearchWorkers({ state, workers, access: workerAccess, modules, root, buildFile, taskText: task,
        executable: values.codex || process.env.DEEPSCIENTIST_MATH_CODEX_EXECUTABLE || 'codex',
        profile: process.env.CODEX_HOME || path.join(os.homedir(), '.config/deepscientist/math-sol-codex'),
        signal, deadline, maxTurns, maxTurnMs, proofTimeoutMs: maxRunMs === Infinity ? Infinity : undefined, save, emit });
      let evaluation: Record<string, unknown> = { status: 'skipped', reason: 'proof_incomplete' };
      if (winner) {
        state.phase = 'evaluating'; save();
        readMathBuildManifest(buildFile, root, bundleRoot);
        const integration = integrateResearch(state.problem,
          [{ commit: winner.check.commit, sourceDigest: winner.check.sourceDigest }], [winner.check]);
        if (integration.candidate && integration.dependenciesClosed) {
          const evaluationStarted = Date.now();
          emit('evaluation_started', { workerId: state.winningWorker ?? 'solver' });
          evaluation = await evaluateSolverProof(state.problem, winner.worktree, winner.check, env, signal,
            { command: values['evaluator-command'], timeoutMs: evaluatorMs });
          emit('evaluation_finished', { status: evaluation.status, durationMs: Date.now() - evaluationStarted });
        }
      }
      state.phase = 'finished'; save();
      const status = signal.aborted ? 'limit_reached' : evaluation.status === 'passed' ? 'evaluated_passed' : evaluation.status === 'failed' ? 'evaluated_failed' : evaluation.status === 'error' ? 'runtime_error' : 'incomplete';
      const result = { schema: 'deepscientist.math.run.v2', runId: state.runId, problemId: state.problem.contract.problemId,
        status, run_outcome: status, solution_commit: state.check?.passed ? state.check.commit : null,
        solver_ready_receipt_valid: state.check?.passed === true, completion_signal_valid: evaluation.status === 'passed',
        evaluator: evaluation, turns: state.turns, usage: state.usage, stateFile, winningWorker: state.winningWorker,
        workers: state.workers?.map(worker => ({ id: worker.id, role: worker.role, turns: worker.turns, usage: worker.usage, error: worker.error })) };
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
    await proofEnvironment?.dispose();
  }
}

