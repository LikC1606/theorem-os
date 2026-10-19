import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { parseArgs } from 'node:util';
import { readMathBuildManifest } from '../math/mathBuildManifest';
import { canonicalMathJson, mathDigest, readMathJson, readMathText, withMathRuntimeLease, writeMathJsonDurable } from '../math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../math/mathRuntimeEnvironment';
import { checkResolvedLeanToolchainReadiness } from '../math/leanToolchainReadiness';
import { prepareMathProofEnvironment, MATH_PROOF_ENVIRONMENT_ENV } from '../math/mathProofEnvironment';
import { DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT } from '../math/mathProofEnvironmentCache';
import { resolveMathematicsLakePackagesCache } from '../math/verifier';
import { bindLeanPackages, prepareLeanDiagnosticOverrides, runLeanDiagnostics } from '../math/leanDiagnostics';
import { assertMathCanonicalPath, isMathPathWithin } from '../math/paths';
import { git, readSolverProblem, assertSolverSources } from './problem';
import { solverSourceFeedback } from './feedback';
import { assertMathRetrievalCorpus, createMathRetrievalCorpus, type MathRetrievalCorpus } from '../math/mathRetrievalCorpus';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from './archive';
import { directSolverModules, configuredSolverModules, solverModuleConfiguration, solverMethodDigest, type SolverModules } from './modules';
import { configurableSolverModules } from './modules/custom';
import { researchModulePlanSchema, type ResearchModulePlan } from './modules/policy';
import { researchWorkers } from './modules/organization';
import { runResearchWorkers, type WorkerAccess } from './research';
import { evaluateSolverProof } from './evaluation';
import { solverProofIsCurrent } from './modules/evidence';
import { checkCodexProviderConnectivity } from '../runtime/codexConnectivity';
import { buildTokenBudget } from './usageBudget';
import { selectedDeepSeekProfile } from '../runtime/deepseek';
import { selectedWestlakeProfile } from '../runtime/westlake';

export async function runSolver(args: string[], root: string, customModules?: SolverModules): Promise<number> {
  const { values } = parseArgs({ args, options: {
    workspace: { type: 'string' }, 'receipt-file': { type: 'string' }, 'task-file': { type: 'string' },
    output: { type: 'string' }, 'build-manifest': { type: 'string' }, model: { type: 'string', default: 'gpt-6.1-sol' },
    effort: { type: 'string', default: 'xhigh' }, codex: { type: 'string' }, resume: { type: 'boolean' },
    'max-run-seconds': { type: 'string', default: '1800' }, 'max-turns': { type: 'string', default: '200' },
    'max-total-tokens': { type: 'string', default: '0' },
    'prepare-timeout-seconds': { type: 'string', default: '1800' }, 'max-turn-seconds': { type: 'string', default: '180' },
    'evaluator-command': { type: 'string' }, 'evaluator-timeout-seconds': { type: 'string', default: '1800' },
    'proof-environment-cache-dir': { type: 'string' }, 'startup-only': { type: 'boolean' }, help: { type: 'boolean' },
    method: { type: 'string', default: 'direct' }, workers: { type: 'string', default: '4' },
    'module-plan': { type: 'string' },
    scheduler: { type: 'string', default: 'plan' }, coordination: { type: 'string', default: 'cooperative' },
  } });
  if (values.help) {
    console.log('Usage: theorem-os run --workspace DIR --task-file FILE --output FILE --build-manifest FILE [--receipt-file FILE] [--resume] [--method direct|lemma] [--scheduler plan|goals-first|critical-path|continuation|primary-led] [--module-plan FILE] [--coordination cooperative|independent] [--workers 1|2|3|4] [--model MODEL --effort LEVEL] [--max-run-seconds N --max-turns N --max-turn-seconds N] [--max-total-tokens N] [--prepare-timeout-seconds N] [--evaluator-command CMD --evaluator-timeout-seconds N] [--proof-environment-cache-dir DIR] [--startup-only]\n--module-plan loads the shared research-module plan JSON; use --method direct and --scheduler plan.\nUse 0 for --max-run-seconds, --max-turns, --max-turn-seconds or --evaluator-timeout-seconds to disable that limit. Unlimited total solving time also disables proof verification deadlines.\n--max-total-tokens defaults to 0 (unlimited). A finite value stops new model turns after provider-reported consumption reaches it; in-flight turns finish and may exceed it. Resume retains cumulative usage and the saved allowance unless explicitly changed.');
    return 0;
  }
  const configured = configuredSolverModules(values.method!, values.scheduler!);
  if (customModules && values.scheduler !== 'plan') throw new Error('custom modules cannot combine with --scheduler');
  if (!['cooperative', 'independent'].includes(values.coordination!)) throw new Error('invalid --coordination');
  const coordination = values.coordination as 'cooperative' | 'independent';
  if (values['module-plan'] && (customModules || values.method !== 'direct' || values.scheduler !== 'plan'))
    throw new Error('--module-plan requires --method direct, --scheduler plan and no injected modules');
  const modules = values['module-plan']
    ? configurableSolverModules(researchModulePlanSchema.parse(readMathJson(values['module-plan'])) as ResearchModulePlan, coordination, Number(values.workers))
    : customModules ?? configured;
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
  let maxTotalTokens = Number(values['max-total-tokens']);
  if (!Number.isSafeInteger(maxTotalTokens) || maxTotalTokens < 0) throw new Error('invalid --max-total-tokens');
  const tokenLimitSpecified = args.some(arg => arg === '--max-total-tokens' || arg.startsWith('--max-total-tokens='));
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
      const slots = researchWorkers(path.join(directory, 'worktree'), problem.ownedFiles, workerCount);
      const workers = modules.M5.workers(slots[0].worktree, [...problem.ownedFiles], workerCount);
      if (workers.length !== workerCount || new Set(workers.map(worker => worker.id)).size !== workerCount ||
          workers.some((worker, index) => !/^[a-zA-Z0-9_-]{1,64}$/u.test(worker.id) ||
            worker.worktree !== slots[index].worktree || canonicalMathJson(worker.ownedFiles) !== canonicalMathJson(problem.ownedFiles) ||
            (index === 0 ? worker.id !== 'solver' || worker.role !== 'lead' : !['researcher', 'engineer', 'reviewer'].includes(worker.role))))
        throw new Error('math_solver_worker_outside_ownership');
      let env = resolveMathematicsRuntimeEnvironment();
      let corpusFile = env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS;
      let corpusBytes = corpusFile ? Buffer.from(readMathText(corpusFile), 'utf8') : undefined;
      let corpus = corpusBytes ? JSON.parse(corpusBytes.toString('utf8')) as MathRetrievalCorpus : undefined;
      if (corpusFile) {
        const digest = mathDigest(corpusBytes!);
        if (env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 && env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256 !== digest)
          throw new Error('math_corpus_identity_changed');
        env = { ...env, DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256: digest };
      }
      const profile = process.env.CODEX_HOME || path.join(os.homedir(), '.config/deepscientist/math-sol-codex');
      const westlakeProfile = modules.M1.open === directSolverModules.M1.open ? selectedWestlakeProfile(profile) : undefined;
      const providerProfile = modules.M1.open === directSolverModules.M1.open
        ? selectedDeepSeekProfile(profile) ?? westlakeProfile : undefined;
      const identity = { taskDigest: mathDigest(task), buildDigest: mathDigest(fs.readFileSync(buildFile)),
        providerProfile: providerProfile?.profile, providerProfileDigest: providerProfile?.digest,
        environmentDigest: mathDigest(canonicalMathJson(projectMathematicsRuntimeEnvironment(env))),
        evaluatorDigest: mathDigest(values['evaluator-command'] || 'host-default'), model: values.model!, effort: values.effort!,
        methodDigest: solverMethodDigest(modules, coordination) };
      const moduleConfiguration = solverModuleConfiguration(modules);
      let state: SolverRunState;
      let sourceFeedback: string | undefined;
      if (values.resume) {
        state = readSolverRunState(stateFile);
        if (!tokenLimitSpecified) maxTotalTokens = state.tokenBudget?.maxTotalTokens ?? 0;
        if (!state.methodDigest && modules === directSolverModules && coordination === 'cooperative') state.methodDigest = identity.methodDigest;
        if ((state.coordination ?? 'cooperative') !== coordination) throw new Error('math_resume_coordination_changed');
        if ((state.workerCount ?? 1) !== workerCount) throw new Error('math_resume_worker_count_changed');
        if (workerCount > 1 && (!state.workers || state.workers.length !== workerCount ||
            state.workers.some((worker, index) => worker.id !== workers[index].id ||
              worker.role !== workers[index].role || worker.worktree !== workers[index].worktree)))
          throw new Error('math_resume_worker_identity_changed');
        if (state.schema !== 'deepscientist.math.solver.v1' || state.problem.workspace !== workspace ||
          state.problem.receiptDigest !== problem.receiptDigest ||
          Object.entries(identity).some(([key, value]) => state[key] !== value) ||
          state.worktree !== path.join(directory, 'worktree')) throw new Error('math_resume_identity_changed');
        // Use the current authoritative receipt instead of trusting nested archived source policy.
        state.problem = problem;
        sourceFeedback = solverSourceFeedback(state.problem, state.worktree);
        assertSolverSources(state.problem, workspace);
        if (state.phase === 'finished' && fs.existsSync(output)) {
          const result = readMathJson(output) as { status: string; runId: string; solution_commit: string };
          if (result.status === 'evaluated_passed' || result.status === 'evaluated_failed') {
            const winningWorktree = state.workers?.find(worker => worker.id === state.winningWorker)?.worktree ?? state.worktree;
            assertSolverSources(state.problem, winningWorktree);
            if (!state.check?.passed || result.runId !== state.runId || result.solution_commit !== state.check.commit ||
                !solverProofIsCurrent(state.problem, winningWorktree, state.check) ||
                !solverProofIsCurrent(state.problem, workspace, state.check)) throw new Error('math_resume_completed_proof_changed');
            return result.status === 'evaluated_passed' ? 0 : 2;
          }
        }
      } else {
        if (fs.existsSync(stateFile) || fs.existsSync(output)) throw new Error('math_run_exists_use_resume');
        if (git(workspace, ['status', '--porcelain', '--untracked-files=no'])) throw new Error('math_workspace_has_uncommitted_sources');
        ownsRun = true;
        state = { schema: 'deepscientist.math.solver.v1', runId: crypto.randomUUID(), problem, ...identity,
          worktree: path.join(directory, 'worktree'), phase: 'prepared', turns: 0, dispatchCounts: {}, workerCount,
          coordination, moduleConfiguration, tokenBudget: buildTokenBudget(maxTotalTokens, [],
            westlakeProfile ? 'provider-observed-upstream-request-limit' : undefined) };
        if (workerCount > 1) state.workers = workers
          .map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree, phase: 'prepared', turns: 0, dispatchCounts: {} }));
        git(workspace, ['worktree', 'add', '--detach', state.worktree, problem.baseCommit]);
        writeSolverRunState(stateFile, state);
      }
      ownsRun = true;
      ownedState = state;
      state.tokenBudget = buildTokenBudget(maxTotalTokens, state.workers ?? [state], state.tokenBudget?.enforcement);
      const save = () => writeSolverRunState(stateFile, state);
      for (const worker of workers.slice(1)) {
        signal.throwIfAborted();
        if (!fs.existsSync(worker.worktree)) git(workspace, ['worktree', 'add', '--detach', worker.worktree, problem.baseCommit]);
      }
      const prepareProject = (worktree: string) => {
        const project = path.join(worktree, state.problem.projectRelative);
        fs.mkdirSync(path.join(project, '.lake'), { recursive: true });
        writeMathJsonDurable(path.join(project, '.lake/source-constraints.json'), {
          trustedFiles: state.problem.trustedFiles, declarations: state.problem.declarations,
          sourceStructure: state.problem.sourceStructure, sourceImports: state.problem.sourceImports,
        }, 0o400);
        if (sourcePackages) bindLeanPackages(project, sourcePackages);
        return project;
      };
      const sourceProject = path.join(workspace, problem.projectRelative);
      const sourcePackages = resolveMathematicsLakePackagesCache(sourceProject, env);
      if (!sourcePackages) {
        const manifestFile = path.join(sourceProject, 'lake-manifest.json');
        const manifest = fs.existsSync(manifestFile) ? readMathJson(manifestFile) as { packages?: unknown } : undefined;
        if (Array.isArray(manifest?.packages) && manifest.packages.length) {
          emit('preparation_failed', { workerId: 'solver', diagnostics:
            'No manifest-compatible Lake package cache is configured. Supply a trusted cache with the pinned Git revisions; sandboxed verification never downloads dependencies.' });
          throw new Error('math_lake_packages_unavailable');
        }
      }
      const project = prepareProject(state.worktree);
      if (!values.resume) sourceFeedback = solverSourceFeedback(state.problem, state.worktree);
      if (sourceFeedback) { state.check = undefined; save(); }
      const connectivity = modules.M1.open === directSolverModules.M1.open
        ? await checkCodexProviderConnectivity({ env, signal, profile })
        : { status: 'not-required', diagnostics: 'The custom execution component does not use the built-in Codex provider.' };
      writeMathJsonDurable(path.join(directory, 'provider-connectivity.json'), connectivity);
      if (connectivity.status !== 'reachable' && connectivity.status !== 'not-required') {
        emit('preparation_failed', { workerId: 'solver', diagnostics: connectivity.diagnostics });
        throw new Error('math_codex_provider_unreachable');
      }
      const readiness = checkResolvedLeanToolchainReadiness({ projectRoot: project, env, timeoutMs: 180_000 });
      writeMathJsonDurable(path.join(directory, 'toolchain-readiness.json'), readiness);
      if (readiness.status !== 'ready') {
        emit('preparation_failed', { workerId: 'solver', diagnostics: readiness.diagnostics });
        throw new Error('math_lean_toolchain_unavailable');
      }
      if (sourcePackages) {
        // Model-side path overrides are regenerated after binding the frozen packages.
        // Their worktree-specific paths must not invalidate the preparation cache on resume.
        const overrides = path.join(project, '.lake', 'package-overrides.json');
        assertMathCanonicalPath(overrides);
        fs.rmSync(overrides, { force: true });
        proofEnvironment = await prepareMathProofEnvironment(project, sourcePackages, { env, signal,
          deadlineAt: preparationStarted + preparationMs,
          cacheRoot: values['proof-environment-cache-dir'] || DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT,
          onProgress: phase => emit('proof_environment', { phase }) });
        env = { ...env, [MATH_PROOF_ENVIRONMENT_ENV]: proofEnvironment.environmentValue };
      }
      const checkDependencies = async (workerId: string, projectRoot: string) => {
        if (sourcePackages) prepareLeanDiagnosticOverrides(projectRoot);
        const diagnostics = await runLeanDiagnostics({ projectRoot, files: [...new Set(problem.targets.map(target => target.proofPath))],
          dependenciesOnly: true, excludedFiles: problem.ownedFiles, env, signal,
          timeoutMs: preparationMs - (Date.now() - preparationStarted),
          onProgress: file => emit('dependency_check', { workerId, file }) });
        writeMathJsonDurable(path.join(directory, workerId === 'solver' ? 'preparation-diagnostics.json' : `preparation-${workerId}.json`), diagnostics);
        if (diagnostics.exitCode !== 0 || diagnostics.timedOut) {
          emit('preparation_failed', { workerId, timedOut: diagnostics.timedOut,
            diagnostics: (diagnostics.stderr || diagnostics.stdout || 'Lean dependency check did not finish.').slice(0, 2000) });
          throw new Error('math_lean_dependencies_failed');
        }
        return diagnostics;
      };
      const diagnostics = await checkDependencies('solver', project);
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
        }
        corpusBytes = Buffer.from(readMathText(corpusFile), 'utf8');
        corpus ??= JSON.parse(corpusBytes.toString('utf8')) as MathRetrievalCorpus;
        const digest = mathDigest(corpusBytes);
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
      const prepareAccess = (workerId: string, workerRoot: string, workerProject: string, workerCorpus?: string) => {
        const environmentFile = path.join(directory, `environment-${workerId}.json`);
        const environment = { ...env, DEEPSCIENTIST_MATH_ENV_FILE: environmentFile,
          DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS: workerCorpus };
        writeMathJsonDurable(environmentFile, projectMathematicsRuntimeEnvironment(environment), 0o400);
        workerAccess.set(workerId, { environment: resolveMathematicsRuntimeEnvironment(environment), corpusFile: workerCorpus,
          retrievalRoot: corpus?.projectSubdirectory ? workerRoot : workerProject });
      };
      prepareAccess('solver', state.worktree, project, corpusFile);
      const peerPreparation = await Promise.allSettled(workers.slice(1).map(async worker => {
        signal.throwIfAborted();
        const workerProject = prepareProject(worker.worktree);
        const lake = path.join(workerProject, '.lake');
        await checkDependencies(worker.id, workerProject);
        let workerCorpusFile: string | undefined;
        if (corpusFile) {
          workerCorpusFile = path.join(lake, 'retrieval-corpus.json');
          assertMathCanonicalPath(workerCorpusFile);
          if (fs.existsSync(workerCorpusFile)) {
            if (mathDigest(readMathText(workerCorpusFile)) !== env.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256)
              throw new Error('math_corpus_identity_changed');
          } else fs.writeFileSync(workerCorpusFile, corpusBytes!, { mode: 0o400, flag: 'wx' });
        }
        prepareAccess(worker.id, worker.worktree, workerProject, workerCorpusFile);
      }));
      const failedPreparation = peerPreparation.find(result => result.status === 'rejected');
      if (failedPreparation?.status === 'rejected') throw failedPreparation.reason;
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
      state.solveStartedAt = Date.now();
      state.solveFinishedAt = undefined;
      deadline = state.solveStartedAt + maxRunMs;
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
        profile,
        signal, deadline, maxTurns, maxTurnMs, maxTotalTokens, proofTimeoutMs: maxRunMs === Infinity ? Infinity : undefined, save, emit });
      clearTimeout(timer);
      timer = undefined;
      state.solveFinishedAt = Date.now();
      let evaluation: Record<string, unknown> = { status: 'skipped', reason: 'proof_incomplete' };
      if (winner?.check.passed) {
        state.phase = 'evaluating'; save();
        readMathBuildManifest(buildFile, root, bundleRoot);
        const evaluationStarted = Date.now();
        emit('evaluation_started', { workerId: state.winningWorker ?? 'solver' });
        evaluation = await evaluateSolverProof(state.problem, winner.worktree, winner.check, env, signal,
          { command: values['evaluator-command'], timeoutMs: evaluatorMs });
        emit('evaluation_finished', { status: evaluation.status, durationMs: Date.now() - evaluationStarted });
      }
      state.phase = 'finished'; save();
      const status = signal.aborted ? 'limit_reached' : evaluation.status === 'passed' ? 'evaluated_passed' : evaluation.status === 'failed' ? 'evaluated_failed' : evaluation.status === 'error' ? 'runtime_error' : state.tokenBudget?.reason ? 'limit_reached' : 'incomplete';
      const result = { schema: 'deepscientist.math.run.v2', runId: state.runId, problemId: state.problem.contract.problemId,
        status, run_outcome: status, solution_commit: state.check?.passed ? state.check.commit : null,
        solver_ready_receipt_valid: state.check?.passed === true, completion_signal_valid: evaluation.status === 'passed',
        evaluator: evaluation, turns: state.turns, dispatchCounts: state.dispatchCounts, tokenBudget: state.tokenBudget,
        ...(status === 'limit_reached' && state.tokenBudget?.reason ? { reason: state.tokenBudget.reason } : {}),
        solveWallMs: state.solveFinishedAt - state.solveStartedAt, usage: state.usage, stateFile, winningWorker: state.winningWorker,
        workers: state.workers?.map(worker => ({ id: worker.id, role: worker.role, turns: worker.turns,
          dispatchCounts: worker.dispatchCounts, usage: worker.usage, error: worker.error })) };
      writeMathJsonDurable(output, result);
      emit('finished', { status, output });
      return status === 'evaluated_passed' ? 0 : status === 'evaluated_failed' ? 2 : status === 'runtime_error' ? 1 : 4;
    });
  } catch (error) {
    if (!ownsRun) { emit('rejected', { reason: error instanceof Error ? error.message : 'math_runtime_error' }); return 1; }
    const status = controller.signal.aborted ? 'limit_reached' : 'runtime_error';
    if (ownedState) {
      ownedState.phase = 'finished';
      if (ownedState.solveStartedAt && !ownedState.solveFinishedAt) ownedState.solveFinishedAt = Date.now();
      ownedState.error = controller.signal.aborted ? undefined : error instanceof Error ? error.message : 'math_runtime_error';
      writeSolverRunState(stateFile, ownedState);
    }
    writeMathJsonDurable(output, { schema: 'deepscientist.math.run.v2', status, run_outcome: status,
      reason: controller.signal.aborted ? preparing ? 'math_preparation_stopped' : 'math_run_stopped' : error instanceof Error ? error.message : 'math_runtime_error',
      runId: ownedState?.runId, problemId: ownedState?.problem.contract.problemId, turns: ownedState?.turns,
      dispatchCounts: ownedState?.dispatchCounts, usage: ownedState?.usage, tokenBudget: ownedState?.tokenBudget,
      workers: ownedState?.workers?.map(worker => ({ id: worker.id, role: worker.role, turns: worker.turns,
        dispatchCounts: worker.dispatchCounts, usage: worker.usage, error: worker.error })),
      evaluator: { status: 'skipped' }, stateFile });
    emit('finished', { status, output });
    return controller.signal.aborted ? 4 : 1;
  } finally {
    clearTimeout(timer);
    process.removeListener('SIGINT', abort); process.removeListener('SIGTERM', abort);
    await proofEnvironment?.dispose();
  }
}

