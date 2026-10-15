#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseFlags, required } from './arguments';
import { bootstrapImo2026Problem, IMO2026_SUPPORTED_PROBLEMS, IMO2026_SOURCE_COMMIT } from '../../src/math/imo2026Adapter';
import { readMathBuildManifest } from '../../src/math/mathBuildManifest';
import { mathDigest, canonicalMathJson, readMathText, writeMathJsonDurable } from '../../src/math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../../src/math/mathRuntimeEnvironment';
import { readSolverProblem } from '../../src/solver/problem';
import { readRunInspection } from '../../src/solver/inspection';
import { runMathBatch } from './runMathBatch';
import { configuredSolverModules, solverMethodDigest } from '../../src/solver/modules';
import { proofReceiptsMatch, type ProofCheck } from '../../src/solver/modules/evidence';
import type { SolverRunState } from '../../src/solver/archive';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const arms = ['single', 'independent', 'cooperative'] as const;
type Arm = typeof arms[number];
type Job = { arm: Arm; repetition: number; launch: string; launchDigest: string; output: string; receiptDigest: string; methodDigest: string };
type Plan = {
  schema: 'deepscientist.math.comparison.v1'; problem: string; sourceCommit: string;
  taskDigest: string; buildDigest: string; environmentDigest: string;
  configuration: { model: string; effort: string; method: string; scheduler: string; workers: number;
    maxTurns: number; maxRunSeconds: number; maxTurnSeconds: number };
  jobs: Job[];
};
const json = (file: string) => JSON.parse(readMathText(file));
const writeNew = (file: string, value: unknown) => fs.writeFileSync(file, JSON.stringify(value, null, 2) + '\n', { flag: 'wx', mode: 0o600 });
const environmentDigest = () => mathDigest(canonicalMathJson(projectMathematicsRuntimeEnvironment(resolveMathematicsRuntimeEnvironment())));

/** Rotate arm order between repetitions; repetition labels are not provider sampling seeds. */
export function comparisonOrder(repetitions: number): { arm: Arm; repetition: number }[] {
  return Array.from({ length: repetitions }, (_, index) => arms.map((_, offset) => ({
    arm: arms[(index + offset) % arms.length], repetition: index + 1 }))).flat();
}

/** Preserve every planned attempt, including missing results and unavailable token counters. */
export function comparisonTotals(rows: { arm: Arm; accepted: boolean; totalTokens: number | null }[]) {
  return arms.map(arm => {
    const runs = rows.filter(row => row.arm === arm);
    return { arm, planned: runs.length, accepted: runs.filter(row => row.accepted).length,
      acceptanceRate: runs.length ? runs.filter(row => row.accepted).length / runs.length : null,
      reportedTokens: runs.reduce((sum, row) => sum + (row.totalTokens ?? 0), 0),
      missingTokenRuns: runs.filter(row => row.totalTokens === null).length };
  });
}

export function comparisonReport(directory: string, plan: Plan) {
  const batchFile = path.join(directory, 'batch.json');
  const batch = fs.existsSync(batchFile) ? json(batchFile) : undefined;
  const rows = plan.jobs.map(job => {
    const execution = batch?.jobs?.find((item: { launch: string }) => item.launch === job.launch);
    let status = 'missing', accepted = false, turns: number | null = null, usage: Record<string, unknown> | undefined;
    let dispatchCounts: SolverRunState['dispatchCounts'];
    let solveWallMs: number | null = null;
    let error: string | undefined;
    let workerErrors: { id: string; error: string }[] = [];
    let missingUsageWorkers: string[] = [];
    const numeric = (value: unknown): value is number => typeof value === 'number' && Number.isSafeInteger(value) && value >= 0;
    const tokens = (usage?: Record<string, unknown>) => numeric(usage?.totalTokens) ? usage.totalTokens :
      numeric(usage?.inputTokens) && numeric(usage?.outputTokens) ? usage.inputTokens + usage.outputTokens : null;
    try {
      const { state, result } = readRunInspection(job.output);
      const expectedWorkers = job.arm === 'single' ? 1 : plan.configuration.workers;
      if (state.problem.receiptDigest !== job.receiptDigest || state.taskDigest !== plan.taskDigest ||
          state.buildDigest !== plan.buildDigest || state.environmentDigest !== plan.environmentDigest || state.methodDigest !== job.methodDigest ||
          state.evaluatorDigest !== mathDigest('host-default') ||
          state.model !== plan.configuration.model || state.effort !== plan.configuration.effort ||
          (state.workerCount ?? 1) !== expectedWorkers ||
          (state.coordination ?? 'cooperative') !== (job.arm === 'cooperative' ? 'cooperative' : 'independent'))
        throw new Error('comparison_run_identity_mismatch');
      turns = state.turns; usage = state.usage;
      dispatchCounts = state.dispatchCounts;
      if (numeric(state.solveStartedAt) && numeric(state.solveFinishedAt) && state.solveFinishedAt >= state.solveStartedAt)
        solveWallMs = state.solveFinishedAt - state.solveStartedAt;
      missingUsageWorkers = (state.workers ?? [{ id: 'solver', ...state }]).filter(worker =>
        (worker.turns > 0 || ('error' in worker && worker.error)) && tokens(worker.usage) === null).map(worker => worker.id);
      workerErrors = (state.workers ?? []).flatMap(worker => worker.error ? [{ id: worker.id, error: worker.error }] : []);
      status = state.phase !== 'finished' ? 'unfinished' : String(result?.status ?? 'missing');
      const evaluator = result?.evaluator as { status?: string; method?: string; official?: boolean; verification?: ProofCheck } | undefined;
      accepted = status === 'evaluated_passed' && result?.completion_signal_valid === true &&
        result?.solver_ready_receipt_valid === true && state.check?.passed === true &&
        result?.solution_commit === state.check.commit && evaluator?.status === 'passed' &&
        evaluator.method === 'host-lean-kernel-all-targets' && evaluator.official === false &&
        evaluator.verification?.passed === true && evaluator.verification.commit === state.check.commit &&
        evaluator.verification.sourceDigest === state.check.sourceDigest && state.problem.targets.length > 0 &&
        proofReceiptsMatch(evaluator.verification.verification, state.check.commit, state.problem.targets.map(target => ({
          proofPath: target.proofPath, theoremName: target.theoremName, expectedSourceDeclarationHash: target.declarationHash,
          statementHash: state.problem.contract.statementHash, leanStatementHash: state.problem.contract.leanStatementHash, claim: 'statement' })));
      error = typeof result?.reason === 'string' ? result.reason : undefined;
      if (status === 'evaluated_passed' && !accepted) error = 'comparison_acceptance_evidence_incomplete';
    } catch (cause) {
      status = fs.existsSync(`${job.output}.runtime/state.json`) || fs.existsSync(job.output) ? 'invalid' : 'missing';
      error = cause instanceof Error ? cause.message : String(cause);
    }
    const totalTokens = missingUsageWorkers.length ? null : tokens(usage);
    const elapsed = execution?.startedAt && execution?.finishedAt
      ? Date.parse(execution.finishedAt) - Date.parse(execution.startedAt) : NaN;
    return { arm: job.arm, repetition: job.repetition, status, accepted, turns, dispatches: turns, dispatchCounts, solveWallMs,
      totalTokens, missingUsageWorkers, usage, workerErrors, error, wallMs: Number.isFinite(elapsed) && elapsed >= 0 ? elapsed : null,
      exitCode: execution?.exitCode ?? null, result: job.output, log: execution?.log };
  });
  return { schema: 'deepscientist.math.comparison-report.v1', evidence: 'recorded-not-replayed',
    problem: plan.problem, configuration: plan.configuration, official: false,
    totals: comparisonTotals(rows), runs: rows };
}

export async function compareMathRuns(argv: string[]): Promise<number> {
  const flags = parseFlags(argv, ['phase', 'directory', 'repo', 'problem', 'task-file', 'build-manifest',
    'repetitions', 'model', 'effort', 'method', 'scheduler', 'workers', 'max-turns', 'max-run-seconds', 'max-turn-seconds',
    'proof-environment-cache-dir']);
  if (flags.has('help')) {
    console.log('Usage: theorem-os compare --phase prepare|run|report --directory DIR\n'
      + 'prepare also requires --repo PINNED_IMO_REPO --problem ID --task-file FILE --build-manifest FILE\n'
      + 'Optional: --repetitions 1 --workers 4 --model gpt-6.1-sol --effort xhigh --method direct --scheduler plan|goals-first|critical-path|primary-led\n'
      + '          --max-turns 200 --max-run-seconds 1800 --max-turn-seconds 180\n'
      + '          --proof-environment-cache-dir HOST_PRIVATE_DIR\n'
      + 'prepare never invokes a model. run executes all three arms sequentially. Each arm uses a wall-time limit;\n'
      + '--max-turns is a shared dispatch safety cap, not equal compute. Token usage includes all roles.');
    return 0;
  }
  const phase = required(flags, 'phase');
  if (!['prepare', 'run', 'report'].includes(phase)) throw new Error('invalid --phase');
  const directory = path.resolve(required(flags, 'directory'));
  const planFile = path.join(directory, 'comparison.json');
  if (phase === 'prepare') {
    const number = (key: string, fallback: number) => {
      const value = Number(flags.get(key) ?? fallback);
      if (!Number.isSafeInteger(value) || value < 1) throw new Error(`invalid --${key}: a fixed positive budget is required`);
      return value;
    };
    const repetitions = number('repetitions', 1), workers = number('workers', 4);
    if (workers < 2 || workers > 4) throw new Error('--workers must be 2, 3 or 4');
    const method = flags.get('method') ?? 'direct', scheduler = flags.get('scheduler') ?? 'plan';
    if (!['direct', 'lemma'].includes(method) || !['plan', 'goals-first', 'critical-path', 'primary-led'].includes(scheduler)) throw new Error('invalid method or scheduler');
    const configuration = { model: flags.get('model') ?? 'gpt-6.1-sol', effort: flags.get('effort') ?? 'xhigh', method, scheduler,
      workers, maxTurns: number('max-turns', 200), maxRunSeconds: number('max-run-seconds', 1800), maxTurnSeconds: number('max-turn-seconds', 180) };
    const repositoryRoot = fs.realpathSync(required(flags, 'repo'));
    const problem = required(flags, 'problem');
    if (!IMO2026_SUPPORTED_PROBLEMS.includes(problem as typeof IMO2026_SUPPORTED_PROBLEMS[number])) throw new Error('unsupported IMO problem');
    const build = fs.realpathSync(required(flags, 'build-manifest'));
    const proofCache = flags.has('proof-environment-cache-dir') ? path.resolve(required(flags, 'proof-environment-cache-dir')) : undefined;
    readMathBuildManifest(build, root, path.join(root, 'out/main'));
    const task = readMathText(required(flags, 'task-file'));
    if (!task.trim()) throw new Error('empty task');
    fs.mkdirSync(path.dirname(directory), { recursive: true });
    const canonical = path.join(fs.realpathSync(path.dirname(directory)), path.basename(directory));
    for (const source of [root, repositoryRoot]) if (canonical === source || canonical.startsWith(source + path.sep))
      throw new Error('comparison directory must be outside source checkouts');
    fs.mkdirSync(directory, { mode: 0o700 });
    const taskFile = path.join(directory, 'task.md');
    fs.writeFileSync(taskFile, task, { flag: 'wx', mode: 0o400 });
    const plan: Plan = { schema: 'deepscientist.math.comparison.v1', problem, sourceCommit: IMO2026_SOURCE_COMMIT,
      taskDigest: mathDigest(task), buildDigest: mathDigest(fs.readFileSync(build)), environmentDigest: environmentDigest(), configuration, jobs: [] };
    for (const item of comparisonOrder(repetitions)) {
      const jobRoot = path.join(directory, `${item.repetition}-${item.arm}`);
      fs.mkdirSync(jobRoot, { mode: 0o700 });
      const workspace = path.join(jobRoot, 'workspace'), output = path.join(jobRoot, 'result.json');
      await bootstrapImo2026Problem({ repositoryRoot, problemId: problem as typeof IMO2026_SUPPORTED_PROBLEMS[number], workspaceRoot: workspace });
      const receipt = readSolverProblem(workspace, path.join(workspace, 'active-problem.json'));
      const launch = path.join(jobRoot, 'launch.json');
      writeNew(launch, { cwd: root, ...(process.env.DEEPSCIENTIST_MATH_ENV_FILE ? { envFile: path.resolve(process.env.DEEPSCIENTIST_MATH_ENV_FILE) } : {}),
        args: [process.execPath, path.join(root, 'bin/math.ts'), 'run', '--workspace', workspace, '--task-file', taskFile,
          '--output', output, '--build-manifest', build, '--model', configuration.model, '--effort', configuration.effort,
          '--method', method, '--scheduler', scheduler, '--workers', String(item.arm === 'single' ? 1 : workers),
          '--coordination', item.arm === 'cooperative' ? 'cooperative' : 'independent',
          '--max-turns', String(configuration.maxTurns), '--max-run-seconds', String(configuration.maxRunSeconds),
          '--max-turn-seconds', String(configuration.maxTurnSeconds),
          ...(proofCache ? ['--proof-environment-cache-dir', proofCache] : [])] });
      plan.jobs.push({ ...item, launch, launchDigest: mathDigest(fs.readFileSync(launch)), output, receiptDigest: receipt.receiptDigest,
        methodDigest: solverMethodDigest(configuredSolverModules(method, scheduler), item.arm === 'cooperative' ? 'cooperative' : 'independent') });
    }
    writeNew(planFile, plan);
    console.log(JSON.stringify({ planFile, jobs: plan.jobs.length, status: 'prepared', invokesModel: false }));
    return 0;
  }
  const plan = json(planFile) as Plan;
  if (plan.schema !== 'deepscientist.math.comparison.v1' || !Array.isArray(plan.jobs) || !plan.jobs.length)
    throw new Error('invalid comparison plan');
  let code = 0;
  if (phase === 'run') {
    if (environmentDigest() !== plan.environmentDigest) throw new Error('comparison_environment_changed');
    if (mathDigest(readMathText(path.join(directory, 'task.md'))) !== plan.taskDigest) throw new Error('comparison_task_changed');
    for (const job of plan.jobs) if (mathDigest(fs.readFileSync(job.launch)) !== job.launchDigest) throw new Error('comparison_launch_changed');
    code = await runMathBatch([...plan.jobs.flatMap(job => ['--launch', job.launch]), '--concurrency', '1', '--output', path.join(directory, 'batch.json')]);
  }
  const reportFile = path.join(directory, 'report.json');
  const report = comparisonReport(directory, plan);
  writeMathJsonDurable(reportFile, report);
  console.log(JSON.stringify({ reportFile, totals: report.totals }));
  return code;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  compareMathRuns(process.argv.slice(2)).then(code => { process.exitCode = code; }, error => {
    console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
  });
}
