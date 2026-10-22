import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { compareMathRuns, comparisonOrder, comparisonReport } from '../scripts/mathematics/compareMathRuns';
import { describeModuleExperiment, moduleExperimentPairs, moduleExperimentSchema } from '../scripts/mathematics/moduleExperiment';
import * as batch from '../scripts/mathematics/runMathBatch';
import * as imoAdapter from '../src/math/imo2026Adapter';
import * as buildManifest from '../src/math/mathBuildManifest';
import * as solverProblem from '../src/solver/problem';
import { configuredSolverModules } from '../src/solver/modules';
import { researchWorkers } from '../src/solver/modules/organization';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { runSolver } from '../src/solver/run';
import { buildTokenBudget } from '../src/solver/usageBudget';
import type { TaskRecord } from '../src/solver/tasks';

const root = fileURLToPath(new URL('..', import.meta.url));
const example = () => JSON.parse(fs.readFileSync(path.join(root, 'examples/components/module-experiment.json'), 'utf8'));
const directories: string[] = [];
const temporary = () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-module-experiment-'));
  directories.push(directory);
  return directory;
};
const read = (file: string) => JSON.parse(fs.readFileSync(file, 'utf8'));
afterEach(() => {
  vi.restoreAllMocks();
  vi.unstubAllEnvs();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

async function prepare(repetitions = 1, provider?: string) {
  const directory = temporary(), repository = path.join(directory, 'repo');
  fs.mkdirSync(repository);
  const task = path.join(directory, 'task.md'), manifest = path.join(directory, 'build.json');
  fs.writeFileSync(task, 'Prove all original targets.'); fs.writeFileSync(manifest, '{}');
  vi.spyOn(buildManifest, 'readMathBuildManifest').mockReturnValue({} as never);
  const bootstrap = vi.spyOn(imoAdapter, 'bootstrapImo2026Problem').mockResolvedValue({} as never);
  vi.spyOn(solverProblem, 'readSolverProblem').mockReturnValue({ receiptDigest: 'receipt' } as never);
  vi.spyOn(console, 'log').mockImplementation(() => {});
  const output = path.join(directory, 'comparison');
  await compareMathRuns(['--phase', 'prepare', '--directory', output, '--repo', repository,
    '--problem', 'imo2026_q1', '--task-file', task, '--build-manifest', manifest,
    '--module-experiment', path.join(root, 'examples/components/module-experiment.json'),
    '--repetitions', String(repetitions), '--max-turns', '20', '--max-run-seconds', '600', '--max-total-tokens', '30000',
    ...(provider ? ['--provider', provider] : [])]);
  return { directory: output, plan: read(path.join(output, 'comparison.json')), bootstrap };
}

describe('module experiment definitions', () => {
  it('reports actual changed versions, including combined scheduling and rule injection', () => {
    const experiment = moduleExperimentSchema.parse(example());
    expect(describeModuleExperiment(experiment, 4).map(variant => [variant.id, variant.changedComponents])).toEqual([
      ['default', []], ['essential-context', ['M4']], ['critical-path', ['M3', 'M5']], ['construction-rule', ['M1', 'M4']],
    ]);
    expect(comparisonOrder(2, ['a', 'b', 'c']).map(job => job.arm)).toEqual(['a', 'b', 'c', 'b', 'c', 'a']);
  });

  it.each(['unknown-baseline', 'duplicate-id', 'path-id', 'extra-field', 'one-variant', 'M2-rule'])('rejects malformed experiment %s', kind => {
    const value = example();
    if (kind === 'unknown-baseline') value.baseline = 'absent';
    if (kind === 'duplicate-id') value.variants[1].id = value.variants[0].id;
    if (kind === 'path-id') value.variants[1].id = '../outside';
    if (kind === 'extra-field') value.variants[1].evaluator = 'skip';
    if (kind === 'one-variant') value.variants = value.variants.slice(0, 1);
    if (kind === 'M2-rule') value.variants[3].plan.custom[0].slot = 'M2';
    expect(moduleExperimentSchema.safeParse(value).success).toBe(false);
  });

  it('rejects aliases and disabled rules that produce the same effective configuration', () => {
    const experiment = moduleExperimentSchema.parse(example());
    experiment.variants = [experiment.variants[0], experiment.variants[3]];
    experiment.variants[1].plan.custom[0].enabled = false;
    expect(() => describeModuleExperiment(experiment, 4)).toThrow('duplicate_effective_configuration');
  });

  it('verifies the complete ready-to-assignment path changes real work selection', () => {
    const node = (id: string, kind: 'goal' | 'lemma', dependsOn: string[] = []): TaskRecord => ({
      task: { id, kind, objective: id, dependsOn, revision: 0 }, status: 'pending', attempts: 0,
    });
    const tasks = [node('unneeded', 'lemma'), node('bridge', 'lemma'), node('ready-goal', 'goal'), node('blocked-goal', 'goal', ['bridge'])];
    const workers = researchWorkers('/worktree', [], 4);
    const assigned = (scheduler: string) => {
      const modules = configuredSolverModules('direct', scheduler);
      return modules.M5.assign(modules.M3.ready(tasks), workers[1], workers)?.task.id;
    };
    expect(assigned('plan')).toBe('ready-goal');
    expect(assigned('critical-path')).toBe('bridge');
  });
});

describe('paired module evidence', () => {
  it('keeps missing attempts in acceptance differences and never invents missing costs', () => {
    const experiment = moduleExperimentSchema.parse(example());
    experiment.variants = experiment.variants.slice(0, 2);
    const base = (repetition: number, accepted: boolean, totalTokens: number | null, status = 'evaluated_failed') => ({
      arm: 'default', repetition, accepted, totalTokens, status, solveWallMs: 100,
    });
    const treatment = (repetition: number, accepted: boolean, totalTokens: number | null, status = 'evaluated_failed') => ({
      ...base(repetition, accepted, totalTokens, status), arm: 'essential-context', solveWallMs: 120,
    });
    const [paired] = moduleExperimentPairs(experiment, [
      base(1, true, 1000, 'evaluated_passed'),
      base(2, false, 200), treatment(2, true, 300, 'evaluated_passed'),
      base(3, true, null, 'evaluated_passed'), { ...treatment(3, false, 400), solveWallMs: null },
      base(4, false, null, 'invalid'), treatment(4, false, null, 'unfinished'),
    ]);
    expect(paired).toMatchObject({ plannedPairs: 4, observedPairs: 2, incompletePairs: 2, wins: 1, losses: 1,
      acceptanceRateDelta: -0.25, tokenPairs: 1, meanTokenDelta: 100, timePairs: 1, meanSolveWallDeltaMs: 20 });
    expect(paired.pairs[0]).toMatchObject({ complete: false, treatmentStatus: 'missing', tokenDelta: null, solveWallDeltaMs: null });
  });

  it('does not produce numerical savings from an unexecuted plan', async () => {
    const { directory, plan } = await prepare();
    const report = comparisonReport(directory, plan);
    expect(report.comparisonKind).toBe('module-plan');
    expect(report.totals).toHaveLength(4);
    for (const total of report.totals) expect(total).toMatchObject({ planned: 1, accepted: 0, missingTokenRuns: 1 });
    for (const pair of report.pairedComparisons!) expect(pair).toMatchObject({
      plannedPairs: 1, observedPairs: 0, incompletePairs: 1, tokenPairs: 0, meanTokenDelta: null,
    });
  });

  it('preserves cancellation, skipped launches and batch failures without shrinking planned pairs', async () => {
    const { directory, plan } = await prepare();
    fs.writeFileSync(path.join(directory, 'batch.json'), JSON.stringify({ interruptedBy: 'SIGINT', jobs: [
      { launch: plan.jobs[0].launch, status: 'cancelled', signal: 'SIGKILL', exitCode: null },
      { launch: plan.jobs[1].launch, status: 'skipped' },
      { launch: plan.jobs[2].launch, status: 'failed', error: 'spawn failed' },
    ] }));
    const report = comparisonReport(directory, plan);
    expect(report.runs[0]).toMatchObject({ status: 'missing', batchStatus: 'cancelled', signal: 'SIGKILL',
      batchError: null, accepted: false, totalTokens: null });
    expect(report.runs[1]).toMatchObject({ status: 'missing', batchStatus: 'skipped', signal: null,
      batchError: null, accepted: false, totalTokens: null });
    expect(report.runs[2]).toMatchObject({ batchStatus: 'failed', batchError: 'spawn failed' });
    expect(report.runs[3]).toMatchObject({ batchStatus: null, signal: null, batchError: null });
    for (const pair of report.pairedComparisons!) expect(pair).toMatchObject({
      plannedPairs: 1, observedPairs: 0, incompletePairs: 1, tokenPairs: 0, meanTokenDelta: null,
    });
  });
});

describe('frozen module comparison launches', () => {
  it.each([
    ['deepseek', 'deepseek-v4-pro', 'DEEPSEEK_API_KEY', 'https://api.deepseek.com', 'responses'],
    ['westlake', 'deepseek-flash', 'WESTLAKEHPC_API_KEY', 'https://hpc-api.westlake.edu.cn/v1', 'chat-completions'],
    ['sub2api', 'deepseek-flash', 'SUB2API_WESTLAKE_API_KEY', 'http://127.0.0.1:8080/v1', 'responses'],
  ])('prepares %s experiments without a key or model call and isolates every provider profile', async (provider, model, envKey, baseUrl, wireApi) => {
    vi.stubEnv(envKey, '');
    const run = vi.spyOn(batch, 'runMathBatch').mockResolvedValue(0);
    const { directory, plan } = await prepare(2, provider);
    expect(plan.configuration).toMatchObject({ provider, model, effort: provider === 'deepseek' ? 'high' : 'max' });
    expect(new Set(plan.jobs.map(job => job.codexProfile)).size).toBe(8);
    for (const job of plan.jobs) {
      expect(read(job.launch).codexHome).toBe(job.codexProfile);
      expect(job.codexProfileDigest).toMatch(/^[a-f0-9]{64}$/u);
      expect(fs.statSync(path.join(job.codexProfile, 'config.toml')).mode & 0o222).toBe(0);
    }
    expect(comparisonReport(directory, plan).provider).toMatchObject({
      id: provider, baseUrl, wireApi, apiKeyEnvironment: envKey,
    });
    expect(run).not.toHaveBeenCalled();
  });

  it.each(['config.toml', 'models.json'])('rejects a modified DeepSeek %s before launching a model', async name => {
    const { directory, plan } = await prepare(1, 'deepseek');
    const run = vi.spyOn(batch, 'runMathBatch').mockResolvedValue(0);
    const file = path.join(plan.jobs[0].codexProfile, name);
    fs.chmodSync(file, 0o600); fs.appendFileSync(file, '\n');
    await expect(compareMathRuns(['--phase', 'run', '--directory', directory])).rejects.toThrow('comparison_provider_profile_changed');
    expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ accepted: false, totalTokens: null });
    expect(run).not.toHaveBeenCalled();
  });

  it.each(['config.toml', 'models.json'])('rejects a modified Westlake %s before launching a model', async name => {
    const { directory, plan } = await prepare(1, 'westlake');
    const run = vi.spyOn(batch, 'runMathBatch').mockResolvedValue(0);
    const file = path.join(plan.jobs[0].codexProfile, name);
    fs.chmodSync(file, 0o600); fs.appendFileSync(file, '\n');
    await expect(compareMathRuns(['--phase', 'run', '--directory', directory])).rejects.toThrow('comparison_provider_profile_changed');
    expect(run).not.toHaveBeenCalled();
  });

  it('rejects a missing or changed DeepSeek profile identity in the frozen plan', async () => {
    const { directory, plan } = await prepare(1, 'deepseek');
    plan.jobs[0].codexProfileDigest = 'different-profile';
    expect(() => comparisonReport(directory, plan)).toThrow('comparison_provider_profile_identity_mismatch');
  });

  it('rejects changing the provider after preparation', async () => {
    await expect(compareMathRuns(['--phase', 'report', '--directory', '/unused', '--provider', 'deepseek']))
      .rejects.toThrow('provider is frozen during prepare');
  });

  it('prepares isolated fixed-budget cooperative attempts and freezes every module plan', async () => {
    const { directory, plan, bootstrap } = await prepare(2);
    expect(bootstrap).toHaveBeenCalledTimes(8);
    expect(new Set(plan.jobs.map((job: { methodDigest: string }) => job.methodDigest)).size).toBe(4);
    expect(plan.jobs.map((job: { arm: string }) => job.arm)).toEqual([
      'default', 'essential-context', 'critical-path', 'construction-rule',
      'essential-context', 'critical-path', 'construction-rule', 'default',
    ]);
    for (const job of plan.jobs) {
      const launch = read(job.launch), arg = (name: string) => launch.args[launch.args.indexOf(name) + 1];
      expect(arg('--coordination')).toBe('cooperative'); expect(arg('--workers')).toBe('4');
      expect(arg('--max-turns')).toBe('20'); expect(arg('--max-run-seconds')).toBe('600');
      expect(arg('--max-total-tokens')).toBe('30000'); expect(arg('--module-plan')).toBe(job.modulePlan);
      expect(arg('--task-file')).toBe(path.join(directory, 'task.md'));
      expect(job.modulePlanDigest).toBe(mathDigest(fs.readFileSync(job.modulePlan)));
      expect(fs.statSync(job.modulePlan).mode & 0o222).toBe(0);
    }
  });

  it('rejects modified module configuration before launching any model', async () => {
    const { directory, plan } = await prepare();
    const run = vi.spyOn(batch, 'runMathBatch').mockResolvedValue(0);
    const file = plan.jobs[0].modulePlan;
    fs.chmodSync(file, 0o600); fs.writeFileSync(file, JSON.stringify(plan.moduleExperiment.variants[1].plan));
    await expect(compareMathRuns(['--phase', 'run', '--directory', directory])).rejects.toThrow('comparison_module_plan_changed');
    expect(run).not.toHaveBeenCalled();
  });

  it.each([['--workers', '2'], ['--scheduler', 'continuation']])('rejects incompatible common option %s %s', async (flag, value) => {
    await expect(compareMathRuns(['--phase', 'prepare', '--directory', '/unused', flag, value,
      '--module-experiment', path.join(root, 'examples/components/module-experiment.json')])).rejects.toThrow('module experiments require');
  });

  it('rejects the removed lemma method when preparing a comparison', async () => {
    await expect(compareMathRuns(['--phase', 'prepare', '--directory', '/unused', '--method', 'lemma']))
      .rejects.toThrow('invalid method or scheduler');
  });

  it('rejects a dropped planned attempt instead of silently shrinking the denominator', async () => {
    const { directory, plan } = await prepare();
    plan.jobs.pop();
    expect(() => comparisonReport(directory, plan)).toThrow('comparison_module_plan_identity_mismatch');
  });

  it('rejects dropping an entire repetition instead of treating the smaller matrix as the original plan', async () => {
    const { directory, plan } = await prepare(2);
    plan.jobs = plan.jobs.filter((job: { repetition: number }) => job.repetition === 1);
    expect(() => comparisonReport(directory, plan)).toThrow('comparison_module_plan_identity_mismatch');
  });

  it('rejects changing a frozen suite during report or run', async () => {
    await expect(compareMathRuns(['--phase', 'report', '--directory', '/unused', '--module-experiment', '/unused.json']))
      .rejects.toThrow('frozen during prepare');
  });

  it.each([undefined, 'deepseek', 'westlake'])('requires runtime method and provider identity to match the experimental variant (%s)', async provider => {
    const { directory, plan } = await prepare(1, provider);
    const job = plan.jobs[0], runtime = job.output + '.runtime'; fs.mkdirSync(runtime);
    const state = { schema: 'deepscientist.math.solver.v1', runId: 'run',
      problem: { workspace: directory, receiptDigest: job.receiptDigest },
      taskDigest: plan.taskDigest, buildDigest: plan.buildDigest, environmentDigest: plan.environmentDigest,
      evaluatorDigest: mathDigest('host-default'), methodDigest: job.methodDigest, model: plan.configuration.model,
      ...(provider ? { providerProfile: fs.realpathSync(job.codexProfile), providerProfileDigest: job.codexProfileDigest } : {}),
      effort: plan.configuration.effort, workerCount: 4, coordination: 'cooperative', worktree: directory,
      phase: 'finished', turns: 1, workers: Array.from({ length: 4 }, (_, index) => ({
        id: `w${index}`, role: index === 0 ? 'lead' : 'researcher', phase: 'finished', worktree: directory, turns: 0,
      })), tokenBudget: buildTokenBudget(30000, []) };
    fs.writeFileSync(path.join(runtime, 'state.json'), JSON.stringify(state));
    fs.writeFileSync(job.output, JSON.stringify({ schema: 'deepscientist.math.run.v2', runId: 'run',
      stateFile: path.join(runtime, 'state.json'), status: 'limit_reached' }));
    expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ status: 'limit_reached', accepted: false });
    fs.writeFileSync(path.join(runtime, 'state.json'), JSON.stringify({ ...state, methodDigest: 'different-policy' }));
    expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ status: 'invalid', accepted: false });
    if (provider) {
      fs.writeFileSync(path.join(runtime, 'state.json'), JSON.stringify({ ...state, providerProfileDigest: undefined }));
      expect(comparisonReport(directory, plan).runs[0]).toMatchObject({ status: 'invalid', accepted: false,
        error: 'comparison_provider_identity_mismatch' });
    }
  });
});

describe('CLI module-plan boundary', () => {
  it('validates a plan before creating a run or connecting to a provider', async () => {
    const directory = temporary(), file = path.join(directory, 'module-plan.json');
    fs.writeFileSync(file, JSON.stringify({ ...example().variants[0].plan, context: 'none' }));
    await expect(runSolver(['--module-plan', file], root)).rejects.toThrow();
    expect(fs.readdirSync(directory)).toEqual(['module-plan.json']);
  });

  it('rejects a conflicting scheduler before reading a module plan', async () => {
    await expect(runSolver(['--module-plan', '/unused.json', '--scheduler', 'critical-path'], root)).rejects.toThrow('--module-plan requires');
  });

  it('rejects the removed lemma method', async () => {
    await expect(runSolver(['--module-plan', '/unused.json', '--method', 'lemma'], root)).rejects.toThrow('invalid --method');
  });
});
