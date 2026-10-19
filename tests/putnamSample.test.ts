import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { compareMathRuns, comparisonReport } from '../scripts/mathematics/compareMathRuns';
import { samplePutnamRuns } from '../scripts/mathematics/samplePutnamRuns';
import * as batch from '../scripts/mathematics/runMathBatch';
import * as putnam from '../src/math/putnamBench';
import * as imoAdapter from '../src/math/imo2026Adapter';
import * as buildManifest from '../src/math/mathBuildManifest';
import * as solverProblem from '../src/solver/problem';
import * as inspection from '../src/solver/inspection';
import { bootstrapLeanTask } from '../src/math/leanTask';
import { getLeanTaskEnvironment } from '../src/math/leanTaskEnvironment';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { buildTokenBudget } from '../src/solver/usageBudget';

type Plan = Parameters<typeof comparisonReport>[1];
type Sample = {
  selection: { count: number; seed: string; poolDigest: string; eligibleCount: number };
  problems: { id: string; sourceSha256: string; theoremNames: string[]; comparisonDirectory: string; comparisonDigest: string }[];
  [key: string]: unknown;
};
const directories: string[] = [];
const temporary = () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-putnam-sample-'));
  directories.push(directory);
  return directory;
};
const read = <T = Record<string, any>>(file: string): T => JSON.parse(fs.readFileSync(file, 'utf8'));
const rewrite = (file: string, value: unknown) => {
  fs.chmodSync(file, 0o600);
  fs.writeFileSync(file, JSON.stringify(value));
};
const argument = (args: string[], name: string) => args[args.indexOf(name) + 1];

afterEach(() => {
  vi.restoreAllMocks();
  vi.unstubAllEnvs();
  vi.unstubAllGlobals();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

function fixture(realReceipts = false) {
  const directory = temporary(), repository = path.join(directory, 'repo');
  fs.mkdirSync(repository);
  const manifest = path.join(directory, 'build.json'), task = path.join(directory, 'task.md');
  fs.writeFileSync(manifest, '{}');
  fs.writeFileSync(task, 'Prove every original target without changing its statement.');
  const environment = getLeanTaskEnvironment('mathlib');
  const problems = ['putnam_1962_a1', 'putnam_1987_b2', 'putnam_2001_a3', 'putnam_2019_b4', 'putnam_2024_a5'].map((id, index) => {
    const source = `import Mathlib\n\ntheorem ${id} (n : Nat) : n + ${index} = n + ${index} := by\n  sorry\n`;
    return { id, source, sourceRelativePath: `lean4/src/${id}.lean`, sourceSha256: mathDigest(source),
      theoremNames: [id] };
  });
  const catalog = {
    repositoryUrl: putnam.PUTNAM_BENCH_REPOSITORY_URL, sourceCommit: putnam.PUTNAM_BENCH_SOURCE_COMMIT,
    toolchain: environment.toolchain, mathlibRevision: environment.mathlibRevision!, environmentDigest: environment.dependencyDigest,
    problems, excluded: [], excludedCounts: {},
  };
  const readCatalog = vi.spyOn(putnam, 'readPutnamBenchCatalog').mockReturnValue(catalog);
  const readProblem = vi.spyOn(putnam, 'readPutnamBenchProblem').mockImplementation((_repository, id) => {
    const problem = problems.find(problem => problem.id === id);
    if (!problem) throw new Error('unknown_fixture_problem');
    return problem;
  });
  const bootstrap = vi.spyOn(putnam, 'bootstrapPutnamBenchProblem').mockImplementation(input => {
    const problem = problems.find(problem => problem.id === input.problemId)!;
    if (realReceipts) return bootstrapLeanTask(input.workspaceRoot, {
      source: problem.source, task: 'Prove the original Putnam target.', environment: 'mathlib',
    });
    fs.mkdirSync(input.workspaceRoot, { recursive: true });
    return {} as never;
  });
  if (!realReceipts) vi.spyOn(solverProblem, 'readSolverProblem').mockImplementation(workspace => ({
    receiptDigest: mathDigest(workspace),
  }) as never);
  vi.spyOn(buildManifest, 'readMathBuildManifest').mockReturnValue({} as never);
  const runBatch = vi.spyOn(batch, 'runMathBatch').mockResolvedValue(0);
  const fetch = vi.fn(() => { throw new Error('unexpected_network_in_offline_preparation'); });
  vi.stubGlobal('fetch', fetch);
  vi.stubEnv('WESTLAKEHPC_API_KEY', '');
  const log = vi.spyOn(console, 'log').mockImplementation(() => {});
  return { directory, repository, manifest, task, catalog, problems, bootstrap, readCatalog, readProblem, runBatch, fetch, log };
}

async function prepare(options: { realReceipts?: boolean; flags?: string[] } = {}) {
  const context = fixture(options.realReceipts), output = path.join(context.directory, 'sample');
  await samplePutnamRuns(['--phase', 'prepare', '--directory', output, '--repo', context.repository,
    '--build-manifest', context.manifest, ...(options.flags ?? [])]);
  const sampleFile = path.join(output, 'sample.json'), sample = read<Sample>(sampleFile);
  const plans = sample.problems.map(problem => read<Plan>(path.join(problem.comparisonDirectory, 'comparison.json')));
  return { ...context, output, sampleFile, sample, plans };
}

function recordedRun(plan: Plan, job: Plan['jobs'][number], source: string, totalTokens: number) {
  const workers = Array.from({ length: plan.configuration.workers }, (_, index) => ({
    id: `worker-${index}`, role: index === 0 ? 'lead' : 'researcher', phase: 'finished', worktree: path.dirname(job.output),
    turns: 1, usage: { totalTokens: totalTokens / plan.configuration.workers },
    usageAccounting: { startedTurns: 1, reportedTurns: 1, pending: false, incomplete: false },
  }));
  return {
    state: {
      schema: 'deepscientist.math.solver.v1', runId: job.output,
      problem: { kind: 'lean-task', receiptDigest: job.receiptDigest, contract: { formalStatement: source }, targets: [] },
      taskDigest: plan.taskDigest, buildDigest: plan.buildDigest, environmentDigest: plan.environmentDigest,
      evaluatorDigest: mathDigest('host-default'), methodDigest: job.methodDigest,
      providerProfile: fs.realpathSync(job.codexProfile!), providerProfileDigest: job.codexProfileDigest,
      model: plan.configuration.model, effort: plan.configuration.effort, workerCount: plan.configuration.workers,
      coordination: 'cooperative', worktree: path.dirname(job.output), phase: 'finished', turns: workers.length, workers,
      solveStartedAt: 100, solveFinishedAt: 200 + totalTokens,
      tokenBudget: buildTokenBudget(plan.configuration.maxTotalTokens!, workers as never),
    },
    result: { status: 'limit_reached' },
  };
}

describe('offline PutnamBench module samples', () => {
  it('prepares three proof identities and twelve isolated Westlake attempts without a model or network', async () => {
    const context = await prepare({ realReceipts: true });
    const { sample, plans, bootstrap, readProblem, output } = context;
    expect(sample.selection).toMatchObject({ count: 3, seed: putnam.DEFAULT_PUTNAM_SAMPLE_SEED, eligibleCount: 5 });
    expect(sample.selection.poolDigest).toMatch(/^[a-f0-9]{64}$/u);
    expect(sample.problems).toHaveLength(3);
    expect(new Set(sample.problems.map(problem => problem.id)).size).toBe(3);
    expect(bootstrap).toHaveBeenCalledTimes(12);
    expect(readProblem).toHaveBeenCalledTimes(3);
    const jobs = plans.flatMap(plan => plan.jobs);
    for (const key of ['launch', 'output', 'codexProfile', 'modulePlan'] as const)
      expect(new Set(jobs.map(job => job[key])).size).toBe(12);
    expect(fs.statSync(context.sampleFile).mode & 0o222).toBe(0);
    for (const [index, plan] of plans.entries()) {
      const selected = sample.problems[index], source = context.problems.find(problem => problem.id === selected.id)!;
      expect(plan).toMatchObject({ dataset: 'putnambench', problem: selected.id, sourceCommit: putnam.PUTNAM_BENCH_SOURCE_COMMIT,
        sourceProblem: { sourceRelativePath: source.sourceRelativePath, sourceSha256: source.sourceSha256 },
        configuration: { provider: 'westlake', model: 'deepseek-flash', effort: 'high', workers: 4, repetitions: 1,
          maxTurns: 20, maxRunSeconds: 600, maxTurnSeconds: 180, maxTotalTokens: 30000 } });
      expect(mathDigest(fs.readFileSync(path.join(selected.comparisonDirectory, 'comparison.json')))).toBe(selected.comparisonDigest);
      expect(plan.jobs.map(job => job.arm)).toEqual(['default', 'essential-context', 'critical-path', 'construction-rule']);
      expect(new Set(plan.jobs.map(job => job.methodDigest)).size).toBe(4);
      for (const job of plan.jobs) {
        const launch = read(job.launch), workspace = argument(launch.args, '--workspace');
        expect(job.launch.startsWith(path.join(output, selected.id) + path.sep)).toBe(true);
        expect(launch.codexHome).toBe(job.codexProfile);
        expect(argument(launch.args, '--workers')).toBe('4');
        expect(argument(launch.args, '--coordination')).toBe('cooperative');
        expect(argument(launch.args, '--model')).toBe('deepseek-flash');
        expect(argument(launch.args, '--effort')).toBe('high');
        expect(argument(launch.args, '--max-total-tokens')).toBe('30000');
        expect(argument(launch.args, '--module-plan')).toBe(job.modulePlan);
        expect(mathDigest(fs.readFileSync(job.modulePlan!))).toBe(job.modulePlanDigest);
        expect(fs.statSync(path.join(job.codexProfile!, 'config.toml')).mode & 0o222).toBe(0);
        expect(fs.readFileSync(path.join(workspace, 'generated/problem/Submission.lean'), 'utf8')).toBe(source.source);
        const receipt = solverProblem.readSolverProblem(workspace, path.join(workspace, 'active-problem.json'));
        expect(receipt.kind).toBe('lean-task');
        expect(receipt.receiptDigest).toBe(job.receiptDigest);
        expect(mathDigest(receipt.contract.formalStatement)).toBe(selected.sourceSha256);
        expect(fs.existsSync(job.output)).toBe(false);
      }
    }
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
    expect(JSON.parse(String(context.log.mock.calls.at(-1)![0]))).toMatchObject({
      jobs: 12, status: 'prepared', invokesModel: false,
    });
  });

  it('reports all twelve missing attempts and preserves null costs and each problem\'s planned pairs', async () => {
    const context = await prepare();
    context.readCatalog.mockClear(); context.readProblem.mockClear(); context.bootstrap.mockClear();
    expect(await samplePutnamRuns(['--phase', 'report', '--directory', context.output])).toBe(0);
    const report = read(path.join(context.output, 'report.json'));
    expect(report).toMatchObject({ official: false, evidence: 'recorded-not-replayed' });
    expect(report.runs).toHaveLength(12);
    expect(new Set(report.runs.map(run => run.problem)).size).toBe(3);
    for (const run of report.runs) expect(run).toMatchObject({ status: 'missing', accepted: false, totalTokens: null, solveWallMs: null });
    for (const total of report.totals) expect(total).toMatchObject({ planned: 3, accepted: 0, missingTokenRuns: 3 });
    expect(report.pairedComparisons).toBeUndefined();
    for (const problem of report.problems) {
      expect(problem.report.problem).toBe(problem.problem);
      expect(problem.report.pairedComparisons).toHaveLength(3);
      for (const pair of problem.report.pairedComparisons) expect(pair).toMatchObject({
        plannedPairs: 1, observedPairs: 0, incompletePairs: 1, tokenPairs: 0, meanTokenDelta: null,
        timePairs: 0, meanSolveWallDeltaMs: null,
      });
    }
    expect(context.readCatalog).not.toHaveBeenCalled();
    expect(context.readProblem).not.toHaveBeenCalled();
    expect(context.bootstrap).not.toHaveBeenCalled();
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it('pairs matching arms only within a problem even when other problems reuse repetition one', async () => {
    const context = await prepare();
    const recorded = new Map<string, ReturnType<typeof recordedRun>>();
    for (const [index, plan] of context.plans.entries()) {
      const source = context.problems.find(problem => problem.id === plan.problem)!.source;
      const jobs = index === 0 ? [plan.jobs[0]] : index === 1 ? [plan.jobs[1]] : plan.jobs.slice(0, 2);
      for (const job of jobs) {
        fs.writeFileSync(job.output, '{}');
        recorded.set(job.output, recordedRun(plan, job, source, job.arm === 'default' ? 100 : 200));
      }
    }
    vi.spyOn(inspection, 'readRunInspection').mockImplementation(file => {
      const result = recorded.get(file);
      if (!result) throw new Error('missing_fixture_result');
      return result as never;
    });
    await samplePutnamRuns(['--phase', 'report', '--directory', context.output]);
    const report = read(path.join(context.output, 'report.json'));
    expect(report.runs.filter(run => run.totalTokens !== null)).toHaveLength(4);
    for (const item of report.problems.slice(0, 2)) expect(item.report.pairedComparisons[0]).toMatchObject({
      plannedPairs: 1, observedPairs: 0, incompletePairs: 1, tokenPairs: 0, meanTokenDelta: null,
    });
    expect(report.problems[2].report.pairedComparisons[0]).toMatchObject({
      plannedPairs: 1, observedPairs: 1, incompletePairs: 0, tokenPairs: 1, meanTokenDelta: 100,
    });
    expect(report.pairedComparisons).toBeUndefined();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it.each(['source', 'count', 'eligible-count', 'target', 'directory'])('rejects a modified sample %s identity', async field => {
    const context = await prepare();
    if (field === 'source') context.sample.problems[0].sourceSha256 = mathDigest('different source');
    if (field === 'count') context.sample.selection.count = 2;
    if (field === 'eligible-count') context.sample.selection.eligibleCount = 2;
    if (field === 'target') context.sample.problems[0].theoremNames = [context.sample.problems[1].id];
    if (field === 'directory') context.sample.problems[0].comparisonDirectory = context.sample.problems[1].comparisonDirectory;
    rewrite(context.sampleFile, context.sample);
    await expect(samplePutnamRuns(['--phase', 'report', '--directory', context.output])).rejects.toThrow('putnam_sample_identity_mismatch');
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it('rejects changed child plan bytes before reading run results', async () => {
    const context = await prepare(), problem = context.sample.problems[0];
    fs.appendFileSync(path.join(problem.comparisonDirectory, 'comparison.json'), '\n');
    const inspect = vi.spyOn(inspection, 'readRunInspection');
    await expect(samplePutnamRuns(['--phase', 'report', '--directory', context.output])).rejects.toThrow('putnam_sample_plan_changed');
    expect(inspect).not.toHaveBeenCalled();
  });

  it('rejects a child source change even if its summary digest is updated', async () => {
    const context = await prepare(), problem = context.sample.problems[0], plan = context.plans[0];
    const file = path.join(problem.comparisonDirectory, 'comparison.json');
    plan.sourceProblem!.sourceSha256 = mathDigest('different source');
    rewrite(file, plan);
    problem.comparisonDigest = mathDigest(fs.readFileSync(file));
    rewrite(context.sampleFile, context.sample);
    await expect(samplePutnamRuns(['--phase', 'report', '--directory', context.output])).rejects.toThrow('putnam_sample_identity_mismatch');
  });

  it('rejects replacing a child directory with a symbolic link', async () => {
    const context = await prepare(), original = context.sample.problems[0].comparisonDirectory;
    const replacement = path.join(context.directory, 'replaced-problem');
    fs.renameSync(original, replacement); fs.symlinkSync(replacement, original, 'dir');
    await expect(samplePutnamRuns(['--phase', 'report', '--directory', context.output])).rejects.toThrow('math_path_invalid');
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it.each([['--seed', 'new-seed'], ['--count', '1'], ['--provider', 'profile']])('freezes sample option %s during report', async (flag, value) => {
    const directory = temporary();
    await expect(samplePutnamRuns(['--phase', 'report', '--directory', directory, flag, value]))
      .rejects.toThrow('Sample options are frozen');
  });
});

describe('PutnamBench single-problem comparison entry', () => {
  it('rejects an unsupported dataset before preparing a problem', async () => {
    const context = fixture();
    await expect(compareMathRuns(['--phase', 'prepare', '--directory', path.join(context.directory, 'comparison'),
      '--repo', context.repository, '--problem', context.problems[0].id, '--dataset', 'unknown']))
      .rejects.toThrow('invalid --dataset');
    expect(context.readProblem).not.toHaveBeenCalled();
    expect(context.bootstrap).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it.each(['run', 'report'])('rejects changing the dataset during %s', async phase => {
    const directory = temporary();
    await expect(compareMathRuns(['--phase', phase, '--directory', directory, '--dataset', 'imo2026']))
      .rejects.toThrow('--dataset is frozen during prepare');
  });

  it.each([
    [undefined, 'comparison_dataset_invalid'],
    ['imo2026', 'comparison_imo_source_identity_mismatch'],
  ] as const)('rejects a Putnam plan relabeled as %s before reporting or launching', async (dataset, error) => {
    const context = await prepare(), plan = context.plans[0];
    const directory = context.sample.problems[0].comparisonDirectory;
    plan.dataset = dataset;
    rewrite(path.join(directory, 'comparison.json'), plan);
    expect(() => comparisonReport(directory, plan)).toThrow(error);
    await expect(compareMathRuns(['--phase', 'run', '--directory', directory])).rejects.toThrow(error);
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it.each(['receipt', 'kind', 'source'])('rechecks every Putnam workspace and rejects a changed %s before launching', async field => {
    const context = await prepare({ realReceipts: true }), plan = context.plans[0];
    const lastWorkspace = path.join(path.dirname(plan.jobs.at(-1)!.launch), 'workspace');
    const readOriginal = solverProblem.readSolverProblem;
    const readReceipt = vi.spyOn(solverProblem, 'readSolverProblem').mockImplementation((workspace, file) => {
      const receipt = readOriginal(workspace, file);
      if (workspace !== lastWorkspace) return receipt;
      if (field === 'receipt') return { ...receipt, receiptDigest: mathDigest('a different valid receipt') };
      if (field === 'kind') return { ...receipt, kind: 'imo2026' } as never;
      return { ...receipt, contract: { ...receipt.contract, formalStatement: 'a different formal statement' } };
    });
    await expect(compareMathRuns(['--phase', 'run', '--directory', context.sample.problems[0].comparisonDirectory]))
      .rejects.toThrow('comparison_putnam_source_identity_mismatch');
    expect(readReceipt).toHaveBeenCalledTimes(4);
    expect(readReceipt).toHaveBeenLastCalledWith(lastWorkspace, path.join(lastWorkspace, 'active-problem.json'));
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
  });

  it.each([false, true])('retains the original IMO comparison entry (explicit dataset: %s)', async explicit => {
    const context = fixture(), directory = path.join(context.directory, 'comparison');
    const bootstrap = vi.spyOn(imoAdapter, 'bootstrapImo2026Problem').mockResolvedValue({} as never);
    await compareMathRuns(['--phase', 'prepare', '--directory', directory, '--repo', context.repository,
      '--problem', imoAdapter.IMO2026_SUPPORTED_PROBLEMS[0], '--task-file', context.task, '--build-manifest', context.manifest,
      ...(explicit ? ['--dataset', 'imo2026'] : [])]);
    const plan = read<Plan>(path.join(directory, 'comparison.json'));
    expect(plan).toMatchObject({ dataset: 'imo2026', sourceCommit: imoAdapter.IMO2026_SOURCE_COMMIT });
    expect(plan.sourceProblem).toBeUndefined();
    expect(plan.jobs.map(job => job.arm)).toEqual(['single', 'independent', 'cooperative']);
    expect(bootstrap).toHaveBeenCalledTimes(3);
    expect(context.readProblem).not.toHaveBeenCalled();
    expect(context.bootstrap).not.toHaveBeenCalled();
    expect(context.runBatch).not.toHaveBeenCalled();
    expect(context.fetch).not.toHaveBeenCalled();
    delete plan.dataset;
    expect(() => comparisonReport(directory, plan)).not.toThrow();
  });

  it('rejects runtime evidence from another Putnam source instead of accepting a matching arm', async () => {
    const context = await prepare(), plan = context.plans[0], job = plan.jobs[0];
    fs.writeFileSync(job.output, '{}');
    vi.spyOn(inspection, 'readRunInspection').mockReturnValue(recordedRun(plan, job, 'different formal statement', 100) as never);
    expect(comparisonReport(context.sample.problems[0].comparisonDirectory, plan).runs[0]).toMatchObject({
      status: 'invalid', accepted: false, totalTokens: null, error: 'comparison_putnam_source_identity_mismatch',
    });
  });
});
