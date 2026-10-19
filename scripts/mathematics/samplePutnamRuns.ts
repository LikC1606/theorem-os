#!/usr/bin/env bun
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { z } from 'zod';
import { parseFlags, required } from './arguments';
import { compareMathRuns, comparisonReport, comparisonTotals } from './compareMathRuns';
import { DEFAULT_PUTNAM_SAMPLE_SEED, PUTNAM_BENCH_REPOSITORY_URL, PUTNAM_BENCH_SOURCE_COMMIT,
  readPutnamBenchCatalog, samplePutnamBench } from '../../src/math/putnamBench';
import { canonicalMathJson, mathDigest, readMathJson, readMathText, writeMathJsonDurable } from '../../src/math/mathRuntimeIo';
import { assertMathCanonicalPath, isMathPathWithin } from '../../src/math/paths';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const hash = z.string().regex(/^[0-9a-f]{64}$/u);
const problemId = z.string().regex(/^putnam_[0-9]{4}_[ab][1-6]$/u);
const manifestSchema = z.object({
  schema: z.literal('theorem-os.putnambench-sample.v1'),
  repositoryUrl: z.literal(PUTNAM_BENCH_REPOSITORY_URL), sourceCommit: z.literal(PUTNAM_BENCH_SOURCE_COMMIT),
  selection: z.object({ algorithm: z.literal('sha256-seed-nul-id-v1'), seed: z.string().min(1).max(128),
    count: z.number().int().min(1).max(20), poolDigest: hash, eligibleCount: z.number().int().positive() }).strict(),
  environment: z.object({ toolchain: z.string().min(1), mathlibRevision: z.string().regex(/^[0-9a-f]{40}$/u),
    digest: hash }).strict(),
  excludedCounts: z.record(z.number().int().nonnegative()),
  configuration: z.record(z.unknown()), buildDigest: hash, runtimeEnvironmentDigest: hash,
  moduleExperimentDigest: hash,
  problems: z.array(z.object({ id: problemId, sourceRelativePath: z.string(), sourceSha256: hash,
    theoremNames: z.array(problemId).length(1),
    comparisonDirectory: z.string(), comparisonDigest: hash }).strict()).min(1).max(20),
}).strict();
const prepareOptions = ['repo', 'count', 'seed', 'build-manifest', 'module-experiment', 'provider', 'model', 'effort',
  'workers', 'repetitions', 'max-turns', 'max-run-seconds', 'max-turn-seconds', 'max-total-tokens', 'proof-environment-cache-dir'];
type ComparisonPlan = Parameters<typeof comparisonReport>[1];

export async function samplePutnamRuns(argv: string[]): Promise<number> {
  const flags = parseFlags(argv, ['phase', 'directory', ...prepareOptions]);
  if (flags.has('help')) {
    console.log('Usage: theorem-os sample-putnam --phase prepare|report --directory DIR\n'
      + 'prepare requires --repo PUTNAM_REPO --build-manifest FILE; defaults to 3 proof-only problems, a fixed sampling seed, '
      + 'Westlake deepseek-flash/high and the four module plans.\n'
      + '--count 1..20 --seed TEXT customize the reproducible sample. Budgets apply per problem and variant.\n'
      + 'Both phases are offline and never call a model. Individual comparison.json files retain the explicit run entry.');
    return 0;
  }
  const phase = required(flags, 'phase');
  if (!['prepare', 'report'].includes(phase)) throw new Error('sample-putnam supports only --phase prepare or report');
  const directory = path.resolve(required(flags, 'directory'));
  assertMathCanonicalPath(directory);
  if (isMathPathWithin(root, directory)) throw new Error('Keep PutnamBench experiments outside the source checkout.');
  const sampleFile = path.join(directory, 'sample.json');
  if (phase === 'prepare') {
    if (fs.existsSync(directory)) throw new Error('PutnamBench sample directory already exists; use a new directory.');
    const count = Number(flags.get('count') ?? 3), seed = flags.get('seed') ?? DEFAULT_PUTNAM_SAMPLE_SEED;
    if (!Number.isSafeInteger(count) || count < 1 || count > 20) throw new Error('invalid --count (expected 1..20)');
    if (!seed.trim() || seed.length > 128) throw new Error('invalid --seed');
    const repository = fs.realpathSync(required(flags, 'repo'));
    if (isMathPathWithin(repository, directory)) throw new Error('Keep PutnamBench experiments outside the dataset checkout.');
    const catalog = readPutnamBenchCatalog(repository);
    const selection = samplePutnamBench(catalog, count, seed);
    const manifest = fs.realpathSync(required(flags, 'build-manifest'));
    const moduleFile = path.resolve(flags.get('module-experiment') ?? path.join(root, 'examples/components/module-experiment.json'));
    const taskFile = path.join(root, 'examples/putnambench/experiment-task.md');
    const defaults: Record<string, string> = { provider: 'westlake', workers: '4', repetitions: '1',
      'max-turns': '20', 'max-run-seconds': '600', 'max-turn-seconds': '180', 'max-total-tokens': '30000' };
    const forwarded = ['provider', 'model', 'effort', 'workers', 'repetitions', 'max-turns', 'max-run-seconds',
      'max-turn-seconds', 'max-total-tokens', 'proof-environment-cache-dir'].flatMap(key => {
      const value = flags.get(key) ?? defaults[key];
      return value === undefined ? [] : [`--${key}`, value];
    });
    fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
    const plans: ComparisonPlan[] = [];
    const problems = [];
    for (const problem of selection.problems) {
      const comparisonDirectory = path.join(directory, problem.id);
      await compareMathRuns(['--phase', 'prepare', '--dataset', 'putnambench', '--repo', repository,
        '--problem', problem.id, '--directory', comparisonDirectory, '--build-manifest', manifest,
        '--module-experiment', moduleFile, '--task-file', taskFile, ...forwarded]);
      const planFile = path.join(comparisonDirectory, 'comparison.json');
      const planText = readMathText(planFile);
      plans.push(JSON.parse(planText) as ComparisonPlan);
      problems.push({ id: problem.id, sourceRelativePath: problem.sourceRelativePath,
        sourceSha256: problem.sourceSha256, theoremNames: problem.theoremNames,
        comparisonDirectory,
        comparisonDigest: mathDigest(planText) });
    }
    const first = plans[0];
    const value = manifestSchema.parse({ schema: 'theorem-os.putnambench-sample.v1',
      repositoryUrl: PUTNAM_BENCH_REPOSITORY_URL, sourceCommit: PUTNAM_BENCH_SOURCE_COMMIT,
      selection: { algorithm: selection.algorithm, seed: selection.seed, count: selection.count,
        poolDigest: selection.poolDigest, eligibleCount: selection.eligibleCount },
      environment: { toolchain: catalog.toolchain, mathlibRevision: catalog.mathlibRevision, digest: catalog.environmentDigest },
      excludedCounts: catalog.excludedCounts, configuration: first.configuration,
      buildDigest: first.buildDigest, runtimeEnvironmentDigest: first.environmentDigest,
      moduleExperimentDigest: mathDigest(canonicalMathJson(first.moduleExperiment)), problems });
    writeMathJsonDurable(sampleFile, value);
    fs.chmodSync(sampleFile, 0o400);
    console.log(JSON.stringify({ sampleFile, problems: problems.map(problem => problem.id),
      jobs: plans.reduce((sum, plan) => sum + plan.jobs.length, 0), status: 'prepared', invokesModel: false }));
    return 0;
  }
  if (prepareOptions.some(key => flags.has(key))) throw new Error('Sample options are frozen; report only accepts --directory.');
  const sample = manifestSchema.parse(readMathJson(sampleFile));
  if (sample.selection.count !== sample.problems.length || sample.selection.eligibleCount < sample.selection.count ||
      new Set(sample.problems.map(problem => problem.id)).size !== sample.problems.length)
    throw new Error('putnam_sample_identity_mismatch');
  const reports = sample.problems.map(problem => {
    const comparisonDirectory = path.join(directory, problem.id);
    if (problem.comparisonDirectory !== comparisonDirectory || problem.sourceRelativePath !== `lean4/src/${problem.id}.lean` ||
        problem.theoremNames[0] !== problem.id)
      throw new Error('putnam_sample_identity_mismatch');
    const planFile = path.join(comparisonDirectory, 'comparison.json');
    assertMathCanonicalPath(planFile);
    const planText = readMathText(planFile);
    if (mathDigest(planText) !== problem.comparisonDigest) throw new Error('putnam_sample_plan_changed');
    const plan = JSON.parse(planText) as ComparisonPlan;
    if (plan.dataset !== 'putnambench' || plan.problem !== problem.id || plan.sourceCommit !== sample.sourceCommit ||
        plan.sourceProblem?.sourceSha256 !== problem.sourceSha256 ||
        plan.sourceProblem.toolchain !== sample.environment.toolchain ||
        plan.sourceProblem.mathlibRevision !== sample.environment.mathlibRevision ||
        plan.sourceProblem.environmentDigest !== sample.environment.digest ||
        canonicalMathJson(plan.configuration) !== canonicalMathJson(sample.configuration) ||
        plan.buildDigest !== sample.buildDigest || plan.environmentDigest !== sample.runtimeEnvironmentDigest ||
        mathDigest(canonicalMathJson(plan.moduleExperiment)) !== sample.moduleExperimentDigest)
      throw new Error('putnam_sample_identity_mismatch');
    const report = comparisonReport(comparisonDirectory, plan);
    const reportFile = path.join(comparisonDirectory, 'report.json');
    writeMathJsonDurable(reportFile, report);
    return { problem: problem.id, reportFile, report };
  });
  // Pair strategies only inside a problem; repetitions from different problems are not interchangeable.
  const runs = reports.flatMap(({ problem, report }) => report.runs.map(run => ({ problem, ...run })));
  const names = reports[0].report.totals.map(total => total.arm);
  const reportFile = path.join(directory, 'report.json');
  writeMathJsonDurable(reportFile, { schema: 'theorem-os.putnambench-sample-report.v1',
    official: false, evidence: 'recorded-not-replayed', selection: sample.selection,
    repositoryUrl: sample.repositoryUrl, sourceCommit: sample.sourceCommit,
    environment: sample.environment, configuration: sample.configuration,
    totals: comparisonTotals(runs, names), problems: reports, runs });
  console.log(JSON.stringify({ reportFile, problems: reports.length, plannedRuns: runs.length,
    missingResults: runs.filter(run => run.status === 'missing').length, invokesModel: false }));
  return 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  samplePutnamRuns(process.argv.slice(2)).then(code => { process.exitCode = code; }).catch(error => {
    console.error(error instanceof Error ? error.message : String(error)); process.exitCode = 1;
  });
}
