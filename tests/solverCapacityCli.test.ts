import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { runSolver } from '../src/solver/run';
import { configurableSolverModules } from '../src/solver/modules/custom';
import { defaultResearchModulePlan } from '../src/solver/modules/policy';
import { MAX_RESEARCH_WORKERS } from '../src/solver/modules/organization';
import { compareMathRuns, comparisonReport } from '../scripts/mathematics/compareMathRuns';
import { describeModuleExperiment, moduleExperimentSchema } from '../scripts/mathematics/moduleExperiment';
import * as buildManifest from '../src/math/mathBuildManifest';
import * as imoAdapter from '../src/math/imo2026Adapter';
import * as solverProblem from '../src/solver/problem';

const root = fileURLToPath(new URL('..', import.meta.url));
const directories: string[] = [];
const temporary = () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'math-capacity-cli-'));
  directories.push(directory);
  return directory;
};
const read = (file: string) => JSON.parse(fs.readFileSync(file, 'utf8'));
const experimentFile = path.join(root, 'examples/components/module-experiment.json');

afterEach(() => {
  vi.restoreAllMocks();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

describe('CLI worker capacity', () => {
  it.each([1, 4, 8])('accepts %i workers at both CLI and module-plan boundaries', async workers => {
    expect(() => configurableSolverModules(defaultResearchModulePlan(), 'cooperative', workers)).not.toThrow();
    await expect(runSolver(['--workers', String(workers)], root)).rejects.toThrow('--workspace is required');
  });

  it.each(['0', '-1', '9', '1.5', 'NaN', '9007199254740992'])('rejects invalid worker count %s before accessing a workspace', async workers => {
    await expect(runSolver([`--workers=${workers}`], root)).rejects.toThrow('invalid --workers');
    expect(() => configurableSolverModules(defaultResearchModulePlan(), 'cooperative', Number(workers)))
      .toThrow('math_module_invalid_workers');
  });

  it('allows the expanded module experiment and retains distinct effective variants', () => {
    const experiment = moduleExperimentSchema.parse(read(experimentFile));
    const variants = describeModuleExperiment(experiment, MAX_RESEARCH_WORKERS);
    expect(variants).toHaveLength(experiment.variants.length);
    expect(new Set(variants.map(variant => variant.methodDigest)).size).toBe(variants.length);
    expect(() => describeModuleExperiment(experiment, MAX_RESEARCH_WORKERS + 1)).toThrow('math_module_invalid_workers');
  });

  it('documents the shared capacity in the CLI and example help', async () => {
    const log = vi.spyOn(console, 'log').mockImplementation(() => {});
    expect(await runSolver(['--help'], root)).toBe(0);
    expect(log).toHaveBeenCalledWith(expect.stringContaining('--workers 1..8'));
    const help = spawnSync('bun', ['scripts/mathematics/runExample.ts', '--help'],
      { cwd: root, encoding: 'utf8', timeout: 10_000 });
    expect(help.status, help.stderr).toBe(0);
    expect(help.stdout).toContain('--workers 1..8');
  });

  it.each([8, 9])('validates the example argument and saved configuration for %i workers', workers => {
    const directory = temporary();
    fs.writeFileSync(path.join(directory, 'case.json'), JSON.stringify({ schema: 'theorem-os.example-case.v1',
      mode: 'model', workers, model: 'fixture', effort: 'max', buildManifestRef: path.join(directory, 'absent-build.json') }));
    // A missing workspace stops the accepted case before any build, tool or provider access.
    const result = spawnSync('bun', ['scripts/mathematics/runExample.ts', 'check', '--dir', directory, '--workers', String(workers)],
      { cwd: root, encoding: 'utf8', timeout: 10_000 });
    expect(result.status).toBe(1);
    if (workers === 8) {
      expect(result.stderr).toContain(path.join(directory, 'workspace'));
      expect(result.stderr).not.toContain('Invalid example case');
    } else expect(result.stderr).toContain('--workers must be an integer from 1 to 8');
    expect(fs.readdirSync(directory)).toEqual(['case.json']);
  });

  it('rejects an out-of-range saved example configuration when the CLI count is omitted', () => {
    const directory = temporary();
    fs.writeFileSync(path.join(directory, 'case.json'), JSON.stringify({ schema: 'theorem-os.example-case.v1',
      mode: 'model', workers: 9, model: 'fixture', effort: 'max', buildManifestRef: 'unused' }));
    const result = spawnSync('bun', ['scripts/mathematics/runExample.ts', 'check', '--dir', directory],
      { cwd: root, encoding: 'utf8', timeout: 10_000 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('Invalid example case');
    expect(fs.readdirSync(directory)).toEqual(['case.json']);
  });
});

describe('comparison capacity and frozen launches', () => {
  it.each([undefined, 8])('prepares and reports module experiments with %s workers without model calls', async workers => {
    const directory = temporary(), repository = path.join(directory, 'repo');
    fs.mkdirSync(repository);
    const task = path.join(directory, 'task.md'), manifest = path.join(directory, 'build.json');
    fs.writeFileSync(task, 'Prove every original target.'); fs.writeFileSync(manifest, '{}');
    vi.spyOn(buildManifest, 'readMathBuildManifest').mockReturnValue({} as never);
    const bootstrap = vi.spyOn(imoAdapter, 'bootstrapImo2026Problem').mockResolvedValue({} as never);
    vi.spyOn(solverProblem, 'readSolverProblem').mockReturnValue({ receiptDigest: 'fixture-receipt' } as never);
    vi.spyOn(console, 'log').mockImplementation(() => {});
    const output = path.join(directory, 'comparison');
    expect(await compareMathRuns(['--phase', 'prepare', '--directory', output, '--repo', repository,
      '--problem', imoAdapter.IMO2026_SUPPORTED_PROBLEMS[0], '--task-file', task, '--build-manifest', manifest,
      '--module-experiment', experimentFile, '--max-turns', '0', '--max-run-seconds', '0', '--max-turn-seconds', '0',
      '--max-total-tokens', '0', '--evaluator-timeout-seconds', '0', ...(workers ? ['--workers', String(workers)] : [])])).toBe(0);
    const plan = read(path.join(output, 'comparison.json'));
    expect(plan.configuration).toMatchObject({ workers: workers ?? 4, maxTurns: 0, maxRunSeconds: 0,
      maxTurnSeconds: 0, maxTotalTokens: 0, evaluatorTimeoutSeconds: 0 });
    expect(bootstrap).toHaveBeenCalledTimes(plan.jobs.length);
    for (const job of plan.jobs) {
      const launch = read(job.launch);
      expect(launch.args[launch.args.indexOf('--workers') + 1]).toBe(String(workers ?? 4));
      for (const name of ['max-turns', 'max-run-seconds', 'max-turn-seconds', 'max-total-tokens', 'evaluator-timeout-seconds'])
        expect(launch.args[launch.args.indexOf(`--${name}`) + 1]).toBe('0');
    }
    const report = comparisonReport(output, plan);
    expect(report.runs).toHaveLength(plan.jobs.length);
    expect(report.runs.every(run => run.status === 'missing')).toBe(true);
  });

  it.each(['1', '9'])('rejects out-of-range comparison capacity %s before preparing sources', async workers => {
    await expect(compareMathRuns(['--phase', 'prepare', '--directory', '/unused-comparison', '--workers', workers]))
      .rejects.toThrow('--workers must be an integer from 2 to 8');
  });
});
