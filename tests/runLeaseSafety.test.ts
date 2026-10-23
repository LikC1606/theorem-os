import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { readSolverRunState } from '../src/solver/archive';
import { directSolverModules } from '../src/solver/modules';
import { runSolver } from '../src/solver/run';
import { localExample } from './helpers/solver';

const host = vi.hoisted(() => ({ run: vi.fn(), beforeWrite: undefined as
  ((file: string, value: unknown) => void) | undefined }));
vi.mock('../src/math/mathRuntimeIo', async original => {
  const actual = await original<typeof import('../src/math/mathRuntimeIo')>();
  return { ...actual, writeMathJsonDurable: (...args: Parameters<typeof actual.writeMathJsonDurable>) => {
    host.beforeWrite?.(args[0], args[1]);
    return actual.writeMathJsonDurable(...args);
  } };
});
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
vi.mock('../src/math/leanDiagnostics', async original => ({
  ...await original<typeof import('../src/math/leanDiagnostics')>(),
  runLeanDiagnostics: async () => ({ exitCode: 0, timedOut: false, phases: [] }),
}));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: () => ({ status: 'ready' }) }));
vi.mock('../src/math/verifier', async original => ({
  ...await original<typeof import('../src/math/verifier')>(), resolveMathematicsLakePackagesCache: () => undefined,
}));
vi.mock('../src/solver/research', () => ({ runResearchWorkers: host.run }));

const directories: string[] = [];
const open = vi.fn(() => { throw new Error('fixture_model_call_forbidden'); });
const modules = { ...directSolverModules, M1: { ...directSolverModules.M1, open } };

function fixture() {
  const example = localExample('run-lease-safety-');
  const { directory, workspace } = example;
  directories.push(directory);
  vi.stubEnv('DEEPSCIENTIST_MATH_ENV_FILE', path.join(directory, 'math.env'));
  vi.stubEnv('DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS', '');
  const output = path.join(directory, 'run.json'), stateFile = `${output}.runtime/state.json`;
  const taskFile = path.join(directory, 'task.md'), buildFile = path.join(directory, 'build.json');
  fs.writeFileSync(taskFile, 'Keep the original tutorial statements.');
  fs.writeFileSync(buildFile, '{}');
  const args = ['--workspace', workspace, '--task-file', taskFile, '--build-manifest', buildFile, '--output', output,
    '--workers', '1', '--model', 'fixture', '--max-turns', '0', '--max-run-seconds', '0', '--max-turn-seconds', '0'];
  return { directory, output, stateFile, lockPath: path.join(path.dirname(stateFile), 'run.lock'), args };
}

function competingLock(lockPath: string): number | null {
  const result = spawnSync('/usr/bin/flock', ['--exclusive', '--nonblock', '--conflict-exit-code', '73',
    lockPath, '/usr/bin/true'], { timeout: 5_000 });
  if (result.error) throw result.error;
  return result.status;
}

beforeEach(() => {
  host.run.mockReset(); open.mockClear(); host.beforeWrite = undefined;
  vi.spyOn(console, 'log').mockImplementation(() => {});
});
afterEach(() => {
  host.beforeWrite = undefined;
  vi.restoreAllMocks(); vi.unstubAllEnvs();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

describe('run failure checkpoint ownership', () => {
  it('retains the real run lock while publishing failure state and output', async () => {
    const current = fixture(), writes: string[] = [];
    let failed = false;
    host.beforeWrite = file => {
      if (!failed || ![current.stateFile, current.output].includes(file)) return;
      writes.push(file);
      expect(competingLock(current.lockPath)).toBe(73);
    };
    host.run.mockImplementation(async () => { failed = true; throw new Error('fixture_research_failed'); });
    expect(await runSolver(current.args, current.directory, modules)).toBe(1);
    expect(writes).toEqual([current.stateFile, current.output]);
    expect(readSolverRunState(current.stateFile).error).toBe('fixture_research_failed');
    expect(JSON.parse(fs.readFileSync(current.output, 'utf8'))).toMatchObject({
      status: 'runtime_error', reason: 'fixture_research_failed',
    });
    expect(competingLock(current.lockPath)).toBe(0);
    expect(open).not.toHaveBeenCalled();
  });

  it('publishes one cancellation checkpoint and does not overwrite it after releasing the lease', async () => {
    const current = fixture(), writes: string[] = [];
    let cancelled = false;
    host.beforeWrite = file => {
      if (!cancelled || ![current.stateFile, current.output].includes(file)) return;
      writes.push(file);
      expect(competingLock(current.lockPath)).toBe(73);
    };
    host.run.mockImplementation(async () => {
      cancelled = true;
      process.emit('SIGINT');
      throw new Error('fixture_research_cancelled');
    });
    expect(await runSolver(current.args, current.directory, modules)).toBe(4);
    expect(writes).toEqual([current.stateFile, current.output]);
    const state = readSolverRunState(current.stateFile);
    expect(state.error).toBeUndefined();
    expect(state.solveFinishedAt).toEqual(expect.any(Number));
    expect(JSON.parse(fs.readFileSync(current.output, 'utf8'))).toMatchObject({
      status: 'limit_reached', reason: 'math_run_stopped',
    });
    const finished = vi.mocked(console.log).mock.calls.filter(([message]) =>
      JSON.parse(String(message)).event === 'finished');
    expect(finished).toHaveLength(1);
    expect(competingLock(current.lockPath)).toBe(0);
    expect(open).not.toHaveBeenCalled();
  });

  it('leaves state and output untouched after the lock inode is replaced', async () => {
    const current = fixture(), writes: string[] = [];
    let invalidated = false, before!: Buffer;
    host.beforeWrite = file => {
      if (invalidated && [current.stateFile, current.output].includes(file)) writes.push(file);
    };
    host.run.mockImplementation(async () => {
      before = fs.readFileSync(current.stateFile);
      fs.unlinkSync(current.lockPath);
      fs.writeFileSync(current.lockPath, '', { mode: 0o600 });
      invalidated = true;
      expect(competingLock(current.lockPath)).toBe(0);
      throw new Error('fixture_research_failed_after_lease_replacement');
    });
    expect(await runSolver(current.args, current.directory, modules)).toBe(1);
    expect(writes).toEqual([]);
    expect(fs.readFileSync(current.stateFile)).toEqual(before);
    expect(fs.existsSync(current.output)).toBe(false);
    expect(open).not.toHaveBeenCalled();
  });
});
