import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { MATH_PROOF_ENVIRONMENT_ENV } from '../src/math/mathProofEnvironment';
import { mathDigest, withMathRuntimeLease } from '../src/math/mathRuntimeIo';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState } from '../src/solver/archive';
import { CooperativeResearch } from '../src/solver/cooperation';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { readContinuationPage, readContinuationSnapshot } from '../src/solver/continuationInput';
import * as continuationInput from '../src/solver/continuationInput';
import { directSolverModules } from '../src/solver/modules';
import { commitSolverSources, git } from '../src/solver/problem';
import type { runResearchWorkers } from '../src/solver/research';
import { runSolver } from '../src/solver/run';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import { localExample, solverState } from './helpers/solver';
import { receiptBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), prepare: vi.fn(), dispose: vi.fn(), run: vi.fn(), packages: '' }));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: vi.fn() }));
vi.mock('../src/math/leanDiagnostics', async original => ({
  ...await original<typeof import('../src/math/leanDiagnostics')>(),
  runLeanDiagnostics: async () => ({ exitCode: 0, timedOut: false, phases: [] }),
}));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: () => ({ status: 'ready' }) }));
vi.mock('../src/math/verifier', async original => ({
  ...await original<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, resolveMathematicsLakePackagesCache: () => host.packages,
}));
vi.mock('../src/math/mathProofEnvironment', async original => ({
  ...await original<typeof import('../src/math/mathProofEnvironment')>(), prepareMathProofEnvironment: host.prepare,
}));
vi.mock('../src/solver/research', () => ({ runResearchWorkers: host.run }));

type ResearchInput = Parameters<typeof runResearchWorkers>[0];
const directories: string[] = [];
const taskText = 'Keep the original tutorial statements and continue the frozen proof.\n';
const modules = { ...directSolverModules, M1: { ...directSolverModules.M1,
  open: vi.fn(() => { throw new Error('fixture_model_call_forbidden'); }) } };

function fixture() {
  const example = localExample('run-continuation-seed-');
  const { directory, workspace, problem } = example;
  directories.push(directory);
  const oldDirectory = path.join(directory, 'old.json.runtime');
  fs.mkdirSync(oldDirectory, { mode: 0o700 });
  const sourceWorkers = ['solver', 'engineer'].map((id, index) => {
    const worktree = path.join(oldDirectory, index ? 'worktree-2' : 'worktree');
    git(workspace, ['worktree', 'add', '--quiet', '--detach', worktree, problem.baseCommit]);
    return { id, role: index ? 'engineer' as const : 'lead' as const, worktree, phase: 'running' as const, turns: 1 };
  });
  const source = path.join(sourceWorkers[0].worktree, problem.projectRelative, 'Submission.lean');
  fs.writeFileSync(source, fs.readFileSync(source, 'utf8').replace('namespace Tutorial',
    'namespace Tutorial\n\nlemma saved_helper : True := by trivial'));
  const canonical = commitSolverSources(problem, sourceWorkers[0].worktree);
  fs.writeFileSync(path.join(sourceWorkers[1].worktree, 'RESEARCH.md'), 'Frozen worker notes.\n');
  const helper: CooperativeTask = { id: 'saved_helper', kind: 'lemma', objective: 'Prove the saved helper.',
    theoremName: 'Tutorial.saved_helper', proofPath: 'Submission.lean', type: 'True', ownerId: 'engineer', dependsOn: [], revision: 0 };
  const tasks: CooperativeTask[] = [helper, ...problem.targets.map((target, index) => ({ id: `goal_${index}`, kind: 'goal' as const,
    objective: `Prove ${target.theoremName}.`, theoremName: target.theoremName, proofPath: target.proofPath,
    ownerId: 'engineer', dependsOn: [helper.id], revision: 0 }))];
  const historical: TaskProof = { commit: canonical, sourceDigest: 'historical', passed: true,
    taskDigest: taskVersion(helper), seedCommit: problem.baseCommit, changes: [],
    verification: { status: 'kernel_verified', targetCommit: canonical,
      results: [{ status: 'kernel_verified', targetCommit: canonical, receiptId: 'historical' }] } as TaskProof['verification'] };
  const sourceStateFile = path.join(oldDirectory, 'state.json');
  writeSolverRunState(sourceStateFile, solverState(problem, sourceWorkers[0].worktree, {
    runId: 'historical-run', phase: 'running', taskDigest: mathDigest(taskText), turns: 2,
    workerCount: 2, workers: sourceWorkers, coordination: 'cooperative', cooperation: { canonicalCommit: canonical,
      tasks: tasks.map(task => ({ task, status: task.kind === 'lemma' ? 'integrated' : 'pending', attempts: 1,
        ...(task.kind === 'lemma' ? { integratedCheck: historical } : {}) })),
      groups: [{ group: { id: 'main', objective: 'Prove the tutorial.', status: 'active', revision: 0, engineerId: 'engineer' }, turns: 2 }] },
  }));
  const output = path.join(directory, 'continued.json'), stateFile = `${output}.runtime/state.json`;
  const taskFile = path.join(directory, 'task.md'), buildFile = path.join(directory, 'build.json');
  fs.writeFileSync(taskFile, taskText); fs.writeFileSync(buildFile, '{}');
  host.packages = path.join(directory, 'packages'); fs.mkdirSync(host.packages);
  const args = ['--workspace', workspace, '--task-file', taskFile, '--build-manifest', buildFile, '--output', output,
    '--workers', '2', '--model', 'fixture', '--continuation-source-run', sourceStateFile,
    '--max-turns', '0', '--max-run-seconds', '0', '--max-turn-seconds', '0'];
  return { directory, output, stateFile, sourceStateFile, sourceWorkers, problem, args };
}

beforeEach(() => {
  vi.spyOn(console, 'log').mockImplementation(() => {});
  host.prepare.mockReset().mockResolvedValue({ environmentValue: 'live-run-proof-environment', dispose: host.dispose,
    stats: { files: 0, bytes: 0, publications: 1 } });
  host.dispose.mockReset().mockResolvedValue(undefined);
  host.verify.mockReset().mockImplementation((request: MathematicsVerifierBatchRequest) => receiptBatch(request,
    { sessionId: 'continued', receiptId: (_index, theoremName) => `continued-${request.targetCommit}-${theoremName}` }));
  host.run.mockReset().mockResolvedValue(undefined);
});
afterEach(() => {
  vi.restoreAllMocks(); vi.clearAllMocks();
  for (const directory of directories.splice(0)) fs.rmSync(directory, { recursive: true, force: true });
});

describe('same-process CLI continuation initialization', () => {
  it('shares the held lock, environment and proof objects through restore without another helper verification', async () => {
    const f = fixture(), historical = fs.readFileSync(f.sourceStateFile);
    host.run.mockImplementation(async (input: ResearchInput) => {
      expect(host.dispose).not.toHaveBeenCalled();
      expect(input.maxTurns).toBe(Infinity); expect(input.deadline).toBe(Infinity); expect(input.maxTurnMs).toBe(Infinity);
      const helper = input.state.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!;
      expect(input.freshContinuationChecks).toEqual([helper.integratedCheck]);
      expect(input.freshContinuationChecks![0]).toBe(helper.integratedCheck);
      expect(helper.integratedCheck!.verification.results[0].receiptId).not.toBe('historical');
      await expect(withMathRuntimeLease({ lockPath: path.join(path.dirname(f.stateFile), 'run.lock'),
        flockExecutable: '/usr/bin/flock' }, async () => undefined)).rejects.toThrow('math_runtime_lease_busy');
      for (const worker of input.workers) {
        const access = input.access.get(worker.id)!;
        expect(access.environment[MATH_PROOF_ENVIRONMENT_ENV]).toBe('live-run-proof-environment');
        expect(access.continuation!.digest).toBe(input.state.continuationDigest);
        expect(readContinuationSnapshot(access.continuation!.file, access.continuation!.digest).manifest.attachments)
          .toContainEqual(expect.objectContaining({ id: 'draft-engineer' }));
      }
      const cooperative = new CooperativeResearch({ ...input, exclusiveCheck: check => check() });
      try {
        await cooperative.restore();
        expect(host.verify).toHaveBeenCalledOnce();
        expect(helper.status).toBe('integrated');
      } finally { await cooperative.stop(); }
    });
    expect(await runSolver(f.args, f.directory, modules), fs.readFileSync(f.output, 'utf8')).toBe(4);
    expect(host.run).toHaveBeenCalledOnce(); expect(host.prepare).toHaveBeenCalledOnce(); expect(host.dispose).toHaveBeenCalledOnce();
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][1].env[MATH_PROOF_ENVIRONMENT_ENV]).toBe('live-run-proof-environment');
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(historical);
    expect(modules.M1.open).not.toHaveBeenCalled();
  });

  it('can retain a seeded zero-turn checkpoint without starting research', async () => {
    const f = fixture();
    expect(await runSolver([...f.args, '--startup-only'], f.directory, modules)).toBe(0);
    const state = readSolverRunState(f.stateFile);
    expect(state.phase).toBe('prepared'); expect(state.turns).toBe(0); expect(state.solveStartedAt).toBeUndefined();
    expect(state.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!.status).toBe('integrated');
    expect(state.workers!.every(worker => fs.existsSync(path.join(worker.worktree, f.problem.projectRelative, '.lake/continuation.json')))).toBe(true);
    expect(host.run).not.toHaveBeenCalled(); expect(host.prepare).toHaveBeenCalledOnce(); expect(host.dispose).toHaveBeenCalledOnce();
  });

  it('preserves initialization progress after an error and retries the frozen source with resume', async () => {
    const f = fixture(); let interrupt = true;
    vi.mocked(console.log).mockImplementation(message => {
      if (interrupt && JSON.parse(String(message)).event === 'continuation_seed_checked') {
        interrupt = false; throw new Error('fixture_initialization_interrupted');
      }
    });
    expect(await runSolver(f.args, f.directory, modules)).toBe(1);
    const interrupted = readSolverRunState(f.stateFile), digest = interrupted.continuationDigest;
    expect(interrupted.phase).toBe('prepared'); expect(interrupted.solveStartedAt).toBeUndefined();
    expect(interrupted.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!.status).toBe('integrated');
    expect(host.run).not.toHaveBeenCalled();
    fs.writeFileSync(path.join(f.sourceWorkers[1].worktree, 'RESEARCH.md'), 'Late historical notes.\n');
    expect(await runSolver([...f.args, '--resume'], f.directory, modules)).toBe(4);
    const resumed = readSolverRunState(f.stateFile);
    expect(resumed.continuationDigest).toBe(digest);
    const draft = JSON.parse(readContinuationPage(path.join(path.dirname(f.stateFile), 'continuation.json'), digest!, 'draft-engineer').text);
    expect(draft.notes).toBe('Frozen worker notes.\n');
    expect(host.run).toHaveBeenCalledOnce(); expect(host.verify).toHaveBeenCalledTimes(2); expect(host.dispose).toHaveBeenCalledTimes(2);
  });

  it.each(['continuation-copy', 'environment-write'] as const)(
    'retries %s failure after seeding without leaving the prepared initialization', async failure => {
      const f = fixture(), directory = path.dirname(f.stateFile), historical = fs.readFileSync(f.sourceStateFile);
      const environmentFile = path.join(directory, 'environment-engineer.json');
      const reportFile = path.join(directory, 'continuation-seed.json');
      const target = failure === 'continuation-copy'
        ? path.join(directory, 'worktree-2', f.problem.projectRelative, '.lake/continuation.json') : environmentFile;
      let failPublication = true, refreshEnvironment = failure === 'environment-write';
      // Environment publication may otherwise reuse its first durable write. Make
      // the peer need its file again after the fresh helper check has completed.
      vi.mocked(console.log).mockImplementation(message => {
        if (refreshEnvironment && JSON.parse(String(message)).event === 'continuation_seed_checked') {
          refreshEnvironment = false; fs.unlinkSync(environmentFile);
        }
      });
      const rename = fs.renameSync;
      vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
        if (failPublication && String(to) === target && fs.existsSync(reportFile) &&
            JSON.parse(fs.readFileSync(reportFile, 'utf8')).stage === 'complete') {
          failPublication = false; throw new Error(`fixture_${failure}_interrupted`);
        }
        return rename(from, to);
      });

      expect(await runSolver(f.args, f.directory, modules)).toBe(1);
      expect(failPublication).toBe(false);
      expect(JSON.parse(fs.readFileSync(f.output, 'utf8')).reason).toBe(`fixture_${failure}_interrupted`);
      expect(JSON.parse(fs.readFileSync(reportFile, 'utf8')).stage).toBe('complete');
      const interrupted = readSolverRunState(f.stateFile), digest = interrupted.continuationDigest!;
      const frozenFile = path.join(directory, 'continuation-seed-source.json'), frozenSource = fs.readFileSync(frozenFile);
      expect(interrupted.phase).toBe('prepared'); expect(interrupted.solveStartedAt).toBeUndefined();
      expect(interrupted.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!.status).toBe('integrated');
      expect(host.verify).toHaveBeenCalledOnce(); expect(host.run).not.toHaveBeenCalled();
      // Earlier workers completed real snapshot publication before the peer failed.
      expect(readContinuationSnapshot(path.join(directory, 'worktree', f.problem.projectRelative, '.lake/continuation.json'), digest)
        .digest).toBe(digest);

      fs.writeFileSync(path.join(f.sourceWorkers[1].worktree, 'RESEARCH.md'), 'Late notes after worker publication failed.\n');
      host.run.mockImplementation(async (input: ResearchInput) => {
        const helper = input.state.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!;
        expect(input.freshContinuationChecks![0]).toBe(helper.integratedCheck);
        for (const worker of input.workers) {
          const continuation = input.access.get(worker.id)!.continuation!;
          expect(readContinuationSnapshot(continuation.file, continuation.digest).digest).toBe(digest);
        }
      });
      expect(await runSolver([...f.args, '--resume'], f.directory, modules), fs.readFileSync(f.output, 'utf8')).toBe(4);
      expect(readSolverRunState(f.stateFile).continuationDigest).toBe(digest);
      expect(fs.readFileSync(frozenFile)).toEqual(frozenSource);
      expect(fs.readFileSync(f.sourceStateFile)).toEqual(historical);
      const draft = JSON.parse(readContinuationPage(path.join(directory, 'continuation.json'), digest, 'draft-engineer').text);
      expect(draft.notes).toBe('Frozen worker notes.\n');
      expect(host.run).toHaveBeenCalledOnce(); expect(host.verify).toHaveBeenCalledTimes(2); expect(host.dispose).toHaveBeenCalledTimes(2);
    });

  it.each(['root-snapshot-read', 'ready-observer', 'startup-output'] as const)(
    'retries %s failure after a complete seed while retaining the prepared checkpoint', async failure => {
      const f = fixture(), directory = path.dirname(f.stateFile), historical = fs.readFileSync(f.sourceStateFile);
      const reportFile = path.join(directory, 'continuation-seed.json'), snapshotFile = path.join(directory, 'continuation.json');
      const args = failure === 'startup-output' ? [...f.args, '--startup-only'] : f.args;
      const seedComplete = () => fs.existsSync(reportFile) && JSON.parse(fs.readFileSync(reportFile, 'utf8')).stage === 'complete';
      const fault = `fixture_${failure}_interrupted`;
      let failures = 0;
      if (failure === 'root-snapshot-read') {
        const readSnapshot = continuationInput.readContinuationSnapshot;
        vi.spyOn(continuationInput, 'readContinuationSnapshot').mockImplementation((...input) => {
          if (!failures && input[0] === snapshotFile && seedComplete()) { failures++; throw new Error(fault); }
          return readSnapshot(...input);
        });
      } else if (failure === 'ready-observer') {
        vi.mocked(console.log).mockImplementation(message => {
          if (!failures && JSON.parse(String(message)).event === 'ready' && seedComplete()) {
            failures++; throw new Error(fault);
          }
        });
      } else {
        const rename = fs.renameSync;
        vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
          if (!failures && String(to) === f.output && seedComplete()) { failures++; throw new Error(fault); }
          return rename(from, to);
        });
      }

      expect(await runSolver(args, f.directory, modules)).toBe(1);
      expect(failures).toBe(1);
      expect(seedComplete()).toBe(true);
      expect(JSON.parse(fs.readFileSync(f.output, 'utf8')).reason).toBe(fault);
      const interrupted = readSolverRunState(f.stateFile), digest = interrupted.continuationDigest!;
      const frozenFile = path.join(directory, 'continuation-seed-source.json'), frozenSource = fs.readFileSync(frozenFile);
      expect(interrupted.phase).toBe('prepared'); expect(interrupted.turns).toBe(0);
      expect(interrupted.solveStartedAt).toBeUndefined();
      expect(interrupted.cooperation!.tasks.find(node => node.task.id === 'saved_helper')!.status).toBe('integrated');
      expect(host.verify).toHaveBeenCalledOnce(); expect(host.run).not.toHaveBeenCalled();

      fs.writeFileSync(path.join(f.sourceWorkers[1].worktree, 'RESEARCH.md'), 'Late notes after the prepared checkpoint failed.\n');
      expect(await runSolver([...args, '--resume'], f.directory, modules), fs.readFileSync(f.output, 'utf8'))
        .toBe(failure === 'startup-output' ? 0 : 4);
      const resumed = readSolverRunState(f.stateFile);
      expect(failures).toBe(1); expect(resumed.continuationDigest).toBe(digest);
      expect(fs.readFileSync(frozenFile)).toEqual(frozenSource);
      expect(fs.readFileSync(f.sourceStateFile)).toEqual(historical);
      for (const worker of resumed.workers!) {
        expect(readContinuationSnapshot(path.join(worker.worktree, f.problem.projectRelative, '.lake/continuation.json'), digest)
          .digest).toBe(digest);
      }
      const draft = JSON.parse(readContinuationPage(snapshotFile, digest, 'draft-engineer').text);
      expect(draft.notes).toBe('Frozen worker notes.\n');
      expect(host.run).toHaveBeenCalledTimes(failure === 'startup-output' ? 0 : 1);
      expect(host.verify).toHaveBeenCalledTimes(2); expect(host.dispose).toHaveBeenCalledTimes(2);
      expect(modules.M1.open).not.toHaveBeenCalled();
    });

  it.each([['--workers', '1'], ['--coordination', 'independent'], ['--continuation-manifest', '/unused.json']])(
    'rejects incompatible %s before preparing a workspace', async (flag, value) => {
      await expect(runSolver(['--continuation-source-run', '/unused-run', flag, value], '/unused-root', modules))
        .rejects.toThrow('--continuation-source-run');
      expect(host.run).not.toHaveBeenCalled(); expect(host.prepare).not.toHaveBeenCalled();
    });
});
