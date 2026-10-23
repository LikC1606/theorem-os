import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment, resolveMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';
import { MATH_PROOF_ENVIRONMENT_ENV, MATH_PROOF_ENVIRONMENT_SANDBOX_ENV } from '../src/math/mathProofEnvironment';
import { DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT } from '../src/math/mathProofEnvironmentCache';
import { withMathRuntimeLease } from '../src/math/mathRuntimeIo';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierExecutionOptions } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { seedSolverContinuation } from '../src/solver/continuationSeed';
import { readContinuationPage, readContinuationSnapshot } from '../src/solver/continuationInput';
import { committedSource, git, readSolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { hasTaskConnectionCheck } from '../src/solver/taskConnections';
import { cooperativeResearch } from './helpers/cooperation';
import { failedBatch, receiptBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), build: vi.fn(), prepare: vi.fn(), dispose: vi.fn(),
  resolvePackages: vi.fn(), packages: undefined as string | undefined }));
vi.mock('../src/math/mathBuildManifest', async importOriginal => ({ ...await importOriginal<typeof import('../src/math/mathBuildManifest')>(),
  readMathBuildManifest: host.build }));
vi.mock('../src/math/verifier', async importOriginal => ({ ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, resolveMathematicsLakePackagesCache: host.resolvePackages }));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({ ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(),
  prepareMathProofEnvironment: host.prepare }));

const roots: string[] = [];
const original = 'import Submission.Helpers\nnamespace Submission\ntheorem original : True := by sorry\nend Submission\n';
const emptyHelpers = 'namespace Submission.Helpers\nend Submission.Helpers\n';
const helpers = 'namespace Submission.Helpers\nlemma first_helper : True := by trivial\nlemma second_helper : True := by trivial\nend Submission.Helpers\n';
const commit = (root: string, message: string) => {
  git(root, ['add', '--', '.']);
  git(root, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', message]);
  return git(root, ['rev-parse', 'HEAD']);
};

function fixture() {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'continuation-seed-test-'))); roots.push(root);
  const workspace = path.join(root, 'workspace'), projectRelative = 'generated/fixture', project = path.join(workspace, projectRelative);
  fs.mkdirSync(path.join(project, 'Submission'), { recursive: true });
  const trusted = { 'Challenge.lean': 'theorem challenge : True := by trivial\n',
    'config.json': '{"theorem_names":["original"]}\n', 'holes.json': '{"id":"fixture","holes":[{"name":"original"}]}\n',
    'lean-toolchain': 'leanprover/lean4:v4.31.0\n', 'lakefile.toml': 'name = "fixture"\n[[lean_lib]]\nname = "Submission"\n' };
  for (const [file, text] of Object.entries(trusted)) fs.writeFileSync(path.join(project, file), text);
  fs.writeFileSync(path.join(project, 'Submission.lean'), original);
  fs.writeFileSync(path.join(project, 'Submission/Helpers.lean'), emptyHelpers);
  git(workspace, ['init', '--quiet']); const base = commit(workspace, 'Public solver baseline');
  fs.appendFileSync(path.join(workspace, '.git/info/exclude'), `\n/${projectRelative}/.lake/\n/active-problem.json\n`);
  const payloads = canonicalMathProblemStatementPayloads({ informalStatement: 'Prove the original claim.', formalStatement: original, assumptions: [] });
  const contract: MathProblemContract = { problemId: 'fixture', informalStatement: 'Prove the original claim.', formalStatement: original,
    assumptions: [], knownTraps: [], acceptanceCriteria: ['Prove original'], officialVerificationCommand: 'lake test',
    statementHash: mathDigest(payloads.informal), leanStatementHash: mathDigest(payloads.lean) };
  const receiptFile = path.join(workspace, 'active-problem.json');
  fs.writeFileSync(receiptFile, JSON.stringify({ schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1',
    receiptId: 'fixture', problemId: 'fixture', benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT, catalogHash: 'a'.repeat(64),
    leaderboardSource: 'disabled', contract, workspaceRoot: workspace, projectRoot: project, activeProblemPath: receiptFile,
    createdAt: 1, trustedFiles: Object.keys(trusted), solverOwnedFiles: ['Submission.lean', 'Submission/Helpers.lean'],
    publicObligations: [{ name: 'Submission.original', declarationHash: hashMathFormalSourceDeclaration(original, 'Submission.original') }] }));
  const problem = readSolverProblem(workspace, receiptFile);
  const oldDirectory = path.join(root, 'old.json.runtime'), directory = path.join(root, 'new.json.runtime');
  for (const parent of [oldDirectory, directory]) {
    fs.mkdirSync(parent, { mode: 0o700 });
    for (const name of ['worktree', 'worktree-2']) git(workspace, ['worktree', 'add', '--quiet', '--detach', path.join(parent, name), base]);
  }
  const sourceWorktree = path.join(oldDirectory, 'worktree'), worktree = path.join(directory, 'worktree');
  fs.writeFileSync(path.join(sourceWorktree, projectRelative, 'Submission/Helpers.lean'), helpers);
  const canonical = commit(sourceWorktree, 'Historical helpers');
  const notes = '\ufeffunfinished λ notes\r\n';
  fs.writeFileSync(path.join(oldDirectory, 'worktree-2', projectRelative, 'Submission/Helpers.lean'), helpers.replace('by trivial', 'by sorry'));
  fs.writeFileSync(path.join(oldDirectory, 'worktree-2', 'RESEARCH.md'), notes);
  fs.writeFileSync(path.join(sourceWorktree, 'RESEARCH.md'), 'Old Lead findings, still advisory.\n');
  const tasks: CooperativeTask[] = ['first', 'second'].map(name => ({ id: name, kind: 'lemma', objective: `Prove ${name}`,
    dependsOn: [], revision: 0, ownerId: 'prover-1', proofPath: 'Submission/Helpers.lean',
    theoremName: `Submission.Helpers.${name}_helper`, type: 'True' }));
  tasks.push({ id: 'goal', kind: 'goal', objective: 'Prove original', dependsOn: ['first', 'second'], revision: 0,
    proofPath: 'Submission.lean', theoremName: 'Submission.original' });
  const archivedProof = (task: CooperativeTask): TaskProof => ({ commit: canonical, sourceDigest: 'old-source', passed: true,
    taskDigest: taskVersion(task), seedCommit: base, changes: [], verification: { status: 'kernel_verified', targetCommit: canonical,
      results: [{ status: 'kernel_verified', targetCommit: canonical, receiptId: `old-${task.id}` }] } as TaskProof['verification'] });
  const buildFile = path.join(root, 'manifest.json'); fs.writeFileSync(buildFile, '{"fixture":"new-build"}', { mode: 0o400 });
  const skeleton = { schema: 'deepscientist.math.solver.v1' as const, problem, taskDigest: mathDigest('Original unchanged task.\n'),
    environmentDigest: mathDigest('new-environment'), evaluatorDigest: mathDigest('host-default'), model: 'fixture', effort: 'max',
    coordination: 'cooperative' as const, turns: 0, dispatchCounts: {}, workerCount: 2 };
  const newState: SolverRunState = { ...skeleton, runId: 'new-run', buildDigest: mathDigest(fs.readFileSync(buildFile)),
    methodDigest: 'new-method', phase: 'prepared', worktree, workers: [
      { id: 'solver', role: 'lead', worktree, phase: 'prepared', turns: 0, dispatchCounts: {} },
      { id: 'prover-1', role: 'prover', worktree: path.join(directory, 'worktree-2'), phase: 'prepared', turns: 0, dispatchCounts: {} }] };
  const oldState: SolverRunState = { ...skeleton, runId: 'old-run', buildDigest: 'historical-build', methodDigest: 'old-method',
    phase: 'running', turns: 8, worktree: sourceWorktree, workers: [
      { id: 'solver', role: 'lead', worktree: sourceWorktree, phase: 'running', turns: 3, threadId: 'old-lead-thread' },
      { id: 'prover-1', role: 'prover', worktree: path.join(oldDirectory, 'worktree-2'), phase: 'running', turns: 5, threadId: 'old-prover-thread' }],
    cooperation: { canonicalCommit: canonical, planVersion: 'historical-plan', groups: [{ group: {
      id: 'main', objective: 'Original route', status: 'active', revision: 0 }, turns: 8 }],
      tasks: tasks.map(task => ({ task, status: task.kind === 'goal' ? 'running' : 'integrated', attempts: 2,
        assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'prover-1', seedCommit: base, assignmentId: `old-${task.id}` },
        ...(task.kind === 'lemma' ? { integratedCheck: archivedProof(task) } : {}) })),
      deliveries: [{ id: 'old-delivery', producer: 'prover-1', kind: 'proof', status: 'verified', statement: 'True', premises: [],
        dependencies: [], remainingObligations: [], summary: 'Historical check', evidenceRefs: [], createdAt: 1 }] } };
  const stateFile = path.join(directory, 'state.json'), sourceStateFile = path.join(oldDirectory, 'state.json');
  writeSolverRunState(stateFile, newState); writeSolverRunState(sourceStateFile, oldState);
  const environmentFile = path.join(directory, 'environment-solver.json');
  host.packages = path.join(root, 'packages'); fs.mkdirSync(host.packages);
  fs.writeFileSync(environmentFile, canonicalMathJson(projectMathematicsRuntimeEnvironment({ PATH: '/usr/bin:/bin',
    DEEPSCIENTIST_MATH_ENV_FILE: environmentFile, DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
    [MATH_PROOF_ENVIRONMENT_ENV]: 'disposed-startup-only-fixture' })), { mode: 0o400 });
  const controller = new AbortController();
  const options = { sourceRun: sourceStateFile, run: stateFile, root, buildManifest: buildFile, signal: controller.signal };
  return { root, directory, oldDirectory, workspace, worktree, sourceWorktree, projectRelative, stateFile, sourceStateFile,
    newState, oldState, tasks, notes, base, environmentFile, options, controller, seed: () => seedSolverContinuation(options) };
}

function conditionalFixture() {
  const f = fixture(), worker = f.oldState.workers![1]!.worktree;
  git(worker, ['reset', '--hard', f.oldState.cooperation!.canonicalCommit!]);
  fs.writeFileSync(path.join(worker, f.projectRelative, 'Submission/Helpers.lean'),
    helpers.replace('end Submission.Helpers', 'lemma bridge_helper : True := by exact second_helper\nend Submission.Helpers'));
  const proofCommit = commit(worker, 'Historical conditional bridge');
  fs.writeFileSync(path.join(worker, 'RESEARCH.md'), f.notes);
  const task: CooperativeTask = { id: 'bridge', kind: 'lemma', objective: 'Reuse the missing typed lemma',
    dependsOn: ['second'], revision: 0, ownerId: 'prover-1', proofPath: 'Submission/Helpers.lean',
    theoremName: 'Submission.Helpers.bridge_helper', type: 'True' };
  const condition = { taskId: 'second', taskDigest: taskVersion(f.tasks[1]!) };
  f.oldState.cooperation!.tasks.push({ task, status: 'conditional', attempts: 1,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'prover-1', seedCommit: f.oldState.cooperation!.canonicalCommit!,
      dependencies: [condition] },
    proof: { commit: proofCommit, sourceDigest: 'old-conditional-source', passed: true, taskDigest: taskVersion(task),
      seedCommit: f.oldState.cooperation!.canonicalCommit!, changes: [], conditions: [condition],
      verification: { status: 'kernel_verified', targetCommit: proofCommit,
        results: [{ status: 'kernel_verified', targetCommit: proofCommit, receiptId: 'old-bridge' }] } as TaskProof['verification'] } });
  f.oldState.workers![1]!.sessionTaskId = task.id;
  writeSolverRunState(f.sourceStateFile, f.oldState);
  return { ...f, task, condition, proofCommit };
}

function freshReceipts(request: MathematicsVerifierBatchRequest) {
  return receiptBatch(request, { sessionId: 'fresh-seed', receiptId: (_, name) => `fresh-seed-${request.targetCommit}-${name}` });
}

function cooperationFor(f: ReturnType<typeof fixture>, state: SolverRunState, freshContinuationChecks: readonly TaskProof[] = []) {
  const workers = state.workers!.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree,
    ownedFiles: state.problem.ownedFiles }));
  const environment = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
    [MATH_PROOF_ENVIRONMENT_ENV]: 'live-host-proof-environment' };
  return cooperativeResearch({ state, workers, retrievalRoot: f.root, signal: f.controller.signal,
    freshContinuationChecks, access: new Map(workers.map(worker => [worker.id, { environment, retrievalRoot: f.root }])) });
}

beforeEach(() => {
  host.build.mockReset(); host.verify.mockReset(); host.prepare.mockReset(); host.dispose.mockReset(); host.resolvePackages.mockReset();
  host.resolvePackages.mockImplementation(() => host.packages);
  host.dispose.mockResolvedValue(undefined);
  host.prepare.mockResolvedValue({ environmentValue: 'fresh-seed-proof-environment', dispose: host.dispose,
    stats: { files: 0, bytes: 0, publications: 1 } });
  host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => verifiedBatch(request,
    { sessionId: 'fresh-seed', receipt: 'fresh-seed', checks: true }));
});
afterEach(() => { vi.restoreAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('explicit prepared-run continuation initialization', () => {
  it('owns a fresh proof environment without changing frozen settings or the static run identity', async () => {
    const f = fixture(), savedEnvironment = fs.readFileSync(f.environmentFile);
    const lifecycle: string[] = [];
    host.resolvePackages.mockImplementation((_project: string, env: NodeJS.ProcessEnv) => {
      expect(env[MATH_PROOF_ENVIRONMENT_ENV]).toBeUndefined();
      expect(env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]).toBeUndefined();
      expect(env.DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS).toBe(host.packages);
      lifecycle.push('resolve-packages');
      return host.packages;
    });
    host.prepare.mockImplementation(async () => {
      lifecycle.push('prepare');
      return { environmentValue: 'fresh-seed-proof-environment', dispose: host.dispose,
        stats: { files: 0, bytes: 0, publications: 1 } };
    });
    host.dispose.mockImplementation(async () => { lifecycle.push('dispose'); });
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest, options: MathematicsVerifierExecutionOptions) => {
      expect(host.dispose).not.toHaveBeenCalled();
      expect(options.env![MATH_PROOF_ENVIRONMENT_ENV]).toBe('fresh-seed-proof-environment');
      expect(options.env![MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]).toBeUndefined();
      // The verifier resolves the environment again. The resolved marker must
      // survive the host-side replacement or it would reload the disposed lease.
      expect(resolveMathematicsRuntimeEnvironment(options.env)[MATH_PROOF_ENVIRONMENT_ENV]).toBe('fresh-seed-proof-environment');
      lifecycle.push('verify');
      return verifiedBatch(request, { sessionId: 'fresh-seed', receipt: 'fresh-seed', checks: true });
    });
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual([]);
    expect(lifecycle).toEqual(['resolve-packages', 'prepare', 'verify', 'verify', 'dispose']);
    expect(host.prepare).toHaveBeenCalledExactlyOnceWith(path.join(f.worktree, f.projectRelative), host.packages,
      expect.objectContaining({ env: expect.objectContaining({ DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages }),
        signal: expect.any(AbortSignal), cacheRoot: DEFAULT_MATH_PROOF_ENVIRONMENT_CACHE_ROOT,
        deadlineAt: expect.any(Number) }));
    expect(host.prepare.mock.calls[0][2].env[MATH_PROOF_ENVIRONMENT_ENV]).toBeUndefined();
    expect(host.prepare.mock.calls[0][2].env[MATH_PROOF_ENVIRONMENT_SANDBOX_ENV]).toBeUndefined();
    expect(host.dispose).toHaveBeenCalledOnce();
    expect(state.environmentDigest).toBe(f.newState.environmentDigest);
    expect(state.buildDigest).toBe(f.newState.buildDigest);
    expect(state.methodDigest).toBe(f.newState.methodDigest);
    expect(fs.readFileSync(f.environmentFile)).toEqual(savedEnvironment);
    expect(fs.statSync(f.environmentFile).mode & 0o777).toBe(0o400);
    const reportText = fs.readFileSync(path.join(f.directory, 'continuation-seed.json'), 'utf8');
    expect(reportText).not.toContain('fresh-seed-proof-environment');
    expect(fs.readFileSync(path.join(f.directory, 'continuation-seed-source.json'), 'utf8')).not.toContain('fresh-seed-proof-environment');
  });

  it('disposes the proof environment after verifier exceptions', async () => {
    const f = fixture();
    host.verify.mockRejectedValue(new Error('simulated verifier exception'));
    const report = await f.seed();
    expect(report.stage).toBe('complete');
    expect(report.failed).toEqual(['first', 'second']);
    expect(host.dispose).toHaveBeenCalledOnce();
    expect(readSolverRunState(f.stateFile).cooperation.tasks.some(node => node.status === 'integrated')).toBe(false);
  });

  it('disposes the proof environment after an outer initialization failure', async () => {
    const f = fixture();
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_check') throw new Error('simulated check callback failure');
    } })).rejects.toThrow('simulated check callback failure');
    expect(host.dispose).toHaveBeenCalledOnce();
    expect(host.verify).not.toHaveBeenCalled();
    expect(readSolverRunState(f.stateFile).cooperation.tasks.every(node => node.status === 'pending')).toBe(true);
  });

  it('leaves tasks pending when proof environment preparation fails', async () => {
    const f = fixture(), savedEnvironment = fs.readFileSync(f.environmentFile);
    host.prepare.mockRejectedValue(new Error('simulated proof environment preparation failure'));
    await expect(f.seed()).rejects.toThrow('simulated proof environment preparation failure');
    expect(host.dispose).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
    expect(readSolverRunState(f.stateFile).cooperation.tasks.every(node => node.status === 'pending')).toBe(true);
    expect(fs.readFileSync(f.environmentFile)).toEqual(savedEnvironment);
    expect(readSolverRunState(f.stateFile).environmentDigest).toBe(f.newState.environmentDigest);
  });

  it('keeps proof environment preparation and verification unlimited when requested', async () => {
    const f = fixture();
    await seedSolverContinuation({ ...f.options, timeoutMs: Infinity });
    expect(host.prepare.mock.calls[0][2].deadlineAt).toBeUndefined();
    expect(host.verify.mock.calls.every(([request]) => request.timeoutMs === Infinity && request.batchTimeoutMs === Infinity)).toBe(true);
    expect(host.dispose).toHaveBeenCalledOnce();
  });

  it('retains exact task identities and source drafts, but only fresh receipts authorize imported helpers', async () => {
    const f = fixture();
    f.oldState.workers[1].sessionTaskId = 'second';
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const originalState = fs.readFileSync(f.sourceStateFile), oldSource = fs.readFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'));
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.stage).toBe('complete'); expect(report.failed).toEqual([]); expect(host.verify).toHaveBeenCalledTimes(2);
    expect(state.buildDigest).toBe(f.newState.buildDigest); expect(state.methodDigest).toBe('new-method');
    expect(state.workers).toEqual(f.newState.workers); expect(state.turns).toBe(0); expect(state.phase).toBe('prepared');
    expect(state.cooperation.tasks.map(node => taskVersion(node.task))).toEqual(f.tasks.map(taskVersion));
    expect(state.cooperation.tasks.map(node => node.status)).toEqual(['integrated', 'integrated', 'pending']);
    expect(state.cooperation.tasks.every(node => !node.assignment && !node.proof)).toBe(true);
    expect(state.cooperation.groups[0].turns).toBe(0); expect(state.cooperation.deliveries).toEqual([]);
    for (const node of state.cooperation.tasks.slice(0, 2)) {
      expect(node.integratedCheck.verification.results[0].receiptId).toContain('fresh-seed-');
      expect(git(f.worktree, ['rev-parse', `refs/math/${state.runId}/evidence/${node.integratedCheck.verification.targetCommit}`]))
        .toBe(node.integratedCheck.verification.targetCommit);
    }
    expect(fs.readFileSync(path.join(f.worktree, f.projectRelative, 'Submission/Helpers.lean'), 'utf8')).toBe(helpers);
    expect(fs.existsSync(path.join(f.worktree, 'RESEARCH.md'))).toBe(false);
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(originalState);
    expect(fs.readFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'))).toEqual(oldSource);
    const snapshotFile = path.join(f.directory, 'continuation.json');
    const snapshot = readContinuationSnapshot(snapshotFile, state.continuationDigest);
    expect(snapshot.manifest.attachments.every(item => item.provenance.evidence === 'recorded-not-replayed')).toBe(true);
    const draft = JSON.parse(readContinuationPage(snapshotFile, state.continuationDigest, 'draft-prover-1').text);
    expect(draft.notes).toBe(f.notes); expect(draft.sources['Submission/Helpers.lean']).toContain('by sorry');
    expect(draft.assignment.taskId).toBe('second');
    expect(fs.statSync(path.join(f.directory, 'continuation-seed-source.json')).mode & 0o777).toBe(0o400);
  });

  it('rechecks a conditional declaration absent from canonical source with its exact typed obligation', async () => {
    const f = conditionalFixture(), oldState = fs.readFileSync(f.sourceStateFile);
    expect(fs.readFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'), 'utf8'))
      .not.toContain('bridge_helper');
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual([]);
    expect(report.candidates).toEqual(['first', 'second', 'bridge']);
    expect(host.verify).toHaveBeenCalledTimes(3);
    const bridge = state.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    expect(bridge.status).toBe('conditional');
    expect(bridge.integratedCheck).toBeUndefined();
    expect(bridge.proof?.passed).toBe(true);
    expect(bridge.proof?.conditions).toEqual([f.condition]);
    expect(bridge.proof?.commit).not.toBe(f.proofCommit);
    expect(bridge.proof?.verification.results[0]?.receiptId).toContain('fresh-seed-');
    expect(bridge.proof?.changes.some(change => change.name === 'bridge_helper')).toBe(true);
    expect(bridge.assignment?.seedCommit).not.toBe(f.oldState.cooperation!.canonicalCommit);
    expect(hasTaskConnectionCheck(bridge.task, bridge.assignment!)).toBe(true);
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(oldState);
    const snapshot = readContinuationSnapshot(path.join(f.directory, 'continuation.json'), state.continuationDigest);
    const draft = JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), state.continuationDigest, 'draft-prover-1').text);
    expect(snapshot.manifest.attachments.some(item => item.id === 'seed-history')).toBe(true);
    expect(draft.notes).toBe(f.notes);
    expect(draft.sources['Submission/Helpers.lean']).toContain('bridge_helper');
  });

  it('reuses a held lease and proof environment and hands off only fresh unconditional receipts', async () => {
    const f = conditionalFixture(), seeded = vi.fn();
    const environment = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
      [MATH_PROOF_ENVIRONMENT_ENV]: 'live-host-proof-environment' };
    await withMathRuntimeLease({ lockPath: path.join(f.directory, 'run.lock'), flockExecutable: '/usr/bin/flock' }, async lease => {
      const report = await seedSolverContinuation({ ...f.options, signal: lease.signal, lease,
        preparedEnvironment: environment, onSeeded: seeded });
      expect(report.stage).toBe('complete');
    });
    expect(host.prepare).not.toHaveBeenCalled();
    expect(host.dispose).not.toHaveBeenCalled();
    expect(host.verify.mock.calls.every(([, options]) => options.env[MATH_PROOF_ENVIRONMENT_ENV] === 'live-host-proof-environment')).toBe(true);
    expect(seeded).toHaveBeenCalledOnce();
    const [state, proofs] = seeded.mock.calls[0]!;
    expect(proofs).toHaveLength(2);
    expect(proofs).toContain(state.cooperation.tasks[0].integratedCheck);
    expect(proofs).toContain(state.cooperation.tasks[1].integratedCheck);
    expect(proofs).not.toContain(state.cooperation.tasks[3].proof);
  });

  it('reuses fresh seed receipts through cooperation restore in the same process', async () => {
    const f = fixture(); host.verify.mockImplementation(freshReceipts);
    let state!: SolverRunState, proofs!: TaskProof[];
    await seedSolverContinuation({ ...f.options, onSeeded: (next, checks) => { state = next; proofs = checks; } });
    expect(host.verify).toHaveBeenCalledTimes(2);
    const cooperative = cooperationFor(f, state, proofs);
    try {
      await cooperative.restore();
      expect(host.verify).toHaveBeenCalledTimes(2);
      expect(state.cooperation!.tasks.slice(0, 2).map(node => node.integratedCheck)).toEqual(proofs);
      expect(state.cooperation!.tasks.slice(0, 2).every(node => node.status === 'integrated' && !node.pendingValidation)).toBe(true);
    } finally { f.controller.abort(); await cooperative.stop(); }
  });

  it('checks JSON-restored seed receipts again even when the original fresh objects are supplied', async () => {
    const f = fixture(); host.verify.mockImplementation(freshReceipts);
    let proofs!: TaskProof[];
    await seedSolverContinuation({ ...f.options, onSeeded: (_next, checks) => { proofs = checks; } });
    const state = readSolverRunState(f.stateFile), cooperative = cooperationFor(f, state, proofs);
    try {
      await cooperative.restore();
      expect(host.verify).toHaveBeenCalledTimes(3);
      expect(host.verify.mock.calls[2][0].items.map(item => item.theoremName))
        .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
      expect(state.cooperation!.tasks.slice(0, 2).every(node => node.status === 'integrated' && !node.pendingValidation)).toBe(true);
    } finally { f.controller.abort(); await cooperative.stop(); }
  });

  it('discharges a freshly restored conditional proof through normal cooperation integration', async () => {
    const f = conditionalFixture(); host.verify.mockImplementation(freshReceipts);
    let state!: SolverRunState, proofs!: TaskProof[];
    await seedSolverContinuation({ ...f.options, onSeeded: (next, checks) => { state = next; proofs = checks; } });
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')!.status).toBe('conditional');
    const cooperative = cooperationFor(f, state, proofs);
    try {
      await cooperative.restore();
      const bridge = state.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
      expect(bridge).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
      expect(bridge.integratedCheck!.conditions).toBeUndefined();
      expect(bridge.proof!.projection).toMatchObject({ environmentDigest: state.environmentDigest,
        problemReceiptDigest: state.problem.receiptDigest });
      expect(committedSource(f.worktree, state.cooperation!.canonicalCommit!, `${f.projectRelative}/Submission/Helpers.lean`))
        .toContain('lemma bridge_helper : True := by exact second_helper');
    } finally { f.controller.abort(); await cooperative.stop(); }
  });

  it('prefers an unconditional integrated check after an old conditional proof has been discharged', async () => {
    const f = conditionalFixture(), bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    git(f.sourceWorktree, ['reset', '--hard', f.proofCommit]);
    f.oldState.cooperation!.canonicalCommit = f.proofCommit;
    bridge.status = 'integrated';
    bridge.integratedCheck = { ...bridge.proof!, conditions: undefined };
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual([]); expect(report.candidates).toEqual(['first', 'second', 'bridge']);
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')).toMatchObject({ status: 'integrated',
      integratedCheck: { passed: true } });
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')!.proof).toBeUndefined();
  });

  it('blocks only a conditional candidate whose saved assignment lost its dependencies', async () => {
    const f = conditionalFixture(), bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    delete bridge.assignment!.dependencies;
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['bridge']); expect(host.verify).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')).toMatchObject({ status: 'blocked',
      feedback: 'math_task_condition_version_invalid' });
    expect(state.cooperation!.tasks.slice(0, 2).every(node => node.status === 'integrated')).toBe(true);
  });

  it('keeps a conditional candidate blocked and its draft intact when the historical proof commit is unavailable', async () => {
    const f = conditionalFixture(), bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    bridge.proof!.commit = 'f'.repeat(40);
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['bridge']);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')).toMatchObject({
      status: 'blocked', feedback: expect.stringContaining('math_task_source_unavailable') });
    const draft = JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), state.continuationDigest, 'draft-prover-1').text);
    expect(draft.sources['Submission/Helpers.lean']).toContain('bridge_helper');
  });

  it('rejects a changed conditional dependency contract without promoting its old receipt', async () => {
    const f = conditionalFixture(), bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    bridge.proof!.conditions![0] = { taskId: 'second', taskDigest: mathDigest('changed condition') };
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['bridge']);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')).toMatchObject({
      status: 'blocked', feedback: 'math_task_condition_version_invalid' });
  });

  it('rechecks the same frozen conditional source after later old-run edits', async () => {
    const f = conditionalFixture(), first = await f.seed();
    expect(first.failed).toEqual([]);
    const snapshotDigest = readSolverRunState(f.stateFile).continuationDigest;
    fs.writeFileSync(path.join(f.oldState.workers![1]!.worktree, f.projectRelative, 'Submission/Helpers.lean'), emptyHelpers);
    fs.writeFileSync(path.join(f.oldState.workers![1]!.worktree, 'RESEARCH.md'), 'Late historical edit');
    const second = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(second.failed).toEqual([]);
    expect(state.continuationDigest).toBe(snapshotDigest);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')?.status).toBe('conditional');
    expect(host.verify).toHaveBeenCalledTimes(6);
    const frozen = JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), snapshotDigest, 'conditional-bridge').text);
    expect(frozen.sources['Submission/Helpers.lean']).toContain('bridge_helper');
  });

  it.each(['phase', 'turns', 'thread', 'worker-turns', 'worker-session', 'existing-plan'])('rejects nonfresh target state: %s', async kind => {
    const f = fixture();
    if (kind === 'phase') f.newState.phase = 'running';
    if (kind === 'turns') f.newState.turns = 1;
    if (kind === 'thread') f.newState.threadId = 'some-thread';
    if (kind === 'worker-turns') f.newState.workers[1].turns = 1;
    if (kind === 'worker-session') f.newState.workers[1].sessionAssignmentId = 'some-assignment';
    if (kind === 'existing-plan') f.newState.cooperation = { tasks: [] };
    writeSolverRunState(f.stateFile, f.newState);
    await expect(f.seed()).rejects.toThrow('math_continuation_seed_requires_fresh_prepared_run');
    expect(host.verify).not.toHaveBeenCalled();
    expect(fs.existsSync(path.join(f.directory, 'continuation-seed-source.json'))).toBe(false);
  });

  it('refuses an active target lease even when the on-disk phase still says prepared', async () => {
    const f = fixture();
    await withMathRuntimeLease({ lockPath: path.join(f.directory, 'run.lock'), flockExecutable: '/usr/bin/flock' }, async () => {
      await expect(f.seed()).rejects.toThrow('math_runtime_lease_busy');
    });
    expect(host.verify).not.toHaveBeenCalled();
  });

  it.each(['task', 'receipt', 'source-policy', 'build'])('rejects mismatched identities: %s', async changed => {
    const f = fixture();
    if (changed === 'task') f.oldState.taskDigest = mathDigest('different task');
    if (changed === 'receipt') f.oldState.problem = { ...f.oldState.problem, receiptDigest: mathDigest('different receipt') };
    if (changed === 'source-policy') f.oldState.problem = { ...f.oldState.problem, sourceStructure: {} };
    if (changed === 'build') f.newState.buildDigest = mathDigest('different build');
    writeSolverRunState(f.sourceStateFile, f.oldState); writeSolverRunState(f.stateFile, f.newState);
    await expect(f.seed()).rejects.toThrow(changed === 'build' ? 'math_continuation_seed_build_changed' : 'math_continuation_seed_identity_changed');
    expect(host.verify).not.toHaveBeenCalled(); expect(git(f.worktree, ['rev-parse', 'HEAD'])).toBe(f.base);
  });

  it('does not promote historical acceptance when the fresh helper check fails', async () => {
    const f = fixture();
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => {
      const verified = verifiedBatch(request, { sessionId: 'fresh-seed', receipt: 'fresh-seed', checks: true });
      return request.items.some(item => item.theoremName.endsWith('second_helper'))
        ? failedBatch(verified, { stdoutPreview: () => 'error: unsolved goals' }) : verified;
    });
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['second']);
    expect(state.cooperation.tasks.map(node => node.status)).toEqual(['integrated', 'blocked', 'pending']);
    expect(state.cooperation.tasks[1].integratedCheck.passed).toBe(false);
  });

  it('requires new receipt identities even when a verifier reports kernel_verified', async () => {
    const f = fixture();
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => {
      const verified = verifiedBatch(request, { sessionId: 'fresh-seed', receipt: 'fresh-seed', checks: true });
      return { ...verified, results: verified.results.map(({ receiptId: _receipt, ...result }) => result) };
    });
    const report = await f.seed();
    expect(report.failed).toEqual(['first', 'second']);
    expect(readSolverRunState(f.stateFile).cooperation.tasks.some(node => node.status === 'integrated')).toBe(false);
  });

  it('rejects changed trusted canonical sources before freezing or checking them', async () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Challenge.lean'), 'theorem changed : False := by sorry\n');
    f.oldState.cooperation.canonicalCommit = commit(f.sourceWorktree, 'Invalid trusted change');
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await expect(f.seed()).rejects.toThrow('math_continuation_seed_source_policy_changed');
    expect(readSolverRunState(f.stateFile).cooperation).toBeUndefined();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('rejects frozen-original declaration changes in historical owned sources', async () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission.lean'), original.replace(': True', ': False'));
    f.oldState.cooperation.canonicalCommit = commit(f.sourceWorktree, 'Invalid original change');
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await expect(f.seed()).rejects.toThrow('math_original_declaration_changed');
    expect(readSolverRunState(f.stateFile).cooperation).toBeUndefined();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('does not overwrite new source work during a repeated initialization', async () => {
    const f = fixture(); await f.seed();
    const target = path.join(f.worktree, f.projectRelative, 'Submission/Helpers.lean');
    fs.appendFileSync(target, '\n-- New local proof work\n'); const edited = fs.readFileSync(target);
    await expect(f.seed()).rejects.toThrow('math_continuation_seed_destination_changed');
    expect(fs.readFileSync(target)).toEqual(edited);
  });

  it('leaves unfinished obligations pending on cancellation and retries the frozen capture', async () => {
    const f = fixture();
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    expect(host.dispose).toHaveBeenCalledOnce();
    const interrupted = readSolverRunState(f.stateFile);
    expect(interrupted.cooperation.tasks.map(node => node.status)).toEqual(['integrated', 'pending', 'pending']);
    fs.writeFileSync(path.join(f.oldDirectory, 'worktree-2', 'RESEARCH.md'), 'Newer old-run notes must not replace the frozen capture.');
    const report = await seedSolverContinuation({ ...f.options, signal: new AbortController().signal });
    expect(host.prepare).toHaveBeenCalledTimes(2);
    expect(host.dispose).toHaveBeenCalledTimes(2);
    expect(report.stage).toBe('complete');
    const state = readSolverRunState(f.stateFile), draft = JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'),
      state.continuationDigest, 'draft-prover-1').text);
    expect(draft.notes).toBe(f.notes);
  });

  it('recovers interrupted multi-file snapshot publication without importing any acceptance early', async () => {
    const f = fixture(), rename = fs.renameSync;
    const fail = vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
      if (String(to) === path.join(f.directory, 'continuation.json')) throw new Error('simulated snapshot publication failure');
      return rename(from, to);
    });
    await expect(f.seed()).rejects.toThrow('simulated snapshot publication failure');
    expect(readSolverRunState(f.stateFile).cooperation).toBeUndefined();
    expect(host.verify).not.toHaveBeenCalled(); fail.mockRestore();
    expect((await f.seed()).stage).toBe('complete');
  });

  it('rejects redirected worker draft files before reading or importing them', async () => {
    const f = fixture(), notes = path.join(f.oldDirectory, 'worktree-2', 'RESEARCH.md');
    fs.renameSync(notes, `${notes}.saved`); fs.symlinkSync(`${notes}.saved`, notes);
    await expect(f.seed()).rejects.toThrow('math_path_invalid');
    expect(readSolverRunState(f.stateFile).cooperation).toBeUndefined(); expect(host.verify).not.toHaveBeenCalled();
  });
});
