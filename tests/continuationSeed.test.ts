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
import * as taskProofs from '../src/solver/cooperativeProof';
import { hasTaskConnectionCheck } from '../src/solver/taskConnections';
import { captureResearchBasis, researchSourceDigest, settleResearch } from '../src/solver/researchRecords';
import { researchSourceTasks, scopedResearchSources } from '../src/solver/researchSources';
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

function replaceHelperCandidates(f: ReturnType<typeof fixture>, count: number) {
  const tasks: CooperativeTask[] = Array.from({ length: count }, (_, index) => ({ ...f.tasks[0]!,
    id: `helper_${index}`, objective: `Prove helper ${index}`, theoremName: `Submission.Helpers.helper_${index}` }));
  fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'),
    `namespace Submission.Helpers\n${tasks.map(task => `lemma ${task.id} : True := by trivial\n`).join('')}end Submission.Helpers\n`);
  const canonical = commit(f.sourceWorktree, 'Historical helper batch');
  const historical = f.oldState.cooperation!.tasks[0]!.integratedCheck!;
  f.oldState.cooperation!.canonicalCommit = canonical;
  f.oldState.cooperation!.tasks = [...tasks.map(task => ({ task, status: 'integrated' as const, attempts: 1,
    integratedCheck: { ...historical, commit: canonical, taskDigest: taskVersion(task) } })),
    { task: { ...f.tasks.at(-1)!, dependsOn: tasks.map(task => task.id) }, status: 'pending', attempts: 0 }];
  writeSolverRunState(f.sourceStateFile, f.oldState);
  return tasks;
}

function cooperationFor(f: ReturnType<typeof fixture>, state: SolverRunState, freshContinuationChecks: readonly TaskProof[] = []) {
  const workers = state.workers!.map(worker => ({ id: worker.id, role: worker.role, worktree: worker.worktree,
    ownedFiles: state.problem.ownedFiles }));
  const environment = { PATH: '/usr/bin:/bin', DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
    [MATH_PROOF_ENVIRONMENT_ENV]: 'live-host-proof-environment' };
  return cooperativeResearch({ state, workers, retrievalRoot: f.root, signal: f.controller.signal,
    freshContinuationChecks, access: new Map(workers.map(worker => [worker.id, { environment, retrievalRoot: f.root }])) });
}

function publishCompletedResearch(state: SolverRunState, taskId: string, id: string) {
  const node = state.cooperation!.tasks.find(node => node.task.id === taskId)!;
  const sources = Object.fromEntries(state.problem.ownedFiles.map(file => [file,
    committedSource(state.worktree, state.cooperation!.canonicalCommit!, `${state.problem.projectRelative}/${file}`)]));
  const basis = captureResearchBasis(node.task, { problemReceiptDigest: state.problem.receiptDigest,
    environmentDigest: state.environmentDigest, retrievalDigest: state.retrievalDigest, knowledgeDigest: state.knowledgeDigest,
    sourceDigest: researchSourceDigest(scopedResearchSources(state.problem, node.task, sources, researchSourceTasks(state.cooperation!.tasks))),
    tasks: state.cooperation!.tasks, deliveries: state.cooperation!.deliveries });
  node.assignment = { taskId, taskDigest: taskVersion(node.task), workerId: 'solver', assignmentId: id,
    seedCommit: state.cooperation!.canonicalCommit!, researchBasis: basis,
    dependencies: node.task.dependsOn.map(id => ({ taskId: id,
      taskDigest: taskVersion(state.cooperation!.tasks.find(node => node.task.id === id)!.task) })) };
  const record = settleResearch({ id, assignment: node.assignment, basis, commit: state.cooperation!.canonicalCommit!,
    finding: node.finding!, complete: true })!;
  node.status = 'completed'; node.researchCompletion = record;
  state.cooperation!.deliveries!.push({ id, producer: 'solver', taskId, taskDigest: taskVersion(node.task),
    kind: 'research', status: 'advisory', statement: node.task.objective, premises: [],
    dependencies: node.assignment.dependencies!, remainingObligations: [], summary: node.finding!, evidenceRefs: [],
    createdAt: state.cooperation!.deliveries!.length + 1, commit: state.cooperation!.canonicalCommit!,
    finding: node.finding, findingDigest: mathDigest(node.finding!), researchRecord: record });
  return record;
}

function completedResearchFixture(kind: 'research' | 'sketch' = 'research') {
  const f = fixture(), task: CooperativeTask = { id: 'route_research', kind,
    objective: 'Locate an exact route from the current helper to the original goal', dependsOn: ['first'], revision: 0 };
  const finding = JSON.stringify({ taskId: task.id, taskDigest: taskVersion(task), conclusion: 'inconclusive',
    summary: 'The helper does not close the original goal; the stated arithmetic gap remains.' });
  f.oldState.cooperation!.tasks.push({ task, status: 'completed', attempts: 16, finding,
    assignment: { taskId: task.id, taskDigest: taskVersion(task), workerId: 'solver', assignmentId: 'old-research',
      seedCommit: f.oldState.cooperation!.canonicalCommit!,
      dependencies: [{ taskId: 'first', taskDigest: taskVersion(f.tasks[0]!) }] } });
  const completion = publishCompletedResearch(f.oldState, task.id, 'old-research-completion');
  writeSolverRunState(f.sourceStateFile, f.oldState);
  return { ...f, task, finding, completion };
}

function nextContinuation(f: ReturnType<typeof fixture>, sourceStateFile: string, name: string) {
  const directory = path.join(f.root, `${name}.json.runtime`); fs.mkdirSync(directory, { mode: 0o700 });
  for (const part of ['worktree', 'worktree-2'])
    git(f.workspace, ['worktree', 'add', '--quiet', '--detach', path.join(directory, part), f.base]);
  const stateFile = path.join(directory, 'state.json');
  writeSolverRunState(stateFile, { ...f.newState, runId: name, worktree: path.join(directory, 'worktree'),
    workers: f.newState.workers!.map((worker, index) => ({ ...worker,
      worktree: path.join(directory, index ? 'worktree-2' : 'worktree') })) });
  const environmentFile = path.join(directory, 'environment-solver.json');
  fs.writeFileSync(environmentFile, canonicalMathJson(projectMathematicsRuntimeEnvironment({ PATH: '/usr/bin:/bin',
    DEEPSCIENTIST_MATH_ENV_FILE: environmentFile, DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages })), { mode: 0o400 });
  return { stateFile, directory, seed: () => seedSolverContinuation({ ...f.options, sourceRun: sourceStateFile, run: stateFile }) };
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
afterEach(() => { vi.restoreAllMocks(); vi.unstubAllEnvs(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

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
    expect(lifecycle).toEqual(['resolve-packages', 'prepare', 'verify', 'dispose']);
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
    expect(report.stage).toBe('complete'); expect(report.failed).toEqual([]); expect(host.verify).toHaveBeenCalledOnce();
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
    expect(host.verify).toHaveBeenCalledTimes(2);
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
    expect(host.verify).toHaveBeenCalledOnce();
    const cooperative = cooperationFor(f, state, proofs);
    try {
      await cooperative.restore();
      expect(host.verify).toHaveBeenCalledOnce();
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
      expect(host.verify).toHaveBeenCalledTimes(2);
      expect(host.verify.mock.calls[1][0].items.map(item => item.theoremName))
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
    expect(host.verify).toHaveBeenCalledOnce();
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')).toMatchObject({ status: 'integrated',
      integratedCheck: { passed: true } });
    expect(state.cooperation!.tasks.find(node => node.task.id === 'bridge')!.proof).toBeUndefined();
  });

  it('blocks only a conditional candidate whose saved assignment lost its dependencies', async () => {
    const f = conditionalFixture(), bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    delete bridge.assignment!.dependencies;
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['bridge']); expect(host.verify).toHaveBeenCalledOnce();
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
    expect(host.verify).toHaveBeenCalledOnce();
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
    expect(host.verify).toHaveBeenCalledOnce();
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
    expect(host.verify).toHaveBeenCalledTimes(4);
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
        ? failedBatch(verified, { stdoutPreview: () => 'error: unsolved goals',
          selected: result => result.theoremName === 'Submission.Helpers.second_helper' }) : verified;
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

describe('completed advisory research continuation', () => {
  it.each(['research', 'sketch'] as const)('retains unchanged completed %s and finding without replaying proof or session authority', async kind => {
    const f = completedResearchFixture(kind), prior = f.oldState.cooperation!.tasks.at(-1)!;
    prior.proof = prior.integratedCheck = f.oldState.cooperation!.tasks[0]!.integratedCheck;
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    const retained = state.cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    expect(retained).toMatchObject({ status: 'completed', attempts: 0, finding: f.finding });
    expect(retained.researchCompletion).toEqual(f.completion);
    expect(retained.assignment).toBeUndefined(); expect(retained.proof).toBeUndefined(); expect(retained.integratedCheck).toBeUndefined();
    expect(state.workers!.every(worker => !worker.threadId && !worker.sessionTaskId && !worker.sessionAssignmentId)).toBe(true);
    expect(report.checked).toEqual(['first', 'second']);
    expect(state.cooperation!.tasks[0]!.integratedCheck!.verification.results[0]!.receiptId).not.toBe('old-first');
    expect(state.cooperation!.tasks.find(node => node.task.id === 'goal')?.status).toBe('pending');
    expect(JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), state.continuationDigest,
      'seed-completed-research').text)[0]).toMatchObject({ task: { id: f.task.id }, finding: f.finding });
    await f.seed();
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id)?.researchCompletion).toEqual(f.completion);
  });

  it('does not bind research completed on A to canonical sources B before the first continuation', async () => {
    const f = completedResearchFixture();
    fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'),
      helpers.replace('end Submission.Helpers', 'lemma later_input : True := by trivial\nend Submission.Helpers'));
    f.oldState.cooperation!.canonicalCommit = commit(f.sourceWorktree, 'Canonical B after research completed on A');
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await f.seed(); const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)).toMatchObject({ status: 'pending' });
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ finding: f.finding, researchCompletion: f.completion }));
    const frozen = JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), state.continuationDigest,
      'seed-completed-research').text);
    expect(frozen[0].record).toEqual(f.completion);
  });

  it('compares the same scoped source bytes that were supplied to the research assignment', async () => {
    const f = completedResearchFixture();
    for (const node of f.oldState.cooperation!.tasks) {
      node.task = { ...node.task, sharing: 'problem' };
      if (node.integratedCheck) node.integratedCheck = { ...node.integratedCheck, taskDigest: taskVersion(node.task) };
    }
    const privateTask: CooperativeTask = { ...f.tasks[0]!, id: 'private_helper', groupId: 'private', sharing: 'group',
      theoremName: 'Submission.Helpers.private_helper', ownerId: undefined };
    f.oldState.cooperation!.groups!.push({ group: { id: 'private', objective: 'Independent private route',
      status: 'active', revision: 0 }, turns: 0 });
    f.oldState.cooperation!.tasks.push({ task: privateTask, status: 'pending', attempts: 0 });
    fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission/Helpers.lean'),
      helpers.replace('end Submission.Helpers', 'lemma private_helper : True := by trivial\nend Submission.Helpers'));
    f.oldState.cooperation!.canonicalCommit = commit(f.sourceWorktree, 'Unrelated private canonical helper');
    const completion = publishCompletedResearch(f.oldState, f.task.id, 'scoped-research-completion');
    expect(completion.basis.sourceDigest).not.toBe(researchSourceDigest(Object.fromEntries(f.oldState.problem.ownedFiles.map(file => [file,
      committedSource(f.sourceWorktree, f.oldState.cooperation!.canonicalCommit!, `${f.projectRelative}/${file}`)]))));
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    const retained = readSolverRunState(f.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    expect(retained).toMatchObject({ status: 'completed', finding: f.finding });
    expect(retained.researchCompletion).toEqual(completion);
  });

  it('reopens research when a dependency publishes a new finding without changing its task version', async () => {
    const f = completedResearchFixture(), node = f.oldState.cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    const input: CooperativeTask = { id: 'input_research', kind: 'research', objective: 'Find the missing arithmetic condition',
      revision: 0, dependsOn: [] };
    f.oldState.cooperation!.tasks.push({ task: input, status: 'completed', attempts: 1, finding: 'Old arithmetic condition.' });
    publishCompletedResearch(f.oldState, input.id, 'input-old');
    node.task = { ...node.task, dependsOn: [input.id] };
    const completion = publishCompletedResearch(f.oldState, node.task.id, 'route-before-new-input');
    const dependency = f.oldState.cooperation!.tasks.find(node => node.task.id === input.id)!;
    dependency.finding = 'A new counterexample refutes the old arithmetic condition.';
    publishCompletedResearch(f.oldState, input.id, 'input-new');
    expect(taskVersion(dependency.task)).toBe(taskVersion(input));
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(record => record.task.id === node.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ finding: f.finding, researchCompletion: completion }));
    expect(state.cooperation!.deliveries!.some(delivery => delivery.id === 'input-new' && delivery.finding === dependency.finding)).toBe(true);
  });

  it('preserves a fresh same-text completion at B by its own publication identity across generations', async () => {
    const f = completedResearchFixture(); await f.seed();
    const source = readSolverRunState(f.stateFile), node = source.cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    fs.writeFileSync(path.join(source.worktree, f.projectRelative, 'Submission/Helpers.lean'),
      helpers.replace('end Submission.Helpers', 'lemma recompletion_input : True := by trivial\nend Submission.Helpers'));
    source.cooperation!.canonicalCommit = commit(source.worktree, 'Canonical B before fresh completion');
    const completion = publishCompletedResearch(source, node.task.id, 'fresh-completion-at-B');
    expect(node.finding).toBe(f.finding); expect(completion.basis.sourceDigest).not.toBe(f.completion.basis.sourceDigest);
    writeSolverRunState(f.stateFile, source);
    const second = nextContinuation(f, f.stateFile, 'same-text-at-B'); await second.seed();
    const third = nextContinuation(f, second.stateFile, 'same-text-at-B-again'); await third.seed();
    const state = readSolverRunState(third.stateFile), retained = state.cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    expect(retained).toMatchObject({ status: 'completed', finding: f.finding });
    expect(retained.researchCompletion).toEqual(completion);
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ researchCompletion: f.completion }));
  });

  it('retains a dependency research event without lemma proposals and reopens for a changed event', async () => {
    const f = completedResearchFixture();
    const event = { id: 'dependency-event', producer: 'prover-1', taskId: 'first', taskDigest: taskVersion(f.tasks[0]!),
      kind: 'research' as const, status: 'advisory' as const, statement: 'Arithmetic obstruction', premises: [], dependencies: [],
      remainingObligations: [], summary: 'The event supplies an independent local obstruction.', evidenceRefs: [], createdAt: 10,
      finding: 'Complete dependency-event finding', findingDigest: mathDigest('Complete dependency-event finding') };
    f.oldState.cooperation!.deliveries!.push(event);
    const completion = publishCompletedResearch(f.oldState, f.task.id, 'completion-using-event');
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    const second = nextContinuation(f, f.stateFile, 'event-generation'); await second.seed();
    const source = readSolverRunState(second.stateFile);
    expect(source.cooperation!.tasks.find(node => node.task.id === f.task.id)?.researchCompletion).toEqual(completion);
    expect(source.cooperation!.deliveries).toContainEqual(expect.objectContaining(event));
    source.cooperation!.deliveries!.push({ ...event, id: 'new-dependency-event', summary: 'New contradictory evidence.',
      finding: 'New complete finding', findingDigest: mathDigest('New complete finding'), createdAt: 11 });
    writeSolverRunState(second.stateFile, source);
    const third = nextContinuation(f, second.stateFile, 'changed-event-generation'); await third.seed();
    expect(readSolverRunState(third.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
  });

  it('reopens research when its former proof input fails the independent seed recheck', async () => {
    const f = completedResearchFixture();
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => failedBatch(request));
    await f.seed(); const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ researchCompletion: f.completion }));
    await f.seed();
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
  });

  it('keeps legacy completed research without a publication basis as history', async () => {
    const f = completedResearchFixture(); delete f.oldState.cooperation!.tasks.at(-1)!.researchCompletion;
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: f.task, finding: f.finding }));
  });

  it.each(['environmentDigest', 'retrievalDigest', 'knowledgeDigest'] as const)('reopens research for a changed %s and retains the finding as history', async field => {
    const f = completedResearchFixture();
    f.newState[field] = mathDigest(`changed-${field}`); writeSolverRunState(f.stateFile, f.newState);
    await f.seed(); const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)).toMatchObject({ status: 'pending', attempts: 0 });
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.finding).toBeUndefined();
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: f.task, finding: f.finding }));
  });

  it('retains completed research across generations, but reopens it when its dependency or canonical sources change', async () => {
    const f = completedResearchFixture(); await f.seed();
    const second = nextContinuation(f, f.stateFile, 'second-generation'); await second.seed();
    let state = readSolverRunState(second.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)).toMatchObject({ status: 'completed', finding: f.finding });
    const dependency = state.cooperation!.tasks.find(node => node.task.id === 'first')!;
    dependency.task = { ...dependency.task, revision: dependency.task.revision + 1 };
    writeSolverRunState(second.stateFile, state);
    const third = nextContinuation(f, second.stateFile, 'third-generation'); await third.seed();
    state = readSolverRunState(third.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: f.task, finding: f.finding }));

    state = readSolverRunState(f.stateFile);
    fs.writeFileSync(path.join(state.worktree, f.projectRelative, 'Submission/Helpers.lean'),
      helpers.replace('end Submission.Helpers', 'lemma new_input : True := by trivial\nend Submission.Helpers'));
    state.cooperation!.canonicalCommit = commit(state.worktree, 'New canonical research input');
    writeSolverRunState(f.stateFile, state);
    const changedSources = nextContinuation(f, f.stateFile, 'changed-sources'); await changedSources.seed();
    expect(readSolverRunState(changedSources.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
  });

  it('does not revive an archived completion after a later explicit reopen', async () => {
    const f = completedResearchFixture(); await f.seed();
    const source = readSolverRunState(f.stateFile), node = source.cooperation!.tasks.find(node => node.task.id === f.task.id)!;
    node.task = { ...node.task, revision: 1 }; node.status = 'pending'; node.finding = undefined;
    writeSolverRunState(f.stateFile, source);
    const second = nextContinuation(f, f.stateFile, 'reopened-generation'); await second.seed();
    const third = nextContinuation(f, second.stateFile, 'still-reopened-generation'); await third.seed();
    const state = readSolverRunState(third.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)).toMatchObject({ task: { revision: 1 }, status: 'pending' });
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: f.task, finding: f.finding }));
  });

  it.each(['pending', 'running', 'blocked'] as const)('does not preserve a %s research attempt as completed', async status => {
    const f = completedResearchFixture(); f.oldState.cooperation!.tasks.at(-1)!.status = status;
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.find(node => node.task.id === f.task.id))
      .toMatchObject({ status: 'pending', attempts: 0 });
  });

  it.each(['task', 'dependency'] as const)('reopens a stale completed research assignment after a changed %s contract', async changed => {
    const f = completedResearchFixture(), node = f.oldState.cooperation!.tasks.find(node => node.task.id ===
      (changed === 'task' ? f.task.id : 'first'))!;
    node.task = { ...node.task, revision: 1 };
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ finding: f.finding }));
  });

  it.each(['final-candidate', 'feasibility', 'legacy-final-candidate'] as const)('requires a new %s review', async scope => {
    const f = completedResearchFixture(), node = f.oldState.cooperation!.tasks.at(-1)!;
    node.task = scope === 'legacy-final-candidate' ? { ...node.task, id: 'independent_candidate_review' } :
      { ...node.task, reviewScope: scope };
    writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.find(task => task.task.id === node.task.id)?.status).toBe('pending');
  });

  it('loads a legacy frozen source without completion identity conservatively', async () => {
    const f = completedResearchFixture(), rename = fs.renameSync;
    const fail = vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
      if (String(to) === path.join(f.directory, 'continuation.json')) throw new Error('stop before snapshot publication');
      return rename(from, to);
    });
    await expect(f.seed()).rejects.toThrow('stop before snapshot publication'); fail.mockRestore();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json');
    const source = JSON.parse(fs.readFileSync(sourceFile, 'utf8')); delete source.completedResearch;
    fs.chmodSync(sourceFile, 0o600); fs.writeFileSync(sourceFile, canonicalMathJson(source)); fs.chmodSync(sourceFile, 0o400);
    await f.seed(); const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.tasks[0]!.status).toBe('integrated');
    expect(readContinuationPage(path.join(f.directory, 'continuation.json'), state.continuationDigest, 'seed-history').text).toContain(f.finding.replaceAll('"', '\\"'));
  });

  it('reads a legacy snapshot inputDigest as historical evidence without rebinding it to current inputs', async () => {
    const f = completedResearchFixture(), rename = fs.renameSync;
    const fail = vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
      if (String(to) === path.join(f.directory, 'continuation.json')) throw new Error('freeze legacy completion fixture');
      return rename(from, to);
    });
    await expect(f.seed()).rejects.toThrow('freeze legacy completion fixture'); fail.mockRestore();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json');
    const source = JSON.parse(fs.readFileSync(sourceFile, 'utf8'));
    source.completedResearch = [{ task: f.task, finding: f.finding, inputDigest: mathDigest('legacy guessed binding') }];
    delete source.researchContext;
    fs.chmodSync(sourceFile, 0o600); fs.writeFileSync(sourceFile, canonicalMathJson(source)); fs.chmodSync(sourceFile, 0o400);
    await f.seed(); const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.find(node => node.task.id === f.task.id)?.status).toBe('pending');
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: f.task, finding: f.finding }));
    expect(state.cooperation!.history!.every(item => !item.researchCompletion)).toBe(true);
  });
});

describe('bounded continuation verification batches', () => {
  it('checks identical helper projections once and preserves each target receipt and type', async () => {
    const f = fixture(); host.verify.mockImplementation(freshReceipts);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual([]); expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName))
      .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
    expect(host.verify.mock.calls[0][1].expectedDeclarationTypes).toEqual({
      'Submission.Helpers.first_helper': 'True', 'Submission.Helpers.second_helper': 'True' });
    const proofs = state.cooperation!.tasks.slice(0, 2).map(node => node.integratedCheck!);
    expect(proofs.map(proof => proof.verification.results.map(result => result.theoremName)))
      .toEqual([['Submission.Helpers.first_helper'], ['Submission.Helpers.second_helper']]);
    expect(proofs.map(proof => proof.taskDigest)).toEqual(f.tasks.slice(0, 2).map(taskVersion));
    expect(new Set(proofs.map(proof => proof.verification.results[0]!.receiptId)).size).toBe(2);
    expect(state.cooperation!.tasks.slice(0, 2).every(node => node.status === 'integrated')).toBe(true);
  });

  it('keeps different full projections separate even when candidates share the canonical commit', async () => {
    const f = fixture();
    fs.writeFileSync(path.join(f.sourceWorktree, f.projectRelative, 'Submission.lean'), original.replace('by sorry', 'by trivial'));
    const canonical = commit(f.sourceWorktree, 'Historical original proof');
    f.oldState.cooperation!.canonicalCommit = canonical;
    const goal = f.oldState.cooperation!.tasks.find(node => node.task.kind === 'goal')!;
    goal.status = 'integrated'; goal.integratedCheck = { ...f.oldState.cooperation!.tasks[0]!.integratedCheck!,
      commit: canonical, taskDigest: taskVersion(goal.task) };
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const check = vi.spyOn(taskProofs, 'checkTaskProofs');
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => {
      const source = committedSource(f.worktree, request.targetCommit!, `${f.projectRelative}/Submission.lean`);
      if (request.items.some(item => item.theoremName === 'Submission.original')) expect(source).toContain('theorem original');
      else expect(source).not.toContain('theorem original');
      return freshReceipts(request);
    });
    const report = await f.seed();
    expect(report.failed).toEqual([]);
    expect(check.mock.calls.map(call => call[3].map(request => request.task.id))).toEqual([['first', 'second'], ['goal']]);
    expect(new Set(check.mock.calls.map(call => call[2])).size).toBe(1);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.every(node => node.status === 'integrated')).toBe(true);
  });

  it('includes each conditional target and typed assumptions in the grouping projection', async () => {
    // Reconstructed copies of identical saved sources must have the same commit
    // identity, so this exercises projection grouping beyond the source commit.
    vi.stubEnv('GIT_AUTHOR_DATE', '2000-01-01T00:00:00Z'); vi.stubEnv('GIT_COMMITTER_DATE', '2000-01-01T00:00:00Z');
    const f = conditionalFixture(), worker = f.oldState.workers![1]!.worktree;
    const file = path.join(worker, f.projectRelative, 'Submission/Helpers.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('end Submission.Helpers',
      'lemma bridge_first_helper : True := by exact first_helper\nend Submission.Helpers'));
    const proofCommit = commit(worker, 'Historical bridges with different assumptions');
    const bridge = f.oldState.cooperation!.tasks.find(node => node.task.id === 'bridge')!;
    bridge.proof!.commit = proofCommit;
    const task = { ...f.task, id: 'bridge_first', theoremName: 'Submission.Helpers.bridge_first_helper', dependsOn: ['first'] };
    const condition = { taskId: 'first', taskDigest: taskVersion(f.tasks[0]!) };
    f.oldState.cooperation!.tasks.push({ task, status: 'conditional', attempts: 1,
      assignment: { ...bridge.assignment!, taskId: task.id, taskDigest: taskVersion(task), dependencies: [condition] },
      proof: { ...bridge.proof!, taskDigest: taskVersion(task), conditions: [condition] } });
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const check = vi.spyOn(taskProofs, 'checkTaskProofs'); host.verify.mockImplementation(freshReceipts);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual([]);
    expect(check.mock.calls.map(call => call[3].map(request => request.task.id)))
      .toEqual([['first', 'second'], ['bridge'], ['bridge_first']]);
    const conditionalGroups = check.mock.calls.filter(call => call[3].some(request => request.conditions?.length));
    expect(conditionalGroups).toHaveLength(2); expect(new Set(conditionalGroups.map(call => call[2])).size).toBe(1);
    expect(host.verify.mock.calls.slice(1).map(([, options]) => options.expectedDeclarationType))
      .toEqual(['∀ (second_helper : True), True', '∀ (first_helper : True), True']);
    expect(state.cooperation!.tasks.filter(node => node.task.id.startsWith('bridge')).map(node => node.status))
      .toEqual(['conditional', 'conditional']);
  });

  it('limits identical projections to batches of 32 and executes only one group at a time', async () => {
    const f = fixture(), tasks = replaceHelperCandidates(f, 33), check = taskProofs.checkTaskProofs;
    let active = 0, peak = 0;
    vi.spyOn(taskProofs, 'checkTaskProofs').mockImplementation(async (...args) => {
      active++; peak = Math.max(peak, active);
      try { return await check(...args); } finally { active--; }
    });
    host.verify.mockImplementation(freshReceipts);
    const report = await f.seed();
    expect(report.failed).toEqual([]);
    expect(host.verify.mock.calls.map(([request]) => request.items.length)).toEqual([32, 1]);
    expect(host.verify.mock.calls.flatMap(([request]) => request.items.map(item => item.theoremName)))
      .toEqual(tasks.map(task => task.theoremName));
    expect(peak).toBe(1);
    expect(readSolverRunState(f.stateFile).cooperation!.tasks.filter(node => node.status === 'integrated')).toHaveLength(33);
  });

  it('isolates a candidate that fails projection preflight while batching healthy helpers', async () => {
    const f = fixture(), task = { ...f.tasks[0]!, id: 'missing', theoremName: 'Submission.Helpers.missing_helper' };
    f.oldState.cooperation!.tasks.splice(1, 0, { task, status: 'integrated', attempts: 1,
      integratedCheck: { ...f.oldState.cooperation!.tasks[0]!.integratedCheck!, taskDigest: taskVersion(task) } });
    writeSolverRunState(f.sourceStateFile, f.oldState);
    host.verify.mockImplementation(freshReceipts);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.failed).toEqual(['missing']); expect(report.checked).toHaveLength(3);
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName))
      .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
    expect(state.cooperation!.tasks.find(node => node.task.id === 'missing')).toMatchObject({ status: 'blocked',
      feedback: expect.stringContaining('math_task_missing_declaration') });
    expect(state.cooperation!.tasks.filter(node => ['first', 'second'].includes(node.task.id))
      .every(node => node.status === 'integrated')).toBe(true);
  });

  it('falls back to isolated checks when a planned batch rejects its projection match', async () => {
    const f = fixture(), check = taskProofs.checkTaskProofs;
    const attempts = vi.spyOn(taskProofs, 'checkTaskProofs').mockImplementation(async (...args) => {
      if (args[3].length > 1) throw new Error('math_task_batch_projection_mismatch');
      return check(...args);
    });
    host.verify.mockImplementation(freshReceipts);
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(attempts.mock.calls.map(call => call[3].length)).toEqual([2, 1, 1]);
    expect(host.verify.mock.calls.map(([request]) => request.items.length)).toEqual([1, 1]);
    expect(report.failed).toEqual([]); expect(report.checked).toEqual(['first', 'second']);
    expect(state.cooperation!.tasks.slice(0, 2).every(node => node.status === 'integrated')).toBe(true);
  });

  it('verifies every target again on initialization retry even when the saved report checked them all', async () => {
    const f = fixture(); let verification = 0;
    host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => {
      const sessionId = `seed-attempt-${++verification}`;
      return receiptBatch(request, { sessionId, receiptId: (_, name) => `${sessionId}-${name}` });
    });
    expect((await f.seed()).checked).toEqual(['first', 'second']);
    const before = readSolverRunState(f.stateFile), frozenFile = path.join(f.directory, 'continuation-seed-source.json');
    const frozen = fs.readFileSync(frozenFile), oldReceipt = before.cooperation!.tasks[0]!.integratedCheck!.verification.results[0]!.receiptId;
    host.verify.mockClear();
    const report = await f.seed(), state = readSolverRunState(f.stateFile);
    expect(report.checked).toEqual(['first', 'second']); expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName))
      .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
    expect(state.cooperation!.tasks[0]!.integratedCheck!.verification.results[0]!.receiptId).not.toBe(oldReceipt);
    expect(state.continuationDigest).toBe(before.continuationDigest); expect(fs.readFileSync(frozenFile)).toEqual(frozen);
  });

  it('retains the run lease and proof environment until an aborted batch verification settles', async () => {
    const f = fixture();
    let entered!: () => void, release!: () => void;
    const checking = new Promise<void>(resolve => { entered = resolve; });
    const gate = new Promise<void>(resolve => { release = resolve; });
    host.verify.mockImplementation(async (request: MathematicsVerifierBatchRequest) => {
      entered(); await gate; return freshReceipts(request);
    });
    const running = f.seed(), settled = running.then(() => 'fulfilled', () => 'rejected');
    try {
      await Promise.race([checking, settled.then(status => { throw new Error(`seed_${status}_before_batch_verification`); })]);
      expect(host.verify).toHaveBeenCalledOnce(); expect(host.verify.mock.calls[0][0].items).toHaveLength(2);
      f.controller.abort();
      await expect(withMathRuntimeLease({ lockPath: path.join(f.directory, 'run.lock'),
        flockExecutable: '/usr/bin/flock' }, async () => undefined)).rejects.toThrow('math_runtime_lease_busy');
      expect(host.dispose).not.toHaveBeenCalled();
      expect(readSolverRunState(f.stateFile).cooperation!.tasks.every(node => node.status === 'pending')).toBe(true);
    } finally {
      release(); await settled;
    }
    await expect(running).rejects.toThrow();
    expect(host.dispose).toHaveBeenCalledOnce();
    const state = readSolverRunState(f.stateFile);
    expect(state.phase).toBe('prepared');
    expect(state.cooperation!.tasks.every(node => node.status === 'pending' && !node.integratedCheck && !node.proof)).toBe(true);
    expect(JSON.parse(fs.readFileSync(path.join(f.directory, 'continuation-seed.json'), 'utf8')).checked).toEqual([]);
    await withMathRuntimeLease({ lockPath: path.join(f.directory, 'run.lock'),
      flockExecutable: '/usr/bin/flock' }, async () => undefined);
  });
});
