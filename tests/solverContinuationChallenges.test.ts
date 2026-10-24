import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';
import { canonicalMathJson, mathDigest } from '../src/math/mathRuntimeIo';
import { projectMathematicsRuntimeEnvironment } from '../src/math/mathRuntimeEnvironment';
import { MATH_PROOF_ENVIRONMENT_ENV } from '../src/math/mathProofEnvironment';
import type { MathematicsVerifierBatchRequest } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { seedSolverContinuation } from '../src/solver/continuationSeed';
import { createCapacityExploration } from '../src/solver/capacityExploration';
import { readContinuationSnapshot } from '../src/solver/continuationInput';
import { git, readSolverProblem } from '../src/solver/problem';
import { markTaskAcceptance, taskVersion, type CooperativeTask } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { pendingResearchChallenges, researchChallenges, resolveResearchChallenges,
  type ResearchChallengeDecision } from '../src/solver/researchChallenges';
import { verifiedBatch } from './helpers/verifier';

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
  tasks.push({ id: 'goal', kind: 'goal', objective: 'Prove original', dependsOn: [], revision: 0,
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


beforeEach(() => {
  host.build.mockReset(); host.verify.mockReset(); host.prepare.mockReset(); host.dispose.mockReset(); host.resolvePackages.mockReset();
  host.resolvePackages.mockImplementation(() => host.packages);
  host.dispose.mockResolvedValue(undefined);
  host.prepare.mockResolvedValue({ environmentValue: 'fresh-handoff-seed-environment', dispose: host.dispose,
    stats: { files: 0, bytes: 0, publications: 1 } });
  host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => verifiedBatch(request,
    { sessionId: 'fresh-handoff-seed', receipt: 'fresh-handoff-seed', checks: true }));
});
afterEach(() => { vi.restoreAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

type Fixture = ReturnType<typeof fixture>;
function challengeFixture(status: ResearchChallengeDecision['status'] = 'disputed') {
  const f = fixture(), archive = f.oldState.cooperation!;
  const goal = archive.tasks.find(node => node.task.id === 'goal')!;
  goal.task = { ...goal.task, dependsOn: ['first'] };
  archive.proofRoutes = [{ id: 'route', targetTaskId: 'goal', closingTaskId: 'first', prerequisiteTaskIds: [] }];
  const task: CooperativeTask = { id: 'review', kind: 'research', objective: 'Check the proposed route',
    groupId: 'main', dependsOn: ['goal'], revision: 0, reviewScope: 'feasibility' };
  const finding = JSON.stringify({ taskId: task.id, conclusion: 'refuted', needsDecision: true,
    summary: 'A checked premise is missing', evidenceRefs: ['immutable-counterexample'] });
  archive.tasks.push({ task, finding, status: 'completed', attempts: 1 });
  const delivery: DeliveryRecord = { id: 'route-counterexample', producer: 'solver', taskId: task.id,
    taskDigest: taskVersion(task), groupId: 'main', kind: 'research', status: 'advisory', statement: task.objective,
    premises: [], dependencies: [{ taskId: 'goal', taskDigest: taskVersion(goal.task) }], remainingObligations: ['goal'],
    summary: 'A checked premise is missing', finding, findingDigest: mathDigest(finding),
    evidenceRefs: ['immutable-counterexample'], createdAt: 1, commit: archive.canonicalCommit };
  archive.deliveries!.push(delivery);
  if (status === 'deferred') {
    const waiting = archive.tasks.find(node => node.task.id === 'second')!;
    waiting.status = 'pending'; waiting.integratedCheck = undefined;
  }
  const [challenge] = pendingResearchChallenges(archive);
  archive.challengeDecisions = resolveResearchChallenges(archive, [challenge.id],
    { [challenge.id]: challenge.activationDigest }, archive.tasks.map(node => node.task), [{ id: challenge.id,
      status, reason: `Pinned ${status} rationale`, ...(status === 'disputed' ? { evidenceRefs: ['fixed-counterargument'] } : {}),
      ...(status === 'deferred' ? { waitsOn: ['second'], reopenOn: 'The required new bound is checked.' } : {}) }]);
  writeSolverRunState(f.sourceStateFile, f.oldState);
  return { ...f, delivery, challenge, decision: archive.challengeDecisions[0]! };
}
function nextGeneration(f: Fixture, sourceRun = f.stateFile, name = 'next') {
  const directory = path.join(f.root, `${name}.json.runtime`); fs.mkdirSync(directory, { mode: 0o700 });
  const worktree = path.join(directory, 'worktree');
  for (const workerName of ['worktree', 'worktree-2']) git(f.workspace,
    ['worktree', 'add', '--quiet', '--detach', path.join(directory, workerName), f.base]);
  const buildFile = path.join(f.root, `${name}-manifest.json`);
  fs.writeFileSync(buildFile, JSON.stringify({ fixture: `${name}-build` }), { mode: 0o400 });
  const stateFile = path.join(directory, 'state.json'), state: SolverRunState = { ...f.newState,
    runId: `${name}-run`, buildDigest: mathDigest(fs.readFileSync(buildFile)), methodDigest: `${name}-method`, worktree,
    workers: f.newState.workers!.map((worker, index) => ({ ...worker,
      worktree: path.join(directory, index ? `worktree-${index + 1}` : 'worktree') })) };
  writeSolverRunState(stateFile, state);
  const environmentFile = path.join(directory, 'environment-solver.json');
  fs.writeFileSync(environmentFile, canonicalMathJson(projectMathematicsRuntimeEnvironment({ PATH: '/usr/bin:/bin',
    DEEPSCIENTIST_MATH_ENV_FILE: environmentFile, DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
    [MATH_PROOF_ENVIRONMENT_ENV]: 'disposed-next-startup-fixture' })), { mode: 0o400 });
  const options = { ...f.options, sourceRun, run: stateFile, buildManifest: buildFile };
  return { directory, stateFile, options, seed: () => seedSolverContinuation(options) };
}

/** Freeze the historical format before publication, then run its real initializer. */
async function seedLegacyCapsule(f: Fixture) {
  const rename = fs.renameSync;
  const fail = vi.spyOn(fs, 'renameSync').mockImplementation((from, to) => {
    if (String(to) === path.join(f.directory, 'continuation.json')) throw new Error('freeze historical capsule');
    return rename(from, to);
  });
  try { await expect(f.seed()).rejects.toThrow('freeze historical capsule'); } finally { fail.mockRestore(); }
  const file = path.join(f.directory, 'continuation-seed-source.json');
  const source = JSON.parse(fs.readFileSync(file, 'utf8'));
  delete source.researchChallengeDecisions;
  fs.chmodSync(file, 0o600); fs.writeFileSync(file, canonicalMathJson(source)); fs.chmodSync(file, 0o400);
  await f.seed();
  return { file, bytes: fs.readFileSync(file), snapshot: fs.readFileSync(path.join(f.directory, 'continuation.json')) };
}

describe('research challenge continuation decisions', () => {
  it.each(['revised', 'disputed', 'deferred'] as const)(
    'preserves an exact %s verdict without reopening it or importing old proof acceptance', async status => {
      const f = challengeFixture(status), sourceBytes = fs.readFileSync(f.sourceStateFile);
      const report = await f.seed(), state = readSolverRunState(f.stateFile), archive = state.cooperation!;
      expect(report.failed).toEqual([]);
      expect(report.checked).toEqual(status === 'deferred' ? ['first'] : ['first', 'second']);
      expect(archive.challengeDecisions).toEqual([f.decision]);
      expect(researchChallenges(archive)).toMatchObject([{ id: f.challenge.id, status, decision: f.decision }]);
      expect(pendingResearchChallenges(archive)).toEqual([]);
      expect(archive.tasks.find(node => node.task.id === 'goal')!.status).toBe('pending');
      expect(archive.tasks[0]!.integratedCheck!.verification.results[0]!.receiptId).toContain('fresh-handoff-seed-');
      expect(fs.readFileSync(f.sourceStateFile)).toEqual(sourceBytes);
    });

  it.each(['route', 'context', 'waiting'] as const)(
    'reopens the challenge rather than rebinding the old verdict after a %s change', async changed => {
      const f = challengeFixture(changed === 'waiting' ? 'deferred' : 'disputed'), archive = f.oldState.cooperation!;
      if (changed === 'route') archive.proofRoutes![0] = { ...archive.proofRoutes![0]!, closingTaskId: 'second' };
      if (changed === 'context') f.delivery.commit = f.base;
      if (changed === 'waiting') {
        const waiting = archive.tasks.find(node => node.task.id === 'second')!;
        waiting.task = { ...waiting.task, type: 'True ∧ True', revision: 1 };
      }
      writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
      const restored = readSolverRunState(f.stateFile).cooperation!;
      expect(pendingResearchChallenges(restored)).toMatchObject([{ id: f.challenge.id }]);
      expect(researchChallenges(restored)[0]!.decision).toBeUndefined();
    });

  it.each(['source', 'dependency', 'environment'] as const)(
    'keeps a stale %s finding as superseded history without adopting its old verdict', async changed => {
      const f = challengeFixture(), archive = f.oldState.cooperation!;
      if (changed === 'source' || changed === 'dependency') {
        const node = archive.tasks.find(node => node.task.id === (changed === 'source' ? 'review' : 'goal'))!;
        node.task = { ...node.task, revision: 1, objective: 'A revised mathematical question' };
      } else {
        f.newState.environmentDigest = mathDigest('changed-environment'); writeSolverRunState(f.stateFile, f.newState);
      }
      writeSolverRunState(f.sourceStateFile, f.oldState); await f.seed();
      const restored = readSolverRunState(f.stateFile).cooperation!;
      expect(restored.deliveries!.find(item => item.id === f.delivery.id)!.status).toBe('superseded');
      expect(researchChallenges(restored)).toEqual([]);
      expect(restored.challengeDecisions ?? []).toEqual([]);
    });

  it('waits for fresh acceptance rather than an archived proof flag before reopening a deferred verdict', async () => {
    const f = challengeFixture('deferred'); await f.seed();
    const state = readSolverRunState(f.stateFile), archive = state.cooperation!;
    expect(pendingResearchChallenges(archive)).toEqual([]);
    const waiting = archive.tasks.find(node => node.task.id === 'second')!;
    const proof: TaskProof = { ...archive.tasks[0]!.integratedCheck!, taskDigest: taskVersion(waiting.task) };
    waiting.status = 'integrated'; waiting.integratedCheck = JSON.parse(JSON.stringify(proof));
    expect(pendingResearchChallenges(archive)).toEqual([]);
    markTaskAcceptance(waiting.integratedCheck!);
    expect(pendingResearchChallenges(archive)).toMatchObject([{ id: f.challenge.id, decision: f.decision }]);
    const restored: typeof archive = JSON.parse(JSON.stringify(archive));
    expect(pendingResearchChallenges(restored)).toEqual([]);
  });

  it('retries the frozen verdict after interruption independently of later live source changes', async () => {
    const f = challengeFixture();
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const digest = readSolverRunState(f.stateFile).continuationDigest;
    f.oldState.cooperation!.challengeDecisions = []; f.oldState.cooperation!.deliveries = [];
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await seedSolverContinuation({ ...f.options, signal: new AbortController().signal });
    const restored = readSolverRunState(f.stateFile);
    expect(restored.cooperation!.challengeDecisions).toEqual([f.decision]);
    expect(pendingResearchChallenges(restored.cooperation!)).toEqual([]);
    expect(restored.continuationDigest).toBe(digest); expect(fs.readFileSync(sourceFile)).toEqual(frozen);
  });

  it('preserves valid decisions through two consecutive public continuation migrations', async () => {
    const f = challengeFixture(); await f.seed();
    const second = nextGeneration(f); await second.seed();
    const third = nextGeneration(f, second.stateFile, 'third'); await third.seed();
    for (const file of [f.stateFile, second.stateFile, third.stateFile]) {
      const archive = readSolverRunState(file).cooperation!;
      expect(archive.challengeDecisions).toEqual([f.decision]);
      expect(pendingResearchChallenges(archive)).toEqual([]);
    }
  });

  it('keeps a legacy frozen capsule without challenge fields byte compatible on retry', async () => {
    const f = challengeFixture(), legacy = await seedLegacyCapsule(f);
    expect(JSON.parse(legacy.bytes.toString()).researchChallengeDecisions).toBeUndefined();
    const state = readSolverRunState(f.stateFile);
    expect(readContinuationSnapshot(path.join(f.directory, 'continuation.json'), state.continuationDigest!).manifest.attachments
      .some(item => item.id === 'seed-research-challenge-decisions')).toBe(false);
    expect(state.cooperation!.challengeDecisions).toBeUndefined();
    await f.seed();
    expect(fs.readFileSync(legacy.file)).toEqual(legacy.bytes);
    expect(fs.readFileSync(path.join(f.directory, 'continuation.json'))).toEqual(legacy.snapshot);
    expect(readSolverRunState(f.stateFile).cooperation!.challengeDecisions).toBeUndefined();
  });

  it('recovers the verified ancestor verdict lost by the historical migration and preserves it on the next migration', async () => {
    const f = challengeFixture(), ancestorBytes = fs.readFileSync(f.sourceStateFile);
    await seedLegacyCapsule(f);
    expect(pendingResearchChallenges(readSolverRunState(f.stateFile).cooperation!)).toHaveLength(1);
    const second = nextGeneration(f); await second.seed();
    const third = nextGeneration(f, second.stateFile, 'third'); await third.seed();
    for (const file of [second.stateFile, third.stateFile]) {
      const archive = readSolverRunState(file).cooperation!;
      expect(archive.challengeDecisions).toEqual([f.decision]);
      expect(pendingResearchChallenges(archive)).toEqual([]);
    }
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(ancestorBytes);
  });

  it('does not recover a different live ancestor state after its frozen digest changed', async () => {
    const f = challengeFixture(); await seedLegacyCapsule(f);
    f.oldState.cooperation!.challengeDecisions![0] = { ...f.decision, reason: 'Unbound later rewrite' };
    writeSolverRunState(f.sourceStateFile, f.oldState);
    const second = nextGeneration(f); await second.seed();
    const archive = readSolverRunState(second.stateFile).cooperation!;
    expect(archive.challengeDecisions ?? []).toEqual([]);
    expect(pendingResearchChallenges(archive)).toHaveLength(1);
  });

  it('continues without ancestor recovery when the frozen ancestor state is unavailable', async () => {
    const f = challengeFixture(); await seedLegacyCapsule(f);
    fs.unlinkSync(f.sourceStateFile);
    const second = nextGeneration(f); await expect(second.seed()).resolves.toMatchObject({ stage: 'complete' });
    const archive = readSolverRunState(second.stateFile).cooperation!;
    expect(archive.challengeDecisions ?? []).toEqual([]);
    expect(pendingResearchChallenges(archive)).toHaveLength(1);
  });

  it.each(['current', 'current-stale', 'route-changed'] as const)(
    'does not revive the older ancestor verdict when the live source is %s', async changed => {
      const f = challengeFixture(); await seedLegacyCapsule(f);
      const state = readSolverRunState(f.stateFile), archive = state.cooperation!;
      if (changed !== 'route-changed') {
        const [challenge] = pendingResearchChallenges(archive);
        archive.challengeDecisions = resolveResearchChallenges(archive, [challenge.id],
          { [challenge.id]: challenge.activationDigest }, archive.tasks.map(node => node.task), [{ id: challenge.id,
            status: 'revised', reason: 'A newer explicit decision supersedes the ancestor.' }]);
      }
      const current = archive.challengeDecisions;
      if (changed !== 'current') archive.proofRoutes![0] = { ...archive.proofRoutes![0]!, closingTaskId: 'second' };
      writeSolverRunState(f.stateFile, state);
      const second = nextGeneration(f); await second.seed();
      const restored = readSolverRunState(second.stateFile).cooperation!;
      if (changed === 'current') {
        expect(restored.challengeDecisions).toEqual(current);
        expect(pendingResearchChallenges(restored)).toEqual([]);
      } else {
        expect(restored.challengeDecisions ?? []).toEqual([]);
        expect(pendingResearchChallenges(restored)).toHaveLength(1);
      }
    });

  it('freezes recovered ancestor decisions before an interrupted migration and ignores later ancestor rewrites on retry', async () => {
    const f = challengeFixture(); await seedLegacyCapsule(f);
    const second = nextGeneration(f), controller = new AbortController();
    const buildFile = path.join(f.root, 'next-manifest.json');
    await expect(seedSolverContinuation({ ...f.options, sourceRun: f.stateFile, run: second.stateFile,
      buildManifest: buildFile, signal: controller.signal, onProgress: event => {
        if (event === 'continuation_seed_checked') controller.abort();
      } })).rejects.toThrow();
    const sourceFile = path.join(second.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const digest = readSolverRunState(second.stateFile).continuationDigest;
    f.oldState.cooperation!.challengeDecisions = [];
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await second.seed();
    const state = readSolverRunState(second.stateFile);
    expect(state.cooperation!.challengeDecisions).toEqual([f.decision]);
    expect(pendingResearchChallenges(state.cooperation!)).toEqual([]);
    expect(fs.readFileSync(sourceFile)).toEqual(frozen); expect(state.continuationDigest).toBe(digest);
  });

  it('retries a challenge with a typed handoff after fresh helper checking retires its capacity source', async () => {
    const f = fixture(), archive = f.oldState.cooperation!, target = archive.tasks[0]!;
    target.status = 'pending';
    const node = createCapacityExploration(target, { id: 'prover-1' }, archive.tasks,
      { environmentDigest: f.oldState.environmentDigest, problemReceiptDigest: f.oldState.problem.receiptDigest }, 'construction');
    node.status = 'completed';
    node.finding = JSON.stringify({ taskId: node.task.id, conclusion: 'refuted', needsDecision: true,
      summary: 'The proposed construction needs another premise.', evidenceRefs: ['capacity-counterexample'] });
    archive.tasks.push(node);
    fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), 'Immutable capacity counterexample and exact helper request.\n');
    const notesCommit = commit(f.sourceWorktree, 'Compound capacity research publication');
    const proposal: CooperativeTask = { id: 'proposed', kind: 'lemma', objective: 'Prove the additional premise',
      groupId: 'main', dependsOn: ['first'], revision: 0, proofPath: 'Submission/Helpers.lean',
      theoremName: 'Submission.Helpers.proposed', type: 'True' };
    const delivery: DeliveryRecord = { id: 'compound-capacity-delivery', producer: 'prover-1', kind: 'research',
      status: 'advisory', taskId: node.task.id, taskDigest: taskVersion(node.task), groupId: 'main',
      statement: node.task.objective, premises: [], dependencies: [{ taskId: target.task.id, taskDigest: taskVersion(target.task) }],
      remainingObligations: ['goal'], summary: 'Counterexample and exact typed follow-up', evidenceRefs: ['capacity-counterexample'],
      createdAt: 1, commit: notesCommit, finding: node.finding, findingDigest: mathDigest(node.finding), lemmaRequests: [proposal] };
    archive.deliveries!.push(delivery);
    const [challenge] = pendingResearchChallenges(archive);
    archive.challengeDecisions = resolveResearchChallenges(archive, [challenge.id],
      { [challenge.id]: challenge.activationDigest }, archive.tasks.map(record => record.task), [{ id: challenge.id,
        status: 'disputed', reason: 'The construction already supplies the stated premise.', evidenceRefs: ['checked-construction'] }]);
    writeSolverRunState(f.sourceStateFile, f.oldState);
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    const interrupted = readSolverRunState(f.stateFile).cooperation!;
    expect(interrupted.deliveries).toMatchObject([{ id: delivery.id, status: 'superseded' }]);
    expect(interrupted.challengeDecisions).toEqual([]);
    expect(pendingResearchChallenges(interrupted)).toEqual([]);
    const frozenFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(frozenFile);
    await expect(seedSolverContinuation({ ...f.options, signal: new AbortController().signal }))
      .resolves.toMatchObject({ stage: 'complete' });
    const state = readSolverRunState(f.stateFile), restored = state.cooperation!;
    expect(restored.tasks.some(record => record.task.id === node.task.id)).toBe(false);
    expect(restored.deliveries).toMatchObject([{ id: delivery.id, status: 'superseded' }]);
    expect(restored.challengeDecisions).toEqual([]);
    expect(pendingResearchChallenges(restored)).toEqual([]);
    expect(fs.readFileSync(frozenFile)).toEqual(frozen);
  });

  it.each(['missing', 'corrupt'] as const)(
    'recovers an exact ancestor verdict when its optional older snapshot is %s', async damage => {
      const f = challengeFixture(); await f.seed();
      const second = nextGeneration(f);
      await seedLegacyCapsule({ ...f, ...second, sourceStateFile: f.stateFile });
      const ancestor = fs.readFileSync(f.stateFile), snapshotFile = path.join(f.directory, 'continuation.json');
      if (damage === 'missing') fs.unlinkSync(snapshotFile);
      else { fs.chmodSync(snapshotFile, 0o600); fs.writeFileSync(snapshotFile, '{"schema":'); }
      const third = nextGeneration(f, second.stateFile, 'third');
      await expect(third.seed()).resolves.toMatchObject({ stage: 'complete' });
      const archive = readSolverRunState(third.stateFile).cooperation!;
      expect(archive.challengeDecisions).toEqual([f.decision]);
      expect(pendingResearchChallenges(archive)).toEqual([]);
      expect(fs.readFileSync(f.stateFile)).toEqual(ancestor);
    });

  it('continues without ancestor recovery when the optional ancestor state contains truncated JSON', async () => {
    const f = challengeFixture(); await seedLegacyCapsule(f);
    fs.writeFileSync(f.sourceStateFile, '{"schema":');
    const second = nextGeneration(f); await expect(second.seed()).resolves.toMatchObject({ stage: 'complete' });
    const archive = readSolverRunState(second.stateFile).cooperation!;
    expect(archive.challengeDecisions ?? []).toEqual([]);
    expect(pendingResearchChallenges(archive)).toHaveLength(1);
  });
});
