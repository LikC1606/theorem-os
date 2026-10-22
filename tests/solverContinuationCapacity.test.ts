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
import { createCapacityExploration, currentCapacityExploration, type CapacityExplorationFocus } from '../src/solver/capacityExploration';
import { readContinuationPage, readContinuationSnapshot } from '../src/solver/continuationInput';
import { git, readSolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
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
  host.prepare.mockResolvedValue({ environmentValue: 'fresh-capacity-seed-environment', dispose: host.dispose,
    stats: { files: 0, bytes: 0, publications: 1 } });
  host.verify.mockImplementation((request: MathematicsVerifierBatchRequest) => verifiedBatch(request,
    { sessionId: 'fresh-capacity-seed', receipt: 'fresh-capacity-seed', checks: true }));
});
afterEach(() => { vi.restoreAllMocks(); for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

type Fixture = ReturnType<typeof fixture>;
function addExploration(f: Fixture, focus: CapacityExplorationFocus, status: TaskRecord['status'] = 'running',
  workerId = 'prover-1', environmentDigest = f.oldState.environmentDigest) {
  const target = f.oldState.cooperation!.tasks.find(node => node.task.id === 'goal')!;
  const node = createCapacityExploration(target, { id: workerId }, f.oldState.cooperation!.tasks,
    { environmentDigest, problemReceiptDigest: f.oldState.problem.receiptDigest }, focus);
  node.status = status; node.attempts = 7;
  node.finding = JSON.stringify({ summary: `Retained ${focus} investigation`, conclusion: 'inconclusive' });
  node.assignment = { taskId: node.task.id, taskDigest: taskVersion(node.task), workerId,
    assignmentId: 'old-capacity-assignment', seedCommit: f.base };
  node.proof = f.oldState.cooperation!.tasks[0].integratedCheck;
  node.integratedCheck = node.proof;
  f.oldState.cooperation!.tasks.push(node);
  (f.oldState.cooperation!.capacityExplorationInputs ??= []).push({
    inputDigest: node.capacityExploration!.inputDigest, focus, targetTaskId: target.task.id, taskId: node.task.id });
  return node;
}

function publishNotes(f: Fixture, node: TaskRecord) {
  const text = '\ufeffComplete saved λ candidate\r\n```lean\nnamespace Scratch\nlemma candidate : True := by trivial\nend Scratch\n```\n';
  fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), text);
  const notesCommit = commit(f.sourceWorktree, 'Immutable capacity finding');
  f.oldState.cooperation!.deliveries!.push({ id: 'capacity-research-delivery', producer: node.capacityExploration!.workerId,
    taskId: node.task.id, taskDigest: taskVersion(node.task), kind: 'research', status: 'advisory',
    statement: node.task.objective, premises: [], dependencies: [{ taskId: 'goal',
      taskDigest: taskVersion(f.oldState.cooperation!.tasks.find(item => item.task.id === 'goal')!.task) }],
    remainingObligations: ['goal'], summary: 'The complete code is retained in the immutable notes.', evidenceRefs: [],
    createdAt: 1, commit: notesCommit, finding: node.finding });
  fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), 'Later unrelated live notes must not replace the candidate.\n');
  return { text, notesCommit };
}

function saveSource(f: Fixture) { writeSolverRunState(f.sourceStateFile, f.oldState); }
function readCapacityAttachment(f: Fixture, digest: string) {
  return JSON.parse(readContinuationPage(path.join(f.directory, 'continuation.json'), digest, 'seed-capacity-explorations').text);
}

describe('capacity exploration continuation seeds', () => {
  it('keeps host provenance and the method ledger while rechecking typed proofs and discarding assignments', async () => {
    const f = fixture(), unfinished = addExploration(f, 'construction'), complete = addExploration(f, 'interface', 'completed');
    const delivered = publishNotes(f, complete); saveSource(f);
    const sourceBytes = fs.readFileSync(f.sourceStateFile), liveNotes = fs.readFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'));
    const report = await f.seed(), state = readSolverRunState(f.stateFile), cooperation = state.cooperation!;
    expect(report.checked).toEqual(['first', 'second']); expect(host.verify).toHaveBeenCalledTimes(2);
    expect(cooperation.capacityExplorationInputs).toEqual(f.oldState.cooperation!.capacityExplorationInputs);
    for (const sourceNode of [unfinished, complete]) {
      const node = cooperation.tasks.find(item => item.task.id === sourceNode.task.id)!;
      expect(node.capacityExploration).toEqual(sourceNode.capacityExploration);
      expect(node.task).toEqual(sourceNode.task); expect(node.finding).toBe(sourceNode.finding);
      expect(node.status).toBe(sourceNode.status === 'completed' ? 'completed' : 'pending');
      expect(node.attempts).toBe(0); expect(node.assignment).toBeUndefined();
      expect(node.proof).toBeUndefined(); expect(node.integratedCheck).toBeUndefined();
      expect(currentCapacityExploration(node, cooperation.tasks, { environmentDigest: state.environmentDigest,
        problemReceiptDigest: state.problem.receiptDigest })).toBe(true);
    }
    expect(cooperation.tasks.filter(node => node.integratedCheck).map(node => node.task.id)).toEqual(['first', 'second']);
    expect(cooperation.tasks[0].integratedCheck!.verification.results[0].receiptId).toContain('fresh-capacity-seed-');
    const frozenSource = JSON.parse(fs.readFileSync(path.join(f.directory, 'continuation-seed-source.json'), 'utf8'));
    expect(frozenSource.plan.tasks.map((task: CooperativeTask) => task.id)).toEqual(['first', 'second', 'goal']);
    expect(cooperation.planVersion).toBe(mathDigest(canonicalMathJson(frozenSource.plan)));
    const capacity = readCapacityAttachment(f, state.continuationDigest!);
    expect(capacity.notes).toEqual([{ taskId: complete.task.id, taskDigest: taskVersion(complete.task),
      deliveryId: 'capacity-research-delivery', commit: delivered.notesCommit, notes: delivered.text }]);
    expect(capacity.records).toHaveLength(2);
    const snapshot = readContinuationSnapshot(path.join(f.directory, 'continuation.json'), state.continuationDigest!);
    expect(snapshot.manifest.attachments.find(item => item.id === 'seed-capacity-explorations')!.provenance)
      .toEqual({ evidence: 'recorded-not-replayed', runId: f.oldState.runId, source: f.sourceStateFile });
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(sourceBytes);
    expect(fs.readFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'))).toEqual(liveNotes);
  });

  it.each(['environment', 'target', 'owner', 'stopped'] as const)('archives a stale %s binding without changing its provenance or ledger', async reason => {
    const f = fixture(), node = addExploration(f, 'decomposition', 'running', reason === 'owner' ? 'former-prover' : 'prover-1',
      reason === 'environment' ? mathDigest('previous-environment') : f.oldState.environmentDigest);
    if (reason === 'target') {
      const target = f.oldState.cooperation!.tasks.find(item => item.task.id === 'goal')!;
      target.task = { ...target.task, objective: 'A changed target contract revision', revision: 1 };
    }
    if (reason === 'stopped') node.task = { ...node.task, status: 'stopped' };
    saveSource(f); await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.some(item => item.task.id === node.task.id)).toBe(false);
    expect(state.cooperation!.history).toContainEqual({ task: node.task, capacityExploration: node.capacityExploration,
      status: 'running', producer: node.capacityExploration!.workerId, finding: node.finding });
    expect(state.cooperation!.capacityExplorationInputs).toEqual(f.oldState.cooperation!.capacityExplorationInputs);
    expect(readCapacityAttachment(f, state.continuationDigest!).records[0].capacityExploration).toEqual(node.capacityExploration);
    await expect(f.seed()).resolves.toMatchObject({ stage: 'complete' });
  });

  it('retains previously archived host records as history without scheduling them again', async () => {
    const f = fixture(), node = addExploration(f, 'boundary', 'completed');
    f.oldState.cooperation!.tasks = f.oldState.cooperation!.tasks.filter(item => item !== node);
    f.oldState.cooperation!.history = [{ task: node.task, finding: node.finding,
      ...{ capacityExploration: node.capacityExploration, status: node.status, producer: 'prover-1' } }];
    saveSource(f); await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.map(item => item.task.id)).toEqual(['first', 'second', 'goal']);
    expect(state.cooperation!.history).toContainEqual({ task: node.task, capacityExploration: node.capacityExploration,
      status: 'completed', producer: 'prover-1', finding: node.finding });
    expect(readCapacityAttachment(f, state.continuationDigest!).records[0].archived).toBe(true);
    await expect(f.seed()).resolves.toMatchObject({ stage: 'complete' });
  });

  it('retries an interrupted seed from the frozen host records and complete saved notes', async () => {
    const f = fixture(), node = addExploration(f, 'interface', 'completed'), delivered = publishNotes(f, node); saveSource(f);
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const digest = readSolverRunState(f.stateFile).continuationDigest;
    f.oldState.cooperation!.capacityExplorationInputs = []; f.oldState.cooperation!.tasks.pop(); saveSource(f);
    fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), 'The source changed after the capture.');
    await seedSolverContinuation({ ...f.options, signal: new AbortController().signal });
    const state = readSolverRunState(f.stateFile);
    expect(state.continuationDigest).toBe(digest); expect(fs.readFileSync(sourceFile)).toEqual(frozen);
    expect(state.cooperation!.tasks.find(item => item.task.id === node.task.id)!.status).toBe('completed');
    expect(state.cooperation!.capacityExplorationInputs).toHaveLength(1);
    expect(readCapacityAttachment(f, state.continuationDigest!).notes[0].notes).toBe(delivered.text);
  });

  it('keeps old frozen seeds without capacity fields byte compatible on retry', async () => {
    const f = fixture(); await f.seed();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const previous = readSolverRunState(f.stateFile), snapshot = fs.readFileSync(path.join(f.directory, 'continuation.json'));
    expect(JSON.parse(frozen.toString()).capacityExplorations).toBeUndefined();
    addExploration(f, 'boundary'); saveSource(f);
    await f.seed();
    const state = readSolverRunState(f.stateFile);
    expect(state.continuationDigest).toBe(previous.continuationDigest); expect(fs.readFileSync(sourceFile)).toEqual(frozen);
    expect(fs.readFileSync(path.join(f.directory, 'continuation.json'))).toEqual(snapshot);
    expect(state.cooperation!.capacityExplorationInputs).toBeUndefined();
    expect(state.cooperation!.tasks.some(node => node.capacityExploration)).toBe(false);
  });

  it('carries complete immutable notes through another build after live delivery records were cleared', async () => {
    const f = fixture(), node = addExploration(f, 'interface', 'completed'), delivered = publishNotes(f, node); saveSource(f);
    await f.seed();
    expect(readSolverRunState(f.stateFile).cooperation!.deliveries).toEqual([]);
    const directory = path.join(f.root, 'next.json.runtime'); fs.mkdirSync(directory, { mode: 0o700 });
    const worktree = path.join(directory, 'worktree');
    for (const name of ['worktree', 'worktree-2']) git(f.workspace,
      ['worktree', 'add', '--quiet', '--detach', path.join(directory, name), f.base]);
    const buildFile = path.join(f.root, 'next-manifest.json'); fs.writeFileSync(buildFile, '{"fixture":"next-build"}', { mode: 0o400 });
    const stateFile = path.join(directory, 'state.json'), next: SolverRunState = { ...f.newState,
      runId: 'next-run', buildDigest: mathDigest(fs.readFileSync(buildFile)), methodDigest: 'next-method', worktree,
      workers: f.newState.workers!.map((worker, index) => ({ ...worker,
        worktree: path.join(directory, index ? `worktree-${index + 1}` : 'worktree') })) };
    writeSolverRunState(stateFile, next);
    const environmentFile = path.join(directory, 'environment-solver.json');
    fs.writeFileSync(environmentFile, canonicalMathJson(projectMathematicsRuntimeEnvironment({ PATH: '/usr/bin:/bin',
      DEEPSCIENTIST_MATH_ENV_FILE: environmentFile, DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
      [MATH_PROOF_ENVIRONMENT_ENV]: 'disposed-next-startup-fixture' })), { mode: 0o400 });
    await seedSolverContinuation({ ...f.options, sourceRun: f.stateFile, run: stateFile, buildManifest: buildFile });
    const state = readSolverRunState(stateFile), capacity = JSON.parse(readContinuationPage(path.join(directory, 'continuation.json'),
      state.continuationDigest!, 'seed-capacity-explorations').text);
    expect(capacity.notes[0].notes).toBe(delivered.text); expect(capacity.notes[0].commit).toBe(delivered.notesCommit);
    expect(state.cooperation!.capacityExplorationInputs).toEqual(f.oldState.cooperation!.capacityExplorationInputs);
    expect(state.cooperation!.tasks.find(item => item.task.id === node.task.id)!.capacityExploration).toEqual(node.capacityExploration);
    expect(state.cooperation!.tasks.find(item => item.task.id === node.task.id)!.status).toBe('completed');
    expect(state.cooperation!.tasks.every(item => !item.assignment)).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(4);
  });

  it('refuses a changed destination capacity ledger before reinstalling the frozen seed', async () => {
    const f = fixture(); addExploration(f, 'construction'); saveSource(f); await f.seed();
    const state = readSolverRunState(f.stateFile);
    state.cooperation!.capacityExplorationInputs![0].inputDigest = mathDigest('changed local input');
    writeSolverRunState(f.stateFile, state);
    await expect(f.seed()).rejects.toThrow('math_continuation_seed_destination_changed');
  });
});
