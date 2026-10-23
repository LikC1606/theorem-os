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
import { readContinuationPage, readContinuationSnapshot } from '../src/solver/continuationInput';
import { git, readSolverProblem } from '../src/solver/problem';
import { taskVersion, type CooperativeTask, type TaskRecord } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import type { DeliveryRecord } from '../src/solver/deliveries';
import { pendingResearchHandoffs, researchHandoffs, resolveResearchHandoffs, selectResearchHandoffBatch } from '../src/solver/researchHandoffs';
import { markTaskAcceptance } from '../src/solver/tasks';
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
const typedProposal = (id = 'proposed'): CooperativeTask => ({ id, kind: 'lemma', objective: `Prove ${id}`,
  groupId: 'main', dependsOn: ['first'], revision: 0, proofPath: 'Submission/Helpers.lean',
  theoremName: `Submission.Helpers.${id}`, type: 'True' });
function addResearch(f: Fixture): TaskRecord {
  const node: TaskRecord = { task: { id: 'research', kind: 'research', objective: 'Find exact typed helpers',
    groupId: 'main', dependsOn: ['first'], revision: 0 }, status: 'completed', attempts: 3 };
  f.oldState.cooperation!.tasks.push(node);
  return node;
}
function publishHandoff(f: Fixture, node = addResearch(f), proposals: readonly CooperativeTask[] = [typedProposal()]) {
  const notes = '\ufeff完整的 λ 交付\r\n```lean\nnamespace Scratch\nlemma proposed : True := by trivial\nend Scratch\n```\n';
  fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), notes);
  const notesCommit = commit(f.sourceWorktree, 'Immutable typed handoff notes');
  const delivery: DeliveryRecord = { id: 'typed-research-delivery', producer: node.capacityExploration?.workerId ?? 'solver',
    taskId: node.task.id, taskDigest: taskVersion(node.task), groupId: 'main', kind: 'research', status: 'conditional',
    statement: node.task.objective, premises: [], dependencies: node.task.dependsOn.map(id => ({ taskId: id,
      taskDigest: taskVersion(f.oldState.cooperation!.tasks.find(item => item.task.id === id)!.task) })),
    remainingObligations: ['goal'], summary: 'Typed interfaces and complete immutable notes', evidenceRefs: ['advisory-note'],
    createdAt: 1, commit: notesCommit, finding: 'Complete advisory finding λ', findingDigest: mathDigest('Complete advisory finding λ'),
    lemmaRequests: proposals };
  f.oldState.cooperation!.deliveries!.push(delivery);
  fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), 'Later live notes must not replace the immutable handoff.\n');
  return { delivery, node, notes, notesCommit };
}
function saveSource(f: Fixture) { writeSolverRunState(f.sourceStateFile, f.oldState); }
function readHandoffAttachment(directory: string, digest: string) {
  return JSON.parse(readContinuationPage(path.join(directory, 'continuation.json'), digest, 'seed-research-handoffs').text);
}
function nextGeneration(f: Fixture) {
  const directory = path.join(f.root, 'next.json.runtime'); fs.mkdirSync(directory, { mode: 0o700 });
  const worktree = path.join(directory, 'worktree');
  for (const name of ['worktree', 'worktree-2']) git(f.workspace,
    ['worktree', 'add', '--quiet', '--detach', path.join(directory, name), f.base]);
  const buildFile = path.join(f.root, 'next-manifest.json'); fs.writeFileSync(buildFile, '{"fixture":"next-build"}', { mode: 0o400 });
  const stateFile = path.join(directory, 'state.json'), state: SolverRunState = { ...f.newState,
    runId: 'next-run', buildDigest: mathDigest(fs.readFileSync(buildFile)), methodDigest: 'next-method', worktree,
    workers: f.newState.workers!.map((worker, index) => ({ ...worker,
      worktree: path.join(directory, index ? `worktree-${index + 1}` : 'worktree') })) };
  writeSolverRunState(stateFile, state);
  const environmentFile = path.join(directory, 'environment-solver.json');
  fs.writeFileSync(environmentFile, canonicalMathJson(projectMathematicsRuntimeEnvironment({ PATH: '/usr/bin:/bin',
    DEEPSCIENTIST_MATH_ENV_FILE: environmentFile, DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS: host.packages,
    [MATH_PROOF_ENVIRONMENT_ENV]: 'disposed-next-startup-fixture' })), { mode: 0o400 });
  return { directory, stateFile, seed: () => seedSolverContinuation({ ...f.options,
    sourceRun: f.stateFile, run: stateFile, buildManifest: buildFile }) };
}

describe('typed research handoff continuation seeds', () => {
  it('preserves exact pending requests, dependencies and immutable notes as advisory without importing old acceptance', async () => {
    const f = fixture(), first = typedProposal('requested_first'), second = { ...typedProposal('requested_second'), dependsOn: [first.id] };
    const published = publishHandoff(f, addResearch(f), [second, first]);
    published.delivery.status = 'verified';
    published.delivery.submissionId = 'old-submission'; published.delivery.assignmentKey = 'old-assignment';
    published.delivery.evidence = { passed: true, verification: { status: 'kernel_verified', targetCommit: published.notesCommit,
      results: [{ receiptId: 'old-advisory-receipt' }] } };
    published.delivery.actualReferences = { sourceCommit: published.notesCommit, environmentDigest: f.oldState.environmentDigest,
      contextDigest: mathDigest('old-context'), root: { name: 'Old.proof', file: 'Submission/Helpers.lean' },
      inputs: [], statement: [], proof: [] };
    saveSource(f);
    const sourceBytes = fs.readFileSync(f.sourceStateFile), liveNotes = fs.readFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'));
    const before = pendingResearchHandoffs(f.oldState.cooperation!).map(item => [item.id, item.contextDigest]);
    const report = await f.seed(), state = readSolverRunState(f.stateFile), archive = state.cooperation!;
    expect(report.checked).toEqual(['first', 'second']); expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName))
      .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
    expect(archive.deliveries).toHaveLength(1);
    expect(archive.deliveries![0]).toMatchObject({ id: published.delivery.id, status: 'advisory', kind: 'research',
      taskId: published.node.task.id, taskDigest: taskVersion(published.node.task), lemmaRequests: [second, first],
      dependencies: published.delivery.dependencies, finding: published.delivery.finding, findingDigest: published.delivery.findingDigest });
    for (const key of ['submissionId', 'assignmentKey', 'evidence', 'actualReferences', 'knowledgeUses', 'artifacts'])
      expect(archive.deliveries![0]).not.toHaveProperty(key);
    expect(archive.tasks.some(node => [first.id, second.id].includes(node.task.id))).toBe(false);
    expect(pendingResearchHandoffs(archive).map(item => [item.id, item.contextDigest])).toEqual(before);
    expect(selectResearchHandoffBatch(archive).map(item => item.proposal.id)).toEqual([first.id, second.id]);
    expect(archive.tasks.filter(node => node.integratedCheck).map(node => node.task.id)).toEqual(['first', 'second']);
    expect(archive.tasks[0].integratedCheck!.verification.results[0].receiptId).toContain('fresh-handoff-seed-');
    const capsule = readHandoffAttachment(f.directory, state.continuationDigest!);
    expect(capsule.notes).toEqual([{ deliveryId: published.delivery.id, commit: published.notesCommit, notes: published.notes }]);
    expect(capsule.records[0].sourceTask).toEqual(published.node.task);
    expect(capsule.records[0].inputs).toContainEqual({ taskId: first.id, taskDigest: taskVersion(first) });
    expect(capsule.records[0].inputs).toContainEqual({ taskId: 'first', taskDigest: taskVersion(f.tasks[0]) });
    const snapshot = readContinuationSnapshot(path.join(f.directory, 'continuation.json'), state.continuationDigest!);
    expect(snapshot.manifest.attachments.find(item => item.id === 'seed-research-handoffs')!.provenance)
      .toEqual({ evidence: 'recorded-not-replayed', runId: f.oldState.runId, source: f.sourceStateFile });
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(sourceBytes);
    expect(fs.readFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'))).toEqual(liveNotes);
  });

  it.each(['adopted', 'rejected', 'deferred'] as const)('retains %s decisions without treating the proposal as an accepted proof', async status => {
    const f = fixture(), published = publishHandoff(f), handoff = pendingResearchHandoffs(f.oldState.cooperation!)[0];
    if (status === 'adopted') f.oldState.cooperation!.tasks.push({ task: handoff.proposal, status: 'pending', attempts: 4,
      assignment: { taskId: handoff.proposal.id, taskDigest: taskVersion(handoff.proposal), workerId: 'prover-1',
        seedCommit: f.base, assignmentId: 'historical-adoption' } });
    f.oldState.cooperation!.researchDecisions = resolveResearchHandoffs(f.oldState.cooperation!, [handoff.id],
      f.oldState.cooperation!.tasks.map(node => node.task), status === 'adopted' ? undefined : [{ id: handoff.id, status,
        reason: 'Pinned historical disposition', ...(status === 'deferred' ? { waitsOn: ['first'] } : {}) }]);
    saveSource(f); await f.seed();
    const state = readSolverRunState(f.stateFile), archive = state.cooperation!;
    expect(archive.researchDecisions).toEqual(f.oldState.cooperation!.researchDecisions);
    expect(researchHandoffs(archive)).toMatchObject([{ deliveryId: published.delivery.id, status }]);
    expect(pendingResearchHandoffs(archive)).toEqual([]);
    if (status === 'adopted') {
      expect(archive.tasks.find(node => node.task.id === handoff.proposal.id)).toEqual({ task: handoff.proposal, status: 'pending', attempts: 0 });
    }
    if (status === 'deferred') {
      const checked = archive.tasks.find(node => node.task.id === 'first')!;
      expect(checked.integratedCheck!.verification.results[0].receiptId).toContain('fresh-handoff-seed-');
      markTaskAcceptance(checked.integratedCheck!);
      expect(pendingResearchHandoffs(archive)).toMatchObject([{ status: 'pending', reopened: 'checked-prerequisites' }]);
      expect(pendingResearchHandoffs(readSolverRunState(f.stateFile).cooperation!)).toEqual([]);
    }
    expect(host.verify).toHaveBeenCalledOnce();
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName))
      .toEqual(['Submission.Helpers.first_helper', 'Submission.Helpers.second_helper']);
  });

  it.each(['sharing', 'contract'] as const)
  ('checks the prerequisite %s edit when carrying a legacy adoption through successive builds', async change => {
    const f = fixture(), archive = f.oldState.cooperation!, input = archive.tasks.find(node => node.task.id === 'second')!;
    input.task = { ...input.task, sharing: 'group' };
    const published = publishHandoff(f, addResearch(f), [typedProposal(), typedProposal('still_pending')]
      .map(task => ({ ...task, dependsOn: [input.task.id] })));
    const handoff = pendingResearchHandoffs(archive)[0];
    archive.tasks.push({ task: handoff.proposal, status: 'pending', attempts: 0 });
    archive.researchDecisions = resolveResearchHandoffs(archive, [handoff.id], archive.tasks.map(node => node.task), undefined)
      .map(decision => ({ ...decision, contextDigest: handoff.contextDigest }));
    archive.history = [{ task: input.task }]; input.task = { ...input.task, sharing: 'problem' };
    expect(researchHandoffs(archive)[0].status).toBe('adopted');
    saveSource(f); const sourceBytes = fs.readFileSync(f.sourceStateFile);

    await f.seed();
    const restoredState = readSolverRunState(f.stateFile), restored = restoredState.cooperation!;
    expect(restored.history).toEqual([]);
    expect(restored.researchDecisions![0].contextDigest).not.toBe(handoff.contextDigest);
    expect(researchHandoffs(restored)).toMatchObject([{ deliveryId: published.delivery.id, status: 'adopted' }, { status: 'pending' }]);
    expect(restored.tasks.find(node => node.task.id === handoff.proposal.id)).toMatchObject({ status: 'pending' });
    expect(fs.readFileSync(f.sourceStateFile)).toEqual(sourceBytes);
    const originalInputs = readHandoffAttachment(f.directory, restoredState.continuationDigest!).records[0].inputs;

    const currentInput = restored.tasks.find(node => node.task.id === input.task.id)!;
    restored.history = [{ task: currentInput.task }];
    currentInput.task = { ...currentInput.task, ...(change === 'sharing' ? { sharing: 'group' as const } : { type: 'False' }) };
    currentInput.proof = undefined; currentInput.integratedCheck = undefined; currentInput.status = 'pending';
    expect(researchHandoffs(restored)[0].status).toBe(change === 'sharing' ? 'adopted' : 'pending');
    writeSolverRunState(f.stateFile, restoredState);
    const next = nextGeneration(f); await next.seed();
    const latest = readSolverRunState(next.stateFile).cooperation!;
    expect(latest.deliveries![0].status).toBe(change === 'sharing' ? 'advisory' : 'superseded');
    expect(researchHandoffs(latest).map(item => item.status)).toEqual(change === 'sharing' ? ['adopted', 'pending'] : []);
    const latestState = readSolverRunState(next.stateFile);
    expect(readHandoffAttachment(next.directory, latestState.continuationDigest!).records[0].inputs).toEqual(originalInputs);
  });

  it.each(['environment', 'source-revised', 'source-history', 'source-missing', 'dependency', 'superseded'] as const)(
    'keeps a stale %s publication as superseded provenance without blocking initialization', async reason => {
      const f = fixture(), published = publishHandoff(f);
      if (reason === 'environment') {
        f.newState.environmentDigest = mathDigest('different-destination-environment'); writeSolverRunState(f.stateFile, f.newState);
      }
      if (reason === 'source-revised') {
        f.oldState.cooperation!.history = [{ task: published.node.task }];
        published.node.task = { ...published.node.task, objective: 'Changed mathematical investigation', revision: 1 };
      }
      if (reason === 'source-history' || reason === 'source-missing') {
        f.oldState.cooperation!.tasks = f.oldState.cooperation!.tasks.filter(node => node !== published.node);
        if (reason === 'source-history') f.oldState.cooperation!.history = [{ task: published.node.task }];
      }
      if (reason === 'dependency') published.delivery.dependencies[0].taskDigest = mathDigest('stale-prerequisite-contract');
      if (reason === 'superseded') published.delivery.status = 'superseded';
      saveSource(f); await expect(f.seed()).resolves.toMatchObject({ stage: 'complete' });
      const state = readSolverRunState(f.stateFile), capsule = readHandoffAttachment(f.directory, state.continuationDigest!);
      expect(state.cooperation!.deliveries).toMatchObject([{ id: published.delivery.id, status: 'superseded', lemmaRequests: published.delivery.lemmaRequests }]);
      expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
      expect(capsule.notes[0].notes).toBe(published.notes);
      if (reason === 'source-history' || reason === 'source-revised') expect(capsule.records[0].sourceTask).toMatchObject({ revision: 0 });
      await expect(f.seed()).resolves.toMatchObject({ stage: 'complete' });
    });

  it('retires a capacity source and its handoff after fresh helper rechecking, including an interrupted retry', async () => {
    const f = fixture(), target = f.oldState.cooperation!.tasks[0]; target.status = 'pending';
    const node = createCapacityExploration(target, { id: 'prover-1' }, f.oldState.cooperation!.tasks,
      { environmentDigest: f.oldState.environmentDigest, problemReceiptDigest: f.oldState.problem.receiptDigest }, 'construction');
    node.status = 'completed'; f.oldState.cooperation!.tasks.push(node);
    const published = publishHandoff(f, node); saveSource(f);
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    expect(readSolverRunState(f.stateFile).cooperation!.deliveries![0].status).toBe('superseded');
    await expect(seedSolverContinuation({ ...f.options, signal: new AbortController().signal })).resolves.toMatchObject({ stage: 'complete' });
    const state = readSolverRunState(f.stateFile);
    expect(state.cooperation!.tasks.some(item => item.task.id === node.task.id)).toBe(false);
    expect(state.cooperation!.history).toContainEqual(expect.objectContaining({ task: node.task, capacityExploration: node.capacityExploration }));
    expect(state.cooperation!.deliveries).toMatchObject([{ id: published.delivery.id, status: 'superseded' }]);
    expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
    expect(readHandoffAttachment(f.directory, state.continuationDigest!).notes[0].notes).toBe(published.notes);
    await expect(seedSolverContinuation({ ...f.options, signal: new AbortController().signal })).resolves.toMatchObject({ stage: 'complete' });
  });

  it('retries frozen pending requests and decisions independently of later live source changes', async () => {
    const f = fixture(), published = publishHandoff(f); saveSource(f);
    await expect(seedSolverContinuation({ ...f.options, onProgress: event => {
      if (event === 'continuation_seed_checked') f.controller.abort();
    } })).rejects.toThrow();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const digest = readSolverRunState(f.stateFile).continuationDigest;
    f.oldState.cooperation!.deliveries = []; f.oldState.cooperation!.researchDecisions = []; saveSource(f);
    fs.writeFileSync(path.join(f.sourceWorktree, 'RESEARCH.md'), 'Changed after seed capture');
    await seedSolverContinuation({ ...f.options, signal: new AbortController().signal });
    const state = readSolverRunState(f.stateFile);
    expect(state.continuationDigest).toBe(digest); expect(fs.readFileSync(sourceFile)).toEqual(frozen);
    expect(pendingResearchHandoffs(state.cooperation!)).toMatchObject([{ deliveryId: published.delivery.id }]);
    expect(readHandoffAttachment(f.directory, digest!).notes[0].notes).toBe(published.notes);
  });

  it('keeps old frozen seeds without handoffs byte compatible on retry', async () => {
    const f = fixture(); await f.seed();
    const sourceFile = path.join(f.directory, 'continuation-seed-source.json'), frozen = fs.readFileSync(sourceFile);
    const snapshot = fs.readFileSync(path.join(f.directory, 'continuation.json'));
    const state = readSolverRunState(f.stateFile);
    expect(JSON.parse(frozen.toString()).researchHandoffs).toBeUndefined();
    expect(readContinuationSnapshot(path.join(f.directory, 'continuation.json'), state.continuationDigest!).manifest.attachments
      .some(item => item.id === 'seed-research-handoffs')).toBe(false);
    publishHandoff(f); saveSource(f); await f.seed();
    expect(fs.readFileSync(sourceFile)).toEqual(frozen);
    expect(fs.readFileSync(path.join(f.directory, 'continuation.json'))).toEqual(snapshot);
    expect(readSolverRunState(f.stateFile).cooperation!.deliveries).toEqual([]);
    expect(readSolverRunState(f.stateFile).cooperation!.researchDecisions).toBeUndefined();
  });

  it.each(['unchanged', 'input-changed', 'delivery-cleared'] as const)(
    'preserves origin bindings and complete notes through another build when %s', async mode => {
      const f = fixture(), published = publishHandoff(f, addResearch(f), [{ ...typedProposal(), dependsOn: ['second'] }]);
      const handoff = pendingResearchHandoffs(f.oldState.cooperation!)[0];
      f.oldState.cooperation!.researchDecisions = resolveResearchHandoffs(f.oldState.cooperation!, [handoff.id],
        f.oldState.cooperation!.tasks.map(node => node.task), [{ id: handoff.id, status: 'rejected', reason: 'Pinned rejection' }]);
      saveSource(f); await f.seed();
      const before = readSolverRunState(f.stateFile);
      if (mode === 'input-changed') {
        const input = before.cooperation!.tasks.find(node => node.task.id === 'second')!;
        input.task = { ...input.task, objective: 'Different prerequisite contract', revision: 1 };
        input.proof = undefined; input.integratedCheck = undefined; input.status = 'pending';
      }
      if (mode === 'delivery-cleared') { before.cooperation!.deliveries = []; before.cooperation!.researchDecisions = []; }
      writeSolverRunState(f.stateFile, before);
      const next = nextGeneration(f); await expect(next.seed()).resolves.toMatchObject({ stage: 'complete' });
      const state = readSolverRunState(next.stateFile), capsule = readHandoffAttachment(next.directory, state.continuationDigest!);
      expect(capsule.notes).toEqual([{ deliveryId: published.delivery.id, commit: published.notesCommit, notes: published.notes }]);
      expect(capsule.records[0].inputs).toEqual([{ taskId: 'second', taskDigest: taskVersion(f.tasks[1]) }]);
      expect(state.cooperation!.researchDecisions).toEqual(f.oldState.cooperation!.researchDecisions);
      expect(state.cooperation!.deliveries![0].status).toBe(mode === 'unchanged' ? 'advisory' : 'superseded');
      expect(pendingResearchHandoffs(state.cooperation!)).toEqual([]);
      await expect(next.seed()).resolves.toMatchObject({ stage: 'complete' });
    });

  it.each(['delivery', 'decision'] as const)('rejects a mutated destination %s before reinstalling the seed', async field => {
    const f = fixture(); publishHandoff(f);
    const handoff = pendingResearchHandoffs(f.oldState.cooperation!)[0];
    f.oldState.cooperation!.researchDecisions = resolveResearchHandoffs(f.oldState.cooperation!, [handoff.id],
      f.oldState.cooperation!.tasks.map(node => node.task), [{ id: handoff.id, status: 'rejected', reason: 'Pinned rejection' }]);
    saveSource(f); await f.seed();
    const state = readSolverRunState(f.stateFile);
    if (field === 'delivery') state.cooperation!.deliveries![0].lemmaRequests = [{ ...typedProposal(), type: 'False' }];
    else state.cooperation!.researchDecisions![0] = { ...state.cooperation!.researchDecisions![0], reason: 'Changed local decision' };
    writeSolverRunState(f.stateFile, state);
    await expect(f.seed()).rejects.toThrow('math_continuation_seed_destination_changed');
  });
});
