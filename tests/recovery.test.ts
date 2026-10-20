import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { gzipSync } from 'node:zlib';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration } from '../src/math/leanSource';
import type { MathematicsVerifierBatchRequest, MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverRunState, writeSolverRunState, type SolverRunState } from '../src/solver/archive';
import { readSolverProblem, git } from '../src/solver/problem';
import { recoverMathSnapshot, recheckMathSnapshot } from '../src/solver/recovery';
import { taskVersion, type CooperativeTask } from '../src/solver/tasks';
import type { TaskProof } from '../src/solver/cooperativeProof';
import { failedBatch, verifiedBatch } from './helpers/verifier';

const host = vi.hoisted(() => ({ verify: vi.fn(), packages: undefined as string | undefined }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify,
  resolveMathematicsLakePackagesCache: () => host.packages,
}));

const roots: string[] = [];
const missingTarget = 'f'.repeat(40);
const original = 'namespace Submission\ntheorem original : True := by sorry\nend Submission\n';

function verified(request: MathematicsVerifierBatchRequest) {
  return verifiedBatch(request, { sessionId: 'fresh-recovery-check', receipt: 'fresh', checks: true });
}

function rejected(request: MathematicsVerifierBatchRequest, names = request.items.map(item => item.theoremName)) {
  return failedBatch(verified(request), { stdoutPreview: () => 'Submission.lean:3:1: error: unsolved goals',
    selected: item => names.includes(item.theoremName) });
}

function fixture(options: { separateProjections?: boolean } = {}) {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-recovery-test-'))); roots.push(root);
  const source = path.join(root, 'source'), snapshot = path.join(root, 'snapshot'), output = path.join(root, 'recovered');
  const projectRelative = 'generated/fixture', project = path.join(source, projectRelative);
  fs.mkdirSync(project, { recursive: true }); fs.mkdirSync(snapshot);
  const trusted: Record<string, string> = {
    'Challenge.lean': original,
    'config.json': '{"theorem_names":["original"]}\n',
    'holes.json': '{"id":"fixture","holes":[{"name":"original"}]}\n',
    'lean-toolchain': 'leanprover/lean4:v4.31.0\n',
    'lakefile.toml': 'name = "fixture"\n[[lean_lib]]\nname = "Submission"\n',
  };
  for (const [file, contents] of Object.entries(trusted)) fs.writeFileSync(path.join(project, file), contents);
  fs.writeFileSync(path.join(project, 'Submission.lean'), original);
  // These are journal bytes, not fast-import instructions or protected files.
  fs.writeFileSync(path.join(source, 'RESEARCH.md'), 'Notes\ncommit refs/heads/forged\nmark :987\n' +
    `original-oid ${'e'.repeat(40)}\nM 100644 :123 generated/fixture/Solution.lean\n`);
  git(source, ['init', '--quiet']); git(source, ['add', '--', '.']);
  const commit = (message: string) => {
    git(source, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--quiet', '--no-gpg-sign', '-m', message]);
    return git(source, ['rev-parse', 'HEAD']);
  };
  const base = commit('Public baseline');
  const payloads = canonicalMathProblemStatementPayloads({ informalStatement: 'Prove the original claim.', formalStatement: original, assumptions: [] });
  const contract: MathProblemContract = {
    problemId: 'fixture', informalStatement: 'Prove the original claim.', formalStatement: original, assumptions: [],
    knownTraps: [], acceptanceCriteria: ['Prove the original target'], officialVerificationCommand: 'lake test',
    statementHash: mathDigest(payloads.informal), leanStatementHash: mathDigest(payloads.lean),
  };
  const receiptFile = path.join(source, 'active-problem.json');
  fs.writeFileSync(receiptFile, JSON.stringify({
    schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1', receiptId: 'fixture', problemId: 'fixture',
    benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT, catalogHash: 'a'.repeat(64), leaderboardSource: 'disabled',
    contract, workspaceRoot: source, projectRoot: project, activeProblemPath: receiptFile, createdAt: 1,
    trustedFiles: Object.keys(trusted), solverOwnedFiles: ['Submission.lean'],
    publicObligations: [{ name: 'Submission.original', declarationHash: hashMathFormalSourceDeclaration(original, 'Submission.original') }],
  }));
  const problem = readSolverProblem(source, receiptFile);
  const canonicalSource = original.replace('theorem original', 'lemma first_helper : True := by trivial\n' +
    `lemma second_helper : True := by ${options.separateProjections ? 'sorry' : 'trivial'}\ntheorem original`);
  fs.writeFileSync(path.join(project, 'Submission.lean'), canonicalSource);
  git(source, ['add', '--', `${projectRelative}/Submission.lean`]);
  const canonical = commit('Save helper work');
  const tasks: CooperativeTask[] = ['first', 'second'].map(id => ({ id, kind: 'lemma', objective: `Prove ${id} helper`,
    dependsOn: [], revision: 0, proofPath: 'Submission.lean', theoremName: `Submission.${id}_helper`, type: 'True' }));
  const archivedProof = (task: CooperativeTask): TaskProof => ({
    commit: canonical, sourceDigest: 'archived-source', passed: true, taskDigest: `old-version-${task.id}`,
    seedCommit: base, changes: [], verification: { status: 'kernel_verified', targetCommit: missingTarget,
      results: [{ status: 'kernel_verified', targetCommit: missingTarget, receiptId: `old-${task.id}` }] } as TaskProof['verification'],
  });
  const state: SolverRunState = {
    schema: 'deepscientist.math.solver.v1', runId: 'archived-run', problem: { ...problem,
      contract: { ...problem.contract, officialManifestId: `lean-eval:fixture:r1:${base}` } },
    taskDigest: mathDigest('Continue the existing proof.\n'), buildDigest: 'old-build', environmentDigest: 'old-environment',
    evaluatorDigest: 'old-evaluator', model: 'old-model', effort: 'xhigh', worktree: '/original-host/worktree',
    phase: 'checking', turns: 19, check: archivedProof(tasks[0]),
    cooperation: { canonicalCommit: canonical, tasks: [
      { task: tasks[0], attempts: 5, status: 'blocked', feedback: 'The operation was aborted.', proof: archivedProof(tasks[0]),
        assignment: { taskId: 'first', taskDigest: 'old-version-first', seedCommit: base, workerId: 'researcher-1' } },
      { task: tasks[1], attempts: 3, status: 'integrated', integratedCheck: archivedProof(tasks[1]) },
      { task: { id: 'goal', kind: 'goal', objective: 'Prove original', dependsOn: [], revision: 0,
        proofPath: 'Submission.lean', theoremName: 'Submission.original' }, attempts: 0, status: 'pending' },
      { task: { id: 'notes', kind: 'research', objective: 'Inspect library', dependsOn: [], revision: 0 },
        attempts: 1, status: 'completed', finding: 'A useful research note.' },
    ], deliveries: [{ id: 'archived-delivery', producer: 'solver', kind: 'proof', status: 'verified',
      statement: 'True', premises: [], dependencies: [], remainingObligations: [], summary: 'Old receipt', evidenceRefs: [], createdAt: 1 }] },
  };
  const included: string[] = [];
  const put = (relative: string, contents: string | Buffer) => {
    const target = path.join(snapshot, relative); fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, contents); included.push(relative);
  };
  writeSolverRunState(path.join(snapshot, 'state.json'), state); included.push('state.json');
  put('task.md', 'The earlier task text.\n'); put('task-continuation.md', 'Continue the existing proof.\n');
  const exported = execFileSync('git', ['-C', source, 'fast-export', '--all', '--show-original-ids', '--',
    'RESEARCH.md', ...['Submission.lean', 'Challenge.lean', 'lakefile.toml', 'lean-toolchain'].map(file => `${projectRelative}/${file}`)]);
  put('history.fast-export.gz', gzipSync(exported));
  const draft = Buffer.from(canonicalSource.replace('lemma first_helper : True := by trivial',
    'lemma first_helper : True := by\r\n  -- unfinished λ draft\r\n  sorry'));
  for (const id of ['solver', 'researcher-1']) {
    for (const file of ['Submission.lean', 'Challenge.lean', 'lakefile.toml', 'lean-toolchain'])
      put(`workers/${id}/${projectRelative}/${file}`, file === 'Submission.lean'
        ? id === 'solver' ? Buffer.from(canonicalSource) : draft : trusted[file]);
  }
  const writeManifest = () => fs.writeFileSync(path.join(snapshot, 'manifest.json'), JSON.stringify({
    schema: 'lean-eval.problem-snapshot.v1', problemId: 'fixture', runId: state.runId, projectRelative,
    originalBaseCommit: base, workers: ['solver', 'researcher-1'].map(id => ({ id, sourceHeadAfter: canonical })),
    files: included.map(file => { const bytes = fs.readFileSync(path.join(snapshot, file)); return { file, bytes: bytes.length, sha256: mathDigest(bytes) }; }),
  }));
  writeManifest();
  host.packages = path.join(root, 'packages'); fs.mkdirSync(host.packages);
  return { root, source, snapshot, output, base, canonical, canonicalSource, draft, trusted, state, tasks, projectRelative,
    writeManifest, recover: () => recoverMathSnapshot({ snapshot, output, sourceRepository: source }) };
}

beforeEach(() => { host.verify.mockReset().mockImplementation(async request => verified(request)); });
afterEach(() => { for (const root of roots.splice(0)) fs.rmSync(root, { recursive: true, force: true }); });

describe('snapshot recovery', () => {
  it('recovers interrupted candidates and provenance without authorizing archived receipts', () => {
    const f = fixture(), originalState = fs.readFileSync(path.join(f.snapshot, 'state.json'));
    const report = f.recover(), state = readSolverRunState(report.stateFile);
    expect(report).toMatchObject({ originalRunId: f.state.runId, verification: 'not-run',
      evidence: 'recovered-sources-require-recheck', resumable: false, candidates: ['first', 'second'] });
    expect(report.runId).not.toBe(f.state.runId);
    expect(report.originalToImported[f.base]).toMatch(/^[a-f0-9]{40}$/u);
    expect(report.originalToImported[f.canonical]).not.toBe(f.canonical);
    expect(git(report.history, ['show', `${report.originalToImported[f.canonical]}:${f.projectRelative}/Submission.lean`]))
      .toBe(f.canonicalSource.trim());
    expect(report.originalToMaterialized[f.canonical]).toBe(report.canonicalCommit);
    const missing = report.missingCommitReferences.find(item => item.commit === missingTarget);
    expect(missing?.fields).toContain('tasks.0.proof.verification.targetCommit');
    expect(missing?.fields).toContain('tasks.1.integratedCheck.verification.results.0.targetCommit');
    expect(state.check).toBeUndefined();
    expect(state.cooperation!.tasks.map(node => node.status)).toEqual(['pending', 'pending', 'pending', 'completed']);
    for (const node of state.cooperation!.tasks) {
      expect(node.proof).toBeUndefined(); expect(node.integratedCheck).toBeUndefined(); expect(node.assignment).toBeUndefined();
    }
    expect(state.cooperation!.tasks[3].finding).toBe('A useful research note.');
    expect(state.cooperation!.deliveries).toEqual([]);
    expect(host.verify).not.toHaveBeenCalled();
    expect(fs.readFileSync(path.join(f.output, 'task.md'), 'utf8')).toBe('Continue the existing proof.\n');
    expect(fs.readFileSync(path.join(f.snapshot, 'state.json'))).toEqual(originalState);
  });

  it('fills omitted trusted metadata and preserves uncommitted worker bytes in pinned commits', () => {
    const f = fixture(), report = f.recover();
    for (const [file, contents] of Object.entries(f.trusted)) {
      expect(fs.readFileSync(path.join(report.workspace, f.projectRelative, file), 'utf8')).toBe(contents);
      expect(execFileSync('git', ['-C', report.workspace, 'show', `${report.canonicalCommit}:${f.projectRelative}/${file}`]))
        .toEqual(Buffer.from(contents));
    }
    expect(fs.readFileSync(path.join(f.output, 'workers/researcher-1', f.projectRelative, 'Submission.lean'))).toEqual(f.draft);
    expect(execFileSync('git', ['-C', report.workspace, 'show',
      `${report.workerCommits['researcher-1']}:${f.projectRelative}/Submission.lean`])).toEqual(f.draft);
    expect(git(report.workspace, ['rev-parse', `refs/math/${report.runId}/workers/researcher-1`])).toBe(report.workerCommits['researcher-1']);
    expect(report.workerSourceErrors).toEqual({});
  });

  it('rejects changed snapshot bytes before importing history', () => {
    const f = fixture(); fs.appendFileSync(path.join(f.snapshot, 'task.md'), 'changed');
    expect(f.recover).toThrow('math_recovery_snapshot_changed:task.md');
    expect(fs.existsSync(f.output)).toBe(false);
  });

  it.each(['../outside', 'workers/solver/generated/fixture/Solution.lean', 'workers/solver/.git/config'])
  ('rejects an unsafe manifest entry %s', file => {
    const f = fixture(), manifestFile = path.join(f.snapshot, 'manifest.json');
    const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
    manifest.files.push({ file, bytes: 0, sha256: mathDigest('') }); fs.writeFileSync(manifestFile, JSON.stringify(manifest));
    expect(f.recover).toThrow('math_recovery_invalid_snapshot_path');
    expect(fs.existsSync(f.output)).toBe(false);
  });

  it('rejects a symlink even when its bytes match the manifest', () => {
    const f = fixture(), file = path.join(f.snapshot, 'task.md'), target = path.join(f.root, 'linked-task.md');
    fs.copyFileSync(file, target); fs.unlinkSync(file); fs.symlinkSync(target, file);
    expect(f.recover).toThrow('math_recovery_snapshot_symlink');
    expect(fs.existsSync(f.output)).toBe(false);
  });

  it('requires the supplied trusted metadata to match the archived digest', () => {
    const f = fixture(); f.state.problem = { ...f.state.problem,
      trustedFiles: { ...f.state.problem.trustedFiles, 'config.json': mathDigest('different config') } };
    writeSolverRunState(path.join(f.snapshot, 'state.json'), f.state); f.writeManifest();
    expect(f.recover).toThrow('math_recovery_trusted_file_missing:config.json');
    expect(fs.existsSync(path.join(f.output, 'state.json'))).toBe(false);
  });

  it('refuses to overwrite a recovery or create one inside the source snapshot', () => {
    const f = fixture(), report = f.recover(), before = fs.readFileSync(report.stateFile);
    expect(f.recover).toThrow('math_recovery_output_exists');
    expect(fs.readFileSync(report.stateFile)).toEqual(before);
    expect(() => recoverMathSnapshot({ snapshot: f.snapshot, output: path.join(f.snapshot, 'nested') }))
      .toThrow('math_recovery_output_inside_snapshot');
  });

  it('rechecks current task types and pins fresh source and projection evidence', async () => {
    const f = fixture(), report = f.recover();
    const checked = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(checked.report).toMatchObject({ verification: 'finished', evidence: 'fresh-helper-receipts', resumable: false });
    expect(host.verify).toHaveBeenCalledOnce();
    const [request, options] = host.verify.mock.calls[0];
    expect(request.items.map(item => item.theoremName)).toEqual(f.tasks.map(task => task.theoremName));
    expect(options.expectedDeclarationTypes).toEqual({ 'Submission.first_helper': 'True', 'Submission.second_helper': 'True' });
    expect(checked.state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
    for (const node of checked.state.cooperation!.tasks.slice(0, 2)) {
      const proof = node.integratedCheck!;
      expect(node.status).toBe('integrated'); expect(proof.taskDigest).toBe(taskVersion(node.task));
      expect(proof.verification.targetCommit).not.toBe(missingTarget);
      expect(proof.verification.results[0].receiptId).toMatch(/^fresh-/u);
      expect(request.items.find(item => item.theoremName === node.task.theoremName).statementHash).toBe(taskVersion(node.task));
      for (const commit of [proof.commit, proof.verification.targetCommit])
        expect(git(report.workspace, ['rev-parse', `refs/math/${report.runId}/evidence/${commit}`])).toBe(commit);
    }
    expect(checked.state.check).toBeUndefined();
    expect(checked.state.cooperation!.tasks[2].status).toBe('pending');
  });

  it.each(['first', 'second'])('rechecks only %s when its batch failure cannot be attributed', async failed => {
    const f = fixture(); f.recover();
    let shared!: MathematicsVerifierBatchResult;
    host.verify.mockImplementation(async request => {
      const result = verified(request), failedTheorem = `Submission.${failed}_helper`;
      const checked: MathematicsVerifierBatchResult = request.items.some(item => item.theoremName === failedTheorem) ? {
        ...result, status: 'failed', results: result.results.map(item => item.theoremName === failedTheorem
          ? { ...item, status: 'failed', error: 'Expected helper type does not match.' } : item),
      } : result;
      if (request.items.length > 1) shared = checked;
      return checked;
    });
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName))).toEqual([
      ['Submission.first_helper', 'Submission.second_helper'], [`Submission.${failed}_helper`],
    ]);
    const failedNode = state.cooperation!.tasks.find(node => node.task.id === failed)!;
    const passingNode = state.cooperation!.tasks.find(node => node.task.id === (failed === 'first' ? 'second' : 'first'))!;
    expect(failedNode).toMatchObject({ status: 'blocked', feedback: 'Expected helper type does not match.',
      integratedCheck: { passed: false } });
    expect(passingNode).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(passingNode.integratedCheck!.verification.results[0].theoremName).toBe(passingNode.task.theoremName);
    expect(passingNode.integratedCheck!.verification.results[0]).toBe(shared.results.find(result => result.theoremName === passingNode.task.theoremName));
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
    expect(report.verification).toBe('finished');
  });

  it.each(['first', 'second'])('retains the passing helper and deterministic %s failure from one invocation', async failed => {
    const f = fixture(), recovered = f.recover();
    let shared!: MathematicsVerifierBatchResult;
    host.verify.mockImplementation(async request => shared = rejected(request, [`Submission.${failed}_helper`]));
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify).toHaveBeenCalledOnce();
    expect(report).toMatchObject({ verification: 'finished', evidence: 'fresh-helper-receipts' });
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
    for (const node of state.cooperation!.tasks.slice(0, 2)) {
      const receipt = node.integratedCheck!.verification.results[0];
      expect(receipt).toBe(shared.results.find(result => result.theoremName === node.task.theoremName));
      expect(node.status).toBe(node.task.id === failed ? 'blocked' : 'integrated');
      expect(node.integratedCheck!.passed).toBe(node.task.id !== failed);
      expect(node.integratedCheck!.verification.status).toBe(node.task.id === failed ? 'failed' : 'kernel_verified');
      for (const commit of [node.integratedCheck!.commit, node.integratedCheck!.verification.targetCommit])
        expect(git(recovered.workspace, ['rev-parse', `refs/math/${recovered.runId}/evidence/${commit}`])).toBe(commit);
    }
    expect(shared.status).toBe('failed');
    expect(shared.results.find(result => result.theoremName === `Submission.${failed}_helper`)!.error).toBe('Lean exited with status 1.');
  });

  it('retains all shared-source compile failures without individual recompilation', async () => {
    const f = fixture(); f.recover();
    host.verify.mockImplementation(async request => rejected(request));
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify).toHaveBeenCalledOnce();
    expect(state.cooperation!.tasks.slice(0, 2).map(node => ({ status: node.status, passed: node.integratedCheck!.passed })))
      .toEqual([{ status: 'blocked', passed: false }, { status: 'blocked', passed: false }]);
    expect(report).toMatchObject({ verification: 'finished', evidence: 'recovered-sources-require-recheck' });
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
  });

  it('falls back individually for both generic failures and accepts only the fresh results', async () => {
    const f = fixture(); f.recover();
    host.verify.mockImplementation(async request => {
      const result = verified(request);
      return request.items.length > 1 ? { ...result, status: 'failed',
        results: result.results.map(item => ({ ...item, status: 'failed', error: 'Undiagnosed batch failure.' })) } : result;
    });
    const { state } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName))).toEqual([
      ['Submission.first_helper', 'Submission.second_helper'], ['Submission.first_helper'], ['Submission.second_helper'],
    ]);
    expect(state.cooperation!.tasks.slice(0, 2).map(node => node.status)).toEqual(['integrated', 'integrated']);
  });

  it.each(['commit', 'source header', 'order', 'missing', 'duplicate'] as const)
  ('falls back without accepting receipts from a batch with invalid %s identity', async invalid => {
    const f = fixture(); f.recover();
    let shared!: MathematicsVerifierBatchResult;
    host.verify.mockImplementation(async request => {
      const result = verified(request);
      if (request.items.length > 1) {
        if (invalid === 'commit') result.targetCommit = missingTarget;
        else if (invalid === 'source header') result.results[0]!.sourceDeclarationHash = 'wrong-header';
        else if (invalid === 'order') result.results.reverse();
        else if (invalid === 'missing') result.results.pop();
        else result.results[1] = result.results[0]!;
        shared = result;
      }
      return result;
    });
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName))).toEqual([
      ['Submission.first_helper', 'Submission.second_helper'], ['Submission.first_helper'], ['Submission.second_helper'],
    ]);
    expect(report.verification).toBe('finished');
    for (const node of state.cooperation!.tasks.slice(0, 2)) {
      expect(node).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
      expect(shared.results).not.toContain(node.integratedCheck!.verification.results[0]);
    }
  });

  it.each(['blocked', 'unavailable', 'cleanup', 'failed-and-blocked', 'failed-and-unavailable'] as const)
  ('retains %s as infrastructure evidence without upgrading its sibling or rechecking', async failure => {
    const f = fixture(); f.recover();
    let shared!: MathematicsVerifierBatchResult, before: string;
    const status = failure.endsWith('unavailable') ? 'unavailable' : 'blocked';
    host.verify.mockImplementation(async request => {
      const result = failure.startsWith('failed-and-') ? rejected(request, ['Submission.first_helper']) : verified(request);
      if (failure === 'cleanup') result.results[1]!.cleanupError = 'Checkout cleanup failed.';
      else {
        result.results[1]!.status = status;
        result.results[1]!.error = 'Fixture verifier could not complete its check.';
        if (!failure.startsWith('failed-and-')) result.status = status;
      }
      shared = result; before = JSON.stringify(result);
      return result;
    });
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify).toHaveBeenCalledOnce();
    expect(state.cooperation!.tasks.slice(0, 2).map(node => ({ status: node.status, passed: node.integratedCheck!.passed,
      verdict: node.integratedCheck!.verification.status }))).toEqual([0, 1].map(() => ({ status: 'blocked', passed: false, verdict: status })));
    expect(report).toMatchObject({ verification: 'finished', evidence: 'recovered-sources-require-recheck' });
    expect(JSON.stringify(shared)).toBe(before!);
    for (const [index, node] of state.cooperation!.tasks.slice(0, 2).entries())
      expect(node.integratedCheck!.verification.results[0]).toBe(shared.results[index]);
  });

  it('keeps evidence unverified when every helper check is blocked by its environment', async () => {
    const f = fixture(); f.recover();
    host.verify.mockImplementation(async request => {
      const result = verified(request);
      return { ...result, status: 'blocked', results: result.results.map(item => ({ ...item,
        status: 'blocked', error: 'math_lean_toolchain_unavailable' })) };
    });
    const { state, report } = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(host.verify).toHaveBeenCalledOnce();
    expect(report).toMatchObject({ verification: 'finished', evidence: 'recovered-sources-require-recheck', resumable: false });
    expect(state.cooperation!.tasks.slice(0, 2).map(node => node.status)).toEqual(['blocked', 'blocked']);
    expect(state.cooperation!.tasks.slice(0, 2).every(node => node.integratedCheck?.verification.status === 'blocked')).toBe(true);
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 2 });
    expect(state.check).toBeUndefined();
    expect(JSON.parse(fs.readFileSync(path.join(f.output, 'recovery.json'), 'utf8')).evidence)
      .toBe('recovered-sources-require-recheck');
  });

  it.each(['trustedFiles', 'contract', 'task.type'])('rejects changed recovered %s before invoking verification', async field => {
    const f = fixture(), report = f.recover(), state = readSolverRunState(report.stateFile);
    if (field === 'trustedFiles') {
      const { 'config.json': _config, ...remaining } = state.problem.trustedFiles;
      state.problem = { ...state.problem, trustedFiles: remaining };
    } else if (field === 'contract') {
      state.problem = { ...state.problem, contract: { ...state.problem.contract, assumptions: ['False'] } };
    } else {
      state.cooperation!.tasks[0].task = { ...state.cooperation!.tasks[0].task, type: 'False' };
    }
    writeSolverRunState(report.stateFile, state);
    const before = fs.readFileSync(report.stateFile), original = fs.readFileSync(path.join(f.snapshot, 'state.json'));
    await expect(recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal }))
      .rejects.toThrow('math_recovery_identity_changed');
    expect(host.verify).not.toHaveBeenCalled();
    expect(fs.readFileSync(report.stateFile)).toEqual(before);
    expect(fs.readFileSync(path.join(f.snapshot, 'state.json'))).toEqual(original);
    expect(JSON.parse(fs.readFileSync(path.join(f.output, 'recovery.json'), 'utf8')).verification).toBe('not-run');
  });

  it('normalizes an output parent symlink so the recovery can be rechecked through either path', async () => {
    const f = fixture(), parent = path.join(f.root, 'actual-parent'), alias = path.join(f.root, 'output-alias');
    fs.mkdirSync(parent); fs.symlinkSync(parent, alias);
    const linkedOutput = path.join(alias, 'new-parent', 'recovered'), canonicalOutput = path.join(parent, 'new-parent', 'recovered');
    const report = recoverMathSnapshot({ snapshot: f.snapshot, output: linkedOutput, sourceRepository: f.source });
    expect(report.stateFile).toBe(path.join(canonicalOutput, 'state.json'));
    expect(report.workspace).toBe(path.join(canonicalOutput, 'workspace'));
    const checked = await recheckMathSnapshot(linkedOutput, { env: {}, signal: new AbortController().signal });
    expect(checked.report.verification).toBe('finished');
    expect(checked.state.cooperation!.tasks.slice(0, 2).map(node => node.status)).toEqual(['integrated', 'integrated']);
    expect(readSolverRunState(path.join(canonicalOutput, 'state.json')).runId).toBe(report.runId);
  });

  it('rejects an output parent symlink that resolves inside the archived snapshot', () => {
    const f = fixture(), alias = path.join(f.root, 'snapshot-alias'); fs.symlinkSync(f.snapshot, alias);
    const before = fs.readFileSync(path.join(f.snapshot, 'manifest.json'));
    expect(() => recoverMathSnapshot({ snapshot: f.snapshot, output: path.join(alias, 'new-parent', 'recovered'), sourceRepository: f.source }))
      .toThrow('math_recovery_output_inside_snapshot');
    expect(fs.existsSync(path.join(f.snapshot, 'new-parent'))).toBe(false);
    expect(fs.readFileSync(path.join(f.snapshot, 'manifest.json'))).toEqual(before);
  });

  it('preserves completed fresh evidence and unfinished progress when a later check is cancelled', async () => {
    const f = fixture({ separateProjections: true }), report = f.recover(), controller = new AbortController();
    const originalState = fs.readFileSync(path.join(f.snapshot, 'state.json'));
    host.verify.mockImplementation(async request => {
      if (request.items[0].theoremName === 'Submission.second_helper') controller.abort();
      return verified(request);
    });
    await expect(recheckMathSnapshot(f.output, { env: {}, signal: controller.signal })).rejects.toThrow();
    const interrupted = readSolverRunState(report.stateFile);
    expect(JSON.parse(fs.readFileSync(path.join(f.output, 'recovery.json'), 'utf8')).verification).toBe('interrupted');
    expect(interrupted.cooperation!.recheck).toMatchObject({ total: 2, completed: 1, taskId: 'second' });
    expect(interrupted.cooperation!.tasks[0].status).toBe('integrated');
    const commit = interrupted.cooperation!.tasks[0].integratedCheck!.verification.targetCommit;
    expect(git(report.workspace, ['rev-parse', `refs/math/${report.runId}/evidence/${commit}`])).toBe(commit);
    expect(interrupted.cooperation!.tasks[1]).toMatchObject({ status: 'pending' });
    expect(interrupted.cooperation!.tasks[1].integratedCheck).toBeUndefined();
    expect(interrupted.cooperation!.tasks[1].feedback).toBeUndefined();
    expect(fs.readFileSync(path.join(f.snapshot, 'state.json'))).toEqual(originalState);
  });

  it('saves an attributed success before cancelling a generic sibling fallback', async () => {
    const f = fixture(), report = f.recover(), controller = new AbortController();
    host.verify.mockImplementation(async request => {
      const result = verified(request);
      if (request.items.length > 1) return { ...result, status: 'failed', results: result.results.map(item =>
        item.theoremName === 'Submission.second_helper' ? { ...item, status: 'failed', error: 'Undiagnosed batch failure.' } : item) };
      controller.abort(); return result;
    });
    await expect(recheckMathSnapshot(f.output, { env: {}, signal: controller.signal })).rejects.toThrow();
    const interrupted = readSolverRunState(report.stateFile);
    expect(host.verify.mock.calls.map(([request]) => request.items.map(item => item.theoremName))).toEqual([
      ['Submission.first_helper', 'Submission.second_helper'], ['Submission.second_helper'],
    ]);
    expect(interrupted.cooperation!.recheck).toMatchObject({ total: 2, completed: 1, taskId: 'second' });
    expect(interrupted.cooperation!.tasks[0]).toMatchObject({ status: 'integrated', integratedCheck: { passed: true } });
    expect(interrupted.cooperation!.tasks[1]).toMatchObject({ status: 'pending' });
    expect(interrupted.cooperation!.tasks[1].integratedCheck).toBeUndefined();
    expect(interrupted.cooperation!.tasks[1].feedback).toBeUndefined();
    expect(JSON.parse(fs.readFileSync(path.join(f.output, 'recovery.json'), 'utf8')))
      .toMatchObject({ verification: 'interrupted', evidence: 'fresh-helper-receipts' });
    const commit = interrupted.cooperation!.tasks[0].integratedCheck!.verification.targetCommit;
    expect(git(report.workspace, ['rev-parse', `refs/math/${report.runId}/evidence/${commit}`])).toBe(commit);
  });

  it('clears a previous fresh-evidence claim when a new recheck is cancelled before its first result', async () => {
    const f = fixture(), report = f.recover();
    const first = await recheckMathSnapshot(f.output, { env: {}, signal: new AbortController().signal });
    expect(first.report.evidence).toBe('fresh-helper-receipts');
    expect(first.state.cooperation!.tasks.slice(0, 2).every(node => node.integratedCheck?.passed)).toBe(true);
    const controller = new AbortController();
    host.verify.mockImplementation(async request => { controller.abort(); return verified(request); });
    await expect(recheckMathSnapshot(f.output, { env: {}, signal: controller.signal })).rejects.toThrow();
    const state = readSolverRunState(report.stateFile);
    const interrupted = JSON.parse(fs.readFileSync(path.join(f.output, 'recovery.json'), 'utf8'));
    expect(interrupted).toMatchObject({ verification: 'interrupted', evidence: 'recovered-sources-require-recheck' });
    expect(state.cooperation!.recheck).toMatchObject({ total: 2, completed: 0 });
    for (const node of state.cooperation!.tasks.slice(0, 2)) {
      expect(node.status).toBe('pending');
      expect(node.proof).toBeUndefined();
      expect(node.integratedCheck).toBeUndefined();
    }
  });
});
