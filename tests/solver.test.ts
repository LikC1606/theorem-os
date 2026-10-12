import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration, type MathematicsVerifierBatchRequest, type MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverProblem, assertSolverSources, assertSolverProjectSources, commitSolverSources, git, withSolverWorktree, type SolverProblem } from '../src/solver/problem';
import { checkSolverProof } from '../src/solver/modules/evidence';
import { directSolverModules, lemmaSolverModules } from '../src/solver/modules';
import { runSolver } from '../src/solver/run';
import { rememberSolverFailure, solverProofFeedback } from '../src/solver/feedback';
import { createMathRetrievalCorpus } from '../src/math/mathRetrievalCorpus';
import * as retrievalCorpus from '../src/math/mathRetrievalCorpus';
import type { MathAgentOptions } from '../src/runtime/codexSession';
import { checkLemmaResearch, readLemmaPlan } from '../src/solver/lemma';
import { CooperativeResearch, readCooperativePlan, readCooperationPlan, parseCooperationPlan, taskVersion, assignmentDeliveryFile, type CooperativeAction, type CooperativeTask, type RouteGroup } from '../src/solver/cooperation';
import { canonicalMathJson } from '../src/math/mathRuntimeIo';
import { readDeliveryLines, readMathResponse } from '../src/solver/deliveries';
import { isStatementAction, statementSnapshot } from '../src/solver/statementReview';
import { captureProofReferences, proofReferencesUnchanged } from '../src/solver/proofReferences';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn(), officialGate: vi.fn(), build: vi.fn(), delay: vi.fn(),
  prepare: vi.fn(), freeze: vi.fn(), readiness: vi.fn(), packages: undefined as string | undefined }));
vi.mock('../src/math/leanDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: host.prepare,
}));
vi.mock('node:timers/promises', async importOriginal => ({
  ...await importOriginal<typeof import('node:timers/promises')>(), setTimeout: host.delay,
}));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: host.build }));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: host.readiness }));
vi.mock('../src/math/verifier', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/verifier')>(),
  checkManyFormalVerifications: host.verify, resolveMathematicsLakePackagesCache: () => host.packages,
}));
vi.mock('../src/math/mathProofEnvironment', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/mathProofEnvironment')>(),
  prepareMathProofEnvironment: host.freeze,
}));
vi.mock('../src/math/leanEvalBootstrap', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanEvalBootstrap')>(), runPersistedLeanEvalOfficialGate: host.officialGate,
}));
vi.mock('../src/runtime/codexSession', () => ({ createCodexMathSession: host.createSession }));

function verified(request: MathematicsVerifierBatchRequest): MathematicsVerifierBatchResult {
  return { schema: 'deepscientist.mathematics.verification-batch/v1', status: 'kernel_verified',
    targetCommit: request.targetCommit!, sessionId: 'host', events: [], startedAt: 1, checkedAt: 2, durationMs: 1,
    results: request.items.map(item => ({ ...item, sourceDeclarationHash: item.expectedSourceDeclarationHash,
      receiptId: `fixture-${request.targetCommit}-${item.theoremName}`,
      targetCommit: request.targetCommit, status: 'kernel_verified', claim: 'statement' })) as MathematicsVerifierBatchResult['results'] };
}

describe('isolated solver and host acceptance', () => {
  let directory: string;
  let workspace: string;
  let project: string;
  let problem: SolverProblem;
  let output: string;
  let args: string[];
  const original = 'namespace Submission\ndef fixed : Nat := 2\ntheorem first : True := by sorry\ntheorem second : True := by sorry\nend Submission\n';
  beforeEach(() => {
    vi.clearAllMocks();
    host.packages = undefined;
    host.prepare.mockReset().mockResolvedValue({ exitCode: 0, timedOut: false, phases: [] });
    host.readiness.mockReset().mockReturnValue({ status: 'ready' });
    host.freeze.mockReset().mockResolvedValue({ environmentValue: 'fixture', dispose: vi.fn() });
    host.delay.mockReset().mockResolvedValue(undefined);
    vi.spyOn(console, 'log').mockImplementation(() => {});
    directory = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'math-solver-test-')));
    workspace = path.join(directory, 'public'); project = path.join(workspace, 'generated', 'p');
    fs.mkdirSync(project, { recursive: true });
    fs.mkdirSync(`${workspace}.source`);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original);
    fs.writeFileSync(path.join(project, 'Challenge.lean'), original);
    fs.writeFileSync(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.31.0');
    fs.writeFileSync(path.join(project, 'lakefile.toml'), 'name = "proof"\n');
    const payload = canonicalMathProblemStatementPayloads({ informalStatement: 'Prove both claims', formalStatement: original, assumptions: [] });
    const contract: MathProblemContract = { problemId: 'p', informalStatement: 'Prove both claims', formalStatement: original,
      assumptions: [], knownTraps: [], acceptanceCriteria: ['Both original targets'], officialVerificationCommand: 'lake test',
      statementHash: mathDigest(payload.informal), leanStatementHash: mathDigest(payload.lean) };
    const receipt = { schema: 'deepscientist.mathematics.lean-eval-bootstrap-receipt.v1', receiptId: 'fixture', problemId: 'p',
      benchmarkCommit: LEAN_EVAL_BENCHMARK_COMMIT, catalogHash: 'a'.repeat(64), leaderboardSource: 'disabled',
      contract, workspaceRoot: workspace, projectRoot: project, sourceProjectRoot: `${workspace}.source`,
      activeProblemPath: path.join(workspace, 'active-problem.json'), createdAt: 1,
      trustedFiles: ['Challenge.lean', 'lean-toolchain', 'lakefile.toml'], solverOwnedFiles: ['Submission.lean'],
      publicObligations: ['Submission.first', 'Submission.second'].map(name => ({ name,
        declarationHash: hashMathFormalSourceDeclaration(original, name) })) };
    fs.writeFileSync(receipt.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['init', '--quiet']);
    git(workspace, ['add', 'generated']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Public baseline']);
    fs.appendFileSync(path.join(workspace, '.git', 'info', 'exclude'), '\n/active-problem.json\n**/.lake/\n');
    problem = readSolverProblem(workspace, receipt.activeProblemPath);
    output = path.join(directory, 'run.json');
    const task = path.join(directory, 'task.md'); const build = path.join(directory, 'build.json');
    fs.writeFileSync(task, 'Prove the original targets'); fs.writeFileSync(build, '{}');
    args = ['--workspace', workspace, '--task-file', task, '--build-manifest', build, '--output', output, '--max-turns', '1', '--workers', '1'];
    host.verify.mockImplementation(async request => verified(request));
    host.officialGate.mockResolvedValue({ comparison: { status: 'official_verified' } });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId || 'fixture-thread',
      run: async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
  });
  afterEach(() => { vi.restoreAllMocks(); vi.unstubAllEnvs(); fs.rmSync(directory, { recursive: true, force: true }); });

  it.each([false, true])('isolates and releases a disposable proof checkout when failure=%s', async failure => {
    const worktrees = git(workspace, ['worktree', 'list', '--porcelain']);
    let checkout = '';
    const result = withSolverWorktree(workspace, problem.baseCommit, async isolated => {
      checkout = isolated;
      expect(git(isolated, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
      fs.writeFileSync(path.join(isolated, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
      await Promise.resolve();
      if (failure) throw new Error('fixture_check_failed');
      return 'checked';
    });
    if (failure) await expect(result).rejects.toThrow('fixture_check_failed');
    else await expect(result).resolves.toBe('checked');
    expect(fs.existsSync(path.dirname(checkout))).toBe(false);
    expect(git(workspace, ['worktree', 'list', '--porcelain'])).toBe(worktrees);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toBe(original);
  });

  it('rejects modified targets, fixed definitions and trusted inputs', () => {
    const proof = path.join(project, 'Submission.lean');
    fs.writeFileSync(proof, original.replace('first : True', 'first : False'));
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_original_declaration_changed');
    fs.writeFileSync(proof, original.replace('fixed : Nat := 2', 'fixed : Nat := 3'));
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_original_declaration_changed');
    fs.writeFileSync(proof, original);
    fs.writeFileSync(proof, original.replace('theorem first', 'variable (h : False)\ntheorem first'));
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_original_context_changed');
    fs.writeFileSync(proof, original);
    fs.writeFileSync(path.join(workspace, 'outside.txt'), 'unexpected file');
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_source_outside_ownership');
    fs.unlinkSync(path.join(workspace, 'outside.txt'));
    fs.writeFileSync(path.join(project, 'Challenge.lean'), 'different problem');
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_trusted_source_changed');
  });

  it('allows new helper declarations while preserving the original context', () => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first',
      'lemma helper : True := by trivial\ntheorem first'));
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
  });

  it('allows noncomputable new helpers without changing original declarations or context', () => {
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, original.replace('theorem first', 'noncomputable def helper : Nat := 0\ntheorem first'));
    expect(() => assertSolverSources(problem, workspace)).not.toThrow();
    fs.writeFileSync(file, original.replace('def fixed', 'noncomputable def fixed'));
    expect(() => assertSolverSources(problem, workspace)).toThrow('math_original_context_changed');
  });

  it('shares the original source checks with diagnostics before compiling a candidate', () => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'noncomputable section\ntheorem first'));
    expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_context_changed');
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('fixed : Nat := 2', 'fixed : Nat := 3'));
    expect(() => assertSolverProjectSources(problem, project)).toThrow('math_original_declaration_changed');
  });

  it.each([false, true])('starts a fresh context with notes, proof sources, failures and cumulative usage (resume: %s)', async resume => {
    let turn = 0;
    const messages: string[] = [];
    const closes = [vi.fn(), vi.fn()];
    host.verify.mockImplementation(async request => turn === 1 ? { ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed',
        stdoutPreview: 'Submission.lean:4:1: error: unsolved goals\n⊢ True' })) } : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const first = host.createSession.mock.calls.length === 1;
      return { threadId: first ? 'large-thread' : 'continued-thread', lastInputTokens: first ? 100_000 : 1000,
        close: first ? closes[0] : closes[1], interrupt: vi.fn(), run: async (message: string) => {
          messages.push(message); turn++;
          if (first) {
            fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), 'Checked helper: keep this proof.\n' + 'x'.repeat(20000));
            fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('by sorry', 'by trivial'));
          } else {
            expect(options.threadId).toBeUndefined();
            expect(message).toContain('Checked helper: keep this proof.');
            expect(message).toContain('Original problem:');
            expect(message).toContain('unsolved goals');
            expect(Buffer.byteLength(message)).toBeLessThan(10000);
            expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toContain('first : True := by trivial');
            fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
          }
          options.onUsage({ inputTokens: first ? 100000 : 1000, totalTokens: first ? 110000 : 2000 });
          return 'completed';
        } };
    });
    if (resume) {
      expect(await runSolver(args, directory)).toBe(4);
      expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).lastInputTokens).toBe(100000);
    }
    expect(await runSolver([...args, '--max-turns', '2', ...(resume ? ['--resume'] : [])], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.previousThreadIds).toEqual(['large-thread']);
    expect(state.threadId).toBe('continued-thread');
    expect(state.usage).toMatchObject({ inputTokens: 101000, totalTokens: 112000 });
    expect(state.failures).toHaveLength(1);
    expect(closes[0]).toHaveBeenCalledOnce();
  });

  it.each([
    ['target', 'first : True', 'first : False', 'math_original_declaration_changed'],
    ['definition', 'fixed : Nat := 2', 'fixed : Nat := 3', 'math_original_declaration_changed'],
    ['context', 'theorem first', 'variable (h : False)\ntheorem first', 'math_original_context_changed'],
  ])('lets the same session repair a changed %s before checking or integrating it', async (_kind, from, to, reason) => {
    const messages: string[] = [];
    const solved = original.replaceAll('by sorry', 'by trivial');
    const withHelper = solved.replace('theorem first', 'lemma helper : True := by trivial\ntheorem first');
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async (message: string) => {
        messages.push(message);
        if (messages.length === 2) {
          expect(host.verify).not.toHaveBeenCalled();
          expect(git(options.workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
          expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toContain('lemma helper');
        }
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
          messages.length === 1 ? withHelper.replace(from, to) : withHelper);
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(0);
    expect(messages).toHaveLength(2);
    expect(messages[1]).toContain(reason);
    expect(messages[1]).toContain('generated/p/Submission.lean');
    expect(messages[1]).toContain(problem.baseCommit);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toBe(withHelper);
  });

  it('keeps repeated invalid edits incomplete and resumable within the turn budget', async () => {
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('first : True', 'first : False'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 2,
      solution_commit: null, solver_ready_receipt_valid: false, evaluator: { status: 'skipped' } });
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    const messages: string[] = [];
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId!,
      run: async (message: string) => {
        messages.push(message);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--resume', '--max-turns', '3'], directory)).toBe(0);
    expect(messages).toHaveLength(1);
    expect(messages[0]).toContain('math_original_declaration_changed');
    expect(host.createSession.mock.calls[1][0].threadId).toBe('fixture-thread');
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).turns).toBe(3);
  });

  it.each([
    ['trusted input', 'generated/p/Challenge.lean', 'math_trusted_source_changed'],
    ['outside file', 'outside.txt', 'math_source_outside_ownership'],
  ])('stops on a changed %s without sending it through Lean', async (_kind, file, reason) => {
    const run = vi.fn(async (options: MathAgentOptions) => {
      fs.writeFileSync(path.join(options.workspace, file), 'unexpected content');
      return 'completed';
    });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: () => run(options), close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason });
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
  });

  it('requires receipts for every target at the exact frozen commit', async () => {
    const check = await checkSolverProof(problem, workspace, {});
    expect(check.passed).toBe(true);
    expect(host.verify.mock.calls[0][0]).toMatchObject({ timeoutMs: 180_000 });
    expect(host.verify.mock.calls[0][1]).toMatchObject({ prepareLocalDependencies: true });
    host.verify.mockImplementation(async request => { const result = verified(request); result.results.pop(); return result; });
    expect((await checkSolverProof(problem, workspace, {})).passed).toBe(false);
    host.verify.mockImplementation(async request => { const result = verified(request); result.results[0].targetCommit = 'b'.repeat(40); return result; });
    expect((await checkSolverProof(problem, workspace, {})).passed).toBe(false);
  });

  it.each(['', 'Combinatorics'])('checks the frozen Submission declarations for LeanEval namespace %s', async namespace => {
    const receipt = JSON.parse(fs.readFileSync(problem.activeProblemPath, 'utf8'));
    const challenge = original.replaceAll('namespace Submission', `namespace LeanEval${namespace ? `\nnamespace ${namespace}` : ''}`)
      .replaceAll('end Submission', `${namespace ? `end ${namespace}\n` : ''}end LeanEval`);
    fs.writeFileSync(path.join(project, 'Challenge.lean'), challenge);
    receipt.contract.formalStatement = challenge;
    const payload = canonicalMathProblemStatementPayloads(receipt.contract);
    receipt.contract.statementHash = mathDigest(payload.informal);
    receipt.contract.leanStatementHash = mathDigest(payload.lean);
    receipt.publicObligations = ['first', 'second'].map(local => `LeanEval.${namespace ? `${namespace}.` : ''}${local}`).map(name => ({ name,
      declarationHash: hashMathFormalSourceDeclaration(challenge, name) }));
    fs.writeFileSync(problem.activeProblemPath, JSON.stringify(receipt));
    git(workspace, ['add', 'generated/p/Challenge.lean']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Canonical challenge namespace']);
    const mapped = readSolverProblem(workspace, problem.activeProblemPath);
    expect(mapped.targets.map(item => item.theoremName)).toEqual(['Submission.first', 'Submission.second']);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).toBe(original);
    expect((await checkSolverProof(mapped, workspace, {})).passed).toBe(true);
    expect(host.verify.mock.calls[0][0].items.map(item => item.theoremName)).toEqual(['Submission.first', 'Submission.second']);
  });

  it('keeps an exact qualified target when another namespace has the same declaration header', () => {
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('end Submission',
      'namespace Nested\ntheorem first : True := by trivial\nend Nested\nend Submission'));
    expect(readSolverProblem(workspace, problem.activeProblemPath).targets.map(item => item.theoremName))
      .toEqual(['Submission.first', 'Submission.second']);
  });

  it('reuses an identical Lean rejection while rechecking changed proofs, notes and source constraints', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed',
        stdoutPreview: 'Submission.lean:4:1: error: unsolved goals\n⊢ True' })) }));
    const first = await checkSolverProof(problem, workspace, {});
    expect(await checkSolverProof(problem, workspace, {}, undefined, first)).toBe(first);
    expect(host.verify).toHaveBeenCalledTimes(1);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
    const changed = await checkSolverProof(problem, workspace, {}, undefined, first);
    expect(changed.commit).not.toBe(first.commit);
    expect(host.verify).toHaveBeenCalledTimes(2);
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'A different proof route');
    const notes = await checkSolverProof(problem, workspace, {}, undefined, changed);
    expect(notes.sourceDigest).toBe(changed.sourceDigest);
    expect(notes.commit).not.toBe(changed.commit);
    expect(host.verify).toHaveBeenCalledTimes(3);
    const controller = new AbortController();
    controller.abort();
    await expect(checkSolverProof(problem, workspace, {}, controller.signal, notes)).rejects.toThrow();
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('first : True', 'first : False'));
    await expect(checkSolverProof(problem, workspace, {}, undefined, notes)).rejects.toThrow('math_original_declaration_changed');
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it.each([
    ['kernel_verified', undefined, undefined],
    ['failed', 'Process exited without Lean diagnostics', undefined],
    ['failed', 'Submission.lean:4:1: error: unsolved goals', 'checkout cleanup failed'],
    ['blocked', 'Submission.lean:4:1: error: unsolved goals', undefined],
    ['unavailable', 'Submission.lean:4:1: error: unsolved goals', undefined],
  ] as const)('rechecks non-reusable results (status %s, output %s, cleanup %s)', async (status, stdoutPreview, cleanupError) => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status,
      results: verified(request).results.map(item => ({ ...item, status, stdoutPreview, cleanupError })) }));
    const first = await checkSolverProof(problem, workspace, {});
    expect(await checkSolverProof(problem, workspace, {}, undefined, first)).not.toBe(first);
    expect(host.verify).toHaveBeenCalledTimes(2);
  });

  it('checks in the isolated worktree, closes the model, rechecks integration and scores independently', async () => {
    expect(await runSolver(args, directory)).toBe(0);
    const result = JSON.parse(fs.readFileSync(output, 'utf8'));
    expect(result).toMatchObject({ status: 'evaluated_passed', solver_ready_receipt_valid: true,
      completion_signal_valid: true, evaluator: { official: true, method: 'official-comparator' } });
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.verify.mock.calls[0][0].projectRoot).toBe(path.join(`${output}.runtime/worktree`, 'generated/p'));
    expect(host.verify.mock.calls[1][0].projectRoot).toBe(project);
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(result.solution_commit);
    const session = await host.createSession.mock.results[0].value;
    expect(session.close).toHaveBeenCalledBefore(host.officialGate);
    expect(await runSolver([...args, '--resume'], directory)).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(1);
  });

  it('allows replacing context construction without replacing the executor or final acceptance', async () => {
    const execute = vi.fn(directSolverModules.M1.execute);
    const check = vi.fn(directSolverModules.M2.check);
    const build = vi.fn((...inputs: Parameters<typeof directSolverModules.M4.build>) => {
      const context = directSolverModules.M4.build(...inputs);
      return { ...context, message: `${context.message}\nTest context policy`, instructions: `${context.instructions}\nTest context policy` };
    });
    const modules = { ...directSolverModules, M1: { ...directSolverModules.M1, execute },
      M2: { ...directSolverModules.M2, check }, M4: { version: 'test-context-v1', build } };
    expect(await runSolver(args, directory, modules)).toBe(0);
    expect(execute.mock.calls[0][1]).toMatchObject({ scope: 'original-problem-and-allowed-library',
      sources: { problemReceiptDigest: problem.receiptDigest } });
    expect(execute.mock.calls[0][1].message).toContain('Test context policy');
    expect(host.createSession.mock.calls[0][0].instructions).toContain('Test context policy');
    expect(check).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.candidate).toMatchObject({ problemReceiptDigest: problem.receiptDigest, operation: 'direct',
      provenance: { workerId: 'solver', threadId: 'fixture-thread' } });
    expect(state.methodDigest).toMatch(/^[0-9a-f]{64}$/u);
  });

  const planTasks = (): CooperativeTask[] => [
    ...['a', 'b'].map(id => ({ id, kind: 'lemma' as const, objective: `Prove helper ${id}`, dependsOn: [],
      proofPath: 'Submission.lean', theoremName: `Submission.${id}`, type: 'True', revision: 0 })),
    { id: 'first', kind: 'goal', objective: 'Combine both helpers', dependsOn: ['a', 'b'],
      proofPath: 'Submission.lean', theoremName: 'Submission.first', revision: 0 },
    { id: 'second', kind: 'goal', objective: 'Use the checked first goal', dependsOn: ['first'],
      proofPath: 'Submission.lean', theoremName: 'Submission.second', revision: 0 },
  ];
  const writePlan = (worktree: string, tasks: readonly CooperativeTask[], groups?: readonly RouteGroup[]) =>
    fs.writeFileSync(path.join(worktree, 'RESEARCH.md'), '```math-plan\n' + JSON.stringify({ tasks, groups }) + '\n```\n');
  const assignmentFrom = (message: string) => JSON.parse(message.match(/Cooperative assignment:\n([^\n]+)/u)![1]) as CooperativeAction;
  function configureCooperation(run?: (action: CooperativeAction, options: MathAgentOptions, message: string) => Promise<string>) {
    host.verify.mockImplementation(async (request, options) => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      const wrongType = options.expectedDeclarationType && request.items.some(item =>
        source.includes(`${item.theoremName.split('.').at(-1)} : False`));
      const checked = verified(request);
      return !source.includes('sorry') && !wrongType ? checked : { ...checked, status: 'failed',
        results: checked.results.map(item => ({ ...item, status: 'failed',
          stdoutPreview: 'Submission.lean:3:1: error: task type mismatch or unfinished proof\n⊢ True' })) };
    });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      let calls = 0;
      return {
        threadId: options.threadId || `thread-${options.environment!.DEEPSCIENTIST_MATH_WORKER_ID}`,
        close: vi.fn(), interrupt: vi.fn(), run: async (message: string) => {
          calls++; options.onUsage({ inputTokens: calls * 1000, totalTokens: calls * 1200 });
          const action = assignmentFrom(message);
          if (run) return run(action, options, message);
          finishAssignment(action, options);
          return 'completed';
        },
      };
    });
  }
  function finishAssignment(action: CooperativeAction, options: MathAgentOptions) {
    if (action.kind === 'lead') { writePlan(options.workspace, planTasks()); return; }
    if (isStatementAction(action)) {
      fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```' + (action.kind === 'backtranslate' ? 'math-backtranslation' : 'math-statement-review') + '\n' + JSON.stringify({
        reviewId: action.reviewId, snapshotDigest: action.snapshotDigest,
        ...(action.kind === 'backtranslate' ? { mathematics: 'The proposition True holds.', assumptions: [], definitions: [], evidenceRefs: ['STATEMENT.json'] } :
          { verdict: 'accepted', summary: 'The fixed translation agrees with the intended proposition.', evidenceRefs: ['STATEMENT.json'] }),
      }) + '\n```'); return;
    }
    if (action.kind === 'review') {
      fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-review\n' + JSON.stringify({
        commit: action.seedCommit, verdict: 'accepted', summary: 'Both original targets are proved with matching premises.', evidenceRefs: ['Submission.first', 'Submission.second'],
      }) + '\n```'); return;
    }
    if (action.kind !== 'task') throw new Error('assembly_must_not_call_model');
    const file = path.join(options.workspace, 'generated/p/Submission.lean');
    const source = fs.readFileSync(file, 'utf8');
    const id = action.task.id;
    if (action.task.kind === 'lemma') fs.writeFileSync(file, source.includes(`lemma ${id} : True`)
      ? source.replace(`lemma ${id} : True := by sorry`, `lemma ${id} : True := by trivial`)
      : source.replace('theorem first', `lemma ${id} : True := by trivial\ntheorem first`));
    else if (id === 'first') {
      expect(source).toContain('lemma a : True := by trivial');
      expect(source).toContain('lemma b : True := by trivial');
      fs.writeFileSync(file, source.replace('first : True := by sorry', 'first : True := by exact And.left (And.intro a b)'));
    } else fs.writeFileSync(file, source.replace('second : True := by sorry', 'second : True := by exact first'));
  }

  it.each(['lead', 'task', 'backtranslate', 'statement-review', 'review'])('does not charge an unstarted cooperative %s assignment', async stoppedKind => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, stoppedKind.includes('translate') || stoppedKind === 'statement-review' ? statementTasks() : planTasks());
      else finishAssignment(action, options);
      return 'completed';
    });
    const select = vi.fn((...inputs: Parameters<typeof directSolverModules.M3.select>) => {
      const assignment = inputs[4]!;
      const stop = stoppedKind === 'lead' ? true : stoppedKind === 'review' ? assignment.kind === 'review' :
        assignment.kind !== 'lead' && !(stoppedKind === 'statement-review' && assignment.kind === 'backtranslate');
      return stop ? { operation: 'stop' as const, reason: 'no-operation' as const } : directSolverModules.M3.select(...inputs);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '12'], directory,
      { ...directSolverModules, M3: { ...directSolverModules.M3, select } })).toBe(4);
    expect(select.mock.calls.some(call => call[4]?.kind === stoppedKind)).toBe(true);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const spent = stoppedKind === 'review' ? 4 : stoppedKind === 'statement-review' ? 1 : 0;
    expect(state.cooperation.groups?.[0]?.turns ?? 0).toBe(spent);
    expect(state.turns).toBe(spent + (stoppedKind === 'lead' ? 0 : 1));
    expect(state.cooperation.tasks.every((node: any) => node.attempts === (stoppedKind === 'review' ? 1 : 0))).toBe(true);
    if (stoppedKind === 'review') expect(state.cooperation.review.status).toBe('pending');
    if (stoppedKind === 'backtranslate') expect(state.cooperation.statementReviews[0].status).toBe('pending');
    if (stoppedKind === 'statement-review') expect(state.cooperation.statementReviews[0].status).toBe('translated');
  });

  it.each(['direct', 'lemma'])('executes the %s method through cooperative roles without singleton lemma proposals', async method => {
    const operations: string[] = [];
    configureCooperation(async (action, options, message) => {
      expect(message).not.toContain('Propose one new ordinary theorem');
      expect(message).not.toContain('"target":"Original.qualifiedTarget"');
      if (method === 'lemma' && action.kind === 'lead') expect(message).toContain('Test the hardest connection first');
      finishAssignment(action, options); return 'completed';
    });
    const base = method === 'lemma' ? lemmaSolverModules : directSolverModules;
    const execute = vi.fn(async (...inputs: Parameters<typeof directSolverModules.M1.execute>) => {
      operations.push(inputs[2]);
      const candidate = await directSolverModules.M1.execute(...inputs);
      expect(candidate.lemmaPlanError).toBeUndefined();
      return candidate;
    });
    const checkLemma = vi.fn(checkLemmaResearch);
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory,
      { ...base, M1: { ...base.M1, execute }, M2: { ...base.M2, checkLemma } })).toBe(0);
    expect(new Set(operations)).toEqual(new Set(method === 'lemma' ? ['decompose', 'prove-lemma', 'integrate-lemma', 'direct'] : ['direct']));
    expect(checkLemma).not.toHaveBeenCalled();
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('uses replacement task evidence, blind contexts, role slots and reviewer selection in one cooperative solve', async () => {
    const checkTask = vi.fn(directSolverModules.M2.checkTask);
    const workers = vi.fn((...inputs: Parameters<typeof directSolverModules.M5.workers>) =>
      directSolverModules.M5.workers(...inputs).map((worker, index) => index === 1 ? { ...worker, id: 'mathematician' } :
        index === 2 ? { ...worker, id: 'auditor', role: 'reviewer' as const } : worker));
    const reviewer = vi.fn(directSolverModules.M5.reviewer);
    const organize = vi.fn(directSolverModules.M5.organize);
    const statement = vi.fn((...inputs: Parameters<typeof directSolverModules.M4.statement>) => {
      if (inputs[1].kind === 'backtranslate') {
        expect(inputs[0].intendedStatement).toBe(''); expect(inputs[0].premises).toEqual([]);
        expect(inputs[0].translation).toBeUndefined(); expect(JSON.stringify(inputs)).not.toContain('INTENT_SECRET');
      }
      const context = directSolverModules.M4.statement(...inputs);
      return { ...context, instructions: context.instructions + '\nCUSTOM_STATEMENT_CONTEXT' };
    });
    const reviews: string[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, statementTasks());
      else {
        if (isStatementAction(action)) expect(options.instructions).toContain('CUSTOM_STATEMENT_CONTEXT');
        if (isStatementAction(action) || action.kind === 'review') reviews.push(options.environment!.DEEPSCIENTIST_MATH_WORKER_ID!);
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory, {
      ...directSolverModules, M2: { ...directSolverModules.M2, checkTask }, M4: { ...directSolverModules.M4, statement },
      M5: { ...directSolverModules.M5, workers, reviewer, organize },
    })).toBe(0);
    expect(checkTask).toHaveBeenCalled(); expect(statement).toHaveBeenCalledTimes(2); expect(workers).toHaveBeenCalledOnce();
    expect(reviewer).toHaveBeenCalled(); expect(reviews).toEqual(['auditor', 'auditor', 'auditor']);
    expect(organize.mock.calls.every(call => call[1].length === 4)).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('rejects changed module role identities on resume before opening a model session', async () => {
    expect(await runSolver([...args, '--workers', '4', '--startup-only'], directory)).toBe(0);
    const prepared = fs.readFileSync(output, 'utf8');
    const workers = (...inputs: Parameters<typeof directSolverModules.M5.workers>) =>
      directSolverModules.M5.workers(...inputs).map((worker, index) => index === 1 ? { ...worker, id: 'changed' } : worker);
    expect(await runSolver([...args, '--workers', '4', '--resume'], directory,
      { ...directSolverModules, M5: { ...directSolverModules.M5, workers } })).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(prepared); expect(host.createSession).not.toHaveBeenCalled();
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('math_resume_worker_identity_changed'));
  });

  it('rejects task evidence carrying a different assignment version', async () => {
    configureCooperation();
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) =>
      ({ ...await directSolverModules.M2.checkTask(...inputs), taskDigest: 'wrong-version' });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(4);
    expect(cooperationState().tasks.some((node: any) => node.feedback === 'math_task_check_identity_changed')).toBe(true);
    expect(cooperationState().tasks.some((node: any) => node.status === 'integrated')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['worktree', 'files', 'reviewer'])('keeps host ownership when replacement M5 changes %s', async invalid => {
    configureCooperation();
    const workers = (...inputs: Parameters<typeof directSolverModules.M5.workers>) =>
      directSolverModules.M5.workers(...inputs).map((worker, index) => index !== 1 ? worker : invalid === 'worktree' ?
        { ...worker, worktree: workspace } : invalid === 'files' ? { ...worker, ownedFiles: ['Challenge.lean'] } : worker);
    const reviewer = (...inputs: Parameters<typeof directSolverModules.M5.reviewer>) => invalid === 'reviewer' ?
      { id: 'outsider', role: 'reviewer' as const, worktree: workspace, ownedFiles: problem.ownedFiles } : directSolverModules.M5.reviewer(...inputs);
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory,
      { ...directSolverModules, M5: { ...directSolverModules.M5, workers, reviewer } })).toBe(1);
    expect(host.officialGate).not.toHaveBeenCalled();
    if (invalid !== 'reviewer') expect(host.createSession).not.toHaveBeenCalled();
  });

  it('applies revised M4 instructions while resuming the same model thread', async () => {
    const seen: string[] = [], emitted: string[] = [];
    let calls = 0;
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'audit-thread', close: vi.fn(), interrupt: vi.fn(),
      run: async () => {
        seen.push(options.instructions ?? ''); calls++;
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', `by\n  -- ${calls}\n  trivial`));
        return 'completed';
      } }));
    const build = (...inputs: Parameters<typeof directSolverModules.M4.build>) => {
      const bundle = directSolverModules.M4.build(...inputs);
      return { ...bundle, instructions: bundle.instructions + `\nAUDIT_PHASE_${inputs[1].turns}` };
    };
    const execute = async (...inputs: Parameters<typeof directSolverModules.M1.execute>) => {
      emitted.push(inputs[1].instructions); return directSolverModules.M1.execute(...inputs);
    };
    expect(await runSolver([...args, '--max-turns', '2'], directory,
      { ...directSolverModules, M4: { ...directSolverModules.M4, build }, M1: { ...directSolverModules.M1, execute } })).toBe(0);
    expect(emitted[1]).toContain('AUDIT_PHASE_1');
    expect(seen[1]).toContain('AUDIT_PHASE_1'); expect(seen[1]).not.toContain('AUDIT_PHASE_0');
    expect(host.createSession).toHaveBeenCalledTimes(2);
    expect(host.createSession.mock.calls[1][0].threadId).toBe('audit-thread');
  });

  it('rejects a replacement M5 assigning a task to someone other than its explicit owner', async () => {
    const tasks = planTasks(); tasks[0] = { ...tasks[0], ownerId: 'researcher-1' };
    const assignments: any[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task') { assignments.push({ task: action.task.id, owner: action.task.ownerId, assigned: action.assignment.workerId }); finishAssignment(action, options); }
      else finishAssignment(action, options);
      return 'completed';
    });
    const assign = (...inputs: Parameters<typeof directSolverModules.M5.assign>) => inputs[1].id === 'researcher-2'
      ? inputs[0].find(node => node.task.id === 'a') ?? directSolverModules.M5.assign(...inputs)
      : inputs[1].id === 'researcher-1' ? inputs[0].find(node => node.task.id === 'b') ?? directSolverModules.M5.assign(...inputs) : directSolverModules.M5.assign(...inputs);
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory,
      { ...directSolverModules, M5: { ...directSolverModules.M5, assign } })).toBe(0);
    expect(assignments).toContainEqual({ task: 'a', owner: 'researcher-1', assigned: 'researcher-1' });
    expect(assignments).not.toContainEqual({ task: 'a', owner: 'researcher-1', assigned: 'researcher-2' });
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.workers.find((worker: any) => worker.id === 'researcher-2').error).toBe('math_task_assignment_invalid');
  });


  it.each(['single', 'task', 'backtranslate'])('refunds an unopened %s session reservation and keeps its assignment pending', async kind => {
    if (kind !== 'single') configureCooperation(async (action, options) => {
      if (action.kind === 'lead' && kind === 'backtranslate') writePlan(options.workspace, statementTasks());
      else finishAssignment(action, options);
      return 'completed';
    });
    const open = async (...inputs: Parameters<typeof directSolverModules.M1.open>) => {
      if (kind === 'single' || inputs[0].environment!.DEEPSCIENTIST_MATH_WORKER_ID !== 'solver') throw new Error('fixture_transport_unavailable');
      return directSolverModules.M1.open(...inputs);
    };
    expect(await runSolver([...args, '--workers', kind === 'single' ? '1' : '2', '--max-turns', '2'], directory,
      { ...directSolverModules, M1: { ...directSolverModules.M1, open } })).toBe(1);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBe(kind === 'single' ? 0 : 1);
    expect(host.createSession).toHaveBeenCalledTimes(kind === 'single' ? 0 : 1);
    expect(host.verify).not.toHaveBeenCalled();
    if (kind !== 'single') {
      expect(state.cooperation.groups[0].turns).toBe(0);
      expect(state.cooperation.tasks[0]).toMatchObject({ attempts: 0, status: 'pending' });
      expect(state.cooperation.tasks[0].assignment).toBeUndefined();
      if (kind === 'backtranslate') expect(state.cooperation.statementReviews[0].status).toBe('pending');
    }
  });

  it('rejects replacement M2 receipts with a mismatched source declaration hash', async () => {
    configureCooperation();
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const proof = await directSolverModules.M2.checkTask(...inputs);
      return { ...proof, verification: { ...proof.verification, results: proof.verification.results.map(result =>
        ({ ...result, sourceDeclarationHash: 'incorrect-declaration-hash' })) } };
    };
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory,
      { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } })).toBe(4);
    const tasks = cooperationState().tasks;
    expect(tasks.some((node: any) => node.feedback === 'math_task_check_identity_changed')).toBe(true);
    expect(tasks.some((node: any) => node.status === 'integrated')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
  });


  it('filters private statement reviews from both route prompts and cooperation journals', () => {
    const secret = { ...planTasks()[0], groupId: 'private', sharing: 'group' as const };
    const publicTask = { ...planTasks()[1], groupId: 'public' };
    const shared = { ...planTasks()[2], groupId: 'private', sharing: 'problem' as const };
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const peerRoot = path.join(directory, 'peer'); fs.mkdirSync(peerRoot);
    const peer = { id: 'researcher-1', role: 'researcher', worktree: peerRoot, ownedFiles: problem.ownedFiles } as const;
    const assignment = { taskId: publicTask.id, taskDigest: taskVersion(publicTask), workerId: peer.id, seedCommit: problem.baseCommit };
    const action = { kind: 'task' as const, task: publicTask, assignment };
    const reviews = [secret, publicTask, shared].map(task => ({ id: task.id, taskId: task.id, taskDigest: taskVersion(task), status: 'accepted',
      leanStatement: `theorem ${task.id} : True`, intendedStatement: task.id === secret.id ? 'PRIVATE_ROUTE_MARKER' : 'VISIBLE_' + task.id,
      premises: [], dependencies: [], workspace: directory, files: [], commit: problem.baseCommit, snapshotDigest: 'fixture', environmentDigest: 'fixture' }));
    const archive: any = { tasks: [{ task: secret, status: 'integrated', attempts: 1 },
      { task: publicTask, status: 'running', attempts: 0, assignment }, { task: shared, status: 'integrated', attempts: 1 }], statementReviews: reviews };
    const state: any = { problem, runId: 'audit', turns: 0, phase: 'running', failures: [], cooperation: archive,
      workers: [{ id: peer.id, worktree: peerRoot, sessionTaskId: publicTask.id }] };
    const cooperative = new CooperativeResearch({ state, workers: [lead, peer], access: new Map(),
      signal: new AbortController().signal, save: () => {}, emit: () => {}, modules: directSolverModules, exclusiveCheck: async check => check() });
    const scoped = cooperative.contextState(action);
    const bundle = directSolverModules.M4.build(problem, { ...state, cooperation: scoped }, {
      root: directory, worktree: peerRoot, taskText: 'Prove', environment: {}, retrievalRoot: workspace, assignment: action });
    expect(scoped.tasks.map(node => node.task.id)).toEqual([publicTask.id, shared.id]);
    expect(bundle.message).not.toContain('PRIVATE_ROUTE_MARKER');
    expect(bundle.message).toContain('VISIBLE_' + publicTask.id); expect(bundle.message).toContain('VISIBLE_' + shared.id);
    cooperative.activate(peer, action, async () => {}, async () => {});
    expect(JSON.parse(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8')).statements.map((review: any) => review.taskId))
      .toEqual([publicTask.id, shared.id]);
    cooperative.deactivate(peer);
    expect(fs.readFileSync(path.join(peerRoot, 'COOPERATION.json'), 'utf8')).not.toContain('PRIVATE_ROUTE_MARKER');
    expect(cooperative.contextState(undefined, peer).statementReviews?.map(review => review.taskId)).toEqual([publicTask.id, shared.id]);
    expect(cooperative.contextState({ ...action, task: secret }).statementReviews?.map(review => review.taskId)).toContain(secret.id);
    expect(cooperative.contextState(undefined, lead).statementReviews).toHaveLength(3);
  });

  it.each(['stale-body', 'changed-context'])('rejects replacement M2 receipts for a different %s projection', async kind => {
    configureCooperation();
    const task = planTasks()[0];
    const file = path.join(project, 'Submission.lean');
    fs.writeFileSync(file, original.replace('theorem first', 'lemma a : True := by trivial\ntheorem first'));
    const goodCommit = commitSolverSources(problem, workspace);
    const assignment = { taskId: task.id, taskDigest: taskVersion(task), workerId: 'researcher-1', seedCommit: problem.baseCommit };
    const good = await directSolverModules.M2.checkTask(problem, workspace, goodCommit, task, assignment, [], {}, new AbortController().signal);
    expect(good.passed).toBe(true);
    let submittedCommit = goodCommit;
    if (kind === 'stale-body') {
      fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('lemma a : True := by trivial', 'lemma a : True := by sorry'));
      submittedCommit = commitSolverSources(problem, workspace);
    } else {
      await withSolverWorktree(workspace, good.verification.targetCommit!, async checkout => {
        fs.writeFileSync(path.join(checkout, 'generated/p/Challenge.lean'), 'def changedTrusted : Nat := 0\n');
        git(checkout, ['add', '--', 'generated/p/Challenge.lean']);
        git(checkout, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Alter context']);
        const targetCommit = git(checkout, ['rev-parse', 'HEAD']);
        good.verification = { ...good.verification, targetCommit, results: good.verification.results.map(result => ({ ...result, targetCommit })) };
      });
    }
    const checkTask = async (...inputs: Parameters<typeof directSolverModules.M2.checkTask>) => {
      const fresh = await directSolverModules.M2.checkTask(...inputs);
      expect(fresh.passed).toBe(kind !== 'stale-body');
      return { ...fresh, passed: good.passed, verification: good.verification };
    };
    const lead = { id: 'solver', role: 'lead', worktree: workspace, ownedFiles: problem.ownedFiles } as const;
    const state: any = { problem, environmentDigest: 'fixture', cooperation: { tasks: [{ task, status: 'running', attempts: 1, assignment }] } };
    const cooperative = new CooperativeResearch({ state, workers: [lead], access: new Map([[lead.id, { environment: {}, retrievalRoot: workspace }]]),
      signal: new AbortController().signal, save: () => {}, emit: () => {},
      modules: { ...directSolverModules, M2: { ...directSolverModules.M2, checkTask } }, exclusiveCheck: async check => check() });
    await expect((cooperative as any).check(task, assignment, workspace, submittedCommit)).rejects.toThrow('math_task_check_identity_changed');
  });

  it.each([false, true])('keeps healthy peers available while a pending open settles with failure=%s', async failure => {
    configureCooperation();
    const open = async (...inputs: Parameters<typeof directSolverModules.M1.open>) => {
      if (inputs[0].environment!.DEEPSCIENTIST_MATH_WORKER_ID === 'researcher-2') {
        await expect.poll(() => cooperationState().tasks[0].status).toBe('integrated');
        // Let the healthy worker reach its next assignment request while the last turn is still reserved.
        await new Promise(resolve => setImmediate(resolve));
        const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
        expect(state.workers.find((worker: any) => worker.id === 'researcher-1').phase).not.toBe('finished');
        if (failure) throw new Error('fixture_pending_open_failed');
      }
      return directSolverModules.M1.open(...inputs);
    };
    const code = await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory,
      { ...directSolverModules, M1: { ...directSolverModules.M1, open } });
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(code).toBe(failure ? 1 : 4);
    expect(state.turns).toBe(3);
    expect(state.cooperation.tasks.slice(0, 2).map((node: any) => node.status)).toEqual(['integrated', 'integrated']);
    expect(state.cooperation.tasks.slice(0, 2).map((node: any) => node.attempts)).toEqual([1, 1]);
    expect(state.cooperation.groups[0].turns).toBe(2);
    if (failure) expect(state.workers.find((worker: any) => worker.id === 'researcher-1').turns).toBe(2);
  });


  it('keeps preassigned peers available when another worker reserves the last turn', async () => {
    configureCooperation();
    const open = async (...inputs: Parameters<typeof directSolverModules.M1.open>) => {
      if (inputs[0].environment!.DEEPSCIENTIST_MATH_WORKER_ID === 'researcher-1') {
        await new Promise(resolve => setImmediate(resolve));
        const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
        expect(state.workers.find((worker: any) => worker.id === 'researcher-2').phase).not.toBe('finished');
        throw new Error('fixture_pending_open_failed');
      }
      return directSolverModules.M1.open(...inputs);
    };
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '2'], directory,
      { ...directSolverModules, M1: { ...directSolverModules.M1, open } })).toBe(1);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBe(2);
    expect(state.workers.find((worker: any) => worker.id === 'researcher-2').turns).toBe(1);
    expect(state.cooperation.tasks[1]).toMatchObject({ status: 'integrated', attempts: 1 });
  });

  it('rejects replacement M5 assignments outside the configured route engineer', async () => {
    const tasks = planTasks().slice(2).map(task => ({ ...task, dependsOn: [] }));
    const assignments: string[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task') {
        assignments.push(action.assignment.workerId);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    const assign = (...inputs: Parameters<typeof directSolverModules.M5.assign>) => inputs[1].id === 'researcher-1'
      ? inputs[0][0] : directSolverModules.M5.assign(...inputs);
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '4'], directory,
      { ...directSolverModules, M5: { ...directSolverModules.M5, assign } })).toBe(0);
    expect(assignments).toEqual(['engineer', 'engineer']);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.workers.find((worker: any) => worker.id === 'researcher-1').error).toBe('math_task_assignment_invalid');
  });

  it('lets replacement M4 exclude peer history from the final cooperative prompt', async () => {
    const tasks: CooperativeTask[] = [{ id: 'question', kind: 'research', objective: 'Explore first', dependsOn: [], revision: 0 }, ...planTasks()];
    tasks[1] = { ...tasks[1], dependsOn: ['question'] };
    const build = (...inputs: Parameters<typeof directSolverModules.M4.build>) => ({
      ...directSolverModules.M4.build(...inputs), message: 'CUSTOM_CONTEXT_WITHOUT_PEER_HISTORY\nCooperative assignment:\n' + JSON.stringify(inputs[2].assignment) });
    let checked = false;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.kind === 'research')
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math\n{"summary":"EXCLUDED_PEER_HISTORY"}\n```');
      else {
        if (action.kind === 'task' && action.task.id === 'a') {
          expect(message).toContain('CUSTOM_CONTEXT_WITHOUT_PEER_HISTORY');
          expect(message).not.toContain('EXCLUDED_PEER_HISTORY'); checked = true;
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '7'], directory,
      { ...directSolverModules, M4: { ...directSolverModules.M4, build } })).toBe(0);
    expect(checked).toBe(true);
  });

  it('uses one minimal math response format for plans, research, backtranslation and reviews', async () => {
    const tasks: CooperativeTask[] = [{ id: 'question', kind: 'research', objective: 'Explore a route', dependsOn: [], revision: 0 }, ...planTasks()];
    tasks[3] = { ...tasks[3], statementReview: true, informalStatement: 'The proposition True holds.' };
    const write = (workspace: string, value: object) => fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), '```math\n' + JSON.stringify(value) + '\n```');
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') write(options.workspace, { tasks: tasks.map(({ revision: _revision, proofPath: _path, dependsOn, ...task }) =>
        ({ ...task, ...(dependsOn.length ? { dependsOn } : {}) })) });
      else if (action.kind === 'backtranslate') write(options.workspace, { mathematics: 'The proposition True holds.' });
      else if (action.kind === 'statement-review' || action.kind === 'review') write(options.workspace, { verdict: 'accepted', summary: 'The statement matches its intention.' });
      else if (action.kind === 'task' && action.task.kind === 'research') write(options.workspace, { summary: 'True.intro provides the needed proof.' });
      else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '9'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.map((node: any) => node.task)).toEqual(tasks);
    expect(state.cooperation.statementReviews[0]).toMatchObject({ status: 'accepted', translation: {
      mathematics: 'The proposition True holds.', assumptions: [], definitions: [], evidenceRefs: [] } });
    expect(state.cooperation.review.status).toBe('accepted');
    expect(state.cooperation.deliveries.find((record: any) => record.kind === 'research')).toMatchObject({ taskId: 'question', evidenceRefs: [] });
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('keeps explicit response bindings for host validation and rejects ambiguous blocks', () => {
    const file = path.join(workspace, 'RESEARCH.md');
    fs.writeFileSync(file, '```math\n{"summary":"first"}\n```\n```math-result\n{"summary":"second"}\n```');
    expect(() => readMathResponse(workspace, 'math-result')).toThrow('requires_one_block');
    fs.writeFileSync(file, '```math\n{"commit":"wrong-version","summary":"first"}\n```');
    expect(readMathResponse(workspace, 'math-review', { commit: 'assigned-version' }).commit).toBe('wrong-version');
  });

  it('shares simple progress and fixed proofs early without requiring agents to repeat assignment metadata', async () => {
    const bothStarted = deferred(), aDelivered = deferred(); let started = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.kind === 'lemma') {
        if (++started === 2) bothStarted.resolve();
        await bothStarted.promise;
        const log = path.join(options.workspace, assignmentDeliveryFile(action.assignment));
        const progress = JSON.stringify({ summary: 'Working on the assigned helper' });
        fs.appendFileSync(log, progress + '\n' + progress + '\n');
        finishAssignment(action, options);
        fs.appendFileSync(log, JSON.stringify({ kind: 'proof', commit: commitSolverSources(problem, options.workspace), summary: 'Helper proved' }) + '\n');
        await expect.poll(() => cooperationState().tasks.find((node: any) => node.task.id === action.task.id)?.status).toBe('integrated');
        if (action.task.id === 'a') aDelivered.resolve();
        else await aDelivered.promise;
      } else finishAssignment(action, options);
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '5'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(await runSolver([...parallelArgs, '--max-turns', '6', '--resume'], directory)).toBe(0);
    const records = cooperationState().deliveries;
    for (const id of ['a', 'b']) {
      expect(records.filter((record: any) => record.taskId === id && record.kind === 'progress')).toHaveLength(1);
      expect(records.find((record: any) => record.taskId === id && record.kind === 'proof')).toMatchObject({ status: 'verified', taskDigest: taskVersion(planTasks().find(task => task.id === id)!) });
    }
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('keeps simplified delivery logs bound to their assignment across live revisions', async () => {
    const tasks = planTasks(); let oldLog = '', oldCommit = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a') {
        const log = path.join(options.workspace, assignmentDeliveryFile(action.assignment));
        fs.appendFileSync(log, '{"summary":"Same progress text"}\n');
        await expect.poll(() => cooperationState().deliveries.some((record: any) => record.taskId === 'a' &&
          record.taskDigest === action.assignment.taskDigest && record.kind === 'progress')).toBe(true);
        if (action.task.revision === 0) {
          oldLog = log; finishAssignment(action, options); oldCommit = commitSolverSources(problem, options.workspace);
          tasks[0] = { ...tasks[0], revision: 1 };
          fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'simple-revision', baseVersion: cooperationState().planVersion, tasks }) + '\n');
          await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
        } else {
          expect(log).not.toBe(oldLog);
          fs.appendFileSync(oldLog, JSON.stringify({ kind: 'proof', summary: 'Late old proof', commit: oldCommit }) + '\n');
          fs.appendFileSync(log, '{"summary":"New assignment continues"}\n');
          await expect.poll(() => cooperationState().deliveries.some((record: any) => record.summary === 'New assignment continues')).toBe(true);
          finishAssignment(action, options);
        }
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(0);
    const records = cooperationState().deliveries, progress = records.filter((record: any) => record.summary === 'Same progress text');
    expect(progress).toHaveLength(2); expect(progress[0].status).toBe('superseded');
    expect(progress[0].submissionId).not.toBe(progress[1].submissionId);
    expect(progress[1].taskDigest).toBe(taskVersion(tasks[0]));
    expect(records.some((record: any) => record.summary === 'Late old proof')).toBe(false);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('requires a new simplified review response after the reviewed proof version changes', async () => {
    const tasks = planTasks(), reviewStopped = deferred(); let reviews = 0, reviewerWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'review') {
        if (++reviews === 1) {
          reviewerWorkspace = options.workspace;
          fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math\n{"verdict":"accepted","summary":"Old version reviewed"}\n```');
          tasks[0] = { ...tasks[0], revision: 1 };
          fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'simple-review-revision', baseVersion: cooperationState().planVersion, tasks }) + '\n');
          await reviewStopped.promise;
        }
        // The next review deliberately writes nothing; the previous response cannot authorize it.
      } else finishAssignment(action, options);
      return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === reviewerWorkspace) reviewStopped.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(4);
    expect(reviews).toBe(2);
    expect(cooperationState().review.status).toBe('changes_requested');
    expect(cooperationState().deliveries.filter((record: any) => record.kind === 'review').map((record: any) => record.status))
      .toEqual(['superseded', 'changes_requested']);
    expect(host.officialGate).not.toHaveBeenCalled();
  }, 20_000);

  it('runs distinct helpers concurrently, combines same-file changes and checks the canonical proof after the turn budget is exhausted', async () => {
    let started = 0;
    let release!: () => void;
    const bothStarted = new Promise<void>(resolve => { release = resolve; });
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.kind === 'lemma') {
        expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(original);
        if (++started === 2) release();
        await bothStarted;
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(started).toBe(2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.map(node => node.status)).toEqual(['integrated', 'integrated', 'integrated', 'integrated']);
    expect(state.turns).toBe(6);
    expect(state.winningWorker).toBe('solver');
    expect(state.usage).toMatchObject({ inputTokens: 6000, totalTokens: 7200 });
    const source = fs.readFileSync(path.join(state.worktree, 'generated/p/Submission.lean'), 'utf8');
    expect(source).toContain('lemma a'); expect(source).toContain('lemma b'); expect(source).not.toContain('sorry');
    const events = vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event));
    const assigned = events.findIndex(event => event.event === 'task_assigned' && event.taskId === 'first');
    for (const id of ['a', 'b']) expect(events.findIndex(event => event.event === 'task_integrated' && event.taskId === id)).toBeLessThan(assigned);
    expect(host.verify.mock.calls.filter(([request]) => request.items.length === 2)).toHaveLength(2);
    expect(host.officialGate).toHaveBeenCalledOnce();
    for (const result of await Promise.all(host.createSession.mock.results.map(result => result.value)))
      expect(result.close).toHaveBeenCalledBefore(host.officialGate);
  });

  it('does not accept checked partial proofs as a solution and rechecks integrated evidence on resume', async () => {
    configureCooperation();
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.slice(0, 2).map(node => node.status)).toEqual(['integrated', 'integrated']);
    expect(state.check).toBeUndefined();
    expect(host.officialGate).not.toHaveBeenCalled();
    const before = fs.readFileSync(output, 'utf8');
    expect(await runSolver([...parallelArgs, '--resume', '--workers', '2'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(before);
    const checks = host.verify.mock.calls.length;
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory)).toBe(0);
    expect(host.verify.mock.calls.slice(checks, checks + 2).map(([request]) => request.items[0].theoremName)).toEqual(['Submission.a', 'Submission.b']);
    for (const [options] of host.createSession.mock.calls.slice(3)) expect(options.threadId).toBe(
      options.environment.DEEPSCIENTIST_MATH_WORKER_ID === 'engineer' || options.instructions.includes('You are the Independent Reviewer') ? undefined : `thread-${options.environment.DEEPSCIENTIST_MATH_WORKER_ID}`);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('keeps cooperative partial checks unlimited when the total solving limit is disabled', async () => {
    configureCooperation();
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '0', '--max-run-seconds', '0'], directory)).toBe(0);
    const partialChecks = host.verify.mock.calls.filter(([request]) => request.items.length === 1);
    expect(partialChecks).toHaveLength(8);
    for (const [request] of partialChecks) expect(request).toMatchObject({ timeoutMs: Infinity, batchTimeoutMs: Infinity });
  });

  const routeGroups = (): RouteGroup[] => [
    { id: 'main', objective: 'Prove the original obligations', status: 'active', revision: 0, engineerId: 'engineer' },
    { id: 'alternative', objective: 'Test an alternative bridge', status: 'active', revision: 0, maxTurns: 2, maxConcurrent: 1 },
  ];
  const groupedTasks = () => planTasks().map(task => ({ ...task, groupId: task.id === 'b' ? 'alternative' : 'main',
    sharing: task.id === 'b' ? 'problem' as const : 'group' as const }));

  it('reuses a checked cross-route lemma with its explicit sharing, producer and version', async () => {
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, groupedTasks(), routeGroups());
      else {
        if (action.kind === 'task' && action.task.id === 'first') {
          expect(message).toContain('"groupId":"alternative"');
          expect(message).toContain('"producer":"researcher-');
          expect(message).toContain('checkedSourceDigest');
          expect(message).toContain('integratedCommit');
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.groups.map(route => [route.group.id, route.turns])).toEqual([['main', 3], ['alternative', 1]]);
    const bridge = state.cooperation.tasks.find(node => node.task.id === 'b');
    expect(bridge.assignment).toMatchObject({ groupId: 'alternative', canonicalCommit: expect.any(String) });
    expect(bridge.integratedCheck.passed).toBe(true);
    expect(state.cooperation.tasks.filter(node => node.task.kind === 'goal').every(node => node.assignment.workerId === 'engineer')).toBe(true);
  });

  it.each(['paused', 'stopped', 'budget'] as const)('keeps inactive-route work idle and continues independent tasks (%s)', async mode => {
    const groups = routeGroups();
    groups[1] = { ...groups[1], ...(mode === 'budget' ? { maxTurns: 0 } : { status: mode }) };
    const tasks = groupedTasks();
    tasks[3] = { ...tasks[3], dependsOn: [] };
    let started = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks, groups);
      else if (action.kind === 'task' && action.task.id === 'second') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('second : True := by sorry', 'second : True := by trivial'));
        started++;
      } else finishAssignment(action, options);
      return 'completed';
    });
    // Spare global turns must not be spent repeatedly asking the Lead to restart an inactive route.
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '10'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(started).toBe(1);
    expect(state.turns).toBe(3);
    expect(state.cooperation.tasks.map(node => node.status)).toEqual(['integrated', 'pending', 'pending', 'integrated']);
    expect(state.cooperation.groups[1].turns).toBe(0);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('enforces per-route concurrency and preserves the accumulated route budget when extended on resume', async () => {
    const groups = [{ ...routeGroups()[0], maxTurns: 1, maxConcurrent: 1 }];
    let active = 0, peak = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, planTasks(), groups);
      else {
        active++; peak = Math.max(peak, active);
        await Promise.resolve();
        finishAssignment(action, options); active--;
      }
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '10'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.groups[0].turns).toBe(1);
    expect(state.turns).toBe(2);
    expect(state.cooperation.tasks[0].status).toBe('integrated');
    writePlan(state.worktree, planTasks(), [{ ...groups[0], maxTurns: 4 }]);
    expect(await runSolver([...parallelArgs, '--resume'], directory)).toBe(0);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.groups[0].turns).toBe(4);
    expect(resumed.cooperation.tasks[0].attempts).toBe(1);
    expect(resumed.cooperation.history).toBeUndefined();
    expect(peak).toBe(1);
  });

  it('shows only a route\'s own artifacts and checked public findings in its task context and seeded source', async () => {
    const tasks: CooperativeTask[] = [
      { ...planTasks()[0], groupId: 'alternative', sharing: 'group' },
      ...planTasks().slice(2).map(task => ({ ...task, groupId: 'main', dependsOn: task.id === 'first' ? [] : ['first'] })),
    ];
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks, routeGroups());
      else if (action.kind === 'task' && action.task.kind === 'goal') {
        expect(message).not.toContain('Prove helper a');
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        const source = fs.readFileSync(file, 'utf8');
        expect(source).not.toContain('lemma a');
        fs.writeFileSync(file, source.replace(`${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '5'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(fs.readFileSync(path.join(state.worktree, 'generated/p/Submission.lean'), 'utf8')).toContain('lemma a');
  });

  it('reactivates a paused route on resume and retains unrelated integrated work', async () => {
    const groups = routeGroups();
    groups[1] = { ...groups[1], status: 'paused' };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, groupedTasks(), groups);
      else finishAssignment(action, options);
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '10'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks[0].status).toBe('integrated');
    writePlan(state.worktree, groupedTasks(), routeGroups());
    expect(await runSolver([...parallelArgs, '--resume'], directory)).toBe(0);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.tasks.map(node => node.attempts)).toEqual([1, 1, 1, 1]);
    expect(resumed.cooperation.groups.map(route => route.turns)).toEqual([3, 1]);
    expect(resumed.cooperation.history).toBeUndefined();
  });

  it('invalidates a revised route and cross-route consumers while preserving the other route\'s verified lemma', async () => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, groupedTasks(), routeGroups());
      else finishAssignment(action, options);
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '5'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks.every(node => node.status === 'integrated')).toBe(true);
    const groups = routeGroups();
    groups[1] = { ...groups[1], revision: 1 };
    writePlan(state.worktree, groupedTasks(), groups);
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '9'], directory)).toBe(0);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.tasks.map(node => node.attempts)).toEqual([1, 2, 2, 2]);
    expect(resumed.cooperation.history.map(node => node.task.id)).toEqual(['b', 'first', 'second']);
    expect(resumed.cooperation.groups[1].turns).toBe(2);
  });

  it.each(['unknown', 'private-dependency', 'concurrency', 'duplicate', 'budget'] as const)('rejects an invalid route plan (%s)', flaw => {
    const tasks = groupedTasks();
    const groups = routeGroups();
    if (flaw === 'unknown') tasks[0] = { ...tasks[0], groupId: 'unknown' };
    if (flaw === 'private-dependency') tasks[1] = { ...tasks[1], sharing: undefined };
    if (flaw === 'concurrency') groups[1] = { ...groups[1], maxConcurrent: 0 };
    if (flaw === 'duplicate') groups.push(groups[0]);
    if (flaw === 'budget') groups[1] = { ...groups[1], maxTurns: -1 };
    writePlan(workspace, tasks, groups);
    expect(() => readCooperationPlan(problem, workspace)).toThrow(/math_plan/u);
  });

  it('lets the Engineer prove an independent goal while both Researchers work on helpers', async () => {
    let started = 0;
    let release!: () => void;
    const threeStarted = new Promise<void>(resolve => { release = resolve; });
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, planTasks().map(task => task.id === 'second' ? { ...task, dependsOn: [] } : task));
      } else if (action.kind === 'task' && action.task.id !== 'first') {
        if (++started === 3) release();
        await threeStarted;
        if (action.task.id === 'second') {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          fs.writeFileSync(file, original.replace('second : True := by sorry', 'second : True := by trivial'));
        } else finishAssignment(action, options);
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(started).toBe(3);
  });

  it('applies a local task revision on resume, invalidates consumers and keeps unrelated checked work', async () => {
    configureCooperation();
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    writePlan(state.worktree, planTasks().map(task => task.id === 'a' ? { ...task, revision: 1 } : task));
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '7'], directory)).toBe(0);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.tasks.slice(0, 2).map(node => node.attempts)).toEqual([2, 1]);
    expect(resumed.cooperation.history.map(node => node.task.id)).toEqual(['a', 'first', 'second']);
    expect(resumed.cooperation.tasks[0].task.revision).toBe(1);
  });

  it('rechecks modified canonical helpers and prevents consumers from using invalid evidence on resume', async () => {
    configureCooperation();
    const parallelArgs = [...args, '--workers', '4', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const file = path.join(state.worktree, 'generated/p/Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('lemma a : True := by trivial', 'lemma a : True := by sorry'));
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '4'], directory)).toBe(4);
    const resumed = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(resumed.cooperation.tasks[0].status).toBe('blocked');
    expect(resumed.cooperation.tasks[1].status).toBe('integrated');
    expect(resumed.cooperation.tasks.slice(2).every(node => node.attempts === 0)).toBe(true);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('rejects a Reviewer that changes the fixed proof and keeps review separate from Lean acceptance', async () => {
    configureCooperation(async (action, options) => {
      finishAssignment(action, options);
      if (action.kind === 'review') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('by exact first', 'by trivial'));
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.review).toMatchObject({ status: 'changes_requested', summary: 'math_review_source_changed' });
    expect(state.check).toBeUndefined();
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each([false, true])('blocks the wrong helper type and retries only after a Lead revision (revise: %s)', async revise => {
    let leadTurns = 0, helperTurns = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        const tasks = planTasks();
        if (++leadTurns > 1) {
          expect(message).toContain('task type mismatch');
          if (revise) tasks[0] = { ...tasks[0], revision: 1 };
        }
        writePlan(options.workspace, tasks);
      } else if (action.kind === 'task' && action.task.id === 'a' && ++helperTurns === 1) {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, original.replace('theorem first', 'lemma a : False := by trivial\ntheorem first'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(revise ? 0 : 4);
    expect(helperTurns).toBe(revise ? 2 : 1);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.cooperation.tasks[0].status).toBe(revise ? 'integrated' : 'blocked');
    expect(host.verify.mock.calls.filter(([, options]) => options.expectedDeclarationType).every(([, options]) => options.expectedDeclarationType === 'True')).toBe(true);
  });

  it.each(['cycle', 'missing', 'duplicate', 'coverage', 'target'])('rejects a %s plan before dispatch', flaw => {
    const tasks = planTasks();
    if (flaw === 'cycle') tasks[0] = { ...tasks[0], dependsOn: ['first'] };
    if (flaw === 'missing') tasks[0] = { ...tasks[0], dependsOn: ['unknown'] };
    if (flaw === 'duplicate') tasks.push({ ...tasks[2], id: 'duplicate' });
    if (flaw === 'coverage') tasks.pop();
    if (flaw === 'target') tasks[2] = { ...tasks[2], theoremName: 'Submission.changed' };
    writePlan(workspace, tasks);
    expect(() => readCooperativePlan(problem, workspace)).toThrow(/math_plan/u);
  });

  it('shares routine research findings without a Lead relay or accepting them as proof', async () => {
    const tasks: CooperativeTask[] = [{ id: 'route', kind: 'research', objective: 'Review the route and look for counterexamples', dependsOn: [], revision: 0 },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: ['route'] }))];
    let leadTurns = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') {
        if (++leadTurns > 1) expect(message).toContain('Use True.intro');
        writePlan(options.workspace, tasks);
      } else if (action.kind === 'task' && action.task.kind === 'research') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' +
          JSON.stringify({ taskId: 'route', summary: 'Use True.intro', conclusion: 'supporting', evidenceRefs: ['Lean core: True.intro'] }) + '\n```');
      } else if (action.kind === 'review') finishAssignment(action, options);
      else if (action.kind === 'task') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        const name = action.task.id;
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${name} : True := by sorry`, `${name} : True := by trivial`));
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(leadTurns).toBe(1);
    expect(host.verify.mock.calls.some(([request]) => request.items.some(item => item.theoremName === 'route'))).toBe(false);
  });

  it('cancels active task sessions, preserves drafts and resumes the same assignments', async () => {
    let started = 0;
    const stop = new Map<string, () => void>();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({
      threadId: `thread-${options.environment!.DEEPSCIENTIST_MATH_WORKER_ID}`, interrupt: vi.fn(),
      close: vi.fn(async () => { stop.get(options.workspace)?.(); }),
      run: async (message: string) => {
        const action = assignmentFrom(message);
        if (action.kind === 'lead') { finishAssignment(action, options); return 'completed'; }
        if (action.kind !== 'task') throw new Error('unexpected_action');
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, original.replace('theorem first', `lemma ${action.task.id} : True := by sorry\ntheorem first`));
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), `Draft ${action.task.id}`);
        const stopped = new Promise<void>(resolve => { stop.set(options.workspace, resolve); });
        if (++started === 2) process.emit('SIGTERM');
        await stopped; return 'interrupted';
      },
    }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '3'], directory)).toBe(4);
    expect(host.verify).not.toHaveBeenCalled();
    for (const result of await Promise.all(host.createSession.mock.results.map(result => result.value))) expect(result.close).toHaveBeenCalledOnce();
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.kind === 'lemma') {
        expect(options.threadId).toBe(`thread-${options.environment!.DEEPSCIENTIST_MATH_WORKER_ID}`);
        expect(fs.readFileSync(path.join(options.workspace, 'RESEARCH.md'), 'utf8')).toBe(`Draft ${action.task.id}`);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`lemma ${action.task.id} : True := by sorry`, `lemma ${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8', '--resume'], directory)).toBe(0);
  });

  const deferred = () => {
    let resolve!: () => void;
    const promise = new Promise<void>(done => { resolve = done; });
    return { promise, resolve };
  };
  const cooperationState = () => JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).cooperation;
  const appendDelivery = (options: MathAgentOptions, action: Extract<CooperativeAction, { kind: 'task' }>, value: Record<string, unknown>) =>
    fs.appendFileSync(path.join(options.workspace, 'DELIVERIES.jsonl'), JSON.stringify({ taskId: action.task.id,
      taskDigest: action.assignment.taskDigest, evidenceRefs: [], ...value }) + '\n');

  const statementTasks = () => {
    const tasks = planTasks();
    tasks[0] = { ...tasks[0], statementReview: true, informalStatement: 'INTENT_SECRET: the proposition True holds.' };
    return tasks;
  };

  it('reviews a fixed statement before its proof finishes, using blind fresh sessions and the shared budget', async () => {
    const tasks = statementTasks(), proofStarted = deferred(), comparisonDone = deferred();
    const statements: MathAgentOptions[] = [];
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'task' && action.task.id === 'a') { proofStarted.resolve(); await comparisonDone.promise; }
      if (isStatementAction(action)) {
        statements.push(options);
        expect(options.threadId).toBeUndefined(); expect(options.workspace).toBe(action.workspace);
        expect(Object.keys(options.environment!).filter(key => key.startsWith('DEEPSCIENTIST_MATH_')).sort())
          .toEqual(['DEEPSCIENTIST_MATH_WORKER_ID', 'DEEPSCIENTIST_MATH_WORKER_WORKTREE']);
        expect(fs.existsSync(path.join(options.workspace, '.git'))).toBe(false);
        expect(fs.existsSync(path.join(options.workspace, 'COOPERATION.json'))).toBe(false);
        const view = fs.readFileSync(path.join(options.workspace, 'STATEMENT.json'), 'utf8') +
          fs.readdirSync(path.join(options.workspace, 'definitions')).map(file => fs.readFileSync(path.join(options.workspace, 'definitions', file), 'utf8')).join('');
        expect(view).not.toContain('INTENT_SECRET'); expect(view).not.toContain('by sorry');
        if (action.kind === 'backtranslate') {
          expect(message + options.instructions).not.toContain('INTENT_SECRET'); expect(message).not.toContain('Original problem:');
          await proofStarted.promise;
        } else {
          expect(message).toContain('INTENT_SECRET'); expect(message).toContain('The proposition True holds.');
          expect(cooperationState().tasks[0].status).toBe('running');
          expect(host.officialGate).not.toHaveBeenCalled(); comparisonDone.resolve();
        }
      }
      finishAssignment(action, options); return 'completed';
    });
    const execute = vi.fn(directSolverModules.M1.execute);
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory,
      { ...directSolverModules, M1: { ...directSolverModules.M1, execute } })).toBe(0);
    expect(statements).toHaveLength(2); expect(execute.mock.calls.every(call => call[1].scope !== 'fixed-statement')).toBe(true);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBe(8); expect(state.usage).toMatchObject({ inputTokens: 8000, totalTokens: 9600 });
    expect(state.cooperation.groups[0].turns).toBe(6); expect(state.cooperation.statementReviews).toHaveLength(1);
    expect(state.cooperation.statementReviews[0]).toMatchObject({ status: 'accepted', translation: { mathematics: 'The proposition True holds.' } });
    const records = state.cooperation.deliveries.filter((record: any) => ['backtranslation', 'statement-review'].includes(record.kind));
    expect(records.map((record: any) => record.status)).toEqual(['advisory', 'accepted']);
    expect(records.every((record: any) => record.evidence === undefined)).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  });

  it('counts both statement phases against route limits without granting any proof acceptance', async () => {
    const tasks = statementTasks();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks, [{ id: 'main', objective: 'Prove both goals', status: 'active', revision: 0, maxTurns: 2 }]);
      else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(4);
    expect(cooperationState().statementReviews[0].status).toBe('accepted');
    expect(cooperationState().tasks.every((node: any) => node.status === 'pending')).toBe(true);
    expect(cooperationState().groups[0].turns).toBe(2);
    expect(host.verify).not.toHaveBeenCalled(); expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('waits for the blind session to close before another worker can compare its statement', async () => {
    const tasks = statementTasks(), closing = deferred(), releaseClose = deferred();
    let blindWorkspace = '', closed = false, comparisonStarted = false, closeHeld = false;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') blindWorkspace = options.workspace;
      if (action.kind === 'statement-review') { expect(closed).toBe(true); comparisonStarted = true; }
      if (action.kind === 'task' && action.task.id === 'a') {
        await closing.promise;
        expect(comparisonStarted).toBe(false); releaseClose.resolve();
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const session = await create(options);
      return { ...session, close: vi.fn(async () => {
        if (options.workspace === blindWorkspace && !closeHeld) {
          closeHeld = true; closing.resolve(); await releaseClose.promise; closed = true;
        }
        await session.close();
      }) };
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(0);
    expect(comparisonStarted).toBe(true);
  });

  it.each(['meaning-rejected', 'snapshot-tampered'])('withholds final acceptance when the statement is %s', async failure => {
    const tasks = statementTasks();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else {
        finishAssignment(action, options);
        if (action.kind === 'backtranslate' && failure === 'snapshot-tampered') fs.appendFileSync(path.join(options.workspace, 'STATEMENT.json'), ' ');
        if (action.kind === 'statement-review' && failure === 'meaning-rejected') {
          const file = path.join(options.workspace, 'RESEARCH.md');
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('"verdict":"accepted"', '"verdict":"changes_requested"'));
        }
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '12'], directory)).toBe(4);
    expect(cooperationState().statementReviews[0].status).toBe('changes_requested');
    if (failure === 'snapshot-tampered') expect(cooperationState().statementReviews[0]).toMatchObject({ summary: 'math_statement_snapshot_changed' });
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('cancels a blind translation after a live statement revision and archives its stale delivery', async () => {
    const tasks = statementTasks(), cancelled = deferred(); let translations = 0, oldWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate' && ++translations === 1) {
        oldWorkspace = options.workspace; tasks[0] = { ...tasks[0], revision: 1, informalStatement: 'REVISED_INTENT: True holds.' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'revise-statement', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await cancelled.promise;
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === oldWorkspace) cancelled.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(0);
    expect(translations).toBe(2);
    expect(cooperationState().statementReviews.map((review: any) => review.status)).toEqual(['superseded', 'accepted']);
    expect(cooperationState().deliveries.find((record: any) => record.kind === 'backtranslation').status).toBe('superseded');
    expect(cooperationState().statementReviews[1].intendedStatement).toContain('REVISED_INTENT');
  });

  it('resumes an interrupted comparison in a fresh session without repeating its saved backtranslation', async () => {
    const tasks = statementTasks(); let translations = 0, comparisons = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      if (action.kind === 'statement-review') {
        expect(options.threadId).toBeUndefined(); expect(message).toContain('The proposition True holds.');
        if (++comparisons === 1) { finishAssignment(action, options); return 'checkpoint'; }
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '3'], directory)).toBe(4);
    expect(cooperationState().statementReviews[0].status).toBe('translated'); expect(host.officialGate).not.toHaveBeenCalled();
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '9', '--resume'], directory)).toBe(0);
    expect(translations).toBe(1); expect(comparisons).toBe(2);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.turns).toBe(9); expect(state.usage).toMatchObject({ inputTokens: 9000, totalTokens: 10800 });
  });

  it('releases a paused statement session, resumes it freshly and keeps peer notifications out', async () => {
    const tasks = statementTasks(), cancelled = deferred();
    const notices: ReturnType<typeof vi.fn>[] = []; let translations = 0, oldWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate' && ++translations === 1) {
        oldWorkspace = options.workspace; tasks[0] = { ...tasks[0], status: 'paused' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'pause-statement', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await cancelled.promise;
        expect(cooperationState().statementReviews[0].status).toBe('pending');
        tasks[0] = { ...tasks[0], status: 'active' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'resume-statement', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'resume-statement' && edit.status === 'applied')).toBe(true);
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      const notify = vi.fn(); if (options.workspace.includes('/statement-reviews/')) notices.push(notify);
      return { ...await create(options), notify,
        interrupt: vi.fn(async () => { if (options.workspace === oldWorkspace) cancelled.resolve(); }) };
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(0);
    expect(translations).toBe(2); expect(cooperationState().statementReviews).toHaveLength(1);
    expect(notices.every(notify => !notify.mock.calls.length)).toBe(true);
  });

  it('invalidates an accepted statement review when integrated definitions change, while keeping proof-only changes valid', async () => {
    const tasks = statementTasks(); let translations = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') { writePlan(options.workspace, tasks); return 'completed'; }
      if (action.kind === 'backtranslate') translations++;
      finishAssignment(action, options);
      if (action.kind === 'task' && action.task.id === 'a') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'def extra : Nat := 0\ntheorem first'));
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(0);
    const reviews = cooperationState().statementReviews;
    expect(translations).toBe(2); expect(reviews.map((review: any) => review.status)).toEqual(['superseded', 'accepted']);
    expect(reviews[0].snapshotDigest).not.toBe(reviews[1].snapshotDigest); expect(reviews[0].summary).toContain('agrees');
    expect(cooperationState().deliveries.filter((record: any) => record.statementReviewId === reviews[0].id)
      .every((record: any) => record.status === 'superseded')).toBe(true);
  });

  it('builds a formal-only statement snapshot that binds definitions and dependency versions', () => {
    const tasks = statementTasks(), snapshot = () => statementSnapshot(problem, tasks[2], workspace, git(workspace, ['rev-parse', 'HEAD']), 'fixed-env',
      [{ task: tasks[0], taskDigest: taskVersion(tasks[0]) }]);
    const before = snapshot();
    expect(before.definitions.find(definition => definition.file === 'Submission.lean')!.source)
      .toContain('namespace Submission\ndef fixed : Nat := 2\ntheorem first : True\nend Submission');
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replaceAll('by sorry', 'by trivial /- PROOF_SECRET -/'));
    commitSolverSources(problem, workspace);
    expect(snapshot().snapshotDigest).toBe(before.snapshotDigest);
    expect(JSON.stringify(snapshot())).not.toContain('PROOF_SECRET'); expect(JSON.stringify(snapshot())).not.toContain('INTENT_SECRET');
    tasks[0] = { ...tasks[0], revision: 1 }; expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
    tasks[0] = { ...tasks[0], revision: 0 };
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'def additional : Nat := 3\ntheorem first'));
    commitSolverSources(problem, workspace); expect(snapshot().snapshotDigest).not.toBe(before.snapshotDigest);
  });

  const configureReferenceReports = (extra: Record<string, string[]> = {}) => {
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const result = await verify(request, options);
      if (!options.collectDeclarationReferences) return result;
      return { ...result, results: result.results.map(item => ({ ...item, declarationReferences: { statement: [],
        proof: (extra[item.theoremName.split('.').at(-1)] ?? ({ first: ['a', 'b'], second: ['first', 'a', 'b'] }[item.theoremName.split('.').at(-1)] ?? []))
          .map(name => ({ name: `Submission.${name}`, file: 'Submission.lean' })) } })) };
    });
  };

  it('keeps an integrated proof and its deliveries after an unused planned dependency is revised, including on resume', async () => {
    const tasks = planTasks(); tasks[3] = { ...tasks[3], status: 'paused' };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact b'));
        appendDelivery(options, action, { id: 'first-ready', kind: 'proof', summary: 'Only b is used', commit: commitSolverSources(problem, options.workspace) });
        await expect.poll(() => cooperationState().tasks[2].status).toBe('integrated');
        tasks[0] = { ...tasks[0], revision: 1, status: 'paused' }; tasks[3] = { ...tasks[3], status: 'active' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'unused-revision', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'unused-revision' && edit.status === 'applied')).toBe(true);
        expect(cooperationState().tasks[2].status).toBe('integrated');
        const edit = cooperationState().edits.find((record: any) => record.id === 'unused-revision');
        expect(edit).toMatchObject({ status: 'applied', receivedAt: expect.any(Number), appliedAt: expect.any(Number),
          planVersion: cooperationState().planVersion, affectedTasks: ['a'],
          recheck: { status: 'pending', tasks: [{ taskId: 'a', taskDigest: taskVersion(tasks[0]), status: 'pending' }] } });
        expect(edit.recheck.tasks[0].lastCheck).toBeUndefined();
      } else {
        if (action.kind === 'task' && action.task.id === 'second') {
          expect(action.assignment.dependencies?.map(dependency => dependency.taskId)).toEqual(['first', 'b']);
          const context = JSON.parse(fs.readFileSync(path.join(options.workspace, 'COOPERATION.json'), 'utf8'));
          expect(context.deliveries.some((record: any) => record.submissionId === 'first-ready')).toBe(true);
          expect(context.peers.find((peer: any) => peer.id === 'a').status).toBe('pending');
          expect(context.edits.find((record: any) => record.id === 'unused-revision').recheck.status).toBe('pending');
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    configureReferenceReports({ first: ['b'], second: ['first', 'b'] });
    const parallelArgs = [...args, '--workers', '2', '--max-turns', '5'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const before = cooperationState(), delivery = before.deliveries.find((record: any) => record.submissionId === 'first-ready');
    expect(before.history.map((node: any) => node.task.id)).toEqual(['a']);
    expect(delivery).toMatchObject({ status: 'verified', dependencies: [{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }] });
    expect(before.deliveries.some((record: any) => record.taskId === 'first' && record.status === 'superseded')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
    host.verify.mockClear();
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '6'], directory)).toBe(0);
    const resumed = cooperationState();
    expect(resumed.tasks.map((node: any) => node.attempts)).toEqual([1, 1, 1, 1]);
    expect(resumed.tasks[0].status).toBe('pending');
    expect(resumed.edits[0].recheck.status).toBe('pending');
    expect(resumed.deliveries.find((record: any) => record.id === delivery.id).commit).toBe(delivery.commit);
    for (const name of ['b', 'first', 'second']) expect(host.verify.mock.calls.some(([request]) =>
      request.items.length === 1 && request.items[0].theoremName === `Submission.${name}`)).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it.each(['actual', 'missing', 'whole-module'] as const)('invalidates dependent proofs and archives their old deliveries after a live revision (%s references)', async trace => {
    const tasks = planTasks(), reviewStopped = deferred();
    let reviews = 0, reviewerWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'review' && ++reviews === 1) {
        reviewerWorkspace = options.workspace; tasks[0] = { ...tasks[0], revision: 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'used-revision', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await reviewStopped.promise;
        finishAssignment(action, options);
      } else finishAssignment(action, options);
      return 'completed';
    });
    if (trace !== 'missing') configureReferenceReports(trace === 'actual'
      ? { first: ['a', 'b'], second: ['first', 'a', 'b'] }
      : { first: ['generated'], second: ['first', 'generated'] });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === reviewerWorkspace) reviewStopped.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '12'], directory)).toBe(0);
    const state = cooperationState();
    expect(state.history.map((node: any) => node.task.id)).toEqual(['a', 'first', 'second']);
    expect(state.tasks.map((node: any) => node.attempts)).toEqual([2, 1, 2, 2]);
    for (const id of ['a', 'first', 'second']) expect(state.deliveries.filter((record: any) => record.taskId === id && record.kind === 'proof')
      .map((record: any) => record.status)).toEqual(['superseded', 'verified']);
    const edit = state.edits[0];
    expect(edit).toMatchObject({ status: 'applied', affectedTasks: ['a', 'first', 'second'], recheck: { status: 'passed' } });
    for (const result of edit.recheck.tasks) {
      const proof = state.tasks.find((node: any) => node.task.id === result.taskId).integratedCheck;
      expect(result).toMatchObject({ status: 'passed', taskDigest: proof.taskDigest,
        lastCheck: { commit: proof.commit, sourceDigest: proof.sourceDigest, passed: true, conditional: false,
          receiptIds: proof.verification.results.map((receipt: any) => receipt.receiptId) } });
    }
    const events = vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event));
    expect(events.findIndex(event => event.event === 'edit_received')).toBeLessThan(events.findIndex(event => event.event === 'edit_applied'));
    expect(events.find(event => event.event === 'edit_applied').recheck.status).toBe('pending');
    if (trace === 'actual') expect(state.tasks[2].integratedCheck.references.tasks).toContainEqual({ taskId: 'a', taskDigest: taskVersion(tasks[0]) });
    expect(reviews).toBe(2); expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('records kernel-reported actual dependencies separately from the planned graph and binds their source and environment', async () => {
    const tasks = planTasks();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact b'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    configureReferenceReports({ first: ['b'], second: ['first', 'b'] });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '6'], directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const first = state.cooperation.tasks[2];
    expect(first.task.dependsOn).toEqual(['a', 'b']);
    expect(first.integratedCheck.references.tasks).toEqual([{ taskId: 'b', taskDigest: taskVersion(tasks[1]) }]);
    expect(first.integratedCheck.references).toMatchObject({ sourceCommit: first.integratedCheck.commit, environmentDigest: state.environmentDigest });
    expect(first.integratedCheck.references.inputs.map((input: any) => input.name)).toEqual(['b', 'first']);
    const live = JSON.parse(fs.readFileSync(path.join(state.worktree, 'COOPERATION.json'), 'utf8'));
    expect(live.peers[2].actualReferences.tasks).toEqual(first.integratedCheck.references.tasks);
  });

  it('rechecks a changed definition consumer while retaining the unrelated checked proof at its original receipt commit', async () => {
    const update: CooperativeTask = { id: 'update', kind: 'research', objective: 'Request a definition revision', dependsOn: ['a', 'b'], revision: 0 };
    const tasks = planTasks(); tasks.splice(2, 0, update); let leads = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, tasks);
        if (++leads === 2) {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('def selected : Nat := 2', 'def selected : Nat := 3'));
        }
      } else if (action.kind === 'task' && action.task.id === 'a') {
        finishAssignment(action, options);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('lemma a', 'def selected : Nat := 2\nlemma a'));
      } else if (action.kind === 'task' && action.task.id === 'update') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({ taskId: 'update',
          summary: 'Revise the selected definition', conclusion: 'supporting', needsDecision: true, evidenceRefs: [] }) + '\n```');
      } else finishAssignment(action, options);
      return 'completed';
    });
    configureReferenceReports({ a: ['selected'] });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '8'], directory)).toBe(0);
    expect(leads).toBe(2);
    for (const [name, count] of [['a', 3], ['b', 2]] as const)
      expect(host.verify.mock.calls.filter(([request]) => request.items.length === 1 && request.items[0].theoremName === `Submission.${name}`)).toHaveLength(count);
    const state = cooperationState();
    expect(state.tasks[0].integratedCheck.references.inputs.find((input: any) => input.name === 'selected')).toBeDefined();
    expect(state.tasks[1].integratedCheck.commit).not.toBe(state.canonicalCommit);
    const events = vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event));
    expect(events.filter(event => event.event === 'task_check_reused').map(event => event.taskId)).toContain('b');
    expect(events.filter(event => event.event === 'task_check_reused').map(event => event.taskId)).not.toContain('a');
  });

  it('revalidates archived reference evidence on resume instead of trusting an unchanged recorded footprint', async () => {
    configureCooperation(); configureReferenceReports();
    const parallelArgs = [...args, '--workers', '2', '--max-turns', '3'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    expect(cooperationState().tasks[0].integratedCheck.references).toBeDefined();
    host.verify.mockClear();
    expect(await runSolver([...parallelArgs, '--max-turns', '6', '--resume'], directory)).toBe(0);
    for (const id of ['a', 'b']) expect(host.verify.mock.calls.some(([request]) => request.items.length === 1 && request.items[0].theoremName === `Submission.${id}`)).toBe(true);
  });

  it('preserves a reviewed statement after unrelated definitions change once Lean has identified its actual statement references', async () => {
    const tasks = statementTasks();
    tasks.splice(2, 0, { id: 'update', kind: 'research', objective: 'Revise an unrelated helper definition', dependsOn: ['a', 'b'], revision: 0 });
    let leads = 0, translations = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        writePlan(options.workspace, tasks);
        if (++leads === 2) {
          expect(cooperationState().statementReviews[0].references.scope).toBe('statement');
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('theorem first', 'def unrelated : Nat := 10\ntheorem first'));
        }
      } else if (action.kind === 'task' && action.task.id === 'update') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({ taskId: 'update',
          summary: 'Add unrelated helper definition', conclusion: 'supporting', needsDecision: true, evidenceRefs: [] }) + '\n```');
      } else {
        if (action.kind === 'backtranslate') translations++;
        finishAssignment(action, options);
      }
      return 'completed';
    });
    configureReferenceReports();
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '10'], directory)).toBe(0);
    expect(translations).toBe(1); expect(cooperationState().statementReviews).toHaveLength(1);
    expect(cooperationState().statementReviews[0].status).toBe('accepted');
  });

  it('binds statement references to types and definitions while preserving them across proof-body changes', () => {
    const file = path.join(project, 'Submission.lean');
    const source = original.replace('theorem first', 'def selected : Nat := 2\nlemma supporting : True := by trivial\ntheorem first');
    fs.writeFileSync(file, source); const commit = commitSolverSources(problem, workspace);
    const references = captureProofReferences(problem, workspace, commit, { name: 'Submission.first', file: 'Submission.lean' },
      { statement: [{ name: 'Submission.selected', file: 'Submission.lean' }, { name: 'Submission.supporting', file: 'Submission.lean' }], proof: [] }, 'fixed-env', 'statement')!;
    fs.writeFileSync(file, source.replace('first : True := by sorry', 'first : True := by trivial').replace('supporting : True := by trivial', 'supporting : True := True.intro'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'fixed-env')).toBe(true);
    fs.writeFileSync(file, source.replace('selected : Nat := 2', 'selected : Nat := 3'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'fixed-env')).toBe(false);
  });

  it('tracks definition fingerprints from the Lean report, preserving proofs after unrelated changes', () => {
    const file = path.join(project, 'Submission.lean');
    let source = original.replace('theorem first', 'def used : Nat := 2\ndef unrelated : Nat := 0\ntheorem first');
    fs.writeFileSync(file, source); const commit = commitSolverSources(problem, workspace);
    const references = captureProofReferences(problem, workspace, commit, { name: 'Submission.first', file: 'Submission.lean' },
      { statement: [{ name: 'Submission.used', file: 'Submission.lean' }], proof: [] }, 'fixed-env')!;
    const unchanged = () => {
      git(workspace, ['add', 'generated/p/Submission.lean']);
      git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--allow-empty', '--no-gpg-sign', '--quiet', '-m', 'Fingerprint inputs']);
      return proofReferencesUnchanged(problem, workspace, git(workspace, ['rev-parse', 'HEAD']), references, 'fixed-env');
    };
    fs.writeFileSync(file, source.replace('unrelated : Nat := 0', 'unrelated : Nat := 1')); expect(unchanged()).toBe(true);
    fs.writeFileSync(file, source.replace('used : Nat := 2', 'used : Nat := 3')); expect(unchanged()).toBe(false);
    fs.writeFileSync(file, source.replace('first : True := by sorry', 'first : True := by trivial')); expect(unchanged()).toBe(false);
    fs.writeFileSync(file, source.replace('namespace Submission', 'namespace Submission\nset_option maxRecDepth 800')); expect(unchanged()).toBe(false);
    fs.writeFileSync(file, source.replace('theorem first', 'instance custom : Inhabited Nat := ⟨2⟩\ntheorem first')); expect(unchanged()).toBe(false);
    fs.writeFileSync(file, source);
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'new-env')).toBe(false);
  });

  it('falls back to a whole module for generated constants and rejects references outside frozen sources', () => {
    const commit = git(workspace, ['rev-parse', 'HEAD']), root = { name: 'Submission.first', file: 'Submission.lean' };
    const references = captureProofReferences(problem, workspace, commit, root,
      { statement: [], proof: [{ name: '_private.Submission.0.internal', file: 'Submission.lean' }] }, 'fixed-env')!;
    expect(references.inputs.some(input => input.file === 'Submission.lean' && !input.name)).toBe(true);
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'def unrelated : Nat := 2\ntheorem first'));
    expect(proofReferencesUnchanged(problem, workspace, commitSolverSources(problem, workspace), references, 'fixed-env')).toBe(false);
    expect(captureProofReferences(problem, workspace, commit, root, { statement: [], proof: [{ name: 'outside', file: '../outside.lean' }] }, 'fixed-env')).toBeUndefined();
  });

  it.each(['direct', 'lemma'])('checks a %s conditional parent while its lemmas run and integrates it without another model turn once they close', async method => {
    const tasks = planTasks(); tasks[2] = { ...tasks[2], conditional: true };
    let parentTurns = 0, conditionalChecks = 0;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.kind === 'lemma') {
        await expect.poll(() => cooperationState().tasks[2].status).toBe('conditional');
        expect(host.officialGate).not.toHaveBeenCalled();
        const parent = cooperationState().tasks[2];
        expect(parent.integratedCheck).toBeUndefined();
        expect(parent.proof.conditions.map((condition: any) => condition.taskId)).toEqual(['a', 'b']);
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'first') {
        if (method === 'lemma') expect(message).toContain('Research operation: bridge.');
        parentTurns++;
        expect(cooperationState().tasks.slice(0, 2).every((node: any) => node.status === 'running')).toBe(true);
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry',
          'first : True := by\n  -- Submission.a remains a reference in this comment.\n  exact And.left (And.intro Submission.a Submission.b)'));
        const commit = commitSolverSources(problem, options.workspace);
        appendDelivery(options, action, { id: 'conditional-parent', kind: 'proof', summary: 'Parent proved assuming a and b', commit });
        await expect.poll(() => cooperationState().deliveries.some((record: any) => record.submissionId === 'conditional-parent' && record.status === 'conditional')).toBe(true);
      } else finishAssignment(action, options);
      return 'completed';
    });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      if (source.includes('theorem first (a : True) (b : True)')) {
        conditionalChecks++;
        expect(source).toContain('exact And.left (And.intro a b)');
        expect(source).toContain('-- Submission.a remains a reference in this comment.');
        expect(source).not.toMatch(/lemma [ab]/u);
        expect(source).not.toContain('sorry');
      }
      return verify(request, options);
    });
    expect(await runSolver([...args, '--method', method, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(parentTurns).toBe(1); expect(conditionalChecks).toBe(1);
    expect(cooperationState().tasks.every((node: any) => node.status === 'integrated')).toBe(true);
    const records = cooperationState().deliveries.filter((record: any) => record.taskId === 'first' && record.kind === 'proof');
    expect(records.map((record: any) => record.status)).toEqual(['conditional', 'verified']);
    expect(records[0].remainingObligations).toEqual(['a', 'b']);
    expect(records[1].remainingObligations).toEqual([]);
    const source = fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8');
    expect(source).not.toContain('(a : True)');
    expect(source).toContain('And.intro Submission.a Submission.b');
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it.each(['unproved-child', 'failed-combination'])('keeps a checked conditional parent incomplete after %s', async failure => {
    const tasks = planTasks(); tasks[2] = { ...tasks[2], conditional: true };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.kind === 'lemma') {
        await expect.poll(() => cooperationState().tasks[2].status).toBe('conditional');
        finishAssignment(action, options);
        if (failure === 'unproved-child' && action.task.id === 'a') {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('a : True := by trivial', 'a : True := by sorry'));
        }
      } else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact a'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const result = await verify(request, options);
      const source = fs.readFileSync(path.join(request.projectRoot, 'Submission.lean'), 'utf8');
      return failure === 'failed-combination' && request.items[0].theoremName === 'Submission.first' && !source.includes('(a : True)')
        ? { ...result, status: 'failed', results: result.results.map((item: any) => ({ ...item, status: 'failed' })) } : result;
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '4'], directory)).toBe(4);
    expect(cooperationState().tasks[2].status).toBe(failure === 'unproved-child' ? 'conditional' : 'blocked');
    expect(cooperationState().tasks[3].attempts).toBe(0);
    expect(cooperationState().deliveries.some((record: any) => record.taskId === 'first' && record.status === 'conditional')).toBe(true);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).solver_ready_receipt_valid).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
  }, 20_000);

  it('closes a chain of conditional parents in dependency order without repeating their model calls', async () => {
    const tasks = planTasks();
    tasks[1] = { ...tasks[1], conditional: true, dependsOn: ['a'] };
    tasks[2] = { ...tasks[2], conditional: true, dependsOn: ['b'] };
    const calls: string[] = [], checkedTypes: string[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task') {
        calls.push(action.task.id);
        if (action.task.id === 'a') {
          await expect.poll(() => cooperationState().tasks.slice(1, 3).every((node: any) => node.status === 'conditional')).toBe(true);
          expect(host.officialGate).not.toHaveBeenCalled(); finishAssignment(action, options);
        } else if (action.task.id === 'b' || action.task.id === 'first') {
          const file = path.join(options.workspace, 'generated/p/Submission.lean'), source = fs.readFileSync(file, 'utf8');
          fs.writeFileSync(file, action.task.id === 'b'
            ? source.replace('theorem first', 'lemma b : True := by exact a\ntheorem first')
            : source.replace('first : True := by sorry', 'first : True := by exact b'));
        } else finishAssignment(action, options);
      } else finishAssignment(action, options);
      return 'completed';
    });
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      if (request.items[0].theoremName === 'Submission.b' && options.expectedDeclarationType) checkedTypes.push(options.expectedDeclarationType);
      return verify(request, options);
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(calls.filter(id => id === 'b')).toHaveLength(1); expect(calls.filter(id => id === 'first')).toHaveLength(1);
    expect(checkedTypes).toContain('∀ (a : True), True'); expect(checkedTypes).toContain('True');
    expect(cooperationState().deliveries.filter((record: any) => record.status === 'verified').map((record: any) => record.taskId))
      .toEqual(['a', 'b', 'first', 'second']);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('invalidates a conditional parent when a live edit changes its assumed lemma version', async () => {
    const tasks = planTasks(); tasks[2] = { ...tasks[2], conditional: true };
    let parentTurns = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a' && action.task.revision === 0) {
        await expect.poll(() => cooperationState().deliveries.some((record: any) => record.taskId === 'first' && record.status === 'conditional')).toBe(true);
        tasks[0] = { ...tasks[0], revision: 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'revise-assumption', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'revise-assumption' && edit.status === 'applied')).toBe(true);
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'a' && action.task.revision === 1) {
        await expect.poll(() => cooperationState().tasks[2].status).toBe('conditional');
        const result = cooperationState().edits[0].recheck.tasks.find((result: any) => result.taskId === 'first');
        expect(result).toMatchObject({ status: 'conditional', lastCheck: { passed: true, conditional: true } });
        expect(cooperationState().edits[0].recheck.status).toBe('pending');
        expect(host.officialGate).not.toHaveBeenCalled();
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'first') {
        parentTurns++;
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact a'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(0);
    expect(parentTurns).toBe(2);
    const state = cooperationState();
    expect(state.history.find((record: any) => record.task.id === 'first').proof.conditions)
      .toContainEqual({ taskId: 'a', taskDigest: taskVersion({ ...tasks[0], revision: 0 }) });
    expect(state.deliveries.some((record: any) => record.taskId === 'first' && record.status === 'superseded')).toBe(true);
    expect(state.tasks[2]).toMatchObject({ status: 'integrated', attempts: 2 });
    expect(state.edits[0].recheck.status).toBe('passed');
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('resumes a saved conditional parent, rechecks its archived evidence and avoids repeating the parent model call', async () => {
    const tasks = planTasks(); tasks[0] = { ...tasks[0], status: 'paused' }; tasks[1] = { ...tasks[1], status: 'paused' };
    tasks[2] = { ...tasks[2], conditional: true };
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact a'));
      } else throw new Error('Only the conditional parent should run');
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '2'], directory)).toBe(4);
    const before = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(before.cooperation.tasks[2]).toMatchObject({ status: 'conditional', attempts: 1 });
    writePlan(before.worktree, tasks.map(task => ({ ...task, status: 'active' })));
    const resumed: string[] = [];
    configureCooperation(async (action, options) => {
      if (action.kind === 'task') resumed.push(action.task.id);
      finishAssignment(action, options); return 'completed';
    });
    host.verify.mockClear();
    const result = await runSolver([...args, '--workers', '4', '--max-turns', '6', '--resume'], directory);
    expect(result, JSON.stringify(cooperationState().tasks.map((node: any) => ({ id: node.task.id, status: node.status, feedback: node.feedback })))).toBe(0);
    expect(resumed).not.toContain('first');
    expect(cooperationState().tasks[2]).toMatchObject({ status: 'integrated', attempts: 1 });
    expect(host.verify.mock.calls.filter(([request]) => {
      const source = request.items[0].theoremName === 'Submission.first' && request.items[0].expectedSourceDeclarationHash;
      return source === hashMathFormalSourceDeclaration('namespace Submission\ntheorem first (a : True) (b : True) : True := by exact a\nend Submission\n', 'Submission.first');
    })).toHaveLength(1);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('integrates helpers and starts independent consumers while a mathematical Lead decision is still running', async () => {
    const leadBusy = deferred(), consumerStarted = deferred();
    let leadTurns = 0;
    const tasks: CooperativeTask[] = [{ id: 'question', kind: 'research', objective: 'Decide a mathematical route', dependsOn: [], revision: 0 }, ...planTasks()];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') {
        if (++leadTurns === 2) { leadBusy.resolve(); await consumerStarted.promise; }
        writePlan(options.workspace, tasks);
      } else if (action.kind === 'task' && action.task.id === 'question') {
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({
          taskId: 'question', summary: 'Please choose a route', conclusion: 'inconclusive', evidenceRefs: [], needsDecision: true }) + '\n```');
      } else {
        if (action.kind === 'task' && action.task.id === 'a') await leadBusy.promise;
        if (action.kind === 'task' && action.task.id === 'first') {
          expect(leadTurns).toBe(2); consumerStarted.resolve();
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '9'], directory)).toBe(0);
    expect(cooperationState().tasks.filter((node: any) => node.task.kind !== 'research').every((node: any) => node.status === 'integrated')).toBe(true);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('checks and integrates an immutable early proof before its producer finishes the turn', async () => {
    const consumerStarted = deferred();
    let deliveredCommit: string | undefined;
    configureCooperation(async (action, options, message) => {
      if (action.kind === 'task' && action.task.id === 'a') {
        finishAssignment(action, options);
        deliveredCommit = commitSolverSources(problem, options.workspace);
        appendDelivery(options, action, { id: 'early-a', kind: 'proof', summary: 'The helper is ready', commit: deliveredCommit });
        await consumerStarted.promise;
        expect(cooperationState().tasks[0].status).toBe('integrated');
      } else {
        if (action.kind === 'task' && action.task.id === 'first') {
          expect(message).toContain('early-a');
          expect(host.officialGate).not.toHaveBeenCalled();
          consumerStarted.resolve();
        }
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(cooperationState().deliveries.find((record: any) => record.submissionId === 'early-a')).toMatchObject({
      kind: 'proof', status: 'verified', producer: 'researcher-1', commit: deliveredCommit,
      statement: 'True', remainingObligations: [], evidence: { passed: true } });
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('starts a conditional sketch before its proof dependency, steers it with public progress and retains the unproved obligation', async () => {
    const sketchStarted = deferred(), progressNotified = deferred();
    const tasks: CooperativeTask[] = [
      { ...planTasks()[0], groupId: 'alternative', sharing: 'problem' },
      { id: 'draft', kind: 'sketch', objective: 'Explore the bridge before it is proved', dependsOn: ['a'], revision: 0, groupId: 'main' },
      ...planTasks().slice(2).map(task => ({ ...task, dependsOn: task.id === 'first' ? ['draft'] : ['first'], groupId: 'main' })),
    ];
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks, routeGroups());
      else if (action.kind === 'task' && action.task.id === 'a') {
        await sketchStarted.promise;
        appendDelivery(options, action, { id: 'hint-a', kind: 'progress', summary: 'Try True.intro', remainingObligations: ['a'] });
        await progressNotified.promise;
        await expect.poll(() => cooperationState().tasks.find((node: any) => node.task.id === 'draft')?.status).toBe('completed');
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'draft') {
        const peers = JSON.parse(fs.readFileSync(path.join(options.workspace, 'COOPERATION.json'), 'utf8')).peers;
        expect(peers.find((peer: any) => peer.id === 'a')).toMatchObject({ status: 'running', owner: 'researcher-1' });
        sketchStarted.resolve(); await progressNotified.promise;
        fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-result\n' + JSON.stringify({
          taskId: 'draft', summary: 'Conditional argument using a', conclusion: 'supporting', evidenceRefs: ['hint-a'] }) + '\n```');
      } else if (action.kind === 'task') {
        expect(cooperationState().tasks[0].status).toBe('integrated');
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace(`${action.task.id} : True := by sorry`, `${action.task.id} : True := by trivial`));
      } else finishAssignment(action, options);
      return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options), notify: vi.fn(async () => {
      const snapshot = JSON.parse(fs.readFileSync(path.join(options.workspace, 'COOPERATION.json'), 'utf8'));
      if (snapshot.deliveries.some((record: any) => record.submissionId === 'hint-a')) progressNotified.resolve();
    }) }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    const records = cooperationState().deliveries;
    expect(records.find((record: any) => record.submissionId === 'hint-a')).toMatchObject({ status: 'conditional', remainingObligations: ['a'] });
    expect(records.find((record: any) => record.taskId === 'draft' && record.kind === 'research')).toMatchObject({
      status: 'conditional', dependencies: [{ taskId: 'a', taskDigest: taskVersion(tasks[0]) }], remainingObligations: ['a'] });
    expect(host.verify.mock.calls.some(([request]) => request.items.some(item => item.theoremName === 'draft'))).toBe(false);
  }, 20_000);

  it('applies live versions, cancels only the affected writer, retains over 32 historical versions and archives late deliveries', async () => {
    const oldStarted = deferred(), oldStopped = deferred();
    let oldWorkspace = '', oldInterrupts = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.id === 'a' && action.task.revision === 0) {
        oldWorkspace = options.workspace; oldStarted.resolve(); await oldStopped.promise;
        finishAssignment(action, options); return 'completed';
      }
      if (action.kind === 'task' && action.task.id === 'b') {
        await oldStarted.promise;
        const state = cooperationState(); let baseVersion = state.planVersion;
        const groups = state.groups.map((route: any) => route.group);
        const edits = Array.from({ length: 35 }, (_, index) => {
          const tasks = planTasks(); tasks[0] = { ...tasks[0], revision: index + 1 };
          const edit = { id: `revision-${index + 1}`, baseVersion, tasks, groups };
          baseVersion = mathDigest(canonicalMathJson(parseCooperationPlan(problem, edit)));
          return JSON.stringify(edit);
        });
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, edits.join('\n') + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'revision-35' && edit.status === 'applied')).toBe(true);
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === oldWorkspace) { oldInterrupts++; oldStopped.resolve(); } }) }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(0);
    const state = cooperationState();
    expect(state.edits.filter((edit: any) => edit.status === 'applied')).toHaveLength(35);
    expect(state.edits.slice(0, -1).every((edit: any) => edit.recheck.status === 'superseded')).toBe(true);
    expect(state.edits.at(-1).recheck.status).toBe('passed');
    expect(state.history.filter((node: any) => node.task.id === 'a')).toHaveLength(35);
    expect(state.history[0].task.revision).toBe(0);
    expect(state.tasks[1]).toMatchObject({ attempts: 1, status: 'integrated' });
    expect(state.tasks[0].task.revision).toBe(35);
    expect(oldInterrupts).toBe(1);
    expect(state.deliveries.find((record: any) => record.status === 'superseded' && record.taskId === 'a')).toMatchObject({
      taskDigest: taskVersion(planTasks()[0]), commit: expect.stringMatching(/^[a-f0-9]{40}$/u) });
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('pauses a live task and transfers its responsibility without invalidating independent checked work', async () => {
    const oldStarted = deferred(), oldStopped = deferred();
    let oldWorkspace = '', newOwner: string | undefined;
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.id === 'a' && action.task.ownerId === undefined) {
        oldWorkspace = options.workspace; oldStarted.resolve(); await oldStopped.promise;
        return 'interrupted';
      }
      if (action.kind === 'task' && action.task.id === 'b') {
        await oldStarted.promise;
        const tasks = planTasks(); tasks[0] = { ...tasks[0], status: 'paused' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'pause', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'pause' && edit.status === 'applied')).toBe(true);
        await expect.poll(() => JSON.parse(fs.readFileSync(path.join(oldWorkspace, 'COOPERATION.json'), 'utf8'))
          .agents.find((agent: any) => agent.id === 'researcher-1').status).toBe('idle');
        expect(cooperationState().history).toBeUndefined();
        tasks[0] = { ...tasks[0], status: 'active', ownerId: 'researcher-2' };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'transfer', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === 'transfer' && edit.status === 'applied')).toBe(true);
      }
      if (action.kind === 'task' && action.task.id === 'a') newOwner = action.assignment.workerId;
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === oldWorkspace) oldStopped.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '8'], directory)).toBe(0);
    expect(newOwner).toBe('researcher-2');
    expect(cooperationState().tasks[1]).toMatchObject({ status: 'integrated', attempts: 1 });
    expect(cooperationState().history).toBeUndefined();
    expect(cooperationState().edits.map((edit: any) => edit.recheck.status)).toEqual(['not-required', 'not-required']);
  }, 20_000);

  it('discards a review invalidated by a live edit and independently reviews the replacement version', async () => {
    const reviewStopped = deferred();
    let reviews = 0, reviewerWorkspace = '';
    configureCooperation(async (action, options) => {
      if (action.kind === 'review' && ++reviews === 1) {
        reviewerWorkspace = options.workspace;
        const tasks = planTasks(); tasks[0] = { ...tasks[0], revision: 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'during-review', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await reviewStopped.promise;
      }
      finishAssignment(action, options); return 'completed';
    });
    const create = host.createSession.getMockImplementation()!;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ ...await create(options),
      interrupt: vi.fn(async () => { if (options.workspace === reviewerWorkspace) reviewStopped.resolve(); }) }));
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '12'], directory)).toBe(0);
    expect(reviews).toBe(2);
    const records = cooperationState().deliveries.filter((record: any) => record.kind === 'review');
    expect(records.map((record: any) => record.status)).toEqual(['superseded', 'accepted']);
    expect(records[0].commit).not.toBe(records[1].commit);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('counts an early proof producer until its turn ends when enforcing route concurrency', async () => {
    let helperTurns = 0;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, planTasks(), [{ id: 'main', objective: 'One proof worker at a time', revision: 0, status: 'active', maxConcurrent: 1 }]);
      else if (action.kind === 'task' && action.task.id === 'a') {
        helperTurns++; finishAssignment(action, options);
        const commit = commitSolverSources(problem, options.workspace);
        appendDelivery(options, action, { id: 'bounded-early-proof', kind: 'proof', summary: 'Proof ready; still writing notes', commit });
        await expect.poll(() => cooperationState().tasks[0].status).toBe('integrated');
        expect(cooperationState().groups[0].busy).toBe(1);
        expect(helperTurns).toBe(1);
      } else {
        if (action.kind === 'task' && action.task.id === 'b') helperTurns++;
        finishAssignment(action, options);
      }
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(helperTurns).toBe(2);
  }, 20_000);

  it('rejects stale and cyclic human edits without stopping independent proof work', async () => {
    configureCooperation(async (action, options) => {
      if (action.kind === 'task' && action.task.id === 'a') {
        const state = cooperationState(), tasks = planTasks(); tasks[0] = { ...tasks[0], dependsOn: ['first'] };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, [
          { id: 'stale', baseVersion: 'old-version', tasks: planTasks() },
          { id: 'cycle', baseVersion: state.planVersion, tasks },
        ].map(edit => JSON.stringify(edit)).join('\n') + '\n');
        await expect.poll(() => cooperationState().edits?.length).toBe(2);
      }
      finishAssignment(action, options); return 'completed';
    });
    expect(await runSolver([...args, '--workers', '4', '--max-turns', '6'], directory)).toBe(0);
    expect(cooperationState().edits).toMatchObject([
      { id: 'stale', status: 'rejected', reason: 'math_edit_version_conflict' },
      { id: 'cycle', status: 'rejected', reason: 'math_plan_dependency_cycle' },
    ]);
    for (const edit of cooperationState().edits) {
      expect(edit.receivedAt).toEqual(expect.any(Number)); expect(edit.recheck).toBeUndefined();
    }
    expect(cooperationState().history).toBeUndefined();
  }, 20_000);

  it('revalidates an applied edit on resume and reports a failed Lean receipt instead of the archived success', async () => {
    const tasks = planTasks();
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a' && action.task.revision === 0) {
        tasks[0] = { ...tasks[0], revision: 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'rechecked-edit', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
        finishAssignment(action, options);
      } else finishAssignment(action, options);
      return 'completed';
    });
    const parallelArgs = [...args, '--workers', '2', '--max-turns', '4'];
    expect(await runSolver(parallelArgs, directory)).toBe(4);
    const before = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const check = before.cooperation.edits[0].recheck.tasks.find((result: any) => result.taskId === 'a');
    expect(check).toMatchObject({ status: 'passed', lastCheck: { passed: true } });
    const file = path.join(before.worktree, 'generated/p/Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('lemma a : True := by trivial', 'lemma a : True := by sorry'));
    expect(await runSolver([...parallelArgs, '--resume', '--max-turns', '5'], directory)).toBe(4);
    const resumed = cooperationState(), failed = resumed.edits[0].recheck.tasks.find((result: any) => result.taskId === 'a');
    expect(resumed.edits[0]).toMatchObject({ status: 'applied', recheck: { status: 'failed' } });
    expect(failed).toMatchObject({ status: 'failed', lastCheck: { passed: false, conditional: false } });
    expect(failed.lastCheck.commit).not.toBe(check.lastCheck.commit);
    expect(failed.lastCheck.receiptIds).toEqual(resumed.tasks[0].integratedCheck.verification.results.map((receipt: any) => receipt.receiptId));
    expect(resumed.tasks[1].status).toBe('integrated'); expect(host.officialGate).not.toHaveBeenCalled();
  }, 20_000);

  it('finishes a durably received edit on resume and applies repeated delivery of its id only once', async () => {
    configureCooperation();
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '1'], directory)).toBe(4);
    const file = `${output}.runtime/state.json`, state = JSON.parse(fs.readFileSync(file, 'utf8'));
    const tasks = planTasks(); tasks[0] = { ...tasks[0], revision: 1 };
    const edit = { id: 'received-before-stop', baseVersion: state.cooperation.planVersion, tasks };
    state.cooperation.edits = [{ id: edit.id, baseVersion: edit.baseVersion, status: 'received', receivedAt: 100 }];
    fs.writeFileSync(file, JSON.stringify(state));
    fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify(edit) + '\n' + JSON.stringify(edit) + '\n');
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '9', '--resume'], directory)).toBe(0);
    const resumed = cooperationState();
    expect(resumed.edits).toHaveLength(1);
    expect(resumed.edits[0]).toMatchObject({ id: edit.id, status: 'applied', receivedAt: 100, recheck: { status: 'passed' } });
    expect(resumed.history.filter((node: any) => node.task.id === 'a')).toHaveLength(1);
    const events = vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event));
    expect(events.filter(event => event.event === 'edit_applied' && event.id === edit.id)).toHaveLength(1);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('keeps the old check receipt after another edit supersedes a completed task with unchanged consumer digests', async () => {
    const tasks = planTasks(); let oldCheck: any;
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a' && action.task.revision < 2) {
        if (action.task.revision === 1) {
          finishAssignment(action, options);
          appendDelivery(options, action, { id: 'revision-one-proof', kind: 'proof', summary: 'First revised version proved',
            commit: commitSolverSources(problem, options.workspace) });
          await expect.poll(() => cooperationState().edits[0].recheck.tasks[0].status).toBe('passed');
          oldCheck = cooperationState().edits[0].recheck.tasks[0].lastCheck;
        }
        tasks[0] = { ...tasks[0], revision: action.task.revision + 1 };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: `edit-${tasks[0].revision}`, baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.some((edit: any) => edit.id === `edit-${tasks[0].revision}` && edit.status === 'applied')).toBe(true);
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '9'], directory)).toBe(0);
    const edits = cooperationState().edits;
    expect(edits[0].recheck.status).toBe('superseded');
    expect(edits[0].recheck.tasks[0]).toMatchObject({ status: 'superseded', lastCheck: oldCheck });
    expect(edits[0].recheck.tasks[1]).toMatchObject({ taskDigest: taskVersion(tasks[2]), status: 'superseded' });
    expect(edits[1].recheck.status).toBe('passed');
    expect(edits[1].recheck.tasks[0].taskDigest).not.toBe(edits[0].recheck.tasks[0].taskDigest);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('includes added formal tasks and removed task versions in an edit without checking a removed obligation', async () => {
    const tasks = planTasks(), removedDigest = taskVersion(tasks[1]);
    configureCooperation(async (action, options) => {
      if (action.kind === 'lead') writePlan(options.workspace, tasks);
      else if (action.kind === 'task' && action.task.id === 'a') {
        tasks[1] = { ...tasks[1], id: 'c', theoremName: 'Submission.c' };
        tasks[2] = { ...tasks[2], dependsOn: ['a', 'c'] };
        fs.appendFileSync(`${output}.runtime/edits.jsonl`, JSON.stringify({ id: 'replace-helper', baseVersion: cooperationState().planVersion, tasks }) + '\n');
        await expect.poll(() => cooperationState().edits?.[0]?.status).toBe('applied');
        const recheck = cooperationState().edits[0].recheck;
        expect(recheck.tasks.find((result: any) => result.taskId === 'b')).toEqual({ taskId: 'b', taskDigest: removedDigest, status: 'removed' });
        expect(recheck.tasks.find((result: any) => result.taskId === 'c')).toMatchObject({ taskDigest: taskVersion(tasks[1]), status: 'pending' });
        finishAssignment(action, options);
      } else if (action.kind === 'task' && action.task.id === 'first') {
        const file = path.join(options.workspace, 'generated/p/Submission.lean');
        fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('first : True := by sorry', 'first : True := by exact a'));
      } else finishAssignment(action, options);
      return 'completed';
    });
    expect(await runSolver([...args, '--workers', '2', '--max-turns', '6'], directory)).toBe(0);
    expect(cooperationState().edits[0]).toMatchObject({ affectedTasks: ['b', 'first', 'second', 'c'], recheck: { status: 'passed' } });
    expect(host.verify.mock.calls.some(([request]) => request.items.some(item => item.theoremName === 'Submission.b'))).toBe(false);
    expect(host.officialGate).toHaveBeenCalledOnce();
  }, 20_000);

  it('reads appended delivery lines without consuming a partial write or replaying a saved cursor', () => {
    const file = path.join(directory, 'deliveries.jsonl');
    fs.writeFileSync(file, '{"id":"one"}\n{"id":');
    const first = readDeliveryLines(file, 0);
    expect(first.lines).toEqual(['{"id":"one"}']);
    fs.appendFileSync(file, '"two"}\n');
    const second = readDeliveryLines(file, first.offset);
    expect(second.lines).toEqual(['{"id":"two"}']);
    expect(readDeliveryLines(file, second.offset).lines).toEqual([]);
    fs.truncateSync(file, 0);
    expect(() => readDeliveryLines(file, second.offset)).toThrow('math_delivery_log_invalid');
  });

  function configureLemmaRun(proveHelper = true) {
    const operations: string[] = [];
    const plan = { proofPath: 'Submission.lean', target: 'Submission.first', lemma: 'Submission.helper', type: 'True' };
    host.verify.mockImplementation(async (request, options) => {
      const source = fs.readFileSync(path.join(request.projectRoot, request.items[0].proofPath), 'utf8');
      if (request.items.length === 1 && request.items[0].theoremName === plan.target) {
        expect(source).toContain('theorem first (helper : True) : True');
        expect(source).not.toContain('theorem helper');
        expect(source).not.toContain('theorem second');
      }
      if (request.items[0].theoremName === plan.lemma) {
        expect(options).toMatchObject({ expectedDeclarationType: 'True' });
        expect(options.prepareLocalDependencies).toBeUndefined();
        expect(source).not.toContain('theorem first');
        expect(source).not.toContain('theorem second');
      }
      const valid = !source.includes('sorry') && !(options.expectedDeclarationType && source.includes('helper : False'));
      const checked = verified(request);
      return valid ? checked : { ...checked, status: 'failed', results: checked.results.map(item => ({ ...item,
        status: 'failed', error: 'Proof source contains sorry or has a different helper type.' })) };
    });
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId || 'fixture-thread',
      run: async (message: string) => {
        const operation = /Research operation: ([\w-]+)\./u.exec(message)?.[1] || 'direct';
        operations.push(operation);
        if (operation !== 'direct') {
          const file = path.join(options.workspace, 'generated/p/Submission.lean');
          const helper = operation === 'decompose' || !proveHelper ? 'sorry' : 'trivial';
          const second = operation === 'integrate-lemma' ? 'trivial' : 'sorry';
          fs.writeFileSync(file, original.replace('theorem first', `theorem helper : True := by ${helper}\ntheorem first`)
            .replace('first : True := by sorry', 'first : True := by exact helper').replace('second : True := by sorry', `second : True := by ${second}`));
          fs.writeFileSync(path.join(options.workspace, 'RESEARCH.md'), '```math-lemma\n' + JSON.stringify(plan) + '\n```\n');
        }
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    return operations;
  }

  it('checks a conditional bridge, proves its lemma, then independently accepts every original target', async () => {
    const operations = configureLemmaRun();
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '4'], directory)).toBe(0);
    expect(operations).toEqual(['direct', 'decompose', 'prove-lemma', 'integrate-lemma']);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.lemmaResearch.bridge).toMatchObject({ obligation: 'bridge', passed: true });
    expect(state.lemmaResearch.lemma).toMatchObject({ obligation: 'lemma', passed: true });
    expect(state.lemmaResearch.bridge.planDigest).toBe(state.lemmaResearch.lemma.planDigest);
    expect(state.lemmaResearch.bridge.sourceCommit).toBe(state.lemmaResearch.lemma.sourceCommit);
    expect(state.lemmaResearch.bridge.commit).not.toBe(state.lemmaResearch.bridge.sourceCommit);
    expect(state.lemmaResearch.bridge.reused).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(8);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')).not.toContain('(helper : True)');
  });

  it('does not accept a checked connection whose lemma is unproved, and shares the original turn budget', async () => {
    const operations = configureLemmaRun(false);
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '3'], directory)).toBe(4);
    expect(operations).toEqual(['direct', 'decompose', 'prove-lemma']);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.lemmaResearch.bridge.passed).toBe(true);
    expect(state.lemmaResearch.lemma.passed).toBe(false);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ turns: 3, status: 'incomplete',
      solver_ready_receipt_valid: false, completion_signal_valid: false, solution_commit: null });
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    expect(git(workspace, ['worktree', 'list', '--porcelain']).match(/^worktree /gmu)).toHaveLength(2);
  });

  it('repairs a failed connection before investing in its lemma', async () => {
    const operations = configureLemmaRun();
    const verify = host.verify.getMockImplementation()!;
    host.verify.mockImplementation(async (request, options) => {
      const checked = await verify(request, options);
      return request.items.length === 1 ? { ...checked, status: 'failed',
        results: checked.results.map(item => ({ ...item, status: 'failed', error: 'Unsolved target under the lemma premise' })) } : checked;
    });
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '3'], directory)).toBe(4);
    expect(operations).toEqual(['direct', 'decompose', 'bridge']);
    expect(host.verify.mock.calls.some(([request]) => request.items[0].theoremName === 'Submission.helper')).toBe(false);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('reconsiders a lemma route after the same failed obligation remains unchanged twice', async () => {
    const operations = configureLemmaRun(false);
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '4'], directory)).toBe(4);
    expect(operations).toEqual(['direct', 'decompose', 'prove-lemma', 'decompose']);
    const events = vi.mocked(console.log).mock.calls.map(([event]) => JSON.parse(event));
    expect(events).toContainEqual(expect.objectContaining({ event: 'research_action', operation: 'decompose', reason: 'stalled-obligation' }));
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('reuses only checked projections with the same complete inputs and environment', async () => {
    configureLemmaRun();
    const plan = { proofPath: 'Submission.lean', target: 'Submission.first', lemma: 'Submission.helper', type: 'True' };
    fs.writeFileSync(path.join(project, 'Submission.lean'), original.replace('theorem first', 'theorem helper : True := by trivial\ntheorem first')
      .replace('first : True := by sorry', 'first : True := by exact helper'));
    let source = await checkSolverProof(problem, workspace, {});
    let evidence = await checkLemmaResearch(problem, workspace, {}, new AbortController().signal, source, plan);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(false);
    const calls = host.verify.mock.calls.length;

    // Journal edits create a new candidate commit but do not alter proof inputs.
    fs.writeFileSync(path.join(workspace, 'RESEARCH.md'), 'Updated research notes\n');
    source = await checkSolverProof(problem, workspace, {});
    evidence = await checkLemmaResearch(problem, workspace, {}, new AbortController().signal, source, plan, evidence);
    expect(evidence.bridge).toMatchObject({ reused: true, sourceCommit: source.commit, sourceDigest: source.sourceDigest });
    expect(evidence.lemma).toMatchObject({ reused: true, sourceCommit: source.commit });
    expect(host.verify).toHaveBeenCalledTimes(calls + 1);

    const restored = JSON.parse(JSON.stringify(evidence));
    evidence = await checkLemmaResearch(problem, workspace, {}, new AbortController().signal, source, plan, restored);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(false);
    expect(host.verify).toHaveBeenCalledTimes(calls + 3);

    evidence = await checkLemmaResearch(problem, workspace, { LEAN_NUM_THREADS: '2' }, new AbortController().signal, source, plan, evidence);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(false);
    expect(host.verify).toHaveBeenCalledTimes(calls + 5);

    fs.writeFileSync(path.join(project, 'Submission.lean'), fs.readFileSync(path.join(project, 'Submission.lean'), 'utf8')
      .replace('first : True := by exact helper', 'first : True := by simpa using helper'));
    source = await checkSolverProof(problem, workspace, { LEAN_NUM_THREADS: '2' });
    evidence = await checkLemmaResearch(problem, workspace, { LEAN_NUM_THREADS: '2' }, new AbortController().signal, source, plan, evidence);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(true);
    expect(host.verify).toHaveBeenCalledTimes(calls + 7);

    // Mutable external libraries must be checked even when their path is unchanged.
    fs.mkdirSync(path.join(project, '.lake', 'packages'), { recursive: true });
    evidence = await checkLemmaResearch(problem, workspace, { LEAN_NUM_THREADS: '2' }, new AbortController().signal, source, plan, evidence);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(false);
    expect(host.verify).toHaveBeenCalledTimes(calls + 9);
    evidence = await checkLemmaResearch(problem, workspace, { LEAN_NUM_THREADS: '2' }, new AbortController().signal, source, plan, evidence);
    expect(evidence.bridge?.reused).toBe(false);
    expect(evidence.lemma?.reused).toBe(false);
    expect(host.verify).toHaveBeenCalledTimes(calls + 11);
  });

  it('rechecks auxiliary obligations on resume before choosing integration', async () => {
    const operations = configureLemmaRun();
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '3'], directory)).toBe(4);
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '5', '--resume'], directory)).toBe(0);
    expect(operations).toEqual(['direct', 'decompose', 'prove-lemma', 'bridge', 'integrate-lemma']);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
  });

  it('rejects an altered helper closed type instead of reusing its previous receipt', async () => {
    configureLemmaRun();
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '3'], directory)).toBe(4);
    const file = path.join(`${output}.runtime/worktree`, 'generated/p/Submission.lean');
    fs.writeFileSync(file, fs.readFileSync(file, 'utf8').replace('helper : True := by trivial', 'helper : False := by sorry'));
    const session = await host.createSession.mock.results[0].value;
    host.createSession.mockResolvedValue({ ...session, run: async () => 'completed' });
    expect(await runSolver([...args, '--method', 'lemma', '--max-turns', '4', '--resume'], directory)).toBe(4);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    expect(state.lemmaResearch.lemma.passed).toBe(false);
    expect(state.lemmaResearch.bridge.planDigest).toBe(state.lemmaResearch.lemma.planDigest);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('requires a single proposal bound to an owned original target', () => {
    const file = path.join(workspace, 'RESEARCH.md');
    expect(() => readLemmaPlan(problem, workspace)).toThrow('math_lemma_plan_missing');
    const block = '```math-lemma\n' + JSON.stringify({ proofPath: '../outside.lean', target: 'Submission.first',
      lemma: 'Submission.helper', type: 'True' }) + '\n```\n';
    fs.writeFileSync(file, block);
    expect(() => readLemmaPlan(problem, workspace)).toThrow('math_lemma_plan_invalid');
    fs.writeFileSync(file, block + block);
    expect(() => readLemmaPlan(problem, workspace)).toThrow('math_lemma_plan_requires_one_block');
  });

  it('keeps value estimates separate from stopping decisions and proof acceptance', async () => {
    const estimate = vi.fn(() => [{ operation: 'direct' as const, target: 'remaining-turns' as const,
      value: 100, uncertainty: null, calibration: 'uncalibrated' as const }]);
    const select = vi.fn((...inputs: Parameters<typeof directSolverModules.M3.select>) => {
      expect(inputs[2][0].value).toBe(100);
      expect(inputs[3]).toMatchObject({ maxTurns: 1, aborted: false });
      return { operation: 'stop' as const, reason: 'no-operation' as const };
    });
    const modules = { ...directSolverModules, M3: { ...directSolverModules.M3, estimate, version: 'test-stop-v1', select } };
    expect(await runSolver(args, directory, modules)).toBe(4);
    expect(estimate).toHaveBeenCalledTimes(1);
    expect(select).toHaveBeenCalledTimes(1);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 0,
      solution_commit: null, completion_signal_valid: false });
  });

  it('keeps the host turn limit when a replacement search policy requests more work', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    const modules = { ...directSolverModules, M3: { ...directSolverModules.M3, version: 'test-continue-v1',
      select: () => ({ operation: 'direct' as const, reason: 'continue' as const }) } };
    expect(await runSolver(args, directory, modules)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 1 });
    expect(host.verify).toHaveBeenCalledTimes(1);
  });

  it('disables total, turn and per-turn limits with zero while still requiring final acceptance', async () => {
    const timers = vi.spyOn(globalThis, 'setTimeout');
    const now = Date.now();
    const clock = vi.spyOn(Date, 'now').mockReturnValue(now);
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    let turns = 0;
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async () => {
        turns++;
        clock.mockReturnValue(now + turns * 24 * 60 * 60 * 1000);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
          original.replaceAll('by sorry', `by\n  -- attempt ${turns}\n  trivial`));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-run-seconds', '0', '--max-turns', '0', '--max-turn-seconds', '0',
      '--evaluator-timeout-seconds', '0'], directory)).toBe(0);
    expect(turns).toBe(2);
    expect(host.createSession.mock.calls[0][0].turnTimeoutMs).toBeUndefined();
    for (const [request] of host.verify.mock.calls) expect(request).toMatchObject({ timeoutMs: Infinity, batchTimeoutMs: Infinity });
    expect(timers.mock.calls.some(([, ms]) => ms === Infinity)).toBe(false);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', turns: 2 });
  });

  it('still stops an unlimited solve on SIGTERM and records the solving phase', async () => {
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread',
      run: async () => { process.emit('SIGTERM'); throw new Error('stopped'); },
      close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-run-seconds', '0', '--max-turns', '0', '--max-turn-seconds', '0'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'limit_reached', reason: 'math_run_stopped' });
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).phase).toBe('finished');
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('rejects a changed component version on resume before invoking a model', async () => {
    expect(await runSolver([...args, '--startup-only'], directory)).toBe(0);
    const prepared = fs.readFileSync(output, 'utf8');
    const modules = { ...directSolverModules, M4: { ...directSolverModules.M4, version: 'different-context-v1' } };
    expect(await runSolver([...args, '--resume'], directory, modules)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(prepared);
    expect(host.createSession).not.toHaveBeenCalled();
    expect(host.verify).not.toHaveBeenCalled();
  });

  it('requires fixed host acceptance even if a replacement evidence module reports success', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    const check = async (...inputs: Parameters<typeof checkSolverProof>) => ({ ...await checkSolverProof(...inputs), passed: true });
    const modules = { ...directSolverModules, M2: { version: 'test-false-positive-v1', check } };
    expect(await runSolver(args, directory, modules)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error',
      reason: 'math_integrated_proof_mismatch', evaluator: { status: 'skipped' } });
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it.each(['failed', 'transport_closed'])('checks a saved proof after a %s turn before independent evaluation', async status => {
    const run = vi.fn();
    const close = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      run.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        if (status === 'transport_closed') throw new Error('math_codex_transport_closed');
        return status;
      });
      return { threadId: 'fixture-thread', run, close, interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(0);
    expect(run).toHaveBeenCalledTimes(1);
    expect(close).toHaveBeenCalledBefore(host.verify);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', turns: 1,
      solver_ready_receipt_valid: true, evaluator: { official: true } });
  });

  it.each(['failed', 'transport_closed'])('saves Lean diagnostics after a %s turn and resumes from that failure', async status => {
    const diagnostic = 'Submission.lean:4:1: error: unsolved goals\n⊢ True';
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', stdoutPreview: diagnostic })) }));
    const run = vi.fn(async () => {
      if (status === 'transport_closed') throw new Error('math_codex_transport_closed');
      return status;
    });
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', run, close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(1);
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 1, solver_ready_receipt_valid: false });
    const resumed = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      resumed.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      });
      return { threadId: options.threadId!, run: resumed, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--resume', '--max-turns', '2'], directory)).toBe(0);
    expect(resumed.mock.calls[0][0]).toContain(diagnostic);
    expect(host.createSession.mock.calls[1][0].threadId).toBe('fixture-thread');
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('keeps an invalid source incomplete after a failed turn without retrying the closed session', async () => {
    const run = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      run.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replace('first : True', 'first : False'));
        return 'failed';
      });
      return { threadId: 'fixture-thread', run, close: vi.fn(), interrupt: vi.fn() };
    });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 1, solver_ready_receipt_valid: false });
  });

  it('automatically resumes a rate-limited turn with saved proof and Lean feedback', async () => {
    const diagnostic = 'Submission.lean:4:1: error: unsolved goals\n⊢ True';
    const partial = original.replace('theorem first : True := by sorry', 'theorem first : True := by trivial');
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', stdoutPreview: diagnostic })) }));
    host.createSession.mockImplementationOnce(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      lastError: 'stream disconnected before completion: Concurrency limit exceeded for account, please retry later',
      run: async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), partial);
        return 'failed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    const resumed = vi.fn();
    host.createSession.mockImplementationOnce(async (options: MathAgentOptions) => ({ threadId: options.threadId!,
      run: async (message: string) => {
        resumed(message);
        expect(fs.readFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), 'utf8')).toBe(partial);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(0);
    expect(host.createSession.mock.calls[1][0].threadId).toBe('fixture-thread');
    expect(resumed.mock.calls[0][0]).toContain(diagnostic);
    expect(host.delay).toHaveBeenCalledWith(10_000, undefined, { signal: expect.any(AbortSignal) });
    expect(host.verify).toHaveBeenCalledTimes(3);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', turns: 2 });
  });

  it.each([2, 10])('bounds rate-limit retries by both retry and turn limits (%s turns)', async maxTurns => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', stdoutPreview: 'Submission.lean:4:1: error: unsolved goals\n⊢ True' })) }));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId || 'fixture-thread',
      lastError: 'Concurrency limit exceeded for account', run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', String(maxTurns)], directory)).toBe(4);
    const turns = Math.min(maxTurns, 4);
    expect(host.createSession).toHaveBeenCalledTimes(turns);
    expect(host.delay.mock.calls.map(call => call[0])).toEqual([10_000, 20_000, 40_000].slice(0, turns - 1));
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns });
  });

  it('stops an aborted rate-limit backoff without creating another session', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', lastError: 'Concurrency limit exceeded for account',
      run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() });
    host.delay.mockImplementationOnce(async () => { process.emit('SIGTERM'); });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('limit_reached');
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).check.passed).toBe(false);
  });

  it('does not retry other provider failures', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', lastError: 'Invalid authentication',
      run: vi.fn().mockResolvedValue('failed'), close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.delay).not.toHaveBeenCalled();
  });

  it('stops interrupted turns without starting verification', async () => {
    const run = vi.fn(async () => 'interrupted');
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', run, close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(host.officialGate).not.toHaveBeenCalled();
  });

  it('starts the solve budget after preparation and blocks unusable imports before the model', async () => {
    const clock = Date.now();
    let elapsed = 0;
    vi.spyOn(Date, 'now').mockImplementation(() => clock + elapsed);
    host.prepare.mockImplementationOnce(async () => {
      elapsed += 5000;
      return { exitCode: 0, timedOut: false, phases: [] };
    });
    expect(await runSolver([...args, '--max-run-seconds', '1'], directory)).toBe(0);
    expect(host.createSession.mock.calls[0][0].turnTimeoutMs).toBe(180000);
    const rejected = path.join(directory, 'rejected.json');
    host.prepare.mockResolvedValueOnce({ exitCode: 1, timedOut: false, phases: [], stderr: 'error: unknown module prefix Mathlib' });
    expect(await runSolver([...args, '--output', rejected], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(`${rejected}.runtime/state.json`, 'utf8')).phase).toBe('finished');
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('error: unknown module prefix Mathlib'));
  });

  it('reports the pinned compiler mismatch before starting dependencies or a model', async () => {
    const diagnostics = 'Pinned Lean version mismatch: expected 4.31.0, found 4.30.0. Check PATH and ELAN_HOME.';
    host.readiness.mockReturnValue({ status: 'invalid', diagnostics });
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.prepare).not.toHaveBeenCalled();
    expect(host.createSession).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/toolchain-readiness.json`, 'utf8'))).toMatchObject({ status: 'invalid', diagnostics });
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining(diagnostics));
  });

  it('repairs stale package links for every worker on resume before checking dependencies', async () => {
    host.packages = path.join(directory, 'pinned-packages');
    fs.mkdirSync(host.packages);
    const startup = [...args, '--workers', '4', '--startup-only'];
    expect(await runSolver(startup, directory)).toBe(0);
    const state = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'));
    const obsolete = path.join(directory, 'obsolete-packages');
    fs.mkdirSync(obsolete);
    for (const [index, worker] of state.workers.entries()) {
      const packages = path.join(worker.worktree, 'generated/p/.lake/packages');
      fs.unlinkSync(packages);
      fs.symlinkSync(index % 2 ? obsolete : path.join(directory, 'deleted-packages'), packages, 'dir');
    }
    host.prepare.mockClear().mockImplementation(async input => {
      expect(fs.realpathSync(path.join(input.projectRoot, '.lake/packages'))).toBe(host.packages);
      return { exitCode: 0, timedOut: false, phases: [] };
    });
    expect(await runSolver([...startup, '--resume'], directory)).toBe(0);
    expect(host.prepare).toHaveBeenCalledTimes(4);
    expect(host.freeze.mock.calls.at(-1)![2].deadlineAt).toBeGreaterThan(Date.now());
    expect(host.createSession).not.toHaveBeenCalled();
  });

  it('checks a timed checkpoint and resumes with host diagnostics', async () => {
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', stdoutPreview: 'Submission.lean:4:1: error: unsolved goals' })) }));
    const messages: string[] = [];
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async (message: string) => {
        messages.push(message);
        if (messages.length === 1) return 'checkpoint';
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '2'], directory)).toBe(0);
    expect(messages).toHaveLength(2);
    expect(messages[1]).toContain('unsolved goals');
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('preserves unrelated session errors as runtime failures', async () => {
    host.createSession.mockResolvedValueOnce({ threadId: 'fixture-thread', run: vi.fn().mockRejectedValue(new Error('unexpected failure')),
      close: vi.fn(), interrupt: vi.fn() });
    expect(await runSolver(args, directory)).toBe(1);
    expect(host.verify).not.toHaveBeenCalled();
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', reason: 'unexpected failure' });
  });

  it('keeps repeated unchanged rejections incomplete without recompiling the same commit', async () => {
    host.verify.mockImplementation(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', error: 'open goals',
        stdoutPreview: 'Submission.lean:4:1: error: unsolved goals\n⊢ True' })) }));
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(4);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 3, evaluator: { status: 'skipped' } });
    expect(host.verify).toHaveBeenCalledTimes(1);
    expect(console.log).toHaveBeenCalledWith(expect.stringContaining('"reused":true'));
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
  });

  it.each([false, true])('feeds deduplicated Lean goals back and detects stalled proof work (source changed: %s)', async changed => {
    const messages: string[] = [];
    const leanError = 'Submission.lean:12:4: error: linarith failed to find a contradiction\nx : Nat\nh : 0 < x\n|- False\n';
    host.verify.mockImplementation(async request => messages.length <= 2
      ? { ...verified(request), status: 'failed', results: verified(request).results.map(item => ({ ...item,
        status: 'failed', error: 'lean_compilation_failed', stdoutPreview:
          'Submission.lean:1:1: warning: unused variable\n' + leanError })) }
      : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async (message: string) => {
        messages.push(message);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry',
          changed || messages.length === 3 ? `by\n  -- attempt ${messages.length}\n  trivial` : 'by trivial'));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '3'], directory)).toBe(0);
    expect(messages).toHaveLength(3);
    expect(messages[1].split(leanError.trim())).toHaveLength(2);
    expect(messages[1]).toContain('Submission.first: failed');
    expect(messages[1]).toContain('Submission.second: failed');
    expect(messages[1]).not.toContain('unused variable');
    expect(messages[1]).toContain('subtype .property');
    expect(messages[2]).toContain(changed ? 'same Lean errors and goal contexts' : 'proof source is unchanged');
    expect(host.verify).toHaveBeenCalledTimes(changed ? 4 : 3);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('evaluated_passed');
  });

  it('bounds repair feedback in bytes while retaining the earliest error and its context', async () => {
    const check = await checkSolverProof(problem, workspace, {});
    check.verification.results = check.verification.results.map(item => ({ ...item, status: 'failed',
      stdoutPreview: 'Submission.lean:2:3: error: unsolved goals\nh : True\n|- True\n' + '\u03b1'.repeat(20_000) }));
    const feedback = solverProofFeedback({ ...check, passed: false });
    expect(Buffer.byteLength(feedback)).toBeLessThanOrEqual(16_000);
    expect(feedback).toContain('h : True\n|- True');
    expect(feedback).toContain('[truncated;');
  });

  it('remembers a failure that recurs after another goal without bypassing acceptance', async () => {
    const messages: string[] = [];
    host.verify.mockImplementation(async request => messages.length <= 3
      ? { ...verified(request), status: 'failed', results: verified(request).results.map(item => ({ ...item,
        status: 'failed', stdoutPreview: `Submission.lean:${messages.length + 3}:1: error: unsolved goals\n⊢ ${messages.length === 2 ? 'False' : 'True'}` })) }
      : verified(request));
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: 'fixture-thread',
      run: async (message: string) => {
        messages.push(message);
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'),
          original.replaceAll('by sorry', `by\n  -- attempt ${messages.length}\n  trivial`));
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--max-turns', '4'], directory)).toBe(0);
    expect(messages[2]).not.toContain('already occurred');
    expect(messages[3]).toContain('already occurred 1 time(s)');
    const failures = JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8')).failures;
    expect(failures.map((item: { attempts: number }) => item.attempts)).toEqual([1, 2]);
    expect(host.verify).toHaveBeenCalledTimes(5);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
  });

  it('bounds failure memory and excludes success and missing Lean diagnostics', async () => {
    const accepted = await checkSolverProof(problem, workspace, {});
    let history: ReturnType<typeof rememberSolverFailure> = [];
    for (let index = 0; index < 40; index++) {
      const failed = { ...accepted, passed: false, verification: { ...accepted.verification, status: 'failed' as const,
        results: accepted.verification.results.map(item => ({ ...item, status: 'failed' as const,
          stdoutPreview: `Submission.lean:4:1: error: unsolved goals\n⊢ P${index}` })) } };
      history = rememberSolverFailure(failed, history);
    }
    expect(history).toHaveLength(32);
    expect(JSON.stringify(history)).not.toContain('unsolved goals');
    expect(rememberSolverFailure(accepted, history)).toEqual(history);
    const opaque = { ...accepted, passed: false, verification: { ...accepted.verification, status: 'failed' as const,
      results: accepted.verification.results.map(item => ({ ...item, status: 'failed' as const, stdoutPreview: 'Process exited' })) } };
    expect(rememberSolverFailure(opaque, history)).toEqual(history);
    expect(solverProofFeedback(opaque, undefined, history)).not.toContain('already occurred');
  });

  it('resumes an incomplete proof with its saved Lean feedback', async () => {
    const diagnostic = 'Submission.lean:4:1: error: unsolved goals\nh : True\n|- True';
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed', error: 'open goals', stdoutPreview: diagnostic })) }));
    expect(await runSolver(args, directory)).toBe(4);
    const messages: string[] = [];
    host.createSession.mockImplementation(async (options: MathAgentOptions) => ({ threadId: options.threadId!,
      run: async (message: string) => {
        messages.push(message);
        return 'completed';
      }, close: vi.fn(), interrupt: vi.fn() }));
    expect(await runSolver([...args, '--resume', '--max-turns', '2'], directory)).toBe(0);
    expect(messages).toHaveLength(1);
    expect(messages[0]).toContain(diagnostic);
    expect(messages[0]).toContain('Submission.first: failed');
    expect(messages[0]).toContain('already occurred 1 time(s)');
    expect(host.createSession.mock.calls[1][0].threadId).toBe('fixture-thread');
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).turns).toBe(2);
    expect(host.verify).toHaveBeenCalledTimes(3);
  });

  it('offers verified library lookup to the solver and rejects changed retrieval identities on resume', async () => {
    const library = path.join(project, '.lake/packages/mathlib/Mathlib/Order/Basic.lean');
    fs.mkdirSync(path.dirname(library), { recursive: true });
    fs.writeFileSync(library, 'lemma library_helper : True := by trivial');
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), url: 'https://github.com/leanprover-community/mathlib4' },
    ] }));
    git(workspace, ['add', '--force', '--', 'generated/p/.lake/packages', 'generated/p/lake-manifest.json']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Pinned library fixture']);
    const file = path.join(directory, 'corpus.json');
    fs.writeFileSync(file, JSON.stringify(await createMathRetrievalCorpus(project, ['mathlib'])));
    vi.stubEnv('DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS', file);
    vi.stubEnv('DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256', mathDigest(fs.readFileSync(file)));
    expect(await runSolver(args, directory)).toBe(0);
    const options = host.createSession.mock.calls[0][0] as MathAgentOptions;
    expect(options.instructions).toContain('search-lean --workspace');
    expect(options.instructions).toContain('--sha256');
    expect(options.instructions).toContain(path.join(`${output}.runtime/worktree`, 'generated/p'));
    fs.appendFileSync(file, '\n');
    expect(await runSolver([...args, '--resume'], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8')).status).toBe('evaluated_passed');
  });

  it.each(['unchanged', 'corpus', 'source'])('automatically enables frozen Mathlib lookup and validates it on resume (%s)', async change => {
    const assertCorpus = vi.spyOn(retrievalCorpus, 'assertMathRetrievalCorpus');
    host.freeze.mockImplementation(async (root: string) => {
      expect(fs.existsSync(path.join(root, '.lake/package-overrides.json'))).toBe(false);
      return { environmentValue: 'fixture', dispose: vi.fn() };
    });
    host.packages = path.join(directory, 'packages');
    const library = path.join(host.packages, 'mathlib/Mathlib/Algebra/Basic.lean');
    fs.mkdirSync(path.dirname(library), { recursive: true });
    fs.writeFileSync(library, 'namespace Finset\nlemma sum_bound : True := by trivial\nend Finset\n');
    fs.writeFileSync(path.join(host.packages, 'mathlib/lakefile.toml'), 'name = "mathlib"\n');
    fs.writeFileSync(path.join(project, 'lake-manifest.json'), JSON.stringify({ packages: [
      { name: 'mathlib', rev: 'a'.repeat(40), url: 'https://github.com/leanprover-community/mathlib4' },
    ] }));
    git(workspace, ['add', '--', 'generated/p/lake-manifest.json']);
    git(workspace, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Pinned library']);
    host.verify.mockImplementationOnce(async request => ({ ...verified(request), status: 'failed',
      results: verified(request).results.map(item => ({ ...item, status: 'failed' })) }));
    expect(await runSolver(args, directory)).toBe(4);
    const options = host.createSession.mock.calls[0][0] as MathAgentOptions;
    const corpusFile = options.environment!.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS!;
    expect(options.instructions).toContain('search-lean --workspace');
    expect(options.instructions).toContain(corpusFile);
    expect(options.environment!.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256).toBe(mathDigest(fs.readFileSync(corpusFile)));
    expect(JSON.parse(fs.readFileSync(corpusFile, 'utf8')).sources).toHaveLength(1);
    expect(assertCorpus).not.toHaveBeenCalled();
    if (change === 'corpus') fs.appendFileSync(corpusFile, '\n');
    if (change === 'source') fs.appendFileSync(library, '\n-- changed');
    expect(await runSolver([...args, '--resume', '--max-turns', '2'], directory)).toBe(change === 'unchanged' ? 0 : 1);
    if (change !== 'unchanged') {
      expect(JSON.parse(fs.readFileSync(output, 'utf8')).reason).toBe(
        change === 'corpus' ? 'math_corpus_identity_changed' : 'math_corpus_source_changed'
      );
      expect(host.createSession).toHaveBeenCalledTimes(1);
    } else {
      expect(host.createSession).toHaveBeenCalledTimes(2);
      expect(host.createSession.mock.calls[1][0].environment.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256)
        .toBe(options.environment!.DEEPSCIENTIST_MATH_RETRIEVAL_CORPUS_SHA256);
    }
    expect(assertCorpus).toHaveBeenCalledTimes(change === 'corpus' ? 0 : 1);
  });

  it('resumes a saved passing check before evaluation without another model session or turn', async () => {
    const close = vi.fn().mockRejectedValueOnce(new Error('session close failed'));
    const run = vi.fn();
    host.createSession.mockImplementation(async (options: MathAgentOptions) => {
      run.mockImplementation(async () => {
        fs.writeFileSync(path.join(options.workspace, 'generated/p/Submission.lean'), original.replaceAll('by sorry', 'by trivial'));
        return 'completed';
      });
      return { threadId: 'fixture-thread', run, close, interrupt: vi.fn() };
    });
    expect(await runSolver(args, directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(`${output}.runtime/state.json`, 'utf8'))).toMatchObject({ phase: 'finished', check: { passed: true } });
    expect(git(workspace, ['rev-parse', 'HEAD'])).toBe(problem.baseCommit);
    expect(host.officialGate).not.toHaveBeenCalled();
    expect(await runSolver([...args, '--resume'], directory)).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(run).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'evaluated_passed', turns: 1 });
  });

  it.each([false, true])('invalidates a changed passing checkpoint without starting a session when turns are exhausted (committed: %s)', async committed => {
    host.officialGate.mockRejectedValueOnce(new Error('offline evaluator'));
    expect(await runSolver(args, directory)).toBe(1);
    const worktree = path.join(`${output}.runtime`, 'worktree');
    fs.writeFileSync(path.join(worktree, 'generated/p/Submission.lean'), original);
    if (committed) {
      git(worktree, ['add', '--', 'generated/p/Submission.lean']);
      git(worktree, ['-c', 'user.name=Fixture', '-c', 'user.email=fixture@localhost', 'commit', '--no-gpg-sign', '--quiet', '-m', 'Changed proof']);
    }
    expect(await runSolver([...args, '--resume'], directory)).toBe(4);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.verify).toHaveBeenCalledTimes(2);
    expect(host.officialGate).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'incomplete', turns: 1,
      solution_commit: null, solver_ready_receipt_valid: false, evaluator: { status: 'skipped' } });
  });

  it('resumes an interrupted evaluation without another model turn', async () => {
    host.officialGate.mockRejectedValueOnce(new Error('offline evaluator'));
    expect(await runSolver(args, directory)).toBe(1);
    expect(await runSolver([...args, '--resume'], directory)).toBe(0);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(host.officialGate).toHaveBeenCalledTimes(2);
  });

  it('reports evaluator timeouts as infrastructure errors', async () => {
    host.officialGate.mockResolvedValue({ comparison: { status: 'failed', timedOut: true } });
    expect(await runSolver(args, directory)).toBe(1);
    expect(JSON.parse(fs.readFileSync(output, 'utf8'))).toMatchObject({ status: 'runtime_error', evaluator: { status: 'error' } });
  });

  it('prepares without a model and rejects changed resume identities without overwriting the result', async () => {
    expect(await runSolver([...args, '--startup-only'], directory)).toBe(0);
    expect(host.createSession).not.toHaveBeenCalled();
    const receipt = fs.readFileSync(output, 'utf8');
    const changed = args.map((value, index) => args[index - 1] === '--task-file' ? path.join(directory, 'changed.md') : value);
    fs.writeFileSync(path.join(directory, 'changed.md'), 'Change the task');
    expect(await runSolver([...changed, '--resume'], directory)).toBe(1);
    expect(fs.readFileSync(output, 'utf8')).toBe(receipt);
  });
});
