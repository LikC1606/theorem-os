import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { canonicalMathProblemStatementPayloads, type MathProblemContract } from '../src/math/contracts';
import { LEAN_EVAL_BENCHMARK_COMMIT } from '../src/math/leanEvalCatalogAdapter';
import { mathDigest } from '../src/math/mathRuntimeIo';
import { hashMathFormalSourceDeclaration, type MathematicsVerifierBatchRequest, type MathematicsVerifierBatchResult } from '../src/math/verifier';
import { readSolverProblem, assertSolverSources, assertSolverProjectSources, git, type SolverProblem } from '../src/solver/problem';
import { checkSolverProof } from '../src/solver/modules/evidence';
import { directSolverModules } from '../src/solver/modules';
import { runSolver } from '../src/solver/run';
import { rememberSolverFailure, solverProofFeedback } from '../src/solver/feedback';
import { createMathRetrievalCorpus } from '../src/math/mathRetrievalCorpus';
import * as retrievalCorpus from '../src/math/mathRetrievalCorpus';
import type { MathAgentOptions } from '../src/runtime/codexSession';
import { checkLemmaResearch, readLemmaPlan } from '../src/solver/lemma';
import { readCooperativePlan, readCooperationPlan, type CooperativeAction, type CooperativeTask, type RouteGroup } from '../src/solver/cooperation';

const host = vi.hoisted(() => ({ verify: vi.fn(), createSession: vi.fn(), officialGate: vi.fn(), build: vi.fn(), delay: vi.fn(),
  prepare: vi.fn(), freeze: vi.fn(), packages: undefined as string | undefined }));
vi.mock('../src/math/leanDiagnostics', async importOriginal => ({
  ...await importOriginal<typeof import('../src/math/leanDiagnostics')>(), runLeanDiagnostics: host.prepare,
}));
vi.mock('node:timers/promises', async importOriginal => ({
  ...await importOriginal<typeof import('node:timers/promises')>(), setTimeout: host.delay,
}));
vi.mock('../src/math/mathBuildManifest', () => ({ readMathBuildManifest: host.build }));
vi.mock('../src/math/leanToolchainReadiness', () => ({ checkResolvedLeanToolchainReadiness: () => ({ status: 'ready' }) }));
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

  it('returns research findings to the Lead as advice without accepting them as proof', async () => {
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
    expect(leadTurns).toBe(2);
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
    host.prepare.mockResolvedValueOnce({ exitCode: 1, timedOut: false, phases: [] });
    expect(await runSolver([...args, '--output', rejected], directory)).toBe(1);
    expect(host.createSession).toHaveBeenCalledTimes(1);
    expect(JSON.parse(fs.readFileSync(`${rejected}.runtime/state.json`, 'utf8')).phase).toBe('finished');
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
